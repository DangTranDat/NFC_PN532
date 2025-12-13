/*
  ESP32 + PN532 (SPI) – eMRTD/CCCD
  BAC → Secure Messaging → SELECT/READ EF.COM, DG1, DG2
  DG2 streamer: tăng tốc bằng cách tăng Le + tăng buffer response (bạn đã patch lib)

  BẢN NÀY ĐÃ CHÈN:
    (A) Unwrap R-APDU đệ quy (0x77/0x7C)
    (B) SELECT ưu tiên MAC-only trước (fallback ENC+MAC)
    (C) DG2: PROBE Le lớn → STREAM với Le tối ưu

  Lưu ý quan trọng:
    - respLen trong Adafruit_PN532 API là uint8_t ⇒ tối đa 255.
    - Vì vậy mọi nơi phải set respLen = 0xFF (KHÔNG dùng sizeof(300) vì sẽ tràn).
*/

#include <Arduino.h>
#include <SPI.h>
#include <PN532.h>
#include <Adafruit_PN532.h>
#include <vector>
#include <functional>

// DES tự cài
#include "DES.h"

// SHA-1 (ESP32 core có mbedTLS)
#include <mbedtls/sha1.h>

// ======================= CẤU HÌNH PHẦN CỨNG (SPI) =======================
#define PN532_SCK   18
#define PN532_MISO  19
#define PN532_MOSI  23
#define PN532_SS     5

Adafruit_PN532 nfc(PN532_SS);

// ======================= MRZ INPUT =======================
// String MRZINFO = "203021621303090352809034";
// String MRZINFO = "201008914301061202606129";
String MRZINFO = "179041213079082083908200";
// ======================= DG2 SPEED TUNING =======================
// Danh sách Le thử từ lớn → nhỏ (đề xuất thực chiến)
static const uint8_t DG2_LE_CANDIDATES[] = {
  0xDF, 0xD0, 0xC0, 0xA0, 0x80, 0x60, 0x40, 0x30, 0x23, 0x17
};

// Số lần cho phép re-BAC khi stream DG2 bị rớt
static const int DG2_RESYNC_BUDGET = 2;

// Delay giữa 2 lệnh READ DG2 (0 = nhanh nhất; nếu rớt nhiều thì tăng 200~1000us)
static const uint32_t DG2_INTER_CMD_DELAY_US = 0;

// Nếu muốn benchmark tốc độ NFC thuần (không bị Serial HEX làm chậm),
// set false để KHÔNG dump HEX ảnh (chỉ đếm bytes).
static const bool DG2_DUMP_HEX = true;

// ======================= TIỆN ÍCH IN/CHỜ =======================
static bool g_dumping_hex = false;

static bool waitForIso14443_4() {
  for (int i = 0; i < 60; ++i) {
    if (nfc.inListPassiveTarget()) {
      Serial.println("Đã inlisted thẻ. Thử InPSL lên 424 kbps...");
      if (nfc.inPSL(1, 0x02, 0x02)) {
        Serial.println("InPSL 424 kbps: OK");
      } else {
        Serial.println("InPSL 424 kbps FAIL → giữ 106 kbps.");
      }
      return true;
    }
    delay(500);
  }
  return false;
}

static void printHex(const uint8_t* buf, size_t len, const char* label = nullptr) {
  if (label) { Serial.print(label); if (*label) Serial.println(); }
  for (size_t i = 0; i < len; i++) {
    if (i && (i % 16 == 0)) Serial.println();
    if (buf[i] < 0x10) Serial.print("0");
    Serial.print(buf[i], HEX);
    Serial.print(" ");
  }
  Serial.println();
}

static void randomBytes(uint8_t* out, size_t len) {
  for (size_t i = 0; i < len; ++i) out[i] = (uint8_t)(esp_random() & 0xFF);
}

// ======================= SHA-1 shim =======================
static void sha1_20(const uint8_t* msg, size_t len, uint8_t out20[20]) {
  mbedtls_sha1_context ctx; mbedtls_sha1_init(&ctx);
  mbedtls_sha1_starts(&ctx);
  mbedtls_sha1_update(&ctx, msg, len);
  mbedtls_sha1_finish(&ctx, out20);
  mbedtls_sha1_free(&ctx);
}

// ======================= DES odd parity helpers =======================
static uint8_t oddParity(uint8_t b) {
  uint8_t x = b; x ^= x >> 4; x ^= x >> 2; x ^= x >> 1;
  if ((x & 1) == 0) b ^= 1;
  return b;
}
static void desParityAdjust16(uint8_t key16[16]) { for (int i = 0; i < 16; i++) key16[i] = oddParity(key16[i]); }

// ======================= Kseed, Kenc, Kmac =======================
static void deriveKseed(const String& mrzInfo, uint8_t Kseed[16]) {
  uint8_t h20[20];
  sha1_20((const uint8_t*)mrzInfo.c_str(), mrzInfo.length(), h20);
  memcpy(Kseed, h20, 16);
}
static void deriveKencKmac(const uint8_t Kseed[16], uint8_t Kenc[16], uint8_t Kmac[16]) {
  uint8_t tmp[20];
  {
    uint8_t buf[20]; memcpy(buf, Kseed, 16);
    buf[16]=0; buf[17]=0; buf[18]=0; buf[19]=1;
    sha1_20(buf, sizeof(buf), tmp);
    memcpy(Kenc, tmp, 16);
    desParityAdjust16(Kenc);
  }
  {
    uint8_t buf[20]; memcpy(buf, Kseed, 16);
    buf[16]=0; buf[17]=0; buf[18]=0; buf[19]=2;
    sha1_20(buf, sizeof(buf), tmp);
    memcpy(Kmac, tmp, 16);
    desParityAdjust16(Kmac);
  }
}
static void key16_to_key24(const uint8_t key16[16], uint8_t key24[24]) { memcpy(key24, key16, 16); memcpy(key24+16, key16, 8); }

// ======================= 3DES-CBC (EDE2) =======================
static bool ede2_cbc_encrypt(const uint8_t key16[16], const uint8_t iv[8], const uint8_t* in, size_t inLen, uint8_t* out) {
  if (!in || !out || (inLen % 8) != 0) return false;
  uint8_t key24[24]; key16_to_key24(key16, key24);
  DES des; uint8_t prev[8]; memcpy(prev, iv, 8);
  for (size_t off = 0; off < inLen; off += 8) {
    uint8_t block[8];
    for (int i=0;i<8;i++) block[i] = in[off+i] ^ prev[i];
    des.tripleEncrypt(out+off, block, key24);
    memcpy(prev, out+off, 8);
  }
  return true;
}
static bool ede2_cbc_decrypt(const uint8_t key16[16], const uint8_t iv[8], const uint8_t* in, size_t inLen, uint8_t* out) {
  if (!in || !out || (inLen % 8) != 0) return false;
  uint8_t key24[24]; key16_to_key24(key16, key24);
  DES des; uint8_t prev[8]; memcpy(prev, iv, 8);
  for (size_t off = 0; off < inLen; off += 8) {
    uint8_t tmp[8];
    des.tripleDecrypt(tmp, (void*)(in+off), key24);
    for (int i=0;i<8;i++) out[off+i] = tmp[i] ^ prev[i];
    memcpy(prev, in+off, 8);
  }
  return true;
}

// ======================= Retail MAC (ISO 9797-1 Alg.3) =======================
static bool retail_mac_alg3(const uint8_t Kmac[16], const uint8_t* data, size_t len, uint8_t mac[8]) {
  size_t pad = 8 - ((len + 1) % 8);
  size_t total = len + 1 + (pad % 8);
  uint8_t* buf = (uint8_t*)malloc(total); if (!buf) return false;
  memcpy(buf, data, len);
  buf[len] = 0x80;
  memset(buf + len + 1, 0x00, total - len - 1);

  DES des; uint8_t chain[8] = {0}; uint8_t outb[8], blk[8];
  for (size_t off = 0; off < total; off += 8) {
    for (int i=0;i<8;i++) blk[i] = buf[off+i] ^ chain[i];
    des.encrypt(outb, blk, Kmac);
    memcpy(chain,outb,8);
  }
  uint8_t t[8];
  des.decrypt(t, chain, Kmac + 8);
  des.encrypt(mac, t, Kmac);
  free(buf);
  return true;
}

// ======================= APDU qua PN532 =======================
// NOTE: outLen/respLen là uint8_t → tối đa 255.
static bool apdu_ex(const uint8_t* cmd, uint8_t cmdLen, uint8_t* resp, uint8_t* respLen, uint16_t* sw, uint8_t* rawLen /*optional*/) {
  uint8_t out[255];
  uint8_t outLen = (uint8_t)sizeof(out);   // 255
  bool ok = nfc.inDataExchange((uint8_t*)cmd, cmdLen, out, &outLen);
  if (rawLen) *rawLen = outLen;
  if (!ok) return false;
  if (outLen < 2) return false;

  uint16_t sw12 = ((uint16_t)out[outLen - 2] << 8) | out[outLen - 1];
  if (sw) *sw = sw12;

  uint8_t dataLen = outLen - 2;
  if (resp && respLen) {
    uint8_t cpy = (*respLen < dataLen) ? *respLen : dataLen;
    memcpy(resp, out, cpy);
    *respLen = cpy;
  }
  return (sw12 == 0x9000);
}
static bool apdu(const uint8_t* cmd, uint8_t cmdLen, uint8_t* resp, uint8_t* respLen, uint16_t* sw = nullptr) {
  return apdu_ex(cmd, cmdLen, resp, respLen, sw, nullptr);
}

// ============================ GET RESPONSE ============================
static bool get_response(uint8_t Le, uint8_t* out, uint8_t* outLen) {
  uint8_t cmd[] = { 0x00, 0xC0, 0x00, 0x00, Le };
  uint16_t sw = 0; uint8_t raw = 0;
  *outLen = 0xFF; // quan trọng
  return apdu_ex(cmd, sizeof(cmd), out, outLen, &sw, &raw);
}

// ======================= rotate helpers (debug BAC) =======================
static void rotByteLeft8(const uint8_t in[8], uint8_t out[8]) { for (int i = 0; i < 8; ++i) out[i] = in[(i + 1) & 7]; }
static void rotBitLeft64(const uint8_t in[8], uint8_t out[8]) {
  for (int i = 0; i < 8; ++i) {
    uint8_t prev = in[(i + 7) & 7];
    out[i] = (uint8_t)((in[i] << 1) | (prev >> 7));
  }
}

// ======================= Secure Messaging helpers =======================
static bool USE_M_WITH_LC   = false;
static bool USE_HDR_PAD_80  = true;

static inline void ssc_inc(uint8_t ssc[8]) { for (int i=7;i>=0;--i){ if(++ssc[i]!=0) break; } }
static size_t pad80(const uint8_t* in, size_t inLen, uint8_t* out) {
  memcpy(out, in, inLen);
  out[inLen] = 0x80;
  size_t pad = (8 - ((inLen + 1) % 8)) % 8;
  memset(out + inLen + 1, 0x00, pad);
  return inLen + 1 + pad;
}

static bool sm_mac_alg3(const uint8_t Kmac[16], const uint8_t ssc[8], const uint8_t* M, size_t Mlen, uint8_t mac[8]) {
  size_t tot = 8 + Mlen;
  uint8_t* buf = (uint8_t*)malloc(tot); if (!buf) return false;
  memcpy(buf, ssc, 8);
  memcpy(buf + 8, M, Mlen);
  bool ok = retail_mac_alg3(Kmac, buf, tot, mac);
  free(buf);
  return ok;
}

static size_t tlv_write_len(uint8_t* out, size_t L) {
  if (L <= 0x7F) { out[0]=(uint8_t)L; return 1; }
  if (L <= 0xFF) { out[0]=0x81; out[1]=(uint8_t)L; return 2; }
  out[0]=0x82; out[1]=(uint8_t)(L>>8); out[2]=(uint8_t)L; return 3;
}

static size_t build_DO87(const uint8_t Kenc[16], const uint8_t* plain, size_t plen, uint8_t* out) {
  if (plen == 0) return 0;
  uint8_t tmp[1024]; size_t plen_p = pad80(plain, plen, tmp);
  uint8_t ciph[1024]; uint8_t zeroIV[8]={0};
  if (!ede2_cbc_encrypt(Kenc, zeroIV, tmp, plen_p, ciph)) return 0;
  size_t L = 1 + plen_p;
  size_t off = 0;
  out[off++] = 0x87;
  off += tlv_write_len(out + off, L);
  out[off++] = 0x01;
  memcpy(out + off, ciph, plen_p);
  off += plen_p;
  return off;
}
static size_t build_DO85(const uint8_t* plain, size_t plen, uint8_t* out) {
  if (!plain || plen == 0) return 0;
  size_t off=0;
  out[off++]=0x85;
  off += tlv_write_len(out + off, plen);
  memcpy(out + off, plain, plen);
  off += plen;
  return off;
}
static size_t build_DO97(uint16_t Le, uint8_t* out) { out[0]=0x97; out[1]=0x01; out[2]=(uint8_t)Le; return 3; }
static size_t build_DO8E(const uint8_t* mac8, uint8_t* out) { out[0]=0x8E; out[1]=0x08; memcpy(out+2, mac8, 8); return 10; }
static void build_cmd_header(uint8_t cla_prime, uint8_t ins, uint8_t p1, uint8_t p2, uint8_t out4[4]){ out4[0]=cla_prime; out4[1]=ins; out4[2]=p1; out4[3]=p2; }

static size_t sm_wrap_command_cfg(const uint8_t Kenc[16], const uint8_t Kmac[16], uint8_t ssc[8],
                                 uint8_t cla, uint8_t ins, uint8_t p1, uint8_t p2,
                                 const uint8_t* data, size_t dataLen, uint16_t Le,
                                 bool useEncData, bool includeDO97, bool omitTrailingLe,
                                 uint8_t* out) {
  ssc_inc(ssc);

  uint8_t doBuf87[600]; size_t do87Len = 0;
  uint8_t doBuf85[600]; size_t do85Len = 0;
  if (useEncData) do87Len = build_DO87(Kenc, data, dataLen, doBuf87);
  else           do85Len = build_DO85(data, dataLen, doBuf85);

  uint8_t do97[4]; size_t do97Len = 0;
  if (includeDO97) do97Len = build_DO97(Le, do97);

  uint8_t cla_prime = (uint8_t)((cla & 0xFC) | 0x0C);
  uint8_t hdr[4]; build_cmd_header(cla_prime, ins, p1, p2, hdr);

  size_t Lc = (useEncData ? do87Len : do85Len) + do97Len + 10;
  size_t Mlen = 4 + (USE_HDR_PAD_80 ? 4 : 0) + (USE_M_WITH_LC ? 1 : 0)
              + (useEncData ? do87Len : do85Len) + do97Len;

  uint8_t* M = (uint8_t*)malloc(Mlen);
  size_t off = 0;
  memcpy(M + off, hdr, 4); off += 4;
  if (USE_HDR_PAD_80) { M[off++]=0x80; M[off++]=0x00; M[off++]=0x00; M[off++]=0x00; }
  if (USE_M_WITH_LC)  { M[off++] = (uint8_t)Lc; }

  if (useEncData && do87Len)  { memcpy(M + off, doBuf87, do87Len); off += do87Len; }
  if (!useEncData && do85Len) { memcpy(M + off, doBuf85, do85Len); off += do85Len; }
  if (do97Len) { memcpy(M + off, do97, do97Len); }

  uint8_t mac8[8];
  sm_mac_alg3(Kmac, ssc, M, Mlen, mac8);
  free(M);

  uint8_t do8e[10]; size_t do8eLen = build_DO8E(mac8, do8e);

  size_t apdu_len = 0;
  out[apdu_len++]=cla_prime; out[apdu_len++]=ins; out[apdu_len++]=p1; out[apdu_len++]=p2;
  out[apdu_len++]=(uint8_t)Lc;

  if (useEncData && do87Len){ memcpy(out+apdu_len, doBuf87, do87Len); apdu_len += do87Len; }
  if (!useEncData && do85Len){ memcpy(out+apdu_len, doBuf85, do85Len); apdu_len += do85Len; }
  if (do97Len){ memcpy(out+apdu_len, do97, do97Len); apdu_len += do97Len; }
  memcpy(out+apdu_len, do8e, do8eLen); apdu_len += do8eLen;

  if (!(omitTrailingLe && do97Len > 0)) {
    if (!omitTrailingLe) out[apdu_len++] = 0x00;
  }
  return apdu_len;
}

// ===== TLV helpers =====
static bool tlv_read_len(const uint8_t* p, size_t rem, size_t* lenOut, size_t* adv) {
  if (rem < 1) return false;
  uint8_t b0 = p[0];
  if ((b0 & 0x80) == 0) { *lenOut = b0; *adv = 1; return true; }
  uint8_t n = b0 & 0x7F;
  if (n == 0 || n > 2) return false;
  if (rem < (size_t)(1 + n)) return false;
  size_t L = 0;
  for (uint8_t i=0;i<n;i++) L = (L<<8) | p[1+i];
  *lenOut = L;
  *adv = 1 + n;
  return true;
}

static bool collect_sm_tlvs(const uint8_t* p, size_t rem, int depth,
  const uint8_t** TLV87, size_t* TLV87_len, const uint8_t** DO87, size_t* L87,
  const uint8_t** TLV99, size_t* TLV99_len, const uint8_t** DO99, size_t* L99,
  const uint8_t** TLV8E, size_t* TLV8E_len, const uint8_t** DO8E, size_t* L8E) {
  if (depth > 2) return false;
  while (rem >= 2) {
    const uint8_t* tlv_start = p;
    uint8_t tag = *p++; rem -= 1;

    size_t L=0, adv=0;
    if (!tlv_read_len(p, rem, &L, &adv)) return false;
    p += adv; rem -= adv;
    if (rem < L) return false;

    const uint8_t* val_ptr = p;
    size_t full_len = 1 + adv + L;

    if (tag == 0x77 || tag == 0x7C) {
      if (!collect_sm_tlvs(val_ptr, L, depth+1, TLV87,TLV87_len,DO87,L87, TLV99,TLV99_len,DO99,L99, TLV8E,TLV8E_len,DO8E,L8E)) return false;
    } else if (tag == 0x87) {
      if (TLV87 && !*TLV87) { *TLV87 = tlv_start; *TLV87_len = full_len; }
      if (DO87  && !*DO87 ) { *DO87  = val_ptr;   *L87      = L;        }
    } else if (tag == 0x99) {
      if (TLV99 && !*TLV99) { *TLV99 = tlv_start; *TLV99_len = full_len; }
      if (DO99  && !*DO99 ) { *DO99  = val_ptr;   *L99      = L;        }
    } else if (tag == 0x8E) {
      if (TLV8E && !*TLV8E) { *TLV8E = tlv_start; *TLV8E_len = full_len; }
      if (DO8E  && !*DO8E ) { *DO8E  = val_ptr;   *L8E      = L;        }
    }

    p += L; rem -= L;
  }
  return true;
}

// ======================= Parse R-APDU bảo vệ =======================
static bool sm_unwrap_response(const uint8_t Kenc[16], const uint8_t Kmac[16], uint8_t ssc[8],
                               const uint8_t* rapdu, size_t rapdu_len,
                               uint8_t* plain, size_t* plainLen, uint16_t* sw) {
  ssc_inc(ssc);

  const uint8_t *TLV87=nullptr, *TLV99=nullptr, *TLV8E=nullptr;
  size_t TLV87_len=0, TLV99_len=0, TLV8E_len=0;
  const uint8_t *DO87=nullptr, *DO99=nullptr, *DO8E=nullptr;
  size_t L87=0, L99=0, L8E=0;

  if (!collect_sm_tlvs(rapdu, rapdu_len, 0, &TLV87,&TLV87_len,&DO87,&L87, &TLV99,&TLV99_len,&DO99,&L99, &TLV8E,&TLV8E_len,&DO8E,&L8E)) return false;
  if (!DO99 || L99 != 0x02 || !DO8E || L8E != 0x08) return false;

  *sw = ((uint16_t)DO99[0] << 8) | DO99[1];

  uint8_t Mbuf[1500]; size_t Mlen=0;
  if (TLV87) { memcpy(Mbuf+Mlen, TLV87, TLV87_len); Mlen += TLV87_len; }
  memcpy(Mbuf+Mlen, TLV99, TLV99_len); Mlen += TLV99_len;

  uint8_t mac_chk[8];
  if (!sm_mac_alg3(Kmac, ssc, Mbuf, Mlen, mac_chk)) return false;
  if (memcmp(mac_chk, DO8E, 8) != 0) return false;

  if (DO87) {
    if (L87 < 1+8 || DO87[0] != 0x01) return false;
    const uint8_t* ciph = DO87 + 1;
    size_t clen = L87 - 1;
    uint8_t zeroIV[8]={0};
    if (!ede2_cbc_decrypt(Kenc, zeroIV, ciph, clen, plain)) return false;

    size_t i = clen;
    while (i>0 && plain[i-1]==0x00) --i;
    if (i==0 || plain[i-1]!=0x80) return false;
    *plainLen = i-1;
  } else {
    *plainLen = 0;
  }
  return true;
}

// ======================= BAC MUTUAL AUTH =======================
static const uint8_t MRTD_AID[] = { 0xA0,0x00,0x00,0x02,0x47,0x10,0x01 };

static bool getChallenge_retry(uint8_t out8[8]) {
  const uint8_t cmd_08[] = {0x00,0x84,0x00,0x00,0x08};
  const uint8_t cmd_00[] = {0x00,0x84,0x00,0x00,0x00};
  for (int attempt=1; attempt<=5; ++attempt) {
    uint8_t resp[32]; uint8_t len=sizeof(resp); uint16_t sw=0; uint8_t raw=0; delay(10);
    bool ok = apdu_ex(cmd_08, sizeof(cmd_08), resp, &len, &sw, &raw);
    Serial.printf("GET CHAL try %d (Le=08): SW=%04X, data=%u, raw=%u\n", attempt, sw, len, raw);
    if (ok && len==8) { memcpy(out8, resp, 8); return true; }
    delay(20);
    len=sizeof(resp); sw=0; raw=0;
    ok = apdu_ex(cmd_00, sizeof(cmd_00), resp, &len, &sw, &raw);
    Serial.printf("GET CHAL try %d (Le=00): SW=%04X, data=%u, raw=%u\n", attempt, sw, len, raw);
    if (ok && len==8) { memcpy(out8, resp, 8); return true; }
    delay(30);
  }
  return false;
}

static bool bac_mutual_auth(const uint8_t Kenc[16], const uint8_t Kmac[16],
                            uint8_t sessionKenc[16], uint8_t sessionKmac[16], uint8_t ssc[8]) {
  // SELECT AID
  uint8_t cmd[5 + sizeof(MRTD_AID)];
  cmd[0]=0x00; cmd[1]=0xA4; cmd[2]=0x04; cmd[3]=0x0C; cmd[4]=sizeof(MRTD_AID);
  memcpy(cmd+5, MRTD_AID, sizeof(MRTD_AID));

  uint8_t resp[255]; uint8_t respLen=0xFF; uint16_t sw=0;
  if (!apdu(cmd, sizeof(cmd), resp, &respLen, &sw)) {
    Serial.printf("SELECT AID fail, SW=%04X\n", sw);
    return false;
  }
  Serial.println("SELECT AID OK"); delay(10);

  // GET CHALLENGE
  uint8_t RND_ICC[8];
  if (!getChallenge_retry(RND_ICC)) { Serial.println("GET CHALLENGE thất bại"); return false; }
  printHex(RND_ICC, 8, "RND.ICC: ");

  // RND.IFD & KIFD
  uint8_t RND_IFD[8]; randomBytes(RND_IFD, 8);
  uint8_t KIFD[16];   randomBytes(KIFD, 16);
  printHex(RND_IFD, 8, "RND.IFD: ");
  printHex(KIFD, 16, "KIFD:    ");

  // E_ifd = ENC(S)
  uint8_t S[32];
  memcpy(S,     RND_IFD, 8);
  memcpy(S+8,   RND_ICC, 8);
  memcpy(S+16,  KIFD,    16);

  uint8_t zeroIV[8]={0};
  uint8_t E_ifd[32];
  if (!ede2_cbc_encrypt(Kenc, zeroIV, S, sizeof(S), E_ifd)) {
    Serial.println("3DES encrypt S failed");
    return false;
  }

  uint8_t mac_ifd[8];
  if (!retail_mac_alg3(Kmac, E_ifd, sizeof(E_ifd), mac_ifd)) {
    Serial.println("Compute MAC(E_ifd) failed");
    return false;
  }

  // EXTERNAL AUTHENTICATE (case 4)
  uint8_t maCmd[5 + 32 + 8 + 1];
  maCmd[0]=0x00; maCmd[1]=0x82; maCmd[2]=0x00; maCmd[3]=0x00; maCmd[4]=0x28;
  memcpy(maCmd+5,      E_ifd,   32);
  memcpy(maCmd+5+32,   mac_ifd, 8);
  maCmd[5+32+8]=0x28;

  respLen=0xFF; sw=0; uint8_t raw=0;
  bool ok = apdu_ex(maCmd, sizeof(maCmd), resp, &respLen, &sw, &raw);
  Serial.printf("MA send: SW=%04X, data=%u, raw=%u\n", sw, respLen, raw);

  if ((!ok && (sw >> 8) == 0x61) || (ok && respLen==0)) {
    uint8_t want = (sw >> 8) == 0x61 ? (uint8_t)(sw & 0xFF) : 0x28;
    if (want==0x00) want=0x28;
    respLen=0xFF;
    if (!get_response(want, resp, &respLen)) {
      respLen=0xFF;
      if (!get_response(0x00, resp, &respLen)) {
        Serial.println("GET RESPONSE after MA failed");
        return false;
      }
    }
    sw=0x9000; ok=true;
  } else if (!ok && (sw >> 8) == 0x6C) {
    uint8_t correctLe=(uint8_t)(sw & 0xFF);
    maCmd[sizeof(maCmd)-1]=correctLe;
    respLen=0xFF; sw=0; raw=0;
    ok = apdu_ex(maCmd, sizeof(maCmd), resp, &respLen, &sw, &raw);
    Serial.printf("MA resend Le=%u: SW=%04X, data=%u, raw=%u\n", correctLe, sw, respLen, raw);
    if (!ok) return false;
  }

  if (!ok) {
    Serial.printf("Mutual Authenticate fail, SW=%04X, dataLen=%u\n", sw, respLen);
    return false;
  }
  if (respLen != 40) {
    Serial.printf("MA response thiếu MAC 8B (respLen=%u)\n", respLen);
    return false;
  }

  uint8_t E_icc[32]; memcpy(E_icc, resp, 32);
  uint8_t mac_recv[8]; memcpy(mac_recv, resp+32, 8);

  uint8_t mac_chk[8];
  if (!retail_mac_alg3(Kmac, E_icc, 32, mac_chk)) return false;
  if (memcmp(mac_chk, mac_recv, 8) != 0) { Serial.println("MAC(E_icc) mismatch"); return false; }

  uint8_t R_dec[32];
  if (!ede2_cbc_decrypt(Kenc, zeroIV, E_icc, 32, R_dec)) return false;

  uint8_t RND_ICC_p[8], RND_IFD_p[8], KICC[16];
  memcpy(RND_ICC_p, R_dec, 8);
  memcpy(RND_IFD_p, R_dec+8, 8);
  memcpy(KICC,      R_dec+16, 16);

  bool ifd_ok=false;
  uint8_t exp_ifd_rotByte[8], exp_ifd_rotBit[8];
  rotByteLeft8(RND_IFD, exp_ifd_rotByte);
  rotBitLeft64(RND_IFD, exp_ifd_rotBit);

  if (memcmp(RND_IFD_p, RND_IFD, 8) == 0) ifd_ok = true;
  else if (memcmp(RND_IFD_p, exp_ifd_rotByte, 8) == 0) ifd_ok = true;
  else if (memcmp(RND_IFD_p, exp_ifd_rotBit, 8) == 0) ifd_ok = true;

  if (!ifd_ok) { Serial.println("RND.IFD' mismatch"); return false; }

  uint8_t Kseed_p[16];
  for (int i=0;i<16;i++) Kseed_p[i] = KIFD[i] ^ KICC[i];
  deriveKencKmac(Kseed_p, sessionKenc, sessionKmac);
  printHex(sessionKenc, 16, "Session Kenc: ");
  printHex(sessionKmac, 16, "Session Kmac: ");

  memcpy(ssc,     RND_ICC + 4, 4);
  memcpy(ssc + 4, RND_IFD + 4, 4);
  printHex(ssc, 8, "SSC: ");
  return true;
}

static bool bac_resync_from_mrz(uint8_t outKenc[16], uint8_t outKmac[16], uint8_t outSSC[8]) {
  uint8_t Kseed[16], Kenc0[16], Kmac0[16];
  deriveKseed(MRZINFO, Kseed);
  deriveKencKmac(Kseed, Kenc0, Kmac0);
  return bac_mutual_auth(Kenc0, Kmac0, outKenc, outKmac, outSSC);
}

// ======================= SELECT/READ helpers (SM) =======================
static bool select_by_fid_sm(const uint8_t Kenc[16], const uint8_t Kmac[16], uint8_t ssc[8],
                             uint8_t fid_hi, uint8_t fid_lo) {
  const uint8_t fid[2] = { fid_hi, fid_lo };

  uint8_t apdu_buf[256];
  uint8_t respSM[255];
  uint8_t plain[255];

  uint8_t ssc_try[8]; memcpy(ssc_try, ssc, 8);

  auto one = [&](bool useEncData, bool includeDO97, bool omitTrailingLe) -> bool {
    size_t apdu_len = sm_wrap_command_cfg(Kenc, Kmac, ssc_try,
                                          0x00, 0xA4, 0x02, 0x0C,
                                          fid, sizeof(fid), 0x00,
                                          useEncData, includeDO97, omitTrailingLe,
                                          apdu_buf);

    uint8_t respSMLen = 0xFF;   // QUAN TRỌNG
    uint16_t swSM = 0;
    bool okSM = apdu(apdu_buf, (uint8_t)apdu_len, respSM, &respSMLen, &swSM);

    if (!okSM && (swSM >> 8) == 0x61) {
      uint8_t want = (uint8_t)(swSM & 0xFF); if (want == 0x00) want = 0xFF;
      respSMLen = 0xFF;
      okSM = get_response(want, respSM, &respSMLen);
    }
    if (!okSM) return false;

    size_t plainLen_local = 0;
    uint16_t swp = 0;

    bool okUnwrap = sm_unwrap_response(Kenc, Kmac, ssc_try, respSM, respSMLen,
                                       plain, &plainLen_local, &swp);

    // LUÔN sync SSC global
    memcpy(ssc, ssc_try, 8);

    if (!okUnwrap) return false;
    if (swp != 0x9000) return false;
    return true;
  };

  // Thứ tự thử theo kinh nghiệm của bạn
  if (one(true,  true,  false)) return true;   // ENC+MAC, DO97, có Le đuôi
  memcpy(ssc_try, ssc, 8);
  if (one(false, false, true))  return true;   // MAC-only, no DO97
  memcpy(ssc_try, ssc, 8);
  if (one(false, true,  true))  return true;   // MAC-only, DO97
  memcpy(ssc_try, ssc, 8);
  if (one(true,  true,  true))  return true;   // ENC+MAC, DO97, omitLe
  return false;
}

// READ BINARY SM (adaptive Le giảm dần khi fail)
static bool read_binary_chunk_sm(const uint8_t Kenc[16], const uint8_t Kmac[16],
                                 uint8_t ssc[8], uint16_t offset, uint8_t le_request,
                                 uint8_t* plain, size_t* plainLen, uint16_t* swp) {

  const uint8_t MAX_LE = 0xDF; // cho phép test Le lớn (miễn response <=255)

  uint8_t firstLe = le_request;
  if (firstLe == 0 || firstLe > MAX_LE) firstLe = MAX_LE;

  for (uint8_t le = firstLe; le >= 1; --le) {
    uint8_t apdu_buf[256];
    uint8_t respSM[255];

    uint8_t ssc_try[8]; memcpy(ssc_try, ssc, 8);
    uint8_t P1 = (uint8_t)(offset >> 8), P2 = (uint8_t)(offset & 0xFF);

    size_t apdu_len = sm_wrap_command_cfg(Kenc, Kmac, ssc_try,
                                          0x00, 0xB0, P1, P2,
                                          nullptr, 0, le,
                                          false, true, true,   // MAC-only + DO97, omit Le ngoài
                                          apdu_buf);

    uint8_t respSMLen = 0xFF;  // QUAN TRỌNG
    uint16_t swSM = 0;

    bool okSM = apdu(apdu_buf, (uint8_t)apdu_len, respSM, &respSMLen, &swSM);

    if (!okSM && (swSM >> 8) == 0x61) {
      uint8_t want = (uint8_t)(swSM & 0xFF);
      if (want == 0x00) want = 0xFF;
      respSMLen = 0xFF;
      okSM = get_response(want, respSM, &respSMLen);
    }
    if (!okSM) continue;

    size_t n = 0; uint16_t swp_local = 0;
    bool okUnwrap = sm_unwrap_response(Kenc, Kmac, ssc_try, respSM, respSMLen,
                                       plain, &n, &swp_local);

    // LUÔN sync SSC global (kể cả unwrap fail)
    memcpy(ssc, ssc_try, 8);

    if (!okUnwrap) continue;

    *plainLen = n;
    *swp = swp_local;
    return true;
  }
  return false;
}

// READ BINARY SM (hard Le cố định)
static bool read_binary_chunk_sm_hardLe(const uint8_t Kenc[16], const uint8_t Kmac[16],
                                        uint8_t ssc[8], uint16_t offset, uint8_t le,
                                        uint8_t* plain, size_t* plainLen, uint16_t* swp) {
  uint8_t apdu_buf[256];
  uint8_t respSM[255];

  uint8_t ssc_try[8]; memcpy(ssc_try, ssc, 8);
  uint8_t P1 = (uint8_t)(offset >> 8);
  uint8_t P2 = (uint8_t)(offset & 0xFF);

  size_t apdu_len = sm_wrap_command_cfg(Kenc, Kmac, ssc_try,
                                        0x00, 0xB0, P1, P2,
                                        nullptr, 0, le,
                                        false, true, true,
                                        apdu_buf);

  uint8_t respSMLen = 0xFF; // QUAN TRỌNG
  uint16_t swSM = 0;

  bool okSM = apdu(apdu_buf, (uint8_t)apdu_len, respSM, &respSMLen, &swSM);

  if (!okSM && (swSM >> 8) == 0x61) {
    uint8_t want = (uint8_t)(swSM & 0xFF);
    if (want == 0x00) want = 0xFF;
    respSMLen = 0xFF;
    okSM = get_response(want, respSM, &respSMLen);
  }
  if (!okSM) return false;

  size_t n = 0;
  uint16_t swp_local = 0;

  bool okUnwrap = sm_unwrap_response(Kenc, Kmac, ssc_try,
                                     respSM, respSMLen,
                                     plain, &n, &swp_local);

  memcpy(ssc, ssc_try, 8); // sync SSC global

  if (!okUnwrap) return false;

  *plainLen = n;
  *swp = swp_local;
  return true;
}

static bool read_file_to_vector_sm(const char* label,
                                   const uint8_t Kenc[16], const uint8_t Kmac[16], uint8_t ssc[8],
                                   uint8_t fid_hi, uint8_t fid_lo,
                                   std::vector<uint8_t>& out_buf) {
  if (!select_by_fid_sm(Kenc, Kmac, ssc, fid_hi, fid_lo)) {
    Serial.printf("SELECT %s (FID=%02X%02X) FAIL\n", label, fid_hi, fid_lo);
    return false;
  }
  Serial.printf("SELECT %s OK. Đọc nội dung (vector)...\n", label);

  const uint8_t CHUNK_SAFE = 0x40;  // tăng tốc fallback
  uint16_t off = 0;
  for (;;) {
    uint8_t plain[255]; size_t n=0; uint16_t swp=0;
    if (!read_binary_chunk_sm(Kenc, Kmac, ssc, off, CHUNK_SAFE, plain, &n, &swp)) {
      Serial.println("READ BINARY unwrap FAIL");
      return false;
    }
    if (n) {
      out_buf.insert(out_buf.end(), plain, plain + n);
      off += (uint16_t)n;
    }
    if (n < CHUNK_SAFE || swp != 0x9000) break;
    if (DG2_INTER_CMD_DELAY_US) delayMicroseconds(DG2_INTER_CMD_DELAY_US);
  }
  Serial.printf("Tổng đọc %s (vector): %u bytes\n", label, (unsigned)out_buf.size());
  return true;
}

// ===== TLV scan tiện ích =====
static bool tlv_peek_tag_bytes(const uint8_t* p, size_t rem, const uint8_t** tag_ptr, size_t* tag_len) {
  if (rem < 1) return false;
  size_t len = 1;
  if ((p[0] & 0x1F) == 0x1F) { do { if (len >= rem) return false; ++len; } while (p[len - 1] & 0x80); }
  *tag_ptr = p; *tag_len = len;
  return true;
}

static const char* guess_image_ext(const uint8_t* d, size_t n) {
  if (n >= 3 && d[0] == 0xFF && d[1] == 0xD8 && d[2] == 0xFF) return ".jpg";
  if (n >= 4 && d[0] == 0xFF && d[1] == 0x4F && d[2] == 0xFF && d[3] == 0x51) return ".j2c";
  if (n >= 12 && d[4] == 0x6A && d[5] == 0x50 && d[6] == 0x20 && d[7] == 0x20) return ".jp2";
  return ".bin";
}

static void serial_dump_hex_open(const char* title){ Serial.print("-----BEGIN "); Serial.print(title); Serial.println(" HEX-----"); }
static void serial_dump_hex_close(const char* title){ Serial.print("-----END "); Serial.print(title); Serial.println(" HEX-----"); }

// ======================= DG2: PROBE Le tối ưu =======================
static uint8_t probe_best_le_for_dg2(const uint8_t Kenc[16], const uint8_t Kmac[16], uint8_t ssc[8]) {
  uint8_t plain[255]; size_t n=0; uint16_t swp=0;

  for (uint8_t le : DG2_LE_CANDIDATES) {
    bool ok_all = true;

    // thử 2 lần (offset 0 và offset 0x0100) để tránh “hên/xui”
    for (int t=0; t<2; ++t) {
      uint16_t off = (t==0) ? 0x0000 : 0x0100;
      if (!read_binary_chunk_sm_hardLe(Kenc, Kmac, ssc, off, le, plain, &n, &swp)) { ok_all = false; break; }
      if (swp != 0x9000 || n == 0) { ok_all = false; break; }
    }

    if (ok_all) return le;
  }
  return 0x17;
}

// ======================= DG2 STREAMER (tăng tốc bằng Le lớn) =======================
static bool stream_dg2_face_hex(uint8_t Kenc[16], uint8_t Kmac[16], uint8_t ssc[8]) {
  int resyncBudget = DG2_RESYNC_BUDGET;

  if (!select_by_fid_sm(Kenc, Kmac, ssc, 0x01, 0x02)) {
    Serial.println("SELECT DG2 FAIL");
    return false;
  }
  Serial.println("SELECT DG2 OK. Đang PROBE Le tối ưu...");

  uint8_t bestLe = probe_best_le_for_dg2(Kenc, Kmac, ssc);
  Serial.printf("DG2: chọn Le=%u (0x%02X)\n", bestLe, bestLe);

  uint32_t t_start = millis();

  uint16_t offset = 0;
  size_t bytes_read_total = 0;

  std::vector<uint8_t> prefix; prefix.reserve(16);
  bool total_known=false; size_t total_est=0; size_t header7F61_len=0;

  enum { SEARCHING_TAG, PARSING_LEN, STREAMING, FINISHED } state = SEARCHING_TAG;
  std::vector<uint8_t> carry;  carry.reserve(8);
  std::vector<uint8_t> lenBuf; lenBuf.reserve(3);

  size_t face_len=0, face_emitted=0;
  bool banner_open=false;
  int col=0;

  uint8_t extProbe[16]; size_t extProbeFilled=0; bool extAnnounced=false;

  auto print_progress = [&](bool force = false) {
    if (g_dumping_hex) return;
    if (!total_known || total_est == 0) return;
    int pct = (int)((bytes_read_total * 100UL) / total_est);
    if (pct > 99) pct = 99;
    static int last = -1;
    if (force || pct >= last + 5) {
      Serial.printf("DG2 progress ~%d%% (%u/%u bytes)\n", pct, (unsigned)bytes_read_total, (unsigned)total_est);
      last = pct;
    }
  };

  while (true) {
    uint8_t plain[255];
    size_t  n = 0;
    uint16_t swp = 0;
    uint16_t startOff = offset;

    if (!read_binary_chunk_sm_hardLe(Kenc, Kmac, ssc, offset, bestLe, plain, &n, &swp)) {
      if (resyncBudget > 0) {
        Serial.println("DG2: unwrap FAIL → thử BAC re-sync và đọc tiếp...");
        resyncBudget--;

        uint8_t nKenc[16], nKmac[16], nSSC[8];
        if (!bac_resync_from_mrz(nKenc, nKmac, nSSC)) {
          Serial.println("DG2: re-BAC thất bại → bỏ cuộc.");
          break;
        }

        memcpy(Kenc, nKenc, 16);
        memcpy(Kmac, nKmac, 16);
        memcpy(ssc,  nSSC,  8);

        if (!select_by_fid_sm(Kenc, Kmac, ssc, 0x01, 0x02)) {
          Serial.println("DG2: SELECT DG2 sau re-BAC thất bại.");
          break;
        }

        // PROBE lại Le cho phiên mới (thực tế nên làm)
        bestLe = probe_best_le_for_dg2(Kenc, Kmac, ssc);
        Serial.printf("DG2: (sau re-BAC) Le=%u (0x%02X)\n", bestLe, bestLe);

        offset = startOff;
        continue;
      }

      Serial.println("DG2: READ unwrap FAIL (hết lượt thử).");
      break;
    }

    if (!total_known && startOff == 0 && n > 0) {
      prefix.insert(prefix.end(), plain, plain + min((size_t)n, (size_t)16));
      if (prefix.size() >= 2 && prefix[0] == 0x7F && prefix[1] == 0x61) {
        size_t L = 0, adv = 0;
        if (tlv_read_len(prefix.data() + 2, prefix.size() - 2, &L, &adv)) {
          total_est      = 2 + adv + L;
          header7F61_len = 2 + adv;
          total_known    = true;
          Serial.printf("DG2 tổng ước lượng: ~%u bytes (tag 7F61)\n", (unsigned)total_est);
        }
      }
    }

    bytes_read_total += n;
    offset += (uint16_t)n;

    bool isLastChunk = (n == 0) || (swp != 0x9000);

    std::vector<uint8_t> scan;
    scan.reserve(carry.size() + n);
    scan.insert(scan.end(), carry.begin(), carry.end());
    scan.insert(scan.end(), plain, plain + n);

    size_t cur = 0;

    if (state == SEARCHING_TAG) {
      bool found=false; size_t idx=0;
      for (size_t i=0; i+1<scan.size(); ++i) {
        if (scan[i]==0x5F && scan[i+1]==0x2E) { found=true; idx=i; break; }
      }
      if (found) {
        size_t carrySz = carry.size();
        if (idx < carrySz && (idx + 1) == carrySz) cur = 1;
        else cur = (idx < carrySz) ? 0 : (idx - carrySz) + 2;
        state = PARSING_LEN;
        lenBuf.clear();
        Serial.println("DG2: tìm thấy tag 5F2E, đang đọc độ dài...");
      }
    }

    if (state == PARSING_LEN) {
      while (cur < n && lenBuf.size() < 3) {
        lenBuf.push_back(plain[cur++]);
        size_t L = 0, adv = 0;
        if (tlv_read_len(lenBuf.data(), lenBuf.size(), &L, &adv)) {
          if (adv == lenBuf.size()) {
            face_len = L;
            state = STREAMING;
            Serial.printf("5F2E: L ≈ %u bytes\n", (unsigned)face_len);

            if (DG2_DUMP_HEX && !banner_open) {
              serial_dump_hex_open("DG2_FACE.bin");
              banner_open = true;
              g_dumping_hex = true;
            }
            break;
          }
        }
      }
    }

    if (state == STREAMING) {
      while (cur < n && face_emitted < face_len) {
        size_t can = min((size_t)(n - cur), (size_t)(face_len - face_emitted));

        if (DG2_DUMP_HEX) {
          for (size_t k=0; k<can; ++k) {
            uint8_t b = plain[cur + k];
            if (b < 0x10) Serial.print('0');
            Serial.print(b, HEX);
            col += 2;
            if (col >= 96) { Serial.println(); col = 0; }

            if (extProbeFilled < sizeof(extProbe)) {
              extProbe[extProbeFilled++] = b;
              if (!extAnnounced && !g_dumping_hex) {
                const char* g = guess_image_ext(extProbe, extProbeFilled);
                if ((strcmp(g, ".bin") != 0 && extProbeFilled >= 12) || extProbeFilled >= 64) {
                  Serial.print("\nGợi ý phần mở rộng: "); Serial.println(g);
                  extAnnounced = true;
                }
              }
            }
          }
        }

        face_emitted += can;
        cur += can;
      }

      if (face_emitted >= face_len) {
        if (DG2_DUMP_HEX) {
          if (col) { Serial.println(); col = 0; }
          serial_dump_hex_close("DG2_FACE.bin");
          g_dumping_hex = false;
        }
        Serial.println("DG2: hoàn tất xuất ảnh (5F2E)");
        state = FINISHED;
        print_progress(true);
        break;
      }
    }

    carry.clear();
    if (n) {
      size_t keep = min((size_t)8, n);
      carry.insert(carry.end(), plain + (n - keep), plain + n);
    }

    print_progress(false);

    if (isLastChunk) { print_progress(true); break; }

    if (DG2_INTER_CMD_DELAY_US) delayMicroseconds(DG2_INTER_CMD_DELAY_US);
  }

  uint32_t dt = millis() - t_start;

  if (banner_open && g_dumping_hex) {
    if (col) Serial.println();
    serial_dump_hex_close("DG2_FACE.bin (INCOMPLETE)");
    g_dumping_hex = false;
  }

  if (state == FINISHED) {
    Serial.printf("DG2 hoàn tất: %lu ms (~%.2f s), Le=0x%02X\n",
                  (unsigned long)dt, (double)dt / 1000.0, bestLe);
    return true;
  } else {
    Serial.printf("DG2 thất bại sau %lu ms (~%.2f s), Le=0x%02X\n",
                  (unsigned long)dt, (double)dt / 1000.0, bestLe);
    return false;
  }
}

// ======================= Parse helpers khác =======================
static String bytes_to_printable(const std::vector<uint8_t>& v) {
  String s; s.reserve(v.size());
  for (uint8_t b : v) { char c=(char)b; s += (c>=32 && c<=126)? c : '.'; }
  return s;
}

static void parse_mrz_guess(const String& mrz) {
  Serial.println("MRZ (printable):");
  Serial.println(mrz);

  auto isDigitC = [](char c){ return c >= '0' && c <= '9'; };
  auto isUpperC = [](char c){ return c >= 'A' && c <= 'Z'; };

  int firstDouble = mrz.indexOf("<<");
  if (firstDouble < 0) { Serial.println("Chuỗi không hợp lệ (không có \"<<\")."); return; }

  int j = firstDouble - 1;
  while (j >= 0 && isDigitC(mrz.charAt(j))) j--;
  String digitsRun = mrz.substring(j + 1, firstDouble);
  String cccd = digitsRun.length() >= 12 ? digitsRun.substring(digitsRun.length() - 12) : digitsRun;

  int i = firstDouble + 2;
  if (i < mrz.length() && isDigitC(mrz.charAt(i))) i++;
  if (i + 6 > mrz.length()) { Serial.println("Không đủ dữ liệu."); return; }
  String dob = mrz.substring(i, i + 6); i += 6;
  if (i < mrz.length() && isDigitC(mrz.charAt(i))) i++;
  char sex = (i < mrz.length() ? mrz.charAt(i) : 'X'); i++;
  String expiry = (i + 6 <= mrz.length() ? mrz.substring(i, i + 6) : ""); i += 6;
  if (i < mrz.length() && isDigitC(mrz.charAt(i))) i++;
  String nationality = (i + 3 <= mrz.length() ? mrz.substring(i, i + 3) : "");

  int namesSplit = mrz.lastIndexOf("<<");
  while (namesSplit >= 0) {
    int nxt = namesSplit + 2;
    if (nxt < mrz.length() && isUpperC(mrz.charAt(nxt))) break;
    namesSplit = mrz.lastIndexOf("<<", namesSplit - 1);
  }

  String fullName = "";
  if (namesSplit > 0) {
    int k = namesSplit - 1;
    while (k >= 0 && isUpperC(mrz.charAt(k))) k--;
    int surnameStart = k + 1;

    String surname = mrz.substring(surnameStart, namesSplit);
    String given   = mrz.substring(namesSplit + 2);
    surname.replace("<", " ");
    given.replace("<", " ");
    surname.trim(); given.trim();
    fullName = surname + " " + given;
  }

  const char* sexLabel = (sex == 'M') ? "M (Male)" : (sex == 'F') ? "F (Female)" : "X (Unspecified)";

  Serial.printf("Họ tên: %s\n", fullName.c_str());
  Serial.printf("CCCD: %s\n", cccd.c_str());
  Serial.printf("Ngày sinh: %s\n", dob.c_str());
  Serial.printf("Ngày hết hạn thẻ: %s\n", expiry.c_str());
  Serial.printf("Quốc tịch: %s\n", nationality.c_str());
  Serial.printf("Giới tính: %s\n", sexLabel);
}

// ======================= SETUP/LOOP =======================
void setup() {
  Serial.begin(921600);
  delay(250);
  Serial.println("\n[ESP32 + PN532 (SPI) BAC + SM + READ EF.COM/DG1/DG2 (DG2 fast Le-probe)]");

  SPI.begin(PN532_SCK, PN532_MISO, PN532_MOSI, PN532_SS);
  nfc.begin();

  uint32_t versiondata = nfc.getFirmwareVersion();
  if (!versiondata) {
    Serial.println("Không tìm thấy PN532. Kiểm tra dây SPI, chân CS và DIP (SPI)!");
    while (1) delay(1000);
  }
  Serial.print("PN5"); Serial.println((versiondata >> 24) & 0xFF, HEX);

  nfc.SAMConfig();
  nfc.setPassiveActivationRetries(0x20);

  Serial.println("Đưa CCCD/hộ chiếu NFC vào gần anten...");
  if (!waitForIso14443_4()) {
    Serial.println("Không thấy thẻ ISO14443-4. Thử lại.");
    return;
  }
  Serial.println("Đã phát hiện thẻ.");

  uint8_t Kseed[16], Kenc[16], Kmac[16];
  deriveKseed(MRZINFO, Kseed);
  deriveKencKmac(Kseed, Kenc, Kmac);
  printHex(Kenc, 16, "Kenc: ");
  printHex(Kmac, 16, "Kmac: ");

  uint8_t sKenc[16], sKmac[16], ssc[8];
  if (!bac_mutual_auth(Kenc, Kmac, sKenc, sKmac, ssc)) {
    Serial.println("BAC Mutual Auth thất bại.");
    return;
  }
  Serial.println("BAC Mutual Auth thành công! Sẵn sàng Secure Messaging.");

  // EF.COM (đọc nhanh hơn chút vẫn ổn)
  if (!select_by_fid_sm(sKenc, sKmac, ssc, 0x01, 0x1E)) {
    Serial.println("SELECT EF.COM FAIL.");
    return;
  }
  Serial.println("SELECT EF.COM OK → READ...");
  {
    const uint8_t CHUNK_SAFE = 0x20;
    uint16_t off = 0;
    uint32_t total = 0;
    for (;;) {
      uint8_t plain[255];
      size_t n = 0;
      uint16_t swp = 0;
      if (!read_binary_chunk_sm(sKenc, sKmac, ssc, off, CHUNK_SAFE, plain, &n, &swp)) {
        Serial.println("READ EF.COM unwrap FAIL");
        break;
      }
      if (n) { total += n; off += (uint16_t)n; }
      if (n < CHUNK_SAFE || swp != 0x9000) break;
    }
    Serial.printf("Tổng đọc EF.COM: %lu bytes\n", (unsigned long)total);
  }

  // DG1
  {
    if (select_by_fid_sm(sKenc, sKmac, ssc, 0x01, 0x01)) {
      const uint8_t CHUNK_SAFE = 0x20;
      uint16_t off = 0;
      std::vector<uint8_t> DG1;
      for (;;) {
        uint8_t plain[255];
        size_t n = 0;
        uint16_t swp = 0;
        if (!read_binary_chunk_sm(sKenc, sKmac, ssc, off, CHUNK_SAFE, plain, &n, &swp)) {
          Serial.println("READ DG1 unwrap FAIL");
          break;
        }
        if (n) { DG1.insert(DG1.end(), plain, plain + n); off += (uint16_t)n; }
        if (n < CHUNK_SAFE || swp != 0x9000) break;
      }
      String mrz = bytes_to_printable(DG1);
      Serial.println("DG1 (ASCII):");
      Serial.println(mrz);
      parse_mrz_guess(mrz);
    } else {
      Serial.println("SELECT DG1 FAIL");
    }
  }

  // DG2 Stream (FAST)
  if (!stream_dg2_face_hex(sKenc, sKmac, ssc)) {
    Serial.println("Streamer DG2 không trích được ảnh — fallback: đọc toàn bộ DG2 vào RAM rồi bóc 5F2E...");
    std::vector<uint8_t> DG2buf;

    if (read_file_to_vector_sm("DG2", sKenc, sKmac, ssc, 0x01, 0x02, DG2buf)) {
      std::function<bool(const uint8_t*, size_t, const uint8_t**, size_t*)> find5F2E =
        [&](const uint8_t* p, size_t rem, const uint8_t** val, size_t* L) -> bool {
          while (rem > 0) {
            const uint8_t* tagp; size_t tlen;
            if (!tlv_peek_tag_bytes(p, rem, &tagp, &tlen)) return false;
            p += tlen; rem -= tlen;

            size_t len = 0, adv = 0;
            if (!tlv_read_len(p, rem, &len, &adv)) return false;
            p += adv; rem -= adv;

            const uint8_t* v = p;
            size_t l = len;

            if (tlen == 2 && tagp[0] == 0x5F && tagp[1] == 0x2E) {
              *val = v; *L = l; return true;
            }
            if (l > 0) { if (find5F2E(v, l, val, L)) return true; }

            p += l; rem -= l;
          }
          return false;
        };

      const uint8_t* val = nullptr;
      size_t L = 0;
      if (find5F2E(DG2buf.data(), DG2buf.size(), &val, &L)) {
        const char* ext = guess_image_ext(val, L);
        Serial.printf("Tìm thấy 5F2E (%u bytes), gợi ý ext: %s\n", (unsigned)L, ext);

        if (DG2_DUMP_HEX) {
          serial_dump_hex_open("DG2_FACE.bin");
          int c = 0;
          for (size_t i = 0; i < L; i++) {
            uint8_t b = val[i];
            if (b < 0x10) Serial.print('0');
            Serial.print(b, HEX);
            c += 2;
            if (c >= 96) { Serial.println(); c = 0; }
          }
          if (c) Serial.println();
          serial_dump_hex_close("DG2_FACE.bin");
        }
      } else {
        Serial.println("Không tìm thấy 5F2E trong DG2 (fallback)");
      }
    }
  }
}

void loop() {
  delay(1000);
}
