/*
 * CRT-Coupled Two-Ring Module-LWR Signature Scheme
 *
 * Master ring: Z_q[X]/(X^(2N) - 1) = Z_q[X]/(X^N - 1) × Z_q[X]/(X^N + 1)
 * Security anchor: master ring embedding (N2-dim)
 * Coupling: forces N2-dim attack via unstructured master secret
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include "dehydrate.h"
#include "crt_lwr_sig.h"

// Histogram dump (compile with -DDUMP_HIST=1 to emit arrays)
#ifndef DUMP_HIST
#define DUMP_HIST 0
#endif

// Secret dump (compile with -DDUMP_SECRETS=1 to emit secret coeffs)
#ifndef DUMP_SECRETS
#define DUMP_SECRETS 0
#endif

// Index nonzero counts (compile with -DDUMP_INDEX_COUNTS=1)
#ifndef DUMP_INDEX_COUNTS
#define DUMP_INDEX_COUNTS 0
#endif

// Deterministic nonce for w (compile with -DDETERMINISTIC_W=0 to disable)
#ifndef DETERMINISTIC_W
#define DETERMINISTIC_W 0
#endif

// Signature Huffman mode: 0 = fixed tables, 1 = per-signature codebooks
#ifndef SIG_HUFFMAN_DYNAMIC
#define SIG_HUFFMAN_DYNAMIC 0
#endif

// Signature commitment mode: 1 = send/hash w_cyc only (smaller), 0 = both rings
#ifndef SIG_W_CYC_ONLY
#define SIG_W_CYC_ONLY 0
#endif

// Huffman mode for dual-ring w: 1 = encode (w_cyc,w_neg) pairs, 0 = encode rings separately
#ifndef SIG_W_PAIR_HUFF
#define SIG_W_PAIR_HUFF 0
#endif

// Range coder w model: 1 = encode w_cyc + w_delta (centered), 0 = encode pairs
#ifndef SIG_W_DELTA
#define SIG_W_DELTA 0
#endif

// Range coder w model: 1 = encode w_cyc + conditional w_neg tables
#ifndef SIG_W_COND
#define SIG_W_COND 0
#endif

// Range table calibration pass (prints tables and exits)
#ifndef SIG_RANGE_TABLES_GEN
#define SIG_RANGE_TABLES_GEN 0
#endif
#ifndef SIG_RANGE_TABLES_SAMPLES
#define SIG_RANGE_TABLES_SAMPLES 800
#endif

// Range coder for fixed tables: 1 = use fixed cumulative tables
#ifndef SIG_RANGE_S
#define SIG_RANGE_S 1
#endif
#ifndef SIG_RANGE_W
#define SIG_RANGE_W 1
#endif

// Require w' to round back to w (needed for compact hash-only verification)
#ifndef COMPACT_REQUIRE_ROUND
#define COMPACT_REQUIRE_ROUND 0
#endif

// Debug: print verification max_err vs TAU
#ifndef VERIFY_DEBUG_PRINT
#define VERIFY_DEBUG_PRINT 0
#endif

#if VERIFY_DEBUG_PRINT
static int g_verify_debug = 0;
#endif

// Lossy signature (deterministic zeroed positions; encoding skips them)
#ifndef SIG_LOSSY_ZERO
#define SIG_LOSSY_ZERO 1
#endif
#ifndef SIG_LOSSY_ZERO_K
#define SIG_LOSSY_ZERO_K 0
#endif

// Dehydration for s: DISABLED - requires exact w = s*y but LWR has rounding error
#ifndef SIG_DEHYDRATE_S
#define SIG_DEHYDRATE_S 0
#endif

// Dehydration for w: zero positions in w, store actual values separately
// DISABLED: Storing 50 values × 2 rings × 4 bits = 50 bytes overhead
// but only saves ~17 bytes in range coding compression. Net loss.
#ifndef SIG_DEHYDRATE_W
#define SIG_DEHYDRATE_W 0
#endif
#define DEHYDRATE_W_COUNT 50  // Positions to zero per w ring

// W dehydration v2: rejection-based (no hints, no stored values)
// Signer only zeros positions where w' == w (perfect reconstruction)
// Positions are deterministic but vary with signature (retry-indexed)
#ifndef SIG_DEHYDRATE_W_REJECT
#define SIG_DEHYDRATE_W_REJECT 1
#endif
#define DEHYDRATE_W_REJECT_K 100   // Target positions to check per ring

// Parameters
#define N 256                   // Component ring dimension
#define N2 512                  // Master ring dimension (2×N)
#define Q 499                  // Prime modulus (Q ≡ 3 mod 8, ~138 bit security)
//#define Q 251                  // Previous: ~102 bit security (Arora-GB vulnerable)
#define P 48                   // Rounding modulus (Q/P ≈ 10.4, error bound ≈ 5.2)
#define ETA 1                  // Secret coefficient bound (ternary)
#define TAU 65                 // Verification threshold (scaled for P=48)
#define S_BOUND 50             // Minimal signature s bound
#define W_BOUND 50             // Commitment bound for minimal scheme
#define CHALLENGE_WEIGHT 25     // Sparse challenge weight
#define NONCE_WEIGHT 25          // Sparse nonce weight
#define SECRET_WEIGHT 50        // Sparse secret weight in master ring
#define Y_BOUND 4               // Bounded uniform y: coeffs in [-Y_BOUND, Y_BOUND]
#define MAX_ATTEMPTS 1000
#define SEED_BYTES 16           // 128-bit seed for pk expansion
#define SIGNATURE_CHALLENGE_BYTES 32  // SHA3-256 output size

#if SIG_RANGE_S && !SIG_HUFFMAN_DYNAMIC
#define SIG_S_CODEC "Range"
#else
#define SIG_S_CODEC "Huffman"
#endif

#if SIG_RANGE_W && !SIG_HUFFMAN_DYNAMIC && !SIG_W_CYC_ONLY && (P == 16)
#if SIG_W_DELTA
#define SIG_W_CODEC "RangeDelta"
#elif SIG_W_COND
#define SIG_W_CODEC "RangeCond"
#else
#define SIG_W_CODEC "RangePair"
#endif
#else
#define SIG_W_CODEC "Huffman"
#endif

// Types
typedef int16_t coeff_t;
typedef struct { coeff_t c[N2]; } master_t;
typedef struct { coeff_t c[N]; } ring_t;

typedef struct {
    uint8_t seed[SEED_BYTES];
    ring_t pk_cyc;
    ring_t pk_neg;
} public_key_t;

typedef struct {
    master_t x_master;          // Secret in master ring (projects to x_cyc, x_neg)
    uint8_t seed[SEED_BYTES];
} secret_key_t;

typedef struct {
    ring_t s_cyc;
    ring_t s_neg;
    ring_t w_cyc;          // Rounded commitment in cyclic ring
    ring_t w_neg;          // Rounded commitment in negacyclic ring
} signature_t;

// Compressed signature: s as signed 8-bit, w as unsigned 8-bit
#define SIG_S_BITS 8        // Signed, range [-128, 127], max observed ~50
#define SIG_W_BITS 8        // Unsigned, range [0, P-1]
#define COMPRESSED_SIG_SIZE (N * 4)  // 4 rings × N bytes

typedef struct {
    int8_t s_cyc[N];
    int8_t s_neg[N];
    uint8_t w_cyc[N];
    uint8_t w_neg[N];
} compressed_sig_t;

// Compact signature: just (s, c) - verifier recomputes w
// With sparse secrets: |s| typically < 16, use 5-bit s_cyc, 4-bit s_neg high
// s_cyc: 256×5 = 1280 bits = 160 bytes
// s_neg high bits: 256×4 = 1024 bits = 128 bytes
// challenge hash: 16 bytes (128-bit for proper Fiat-Shamir)
// Total: 304 bytes
#define CHALLENGE_BYTES 16
#define CHALLENGE_FULL_BYTES 16
#define COMPACT_SIG_SIZE (160 + 128 + CHALLENGE_BYTES)
#define MINIMAL_SIG_MAX_SIZE 600
#define MINIMAL_HINT_MAX_SIZE 256

typedef struct {
    uint8_t s_cyc_packed[160];       // 256 coeffs × 5 bits
    uint8_t s_neg_packed[128];       // 256 coeffs × 4 bits (LSB from s_cyc)
    uint8_t challenge[CHALLENGE_BYTES]; // 128-bit hash
} compact_sig_t;

// Compact Huffman signature: Huffman(s) + challenge hash + hints (no w)
typedef struct {
    uint8_t s_data[300];
    int s_len;
    uint8_t challenge[CHALLENGE_FULL_BYTES];
    uint8_t hint_data[MINIMAL_HINT_MAX_SIZE];
    int hint_len;
} compact_huffman_sig_t;

// Huffman-compressed signature: variable length
// s: Huffman compressed (sparse response)
// w: Huffman compressed (commitment clusters near 0)
// With Q=P=131, w needs ~7 bits/value: 2×256×7 = 448 bytes worst case
#define HUFFMAN_SIG_MAX_SIZE 1200

typedef struct {
    uint8_t s_data[600];          // Huffman-compressed s
    int s_len;                    // length of s portion
    uint8_t w_data[600];          // Huffman-compressed w (larger for Q=131)
    int w_len;                    // length of w portion
#if SIG_DEHYDRATE_W
    // Store actual w values at dehydrated positions (4 bits each, 50 positions × 2 rings = 50 bytes)
    uint8_t w_dh_cyc[DEHYDRATE_W_COUNT / 2 + 1]; // 50 values × 4 bits / 8 = ~25 bytes
    uint8_t w_dh_neg[DEHYDRATE_W_COUNT / 2 + 1];
#endif
} huffman_sig_t;

// Minimal signature: challenge hash + Huffman(s_cyc, delta) + w correction hints
typedef struct {
    uint8_t challenge[CHALLENGE_BYTES];
    uint8_t s_data[MINIMAL_SIG_MAX_SIZE];
    int s_len;
    uint8_t hint_data[MINIMAL_HINT_MAX_SIZE];
    int hint_len;
} minimal_sig_t;

// Seedless-w signature: nonce_seed + s (verifier reconstructs w)
// nonce_seed: 12 bytes (96-bit, sufficient for nonce uniqueness)
// c_tilde: 16 bytes (commitment hash for binding)
// attempt: 1 byte (for rejection sampling)
// s_data: ~180 bytes (range coded s_cyc + delta)
// Total: ~209 bytes
#define NONCE_SEED_BYTES 12
#define C_TILDE_BYTES 16
#define SEEDLESS_SIG_MAX_SIZE 300

typedef struct {
    uint8_t nonce_seed[NONCE_SEED_BYTES];  // Public nonce seed
    uint8_t c_tilde[C_TILDE_BYTES];        // Commitment hash H(w || pk || msg)
    uint8_t attempt;                        // Rejection sampling attempt number
    uint8_t s_data[SEEDLESS_SIG_MAX_SIZE];  // Range-coded s
    int s_len;
} seedless_sig_t;

// Compressed public key: 8-bit coefficients (values in [0, P-1])
// pk_cyc + pk_neg: 2×256×8 = 4096 bits = 512 bytes
// seed: 16 bytes (128-bit, expanded via SHA3)
// Total: 528 bytes
#define COMPRESSED_PK_SIZE (512 + SEED_BYTES)

typedef struct {
    uint8_t seed[SEED_BYTES];
    uint8_t pk_cyc[N];       // 256 coeffs × 8 bits for [0, P-1]
    uint8_t pk_neg[N];       // 256 coeffs × 8 bits
} compressed_pk_t;

// Huffman-compressed public key: variable length
#define HUFFMAN_PK_MAX_SIZE 600

typedef struct {
    uint8_t seed[SEED_BYTES];
    uint8_t pk_data[HUFFMAN_PK_MAX_SIZE - SEED_BYTES];
    int pk_len;
} huffman_pk_t;

// Statistics for analysis
typedef struct {
    int master_linf;
    double master_l2;
    int cyc_linf, neg_linf;
    double cyc_l2, neg_l2;
    int err_linf;
    double err_l2;
} stats_t;

// Forward declarations for compact Huffman verification
static void expand_sparse_challenge_len(master_t *c, const uint8_t *commitment,
                                        size_t commitment_len, int weight);
void expand_ring(ring_t *r, const uint8_t *seed, int domain_sep);
void hash_to_challenge(uint8_t *out, const ring_t *w_cyc, const ring_t *w_neg,
                       const public_key_t *pk, const uint8_t *msg, size_t msg_len);
int verify_coupling(const ring_t *s_cyc, const ring_t *s_neg);
int verify_trace_zero(const master_t *s);
static void derive_zero_positions(uint8_t *is_zeroed, int k,
                                  const uint8_t *pk_seed,
                                  const uint8_t *msg, size_t msg_len);
#if SIG_DEHYDRATE_W
static void derive_w_dehydrate_positions(uint8_t positions[DEHYDRATE_W_COUNT],
                                         const uint8_t *pk_seed,
                                         const uint8_t *msg, size_t msg_len,
                                         const char *domain_sep);
static void dehydrate_w_ring(ring_t *w, const uint8_t *pk_seed,
                             const uint8_t *msg, size_t msg_len,
                             const char *domain_sep);
static void rehydrate_w_ring(ring_t *w, const ring_t *w_prime,
                             const uint8_t *pk_seed,
                             const uint8_t *msg, size_t msg_len,
                             const char *domain_sep);
#endif
int sign(signature_t *sig, const secret_key_t *sk, const public_key_t *pk,
         const uint8_t *msg, size_t msg_len);
static void minimal_perm_from_seed(uint8_t perm[N], const uint8_t *seed, size_t seed_len);
static int ring_linf(const ring_t *r);

// ============================================================================
// Basic operations
// ============================================================================

static inline coeff_t mod_q(int32_t x) {
    int32_t r = x % Q;
    return (r < 0) ? r + Q : r;
}

static inline int32_t centered(coeff_t x) {
    return (x > Q/2) ? (int32_t)x - Q : (int32_t)x;
}

static inline coeff_t mod_p(int32_t x) {
    int32_t r = x % P;
    return (r < 0) ? r + P : r;
}

static inline int32_t centered_p(coeff_t x) {
    return (x >= P / 2) ? (int32_t)x - P : (int32_t)x;
}

static inline coeff_t round_to_p(coeff_t x) {
    int32_t c = centered(x);
    int32_t r = (c * P + (c >= 0 ? Q/2 : -Q/2)) / Q;
    return mod_p(r);
}

static inline coeff_t unround_to_q(coeff_t x) {
    return (x * Q + P/2) / P;
}

// ============================================================================
// CRT Projection and Lifting
// ============================================================================

// Project master → cyclic: x_cyc[i] = x[i] + x[i+N]
void project_cyclic(const master_t *x, ring_t *x_cyc) {
    for (int i = 0; i < N; i++) {
        x_cyc->c[i] = mod_q(x->c[i] + x->c[i + N]);
    }
}

// Project master → negacyclic: x_neg[i] = x[i] - x[i+N]
void project_negacyclic(const master_t *x, ring_t *x_neg) {
    for (int i = 0; i < N; i++) {
        x_neg->c[i] = mod_q(x->c[i] - x->c[i + N]);
    }
}

// Lift components → master
// x[i] = (x_cyc[i] + x_neg[i]) / 2
// x[i+N] = (x_cyc[i] - x_neg[i]) / 2
int crt_lift(const ring_t *x_cyc, const ring_t *x_neg, master_t *x) {
    for (int i = 0; i < N; i++) {
        int32_t sum = centered(x_cyc->c[i]) + centered(x_neg->c[i]);
        int32_t diff = centered(x_cyc->c[i]) - centered(x_neg->c[i]);

        // Must be even for integer lift
        if ((sum & 1) != 0 || (diff & 1) != 0) {
            return 0;  // Cannot lift
        }

        x->c[i] = mod_q(sum / 2);
        x->c[i + N] = mod_q(diff / 2);
    }
    return 1;
}

// ============================================================================
// Ring Multiplication
// ============================================================================

// Cyclic: X^N = 1
void mul_cyclic(ring_t *r, const ring_t *a, const ring_t *b) {
    int32_t tmp[N] = {0};
    for (int i = 0; i < N; i++) {
        if (a->c[i] == 0) continue;
        int32_t ai = centered(a->c[i]);
        for (int j = 0; j < N; j++) {
            if (b->c[j] == 0) continue;
            int k = (i + j) % N;
            tmp[k] += ai * centered(b->c[j]);
        }
    }
    for (int i = 0; i < N; i++) r->c[i] = mod_q(tmp[i]);
}

// Negacyclic: X^N = -1
void mul_negacyclic(ring_t *r, const ring_t *a, const ring_t *b) {
    int32_t tmp[N] = {0};
    for (int i = 0; i < N; i++) {
        if (a->c[i] == 0) continue;
        int32_t ai = centered(a->c[i]);
        for (int j = 0; j < N; j++) {
            if (b->c[j] == 0) continue;
            int k = i + j;
            if (k >= N) {
                tmp[k - N] -= ai * centered(b->c[j]);  // Negate on wrap
            } else {
                tmp[k] += ai * centered(b->c[j]);
            }
        }
    }
    for (int i = 0; i < N; i++) r->c[i] = mod_q(tmp[i]);
}

void add_ring(ring_t *r, const ring_t *a, const ring_t *b) {
    for (int i = 0; i < N; i++)
        r->c[i] = mod_q(a->c[i] + b->c[i]);
}

void sub_ring(ring_t *r, const ring_t *a, const ring_t *b) {
    for (int i = 0; i < N; i++)
        r->c[i] = mod_q(a->c[i] - b->c[i]);
}

void round_ring(ring_t *r, const ring_t *a) {
    for (int i = 0; i < N; i++)
        r->c[i] = round_to_p(a->c[i]);
}

void unround_ring(ring_t *r, const ring_t *a) {
    for (int i = 0; i < N; i++)
        r->c[i] = unround_to_q(a->c[i]);
}

// ============================================================================
// Huffman Compression
// ============================================================================

// Bit writer for compact encoding
typedef struct {
    uint8_t *data;
    int byte_pos;
    int bit_pos;
    int capacity;
} bitwriter_t;

static void bitwriter_init(bitwriter_t *bw, uint8_t *buf, int capacity) {
    bw->data = buf;
    bw->byte_pos = 0;
    bw->bit_pos = 0;
    bw->capacity = capacity;
    memset(buf, 0, capacity);
}

static void bitwriter_write(bitwriter_t *bw, uint32_t code, uint8_t nbits) {
    for (int i = nbits - 1; i >= 0; i--) {
        if (bw->byte_pos >= bw->capacity) {
            fprintf(stderr, "ERROR: Bitwriter overflow\n");
            return;
        }
        int bit = (code >> i) & 1;
        bw->data[bw->byte_pos] |= (bit << (7 - bw->bit_pos));
        bw->bit_pos++;
        if (bw->bit_pos == 8) {
            bw->byte_pos++;
            bw->bit_pos = 0;
        }
    }
}

static int bitwriter_finish(bitwriter_t *bw) {
    return (bw->bit_pos > 0) ? bw->byte_pos + 1 : bw->byte_pos;
}

static int bitwriter_can_write(const bitwriter_t *bw, int nbits) {
    int used = bw->byte_pos * 8 + bw->bit_pos;
    return used + nbits <= bw->capacity * 8;
}

static int bitwriter_write_bits(bitwriter_t *bw, uint32_t code, int nbits) {
    if (!bitwriter_can_write(bw, nbits)) {
        return 0;
    }
    bitwriter_write(bw, code, (uint8_t)nbits);
    return 1;
}

// Bit reader for decompression
typedef struct {
    const uint8_t *data;
    int byte_pos;
    int bit_pos;
    int length;
} bitreader_t;

static void bitreader_init(bitreader_t *br, const uint8_t *buf, int length) {
    br->data = buf;
    br->byte_pos = 0;
    br->bit_pos = 0;
    br->length = length;
}

static int bitreader_read_bit(bitreader_t *br) {
    if (br->byte_pos >= br->length) {
        return 0;  // Return 0 on overflow (safe default)
    }
    int bit = (br->data[br->byte_pos] >> (7 - br->bit_pos)) & 1;
    br->bit_pos++;
    if (br->bit_pos == 8) {
        br->byte_pos++;
        br->bit_pos = 0;
    }
    return bit;
}

static int bitreader_remaining_bits(const bitreader_t *br) {
    return (br->length - br->byte_pos) * 8 - br->bit_pos;
}

static int bitreader_read_bits(bitreader_t *br, int nbits, uint32_t *out) {
    if (bitreader_remaining_bits(br) < nbits) {
        return 0;
    }
    uint32_t val = 0;
    for (int i = 0; i < nbits; i++) {
        val = (val << 1) | (uint32_t)bitreader_read_bit(br);
    }
    *out = val;
    return 1;
}

#if SIG_RANGE_S || SIG_RANGE_W
#define RC_TOP (1u << 24)

typedef struct {
    uint8_t *data;
    int pos;
    int cap;
    uint64_t low;
    uint32_t range;
    uint8_t cache;
    uint32_t cache_size;
    int ok;
} rc_enc_t;

typedef struct {
    const uint8_t *data;
    int pos;
    int len;
    uint32_t range;
    uint32_t code;
    int ok;
} rc_dec_t;

static void rc_encode(rc_enc_t *rc, uint32_t cum_low, uint32_t cum_high, uint32_t total);

static void rc_enc_init(rc_enc_t *rc, uint8_t *buf, int cap) {
    rc->data = buf;
    rc->pos = 0;
    rc->cap = cap;
    rc->low = 0;
    rc->range = 0xFFFFFFFFU;
    rc->cache = 0;
    rc->cache_size = 1;
    rc->ok = 1;
}

static void rc_encode_uniform(rc_enc_t *rc, uint32_t value, uint32_t total) {
    rc_encode(rc, value, value + 1, total);
}

static void rc_enc_write_byte(rc_enc_t *rc, uint8_t b) {
    if (!rc->ok) {
        return;
    }
    if (rc->pos >= rc->cap) {
        rc->ok = 0;
        return;
    }
    rc->data[rc->pos++] = b;
}

static void rc_shift_low(rc_enc_t *rc) {
    if (!rc->ok) {
        return;
    }
    if ((uint32_t)rc->low < 0xFF000000U || (uint32_t)(rc->low >> 32) != 0) {
        uint8_t temp = rc->cache;
        uint8_t carry = (uint8_t)(rc->low >> 32);
        do {
            rc_enc_write_byte(rc, (uint8_t)(temp + carry));
            temp = 0xFF;
        } while (--rc->cache_size != 0);
        rc->cache = (uint8_t)((uint32_t)rc->low >> 24);
    }
    rc->cache_size++;
    rc->low = (uint32_t)rc->low << 8;
}

static void rc_encode(rc_enc_t *rc, uint32_t cum_low, uint32_t cum_high, uint32_t total) {
    if (!rc->ok || cum_high <= cum_low || total == 0) {
        rc->ok = 0;
        return;
    }
    uint32_t range = rc->range / total;
    if (range == 0) {
        rc->ok = 0;
        return;
    }
    rc->low += (uint64_t)cum_low * range;
    rc->range = range * (cum_high - cum_low);
    while (rc->range < RC_TOP) {
        rc->range <<= 8;
        rc_shift_low(rc);
    }
}

static int rc_finish(rc_enc_t *rc) {
    for (int i = 0; i < 5; i++) {
        rc_shift_low(rc);
    }
    return rc->ok ? rc->pos : 0;
}

static uint8_t rc_dec_read_byte(rc_dec_t *rc) {
    if (rc->pos >= rc->len) {
        rc->ok = 0;
        return 0;
    }
    return rc->data[rc->pos++];
}

static void rc_dec_init(rc_dec_t *rc, const uint8_t *buf, int len) {
    rc->data = buf;
    rc->pos = 0;
    rc->len = len;
    rc->range = 0xFFFFFFFFU;
    rc->code = 0;
    rc->ok = 1;
    for (int i = 0; i < 5; i++) {
        rc->code = (rc->code << 8) | rc_dec_read_byte(rc);
    }
}

static int rc_decode_symbol(rc_dec_t *rc, const uint32_t *cum, int symbols,
                            uint32_t total, int *out) {
    if (!rc->ok || total == 0) {
        return 0;
    }
    uint32_t range = rc->range / total;
    if (range == 0) {
        return 0;
    }
    uint32_t count = rc->code / range;
    if (count >= total) {
        return 0;
    }
    int sym = 0;
    while (sym + 1 < symbols && cum[sym + 1] <= count) {
        sym++;
    }
    uint32_t low = cum[sym];
    uint32_t high = cum[sym + 1];
    if (high <= low) {
        return 0;
    }
    rc->code -= range * low;
    rc->range = range * (high - low);
    while (rc->range < RC_TOP) {
        rc->range <<= 8;
        rc->code = (rc->code << 8) | rc_dec_read_byte(rc);
    }
    *out = sym;
    return rc->ok;
}

static int rc_decode_uniform(rc_dec_t *rc, uint32_t total, uint32_t *out) {
    if (!rc->ok || total == 0) {
        return 0;
    }
    uint32_t range = rc->range / total;
    if (range == 0) {
        return 0;
    }
    uint32_t count = rc->code / range;
    if (count >= total) {
        return 0;
    }
    rc->code -= range * count;
    rc->range = range;
    while (rc->range < RC_TOP) {
        rc->range <<= 8;
        rc->code = (rc->code << 8) | rc_dec_read_byte(rc);
    }
    *out = count;
    return rc->ok;
}
#endif

// Huffman tree node
typedef struct huffman_node_t {
    int16_t symbol;  // INT16_MIN if internal node
    int freq;
    struct huffman_node_t *left;
    struct huffman_node_t *right;
} huffman_node_t;

// Huffman codebook entry
typedef struct {
    int16_t symbol;
    uint8_t bits;
    uint32_t code;
} huffman_entry_t;

// For signature: values in [-15, 15] -> 31 symbols, offset by 16 -> [0, 30]
#define S_MAX_SYMBOLS 64
#define S_SYMBOL_OFFSET 32

// Compare function for priority queue (min-heap by frequency)
static int compare_nodes(const void *a, const void *b) {
    huffman_node_t *na = *(huffman_node_t**)a;
    huffman_node_t *nb = *(huffman_node_t**)b;
    return na->freq - nb->freq;
}

// Build Huffman tree from frequency table
static huffman_node_t* build_huffman_tree_s(int freq[S_MAX_SYMBOLS], int *num_leaves) {
    huffman_node_t *nodes[S_MAX_SYMBOLS];
    int node_count = 0;

    for (int i = 0; i < S_MAX_SYMBOLS; i++) {
        if (freq[i] > 0) {
            huffman_node_t *node = malloc(sizeof(huffman_node_t));
            node->symbol = i - S_SYMBOL_OFFSET;
            node->freq = freq[i];
            node->left = NULL;
            node->right = NULL;
            nodes[node_count++] = node;
        }
    }

    *num_leaves = node_count;

    if (node_count == 0) {
        fprintf(stderr, "ERROR: No symbols to encode\n");
        return NULL;
    }

    if (node_count == 1) {
        return nodes[0];
    }

    while (node_count > 1) {
        qsort(nodes, node_count, sizeof(huffman_node_t*), compare_nodes);
        huffman_node_t *left = nodes[0];
        huffman_node_t *right = nodes[1];
        huffman_node_t *parent = malloc(sizeof(huffman_node_t));
        parent->symbol = INT16_MIN;
        parent->freq = left->freq + right->freq;
        parent->left = left;
        parent->right = right;
        nodes[0] = parent;
        for (int i = 1; i < node_count - 1; i++) {
            nodes[i] = nodes[i + 1];
        }
        node_count--;
    }

    return nodes[0];
}

// Generate Huffman codes by traversing tree
static void generate_codes_recursive(huffman_node_t *node, uint32_t code, uint8_t depth,
                                     huffman_entry_t codebook[], int *codebook_size) {
    if (node->symbol != INT16_MIN) {
        int idx = (*codebook_size)++;
        codebook[idx].symbol = node->symbol;
        codebook[idx].bits = depth;
        codebook[idx].code = code;
        return;
    }

    if (node->left) {
        generate_codes_recursive(node->left, (code << 1) | 0, depth + 1, codebook, codebook_size);
    }
    if (node->right) {
        generate_codes_recursive(node->right, (code << 1) | 1, depth + 1, codebook, codebook_size);
    }
}

static void generate_codes(huffman_node_t *root, huffman_entry_t codebook[], int *codebook_size) {
    *codebook_size = 0;
    if (root->symbol != INT16_MIN) {
        codebook[0].symbol = root->symbol;
        codebook[0].bits = 1;
        codebook[0].code = 0;
        *codebook_size = 1;
        return;
    }
    generate_codes_recursive(root, 0, 0, codebook, codebook_size);
}

// Free Huffman tree
static void free_huffman_tree(huffman_node_t *node) {
    if (node == NULL) return;
    free_huffman_tree(node->left);
    free_huffman_tree(node->right);
    free(node);
}

// Find entry in codebook
static huffman_entry_t* find_entry_s(huffman_entry_t codebook[], int codebook_size, int16_t symbol) {
    for (int i = 0; i < codebook_size; i++) {
        if (codebook[i].symbol == symbol) {
            return &codebook[i];
        }
    }
    fprintf(stderr, "ERROR: Symbol %d not in codebook\n", symbol);
    return NULL;
}

typedef struct {
    uint16_t code;
    uint8_t bits;
} fixed_code_t;

// Fixed Huffman for s (precomputed from sample distribution, with escape)
#define S_CYC_MIN -4
#define S_CYC_MAX 4
#define S_CYC_SYMBOLS (S_CYC_MAX - S_CYC_MIN + 1)
#define S_CYC_MAX_BITS 7
#define S_CYC_ESC_CODE 127
#define S_CYC_ESC_BITS 7
#define S_CYC_ESC_RAW_BITS 6
#define S_CYC_ESC_BIAS 32

#define S_NEGH_MIN -2
#define S_NEGH_MAX 2
#define S_NEGH_SYMBOLS (S_NEGH_MAX - S_NEGH_MIN + 1)
#define S_NEGH_MAX_BITS 5
#define S_NEGH_ESC_CODE 31
#define S_NEGH_ESC_BITS 5
#define S_NEGH_ESC_RAW_BITS 5
#define S_NEGH_ESC_BIAS 16

// Delta escape parameters (for values outside [-4, 4])
#define S_DELTA_ESC_RAW_BITS 5   // 5 bits for raw value [-16, 15]
#define S_DELTA_ESC_BIAS 16      // Bias to make values non-negative

static const fixed_code_t S_CYC_CODE[S_CYC_SYMBOLS] = {
    { .code = 126, .bits = 7 }, // -4
    { .code = 14, .bits = 4 }, // -3
    { .code = 4, .bits = 3 }, // -2
    { .code = 5, .bits = 3 }, // -1
    { .code = 0, .bits = 2 }, // 0
    { .code = 1, .bits = 2 }, // 1
    { .code = 6, .bits = 3 }, // 2
    { .code = 30, .bits = 5 }, // 3
    { .code = 62, .bits = 6 }, // 4
};

static const fixed_code_t S_NEGH_CODE[S_NEGH_SYMBOLS] = {
    { .code = 14, .bits = 4 }, // -2
    { .code = 2, .bits = 2 }, // -1
    { .code = 0, .bits = 1 }, // 0
    { .code = 6, .bits = 3 }, // 1
    { .code = 30, .bits = 5 }, // 2
};

#if SIG_RANGE_S && !SIG_HUFFMAN_DYNAMIC
// Range coder cumulative tables for small alphabets + escape.
#define S_CYC_SMALL_MIN -6
#define S_CYC_SMALL_MAX 6
#define S_CYC_SMALL_SYMBOLS (S_CYC_SMALL_MAX - S_CYC_SMALL_MIN + 1)
#define S_CYC_SMALL_ESC S_CYC_SMALL_SYMBOLS
#define S_CYC_SMALL_TOTAL_SYMBOLS (S_CYC_SMALL_SYMBOLS + 1)

#define S_NEGH_SMALL_MIN -3
#define S_NEGH_SMALL_MAX 3
#define S_NEGH_SMALL_SYMBOLS (S_NEGH_SMALL_MAX - S_NEGH_SMALL_MIN + 1)
#define S_NEGH_SMALL_ESC S_NEGH_SMALL_SYMBOLS
#define S_NEGH_SMALL_TOTAL_SYMBOLS (S_NEGH_SMALL_SYMBOLS + 1)

// Delta encoding: delta = (s_cyc - s_neg) / 2 = s_master[256:511]
#define S_DELTA_SMALL_MIN -4
#define S_DELTA_SMALL_MAX 4
#define S_DELTA_SMALL_SYMBOLS (S_DELTA_SMALL_MAX - S_DELTA_SMALL_MIN + 1)
#define S_DELTA_SMALL_ESC S_DELTA_SMALL_SYMBOLS
#define S_DELTA_SMALL_TOTAL_SYMBOLS (S_DELTA_SMALL_SYMBOLS + 1)
#define S_DELTA_SMALL_TOT 32768

#define S_CYC_SMALL_TOT 32768
#define S_NEGH_SMALL_TOT 32768

static const uint32_t S_CYC_SMALL_CUM[S_CYC_SMALL_TOTAL_SYMBOLS + 1] = {
    0, 1, 129, 897, 2305, 5761, 12288, 20479, 26622, 30461, 32125, 32765, 32766, 32767, 32768
};

static const uint32_t S_NEGH_SMALL_CUM[S_NEGH_SMALL_TOTAL_SYMBOLS + 1] = {
    0, 1, 1665, 11776, 27519, 32638, 32766, 32767, 32768
};

// Delta cumulative table: values -4 to +4 plus escape
static const uint32_t S_DELTA_SMALL_CUM[S_DELTA_SMALL_TOTAL_SYMBOLS + 1] = {
    0, 115, 952, 3737, 11281, 21716, 28809, 31740, 32523, 32697, 32768
};
#endif

static int decode_fixed_symbol(bitreader_t *br, const fixed_code_t *codes,
                               int count, int min_symbol, int max_bits, int *out) {
    uint32_t bits_read = 0;
    for (int bits = 1; bits <= max_bits; bits++) {
        bits_read = (bits_read << 1) | (uint32_t)bitreader_read_bit(br);
        for (int i = 0; i < count; i++) {
            if (codes[i].bits == bits && codes[i].code == bits_read) {
                *out = i + min_symbol;
                return 1;
            }
        }
    }
    return 0;
}

static int decode_fixed_symbol_esc(bitreader_t *br, const fixed_code_t *codes,
                                   int count, int min_symbol, int max_bits,
                                   uint32_t esc_code, int esc_bits,
                                   int esc_raw_bits, int esc_bias, int *out) {
    uint32_t bits_read = 0;
    for (int bits = 1; bits <= max_bits; bits++) {
        bits_read = (bits_read << 1) | (uint32_t)bitreader_read_bit(br);
        if (bits == esc_bits && bits_read == esc_code) {
            uint32_t raw = 0;
            for (int i = 0; i < esc_raw_bits; i++) {
                raw = (raw << 1) | (uint32_t)bitreader_read_bit(br);
            }
            *out = (int)raw - esc_bias;
            return 1;
        }
        for (int i = 0; i < count; i++) {
            if (codes[i].bits == bits && codes[i].code == bits_read) {
                *out = i + min_symbol;
                return 1;
            }
        }
    }
    return 0;
}

// Fixed Huffman for minimal signature payload (s_cyc and delta)
#define MIN_S_MIN -5
#define MIN_S_MAX 4
#define MIN_S_SYMBOLS (MIN_S_MAX - MIN_S_MIN + 1)
#define MIN_S_MAX_BITS 8
#define MIN_S_ESC_CODE 0xD   // 1101
#define MIN_S_ESC_BITS 4
#define MIN_S_ESC_RAW_BITS 8
#define MIN_S_ESC_BIAS 64

#define MIN_D_MIN -4
#define MIN_D_MAX 3
#define MIN_D_SYMBOLS (MIN_D_MAX - MIN_D_MIN + 1)
#define MIN_D_MAX_BITS 8
#define MIN_D_ESC_CODE 0xFE  // 11111110
#define MIN_D_ESC_BITS 8
#define MIN_D_ESC_RAW_BITS 6
#define MIN_D_ESC_BIAS 32

// Hint encoding for corrected commitments (w_round -> w_hat)
#define MIN_SIG_TARGET 256
#define HINT_INDEX_BITS 9   // 0..511
#define HINT_COUNT_BITS 9
#define HINT_MAX_COUNT ((1 << HINT_COUNT_BITS) - 1)

#if P <= 16
#define HINT_DIFF_BITS 4
#elif P <= 32
#define HINT_DIFF_BITS 5
#elif P <= 64
#define HINT_DIFF_BITS 6
#elif P <= 128
#define HINT_DIFF_BITS 7
#else
#define HINT_DIFF_BITS 8
#endif
#define HINT_DIFF_BIAS (1 << (HINT_DIFF_BITS - 1))

static const fixed_code_t MIN_S_CODE[MIN_S_SYMBOLS] = {
    { .code = 0xF0, .bits = 8 }, // -5
    { .code = 0x76, .bits = 7 }, // -4
    { .code = 0x3A, .bits = 6 }, // -3
    { .code = 0x0C, .bits = 4 }, // -2
    { .code = 0x04, .bits = 3 }, // -1
    { .code = 0x00, .bits = 2 }, // 0
    { .code = 0x01, .bits = 2 }, // 1
    { .code = 0x05, .bits = 3 }, // 2
    { .code = 0x1C, .bits = 5 }, // 3
    { .code = 0x77, .bits = 7 }, // 4
};

static const fixed_code_t MIN_D_CODE[MIN_D_SYMBOLS] = {
    { .code = 0x7E, .bits = 7 }, // -4
    { .code = 0x00, .bits = 0 }, // -3 (escape)
    { .code = 0x1E, .bits = 5 }, // -2
    { .code = 0x06, .bits = 3 }, // -1
    { .code = 0x00, .bits = 1 }, // 0
    { .code = 0x02, .bits = 2 }, // 1
    { .code = 0x0E, .bits = 4 }, // 2
    { .code = 0x3E, .bits = 6 }, // 3
};

#if P == 16
// Fixed Huffman for w (commitment) for P=16, derived from empirical distribution.
#define W_MAX_BITS 9
static const fixed_code_t W_CYC_CODE[P] = {
    { .code = 0, .bits = 1 },   // 0
    { .code = 2, .bits = 2 },   // 1
    { .code = 30, .bits = 5 },  // 2
    { .code = 506, .bits = 9 }, // 3
    { .code = 507, .bits = 9 }, // 4
    { .code = 508, .bits = 9 }, // 5
    { .code = 509, .bits = 9 }, // 6
    { .code = 510, .bits = 9 }, // 7
    { .code = 511, .bits = 9 }, // 8
    { .code = 248, .bits = 8 }, // 9
    { .code = 249, .bits = 8 }, // 10
    { .code = 250, .bits = 8 }, // 11
    { .code = 251, .bits = 8 }, // 12
    { .code = 252, .bits = 8 }, // 13
    { .code = 14, .bits = 4 },  // 14
    { .code = 6, .bits = 3 },   // 15
};

static const fixed_code_t W_NEG_CODE[P] = {
    { .code = 0, .bits = 1 },   // 0
    { .code = 6, .bits = 3 },   // 1
    { .code = 30, .bits = 5 },  // 2
    { .code = 506, .bits = 9 }, // 3
    { .code = 507, .bits = 9 }, // 4
    { .code = 508, .bits = 9 }, // 5
    { .code = 509, .bits = 9 }, // 6
    { .code = 510, .bits = 9 }, // 7
    { .code = 511, .bits = 9 }, // 8
    { .code = 248, .bits = 8 }, // 9
    { .code = 249, .bits = 8 }, // 10
    { .code = 250, .bits = 8 }, // 11
    { .code = 251, .bits = 8 }, // 12
    { .code = 252, .bits = 8 }, // 13
    { .code = 14, .bits = 4 },  // 14
    { .code = 2, .bits = 2 },   // 15
};

#if SIG_RANGE_W && !SIG_HUFFMAN_DYNAMIC && !SIG_W_CYC_ONLY
#ifndef W_PAIR_SYMBOLS
#define W_PAIR_SYMBOLS (P * P)
#endif
#define W_CYC_TOT 32768
#define W_DELTA_TOT 32768
#define W_PAIR_TOT 131072

#if SIG_W_DELTA || SIG_W_COND
static const uint32_t W_CYC_CUM[P + 1] = {
    0, 14974, 21757, 23799, 23800, 23801, 23802, 23803, 23804, 23805, 23806, 23807, 23808, 23809, 23937, 25089,
    32768
};
#endif

#if SIG_W_DELTA
static const uint32_t W_DELTA_CUM[P + 1] = {
    0, 1, 2, 5, 13, 141, 819, 3652, 10722, 22033, 29218, 31974, 32661, 32763, 32766, 32767,
    32768
};
#endif

#if SIG_W_COND
#define W_NEG_COND_BUCKETS 2
static const uint32_t W_NEG_COND_TOT[W_NEG_COND_BUCKETS] = { 32768, 32768 };
static const uint32_t W_NEG_COND_CUM[W_NEG_COND_BUCKETS][P + 1] = {
    { 0, 15734, 21657, 22952, 22953, 22954, 22955, 22956, 22957, 22958, 22959, 22960, 22961, 22962, 22963, 23888, 32768 },
    { 0, 13684, 21148, 24465, 24880, 24881, 24882, 24883, 24884, 24885, 24886, 24887, 24888, 24889, 24890, 25719, 32768 },
};
#endif

#if !SIG_W_DELTA && !SIG_W_COND
static const uint32_t W_PAIR_CUM[W_PAIR_SYMBOLS + 1] = {
    0, 28343, 42486, 44563, 44711, 44712, 44713, 44714, 44715, 44716, 44717, 44718, 44719, 44720, 44799, 47422,
    60763, 74411, 81250, 82713, 82792, 82793, 82794, 82795, 82796, 82797, 82798, 82799, 82800, 82801, 82863, 84138,
    90294, 92491, 93920, 94204, 94205, 94206, 94207, 94208, 94209, 94210, 94211, 94212, 94213, 94214, 94215, 94516,
    95637, 95716, 95795, 95796, 95797, 95798, 95799, 95800, 95801, 95802, 95803, 95804, 95805, 95806, 95807, 95835,
    95914, 95915, 95916, 95917, 95918, 95919, 95920, 95921, 95922, 95923, 95924, 95925, 95926, 95927, 95928, 95929,
    95930, 95931, 95932, 95933, 95934, 95935, 95936, 95937, 95938, 95939, 95940, 95941, 95942, 95943, 95944, 95945,
    95946, 95947, 95948, 95949, 95950, 95951, 95952, 95953, 95954, 95955, 95956, 95957, 95958, 95959, 95960, 95961,
    95962, 95963, 95964, 95965, 95966, 95967, 95968, 95969, 95970, 95971, 95972, 95973, 95974, 95975, 95976, 95977,
    95978, 95979, 95980, 95981, 95982, 95983, 95984, 95985, 95986, 95987, 95988, 95989, 95990, 95991, 95992, 95993,
    95994, 95995, 95996, 95997, 95998, 95999, 96000, 96001, 96002, 96003, 96004, 96005, 96006, 96007, 96008, 96009,
    96010, 96011, 96012, 96013, 96014, 96015, 96016, 96017, 96018, 96019, 96020, 96021, 96022, 96023, 96024, 96025,
    96026, 96027, 96028, 96029, 96030, 96031, 96032, 96033, 96034, 96035, 96036, 96037, 96038, 96039, 96040, 96041,
    96042, 96043, 96044, 96045, 96046, 96047, 96048, 96049, 96050, 96051, 96052, 96053, 96054, 96055, 96056, 96057,
    96058, 96171, 96199, 96200, 96201, 96202, 96203, 96204, 96205, 96206, 96207, 96208, 96209, 96210, 96211, 96212,
    96308, 98692, 99813, 100012, 100013, 100014, 100015, 100016, 100017, 100018, 100019, 100020, 100021, 100022, 100067, 100351,
    101575, 114507, 121243, 122467, 122529, 122530, 122531, 122532, 122533, 122534, 122535, 122536, 122537, 122538, 122617, 123994,
    131072
};
#endif
#endif

#if SIG_W_PAIR_HUFF
#define W_PAIR_MAX_BITS 16
#define W_PAIR_SYMBOLS (P * P)
static const fixed_code_t W_PAIR_CODE[W_PAIR_SYMBOLS] = {
    { .code = 0, .bits = 2 },
    { .code = 8, .bits = 4 },
    { .code = 508, .bits = 9 },
    { .code = 65328, .bits = 16 },
    { .code = 65329, .bits = 16 },
    { .code = 65330, .bits = 16 },
    { .code = 65331, .bits = 16 },
    { .code = 65332, .bits = 16 },
    { .code = 65333, .bits = 16 },
    { .code = 65334, .bits = 16 },
    { .code = 65335, .bits = 16 },
    { .code = 65336, .bits = 16 },
    { .code = 65337, .bits = 16 },
    { .code = 65338, .bits = 16 },
    { .code = 509, .bits = 9 },
    { .code = 2, .bits = 3 },
    { .code = 3, .bits = 3 },
    { .code = 9, .bits = 4 },
    { .code = 56, .bits = 6 },
    { .code = 65339, .bits = 16 },
    { .code = 65340, .bits = 16 },
    { .code = 65341, .bits = 16 },
    { .code = 65342, .bits = 16 },
    { .code = 65343, .bits = 16 },
    { .code = 65344, .bits = 16 },
    { .code = 65345, .bits = 16 },
    { .code = 65346, .bits = 16 },
    { .code = 65347, .bits = 16 },
    { .code = 65348, .bits = 16 },
    { .code = 65349, .bits = 16 },
    { .code = 120, .bits = 7 },
    { .code = 10, .bits = 4 },
    { .code = 57, .bits = 6 },
    { .code = 65350, .bits = 16 },
    { .code = 250, .bits = 8 },
    { .code = 65351, .bits = 16 },
    { .code = 65352, .bits = 16 },
    { .code = 65353, .bits = 16 },
    { .code = 65354, .bits = 16 },
    { .code = 65355, .bits = 16 },
    { .code = 65356, .bits = 16 },
    { .code = 65357, .bits = 16 },
    { .code = 65358, .bits = 16 },
    { .code = 65359, .bits = 16 },
    { .code = 65360, .bits = 16 },
    { .code = 65361, .bits = 16 },
    { .code = 65362, .bits = 16 },
    { .code = 121, .bits = 7 },
    { .code = 65363, .bits = 16 },
    { .code = 65364, .bits = 16 },
    { .code = 65365, .bits = 16 },
    { .code = 65366, .bits = 16 },
    { .code = 65367, .bits = 16 },
    { .code = 65368, .bits = 16 },
    { .code = 65369, .bits = 16 },
    { .code = 65370, .bits = 16 },
    { .code = 65371, .bits = 16 },
    { .code = 65372, .bits = 16 },
    { .code = 65373, .bits = 16 },
    { .code = 65374, .bits = 16 },
    { .code = 65375, .bits = 16 },
    { .code = 65376, .bits = 16 },
    { .code = 65377, .bits = 16 },
    { .code = 65378, .bits = 16 },
    { .code = 65379, .bits = 16 },
    { .code = 65380, .bits = 16 },
    { .code = 65381, .bits = 16 },
    { .code = 65382, .bits = 16 },
    { .code = 65383, .bits = 16 },
    { .code = 65384, .bits = 16 },
    { .code = 65385, .bits = 16 },
    { .code = 65386, .bits = 16 },
    { .code = 65387, .bits = 16 },
    { .code = 65388, .bits = 16 },
    { .code = 65389, .bits = 16 },
    { .code = 65390, .bits = 16 },
    { .code = 65391, .bits = 16 },
    { .code = 65392, .bits = 16 },
    { .code = 65393, .bits = 16 },
    { .code = 65394, .bits = 16 },
    { .code = 65395, .bits = 16 },
    { .code = 65396, .bits = 16 },
    { .code = 65397, .bits = 16 },
    { .code = 65398, .bits = 16 },
    { .code = 65399, .bits = 16 },
    { .code = 65400, .bits = 16 },
    { .code = 65401, .bits = 16 },
    { .code = 65402, .bits = 16 },
    { .code = 65403, .bits = 16 },
    { .code = 65404, .bits = 16 },
    { .code = 65405, .bits = 16 },
    { .code = 65406, .bits = 16 },
    { .code = 65407, .bits = 16 },
    { .code = 65408, .bits = 16 },
    { .code = 65409, .bits = 16 },
    { .code = 65410, .bits = 16 },
    { .code = 65411, .bits = 16 },
    { .code = 65412, .bits = 16 },
    { .code = 65413, .bits = 16 },
    { .code = 65414, .bits = 16 },
    { .code = 65415, .bits = 16 },
    { .code = 65416, .bits = 16 },
    { .code = 65417, .bits = 16 },
    { .code = 65418, .bits = 16 },
    { .code = 65419, .bits = 16 },
    { .code = 65420, .bits = 16 },
    { .code = 65421, .bits = 16 },
    { .code = 65422, .bits = 16 },
    { .code = 65423, .bits = 16 },
    { .code = 65424, .bits = 16 },
    { .code = 65425, .bits = 16 },
    { .code = 65426, .bits = 16 },
    { .code = 65427, .bits = 16 },
    { .code = 65428, .bits = 16 },
    { .code = 65429, .bits = 16 },
    { .code = 65430, .bits = 16 },
    { .code = 65431, .bits = 16 },
    { .code = 65432, .bits = 16 },
    { .code = 65433, .bits = 16 },
    { .code = 65434, .bits = 16 },
    { .code = 65435, .bits = 16 },
    { .code = 65436, .bits = 16 },
    { .code = 65437, .bits = 16 },
    { .code = 65438, .bits = 16 },
    { .code = 65439, .bits = 16 },
    { .code = 65440, .bits = 16 },
    { .code = 65441, .bits = 16 },
    { .code = 65442, .bits = 16 },
    { .code = 65443, .bits = 16 },
    { .code = 65444, .bits = 16 },
    { .code = 65445, .bits = 16 },
    { .code = 65446, .bits = 16 },
    { .code = 65447, .bits = 16 },
    { .code = 65448, .bits = 16 },
    { .code = 65449, .bits = 16 },
    { .code = 65450, .bits = 16 },
    { .code = 65451, .bits = 16 },
    { .code = 65452, .bits = 16 },
    { .code = 65453, .bits = 16 },
    { .code = 65454, .bits = 16 },
    { .code = 65455, .bits = 16 },
    { .code = 65456, .bits = 16 },
    { .code = 65457, .bits = 16 },
    { .code = 65458, .bits = 16 },
    { .code = 65459, .bits = 16 },
    { .code = 65460, .bits = 16 },
    { .code = 65461, .bits = 16 },
    { .code = 65462, .bits = 16 },
    { .code = 65463, .bits = 16 },
    { .code = 65464, .bits = 16 },
    { .code = 65465, .bits = 16 },
    { .code = 65466, .bits = 16 },
    { .code = 65467, .bits = 16 },
    { .code = 65468, .bits = 16 },
    { .code = 65469, .bits = 16 },
    { .code = 65470, .bits = 16 },
    { .code = 65471, .bits = 16 },
    { .code = 65472, .bits = 16 },
    { .code = 65473, .bits = 16 },
    { .code = 65474, .bits = 16 },
    { .code = 65475, .bits = 16 },
    { .code = 65476, .bits = 16 },
    { .code = 65477, .bits = 16 },
    { .code = 65478, .bits = 16 },
    { .code = 65479, .bits = 16 },
    { .code = 65480, .bits = 16 },
    { .code = 65481, .bits = 16 },
    { .code = 65482, .bits = 16 },
    { .code = 65483, .bits = 16 },
    { .code = 65484, .bits = 16 },
    { .code = 65485, .bits = 16 },
    { .code = 65486, .bits = 16 },
    { .code = 65487, .bits = 16 },
    { .code = 65488, .bits = 16 },
    { .code = 65489, .bits = 16 },
    { .code = 65490, .bits = 16 },
    { .code = 65491, .bits = 16 },
    { .code = 65492, .bits = 16 },
    { .code = 65493, .bits = 16 },
    { .code = 65494, .bits = 16 },
    { .code = 65495, .bits = 16 },
    { .code = 65496, .bits = 16 },
    { .code = 65497, .bits = 16 },
    { .code = 65498, .bits = 16 },
    { .code = 65499, .bits = 16 },
    { .code = 65500, .bits = 16 },
    { .code = 65501, .bits = 16 },
    { .code = 65502, .bits = 16 },
    { .code = 65503, .bits = 16 },
    { .code = 65504, .bits = 16 },
    { .code = 65505, .bits = 16 },
    { .code = 65506, .bits = 16 },
    { .code = 65507, .bits = 16 },
    { .code = 65508, .bits = 16 },
    { .code = 65509, .bits = 16 },
    { .code = 65510, .bits = 16 },
    { .code = 65511, .bits = 16 },
    { .code = 65512, .bits = 16 },
    { .code = 65513, .bits = 16 },
    { .code = 65514, .bits = 16 },
    { .code = 65515, .bits = 16 },
    { .code = 65516, .bits = 16 },
    { .code = 65517, .bits = 16 },
    { .code = 65518, .bits = 16 },
    { .code = 65519, .bits = 16 },
    { .code = 65520, .bits = 16 },
    { .code = 65521, .bits = 16 },
    { .code = 65522, .bits = 16 },
    { .code = 65523, .bits = 16 },
    { .code = 65524, .bits = 16 },
    { .code = 65525, .bits = 16 },
    { .code = 65526, .bits = 16 },
    { .code = 65527, .bits = 16 },
    { .code = 65528, .bits = 16 },
    { .code = 65529, .bits = 16 },
    { .code = 65530, .bits = 16 },
    { .code = 65531, .bits = 16 },
    { .code = 65532, .bits = 16 },
    { .code = 65533, .bits = 16 },
    { .code = 65534, .bits = 16 },
    { .code = 65535, .bits = 16 },
    { .code = 32640, .bits = 15 },
    { .code = 32641, .bits = 15 },
    { .code = 251, .bits = 8 },
    { .code = 58, .bits = 6 },
    { .code = 122, .bits = 7 },
    { .code = 123, .bits = 7 },
    { .code = 32642, .bits = 15 },
    { .code = 32643, .bits = 15 },
    { .code = 32644, .bits = 15 },
    { .code = 32645, .bits = 15 },
    { .code = 32646, .bits = 15 },
    { .code = 32647, .bits = 15 },
    { .code = 32648, .bits = 15 },
    { .code = 32649, .bits = 15 },
    { .code = 32650, .bits = 15 },
    { .code = 32651, .bits = 15 },
    { .code = 32652, .bits = 15 },
    { .code = 252, .bits = 8 },
    { .code = 59, .bits = 6 },
    { .code = 11, .bits = 4 },
    { .code = 12, .bits = 4 },
    { .code = 124, .bits = 7 },
    { .code = 32653, .bits = 15 },
    { .code = 32654, .bits = 15 },
    { .code = 32655, .bits = 15 },
    { .code = 32656, .bits = 15 },
    { .code = 32657, .bits = 15 },
    { .code = 32658, .bits = 15 },
    { .code = 32659, .bits = 15 },
    { .code = 32660, .bits = 15 },
    { .code = 32661, .bits = 15 },
    { .code = 32662, .bits = 15 },
    { .code = 32663, .bits = 15 },
    { .code = 253, .bits = 8 },
    { .code = 13, .bits = 4 },
};


#endif
static void w_huff_write_cyc(bitwriter_t *bw, uint8_t val) {
    if (val >= P) {
        return;
    }
    const fixed_code_t *entry = &W_CYC_CODE[val];
    bitwriter_write(bw, entry->code, entry->bits);
}

static void w_huff_write_neg(bitwriter_t *bw, uint8_t val) {
    if (val >= P) {
        return;
    }
    const fixed_code_t *entry = &W_NEG_CODE[val];
    bitwriter_write(bw, entry->code, entry->bits);
}

static int w_huff_read_cyc(bitreader_t *br, uint8_t *out) {
    int val = 0;
    if (!decode_fixed_symbol(br, W_CYC_CODE, P, 0, W_MAX_BITS, &val)) {
        return 0;
    }
    *out = (uint8_t)val;
    return 1;
}

static int w_huff_read_neg(bitreader_t *br, uint8_t *out) {
    int val = 0;
    if (!decode_fixed_symbol(br, W_NEG_CODE, P, 0, W_MAX_BITS, &val)) {
        return 0;
    }
    *out = (uint8_t)val;
    return 1;
}

#if SIG_W_PAIR_HUFF
static void w_huff_write_pair(bitwriter_t *bw, uint16_t pair) {
    if (pair >= W_PAIR_SYMBOLS) {
        return;
    }
    const fixed_code_t *entry = &W_PAIR_CODE[pair];
    bitwriter_write(bw, entry->code, entry->bits);
}

static int w_huff_read_pair(bitreader_t *br, uint16_t *out) {
    int val = 0;
    if (!decode_fixed_symbol(br, W_PAIR_CODE, W_PAIR_SYMBOLS, 0, W_PAIR_MAX_BITS, &val)) {
        return 0;
    }
    *out = (uint16_t)val;
    return 1;
}
#endif
#else
// Fixed Huffman for w (commitment): 0, 1, 2, P-2, P-1 + escape
// Canonical codes (prefix-free):
//   0    -> 0
//   P-1  -> 10
//   1    -> 110
//   2    -> 1110
//   P-2  -> 11110
//   ESC  -> 11111 + 8-bit literal
static void w_huff_write_cyc(bitwriter_t *bw, uint8_t val) {
    switch (val) {
    case 0:
        bitwriter_write(bw, 0x0, 1);
        break;
    case (P - 1):
        bitwriter_write(bw, 0x2, 2);  // 10
        break;
    case 1:
        bitwriter_write(bw, 0x6, 3);  // 110
        break;
    case 2:
        bitwriter_write(bw, 0xE, 4);  // 1110
        break;
    case (P - 2):
        bitwriter_write(bw, 0x1E, 5);  // 11110
        break;
    default:
        bitwriter_write(bw, 0x1F, 5);  // 11111 (escape)
        bitwriter_write(bw, val, 8);
        break;
    }
}

static int w_huff_read_cyc(bitreader_t *br, uint8_t *out) {
    int b0 = bitreader_read_bit(br);
    if (b0 == 0) {
        *out = 0;
        return 1;
    }
    int b1 = bitreader_read_bit(br);
    if (b1 == 0) {
        *out = (uint8_t)(P - 1);
        return 1;
    }
    int b2 = bitreader_read_bit(br);
    if (b2 == 0) {
        *out = 1;
        return 1;
    }
    int b3 = bitreader_read_bit(br);
    if (b3 == 0) {
        *out = 2;
        return 1;
    }
    int b4 = bitreader_read_bit(br);
    if (b4 == 0) {
        *out = (uint8_t)(P - 2);
        return 1;
    }
    uint8_t val = 0;
    for (int i = 0; i < 8; i++) {
        val = (uint8_t)((val << 1) | (uint8_t)bitreader_read_bit(br));
    }
    *out = val;
    return 1;
}

static void w_huff_write_neg(bitwriter_t *bw, uint8_t val) {
    w_huff_write_cyc(bw, val);
}

static int w_huff_read_neg(bitreader_t *br, uint8_t *out) {
    return w_huff_read_cyc(br, out);
}
#endif

// Forward declarations for pk/w Huffman (values in [0,P-1])
#define PK_MAX_SYMBOLS P
static huffman_node_t* build_huffman_tree_pk(int freq[PK_MAX_SYMBOLS], int *num_leaves);
static huffman_entry_t* find_entry_pk(huffman_entry_t codebook[], int codebook_size, int16_t symbol);

static int minimal_write_d(bitwriter_t *bw, int32_t v);

// Huffman encode signature (s_cyc + s_neg, w)
// Signature = (s, w) where w is the commitment
int huffman_encode_sig(const signature_t *sig, const public_key_t *pk,
                       const uint8_t *msg, size_t msg_len, huffman_sig_t *out) {
#if SIG_LOSSY_ZERO
    uint8_t is_zeroed[N];
    derive_zero_positions(is_zeroed, SIG_LOSSY_ZERO_K, pk->seed, msg, msg_len);
#endif

#if SIG_DEHYDRATE_S
    // Dehydrate: zero 25 positions per ring before compression for better Huffman
    // These will be restored by rehydrate_ring() on decode using w = s * y
    ring_t s_cyc_dh, s_neg_dh;
    memcpy(&s_cyc_dh, &sig->s_cyc, sizeof(ring_t));
    memcpy(&s_neg_dh, &sig->s_neg, sizeof(ring_t));

    // Dehydrate each ring independently (different positions via domain separators)
    dehydrate_ring((dehydrate_ring_t*)&s_cyc_dh, pk->seed, msg, msg_len, "DCYC", 0, NULL);
    dehydrate_ring((dehydrate_ring_t*)&s_neg_dh, pk->seed, msg, msg_len, "DNEG", 0, NULL);

    // Use dehydrated versions for encoding
    const ring_t *enc_s_cyc = &s_cyc_dh;
    const ring_t *enc_s_neg = &s_neg_dh;
#else
    const ring_t *enc_s_cyc = &sig->s_cyc;
    const ring_t *enc_s_neg = &sig->s_neg;
#endif

#if SIG_DEHYDRATE_W
    // Get dehydration positions
    uint8_t dh_pos_cyc[DEHYDRATE_W_COUNT], dh_pos_neg[DEHYDRATE_W_COUNT];
    derive_w_dehydrate_positions(dh_pos_cyc, pk->seed, msg, msg_len, "DWCY");
    derive_w_dehydrate_positions(dh_pos_neg, pk->seed, msg, msg_len, "DWNG");

    // Store w values at dehydrated positions (4 bits each, packed)
    memset(out->w_dh_cyc, 0, sizeof(out->w_dh_cyc));
    memset(out->w_dh_neg, 0, sizeof(out->w_dh_neg));
    for (int i = 0; i < DEHYDRATE_W_COUNT; i++) {
        uint8_t val_cyc = (uint8_t)sig->w_cyc.c[dh_pos_cyc[i]] & 0xF;
        uint8_t val_neg = (uint8_t)sig->w_neg.c[dh_pos_neg[i]] & 0xF;
        if (i % 2 == 0) {
            out->w_dh_cyc[i / 2] = val_cyc;
            out->w_dh_neg[i / 2] = val_neg;
        } else {
            out->w_dh_cyc[i / 2] |= val_cyc << 4;
            out->w_dh_neg[i / 2] |= val_neg << 4;
        }
    }

    // Dehydrate w (zero the positions)
    ring_t w_cyc_dh, w_neg_dh;
    memcpy(&w_cyc_dh, &sig->w_cyc, sizeof(ring_t));
    memcpy(&w_neg_dh, &sig->w_neg, sizeof(ring_t));
    dehydrate_w_ring(&w_cyc_dh, pk->seed, msg, msg_len, "DWCY");
    dehydrate_w_ring(&w_neg_dh, pk->seed, msg, msg_len, "DWNG");
    const ring_t *challenge_w_cyc = &w_cyc_dh;
    const ring_t *challenge_w_neg = &w_neg_dh;
#else
    const ring_t *challenge_w_cyc = &sig->w_cyc;
    const ring_t *challenge_w_neg = &sig->w_neg;
#endif

    uint8_t challenge_seed[SIGNATURE_CHALLENGE_BYTES];
    hash_to_challenge(challenge_seed, challenge_w_cyc, challenge_w_neg, pk, msg, msg_len);
    uint8_t perm[N];
    minimal_perm_from_seed(perm, challenge_seed, sizeof(challenge_seed));

#if SIG_RANGE_S && !SIG_HUFFMAN_DYNAMIC
    rc_enc_t s_rc;
    rc_enc_init(&s_rc, out->s_data, sizeof(out->s_data));

#if SIG_DEHYDRATE_S
    // Debug: trace position 2 in both rings
    static int dbg_once = 0;
    if (!dbg_once) {
        dbg_once = 1;
        uint8_t dbg_pos_cyc[DEHYDRATE_COUNT], dbg_pos_neg[DEHYDRATE_COUNT];
        derive_dehydrate_positions_ring(dbg_pos_cyc, pk->seed, msg, msg_len, "DCYC", 0, NULL);
        derive_dehydrate_positions_ring(dbg_pos_neg, pk->seed, msg, msg_len, "DNEG", 0, NULL);
        int pos2_in_cyc = -1, pos2_in_neg = -1;
        for (int dd = 0; dd < DEHYDRATE_COUNT; dd++) {
            if (dbg_pos_cyc[dd] == 2) pos2_in_cyc = dd;
            if (dbg_pos_neg[dd] == 2) pos2_in_neg = dd;
        }
        fprintf(stderr, "DEBUG ENCODE: pos 2 at DCYC index %d, at DNEG index %d\n",
                pos2_in_cyc, pos2_in_neg);
        fprintf(stderr, "DEBUG ENCODE: s_cyc orig[2]=%d, dehydrated[2]=%d\n",
                (int)sig->s_cyc.c[2], (int)enc_s_cyc->c[2]);
        fprintf(stderr, "DEBUG ENCODE: s_neg orig[2]=%d, dehydrated[2]=%d\n",
                (int)sig->s_neg.c[2], (int)enc_s_neg->c[2]);
        // Print ALL DNEG positions
        fprintf(stderr, "DEBUG ENCODE: ALL DNEG positions: ");
        for (int dd = 0; dd < DEHYDRATE_COUNT; dd++) fprintf(stderr, "%d ", dbg_pos_neg[dd]);
        fprintf(stderr, "\n");
    }
#endif

    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        int32_t val = centered(enc_s_cyc->c[i]);
        int sym = (val >= S_CYC_SMALL_MIN && val <= S_CYC_SMALL_MAX)
            ? (val - S_CYC_SMALL_MIN)
            : S_CYC_SMALL_ESC;
        rc_encode(&s_rc, S_CYC_SMALL_CUM[sym], S_CYC_SMALL_CUM[sym + 1], S_CYC_SMALL_TOT);
        if (sym == S_CYC_SMALL_ESC) {
            int32_t raw = val + S_CYC_ESC_BIAS;
            if (raw < 0 || raw >= (1 << S_CYC_ESC_RAW_BITS)) return 0;
            rc_encode_uniform(&s_rc, (uint32_t)raw, (1u << S_CYC_ESC_RAW_BITS));
        }
    }

    // Encode delta = (s_cyc - s_neg) / 2 instead of s_neg directly
    // Delta has lower entropy and verifier can reconstruct s_neg = s_cyc - 2*delta
    for (int i = 0; i < N; i++) {
        int idx = perm[i];
#if SIG_LOSSY_ZERO
        if (is_zeroed[idx]) {
            continue;
        }
#endif
        // Compute delta = (s_cyc - s_neg) / 2
        int32_t s_cyc_val = centered(enc_s_cyc->c[idx]);
        int32_t s_neg_val = centered(enc_s_neg->c[idx]);
        int32_t diff = s_cyc_val - s_neg_val;
        // Coupling guarantees diff is even
        if (diff & 1) return 0;  // Should never happen with valid signature
        int32_t delta = diff / 2;

        int sym = (delta >= S_DELTA_SMALL_MIN && delta <= S_DELTA_SMALL_MAX)
            ? (delta - S_DELTA_SMALL_MIN)
            : S_DELTA_SMALL_ESC;
        rc_encode(&s_rc, S_DELTA_SMALL_CUM[sym], S_DELTA_SMALL_CUM[sym + 1], S_DELTA_SMALL_TOT);
        if (sym == S_DELTA_SMALL_ESC) {
            int32_t raw = delta + S_DELTA_ESC_BIAS;
            if (raw < 0 || raw >= (1 << S_DELTA_ESC_RAW_BITS)) return 0;
            rc_encode_uniform(&s_rc, (uint32_t)raw, (1u << S_DELTA_ESC_RAW_BITS));
        }
    }

    out->s_len = rc_finish(&s_rc);
    if (!s_rc.ok) {
        return 0;
    }
#else
#if SIG_HUFFMAN_DYNAMIC
    // Collect values and build frequency table for s
    int freq[S_MAX_SYMBOLS] = {0};

    // For s_cyc: full 5-bit values [-16, 15]
    for (int i = 0; i < N; i++) {
        int32_t val = centered(enc_s_cyc->c[i]);
        if (val < -31 || val > 31) return 0;  // Out of range
        freq[val + S_SYMBOL_OFFSET]++;
    }

    // For s_neg: full 5-bit values [-16, 15]
    for (int i = 0; i < N; i++) {
        int32_t val = centered(enc_s_neg->c[i]);
        if (val < -31 || val > 31) return 0;
        freq[val + S_SYMBOL_OFFSET]++;
    }

    // Build Huffman tree
    int num_leaves;
    huffman_node_t *root = build_huffman_tree_s(freq, &num_leaves);
    if (!root) return 0;

    // Generate codebook
    huffman_entry_t codebook[S_MAX_SYMBOLS];
    int codebook_size;
    generate_codes(root, codebook, &codebook_size);
#endif

    bitwriter_t bw;
    bitwriter_init(&bw, out->s_data, sizeof(out->s_data));

#if SIG_HUFFMAN_DYNAMIC
    // Write codebook size (6 bits, max 64 entries)
    bitwriter_write(&bw, codebook_size, 6);

    // Write codebook entries: symbol (6 bits), length (4 bits), code
    for (int i = 0; i < codebook_size; i++) {
        int sym_out = codebook[i].symbol + S_SYMBOL_OFFSET;
        bitwriter_write(&bw, sym_out, 6);
        bitwriter_write(&bw, codebook[i].bits, 4);
        bitwriter_write(&bw, codebook[i].code, codebook[i].bits);
    }
#endif

    // Encode s_cyc
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        int32_t val = centered(enc_s_cyc->c[i]);
#if SIG_HUFFMAN_DYNAMIC
        huffman_entry_t *entry = find_entry_s(codebook, codebook_size, val);
        if (!entry) { free_huffman_tree(root); return 0; }
        bitwriter_write(&bw, entry->code, entry->bits);
#else
        if (val < S_CYC_MIN || val > S_CYC_MAX) {
            int32_t raw = val + S_CYC_ESC_BIAS;
            if (raw < 0 || raw >= (1 << S_CYC_ESC_RAW_BITS)) return 0;
            bitwriter_write(&bw, S_CYC_ESC_CODE, S_CYC_ESC_BITS);
            bitwriter_write(&bw, (uint32_t)raw, S_CYC_ESC_RAW_BITS);
        } else {
            const fixed_code_t *entry = &S_CYC_CODE[val - S_CYC_MIN];
            bitwriter_write(&bw, entry->code, entry->bits);
        }
#endif
    }

    // Encode s_neg in permuted order
    for (int i = 0; i < N; i++) {
        int idx = perm[i];
#if SIG_LOSSY_ZERO
        if (is_zeroed[idx]) {
            continue;
        }
#endif
        int32_t val = centered(enc_s_neg->c[idx]);
#if SIG_HUFFMAN_DYNAMIC
        huffman_entry_t *entry = find_entry_s(codebook, codebook_size, val);
        if (!entry) { free_huffman_tree(root); return 0; }
        bitwriter_write(&bw, entry->code, entry->bits);
#else
        if (val < S_CYC_MIN || val > S_CYC_MAX) {
            int32_t raw = val + S_CYC_ESC_BIAS;
            if (raw < 0 || raw >= (1 << S_CYC_ESC_RAW_BITS)) return 0;
            bitwriter_write(&bw, S_CYC_ESC_CODE, S_CYC_ESC_BITS);
            bitwriter_write(&bw, (uint32_t)raw, S_CYC_ESC_RAW_BITS);
        } else {
            const fixed_code_t *entry = &S_CYC_CODE[val - S_CYC_MIN];
            bitwriter_write(&bw, entry->code, entry->bits);
        }
#endif
    }

#if SIG_HUFFMAN_DYNAMIC
    free_huffman_tree(root);
#endif
    out->s_len = bitwriter_finish(&bw);
#endif

#if SIG_RANGE_W && !SIG_HUFFMAN_DYNAMIC && !SIG_W_CYC_ONLY && (P == 16)
    // Use dehydrated w from above (challenge_w_cyc, challenge_w_neg) for encoding
    const ring_t *enc_w_cyc = challenge_w_cyc;
    const ring_t *enc_w_neg = challenge_w_neg;

    rc_enc_t w_rc;
    rc_enc_init(&w_rc, out->w_data, sizeof(out->w_data));
#if SIG_W_DELTA
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        uint32_t w_cyc = (uint32_t)enc_w_cyc->c[i];
        if (w_cyc >= P) {
            return 0;
        }
        rc_encode(&w_rc, W_CYC_CUM[w_cyc], W_CYC_CUM[w_cyc + 1], W_CYC_TOT);
        int32_t delta = centered_p(mod_p((int32_t)enc_w_neg->c[i] - (int32_t)enc_w_cyc->c[i]));
        uint32_t d_idx = (uint32_t)(delta + (P / 2));
        if (d_idx >= P) {
            return 0;
        }
        rc_encode(&w_rc, W_DELTA_CUM[d_idx], W_DELTA_CUM[d_idx + 1], W_DELTA_TOT);
    }
#elif SIG_W_COND
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        uint32_t w_cyc = (uint32_t)enc_w_cyc->c[i];
        if (w_cyc >= P) {
            return 0;
        }
        rc_encode(&w_rc, W_CYC_CUM[w_cyc], W_CYC_CUM[w_cyc + 1], W_CYC_TOT);
        uint32_t w_neg = (uint32_t)enc_w_neg->c[i];
        if (w_neg >= P) {
            return 0;
        }
        int bucket = (w_cyc == 0 || w_cyc == (P - 1)) ? 0 : 1;
        rc_encode(&w_rc, W_NEG_COND_CUM[bucket][w_neg],
                  W_NEG_COND_CUM[bucket][w_neg + 1],
                  W_NEG_COND_TOT[bucket]);
    }
#else
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        uint32_t pair = (uint32_t)enc_w_cyc->c[i] * P + (uint32_t)enc_w_neg->c[i];
        if (pair >= W_PAIR_SYMBOLS) {
            return 0;
        }
        rc_encode(&w_rc, W_PAIR_CUM[pair], W_PAIR_CUM[pair + 1], W_PAIR_TOT);
    }
#endif
    out->w_len = rc_finish(&w_rc);
    if (!w_rc.ok) {
        return 0;
    }
#else
    bitwriter_t w_bw;
    bitwriter_init(&w_bw, out->w_data, sizeof(out->w_data));

#if SIG_HUFFMAN_DYNAMIC
    // Huffman encode w (commitment) - values in [0, P-1]
    // Build frequency table for w
    int w_freq[PK_MAX_SYMBOLS] = {0};
    for (int i = 0; i < N; i++) {
        w_freq[sig->w_cyc.c[i]]++;
#if !SIG_W_CYC_ONLY
        w_freq[sig->w_neg.c[i]]++;
#endif
    }

    // Build Huffman tree for w
    int w_num_leaves;
    huffman_node_t *w_root = build_huffman_tree_pk(w_freq, &w_num_leaves);
    if (!w_root) return 0;

    // Generate w codebook
    huffman_entry_t w_codebook[PK_MAX_SYMBOLS];
    int w_codebook_size;
    generate_codes(w_root, w_codebook, &w_codebook_size);

    // Write w codebook size (8 bits)
    bitwriter_write(&w_bw, w_codebook_size, 8);

    // Write w codebook entries
    for (int i = 0; i < w_codebook_size; i++) {
        bitwriter_write(&w_bw, w_codebook[i].symbol, 8);
        bitwriter_write(&w_bw, w_codebook[i].bits, 5);
        bitwriter_write(&w_bw, w_codebook[i].code, w_codebook[i].bits);
    }
#endif

    // Encode w (commitment)
#if SIG_HUFFMAN_DYNAMIC
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        huffman_entry_t *entry = find_entry_pk(w_codebook, w_codebook_size, sig->w_cyc.c[i]);
        if (!entry) { free_huffman_tree(w_root); return 0; }
        bitwriter_write(&w_bw, entry->code, entry->bits);
    }
#if !SIG_W_CYC_ONLY
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        huffman_entry_t *entry = find_entry_pk(w_codebook, w_codebook_size, sig->w_neg.c[i]);
        if (!entry) { free_huffman_tree(w_root); return 0; }
        bitwriter_write(&w_bw, entry->code, entry->bits);
    }
#endif
#else
#if SIG_W_PAIR_HUFF && !SIG_W_CYC_ONLY && (P == 16)
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        uint16_t pair = (uint16_t)(sig->w_cyc.c[i] * P + sig->w_neg.c[i]);
        w_huff_write_pair(&w_bw, pair);
    }
#else
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        w_huff_write_cyc(&w_bw, (uint8_t)sig->w_cyc.c[i]);
    }
#if !SIG_W_CYC_ONLY
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed[i]) {
            continue;
        }
#endif
        w_huff_write_neg(&w_bw, (uint8_t)sig->w_neg.c[i]);
    }
#endif
#endif
#endif

#if SIG_HUFFMAN_DYNAMIC
    free_huffman_tree(w_root);
#endif
    out->w_len = bitwriter_finish(&w_bw);
#endif
    return 1;
}

static int minimal_write_s(bitwriter_t *bw, int32_t v) {
    if (v < MIN_S_MIN || v > MIN_S_MAX) {
        int32_t raw = v + MIN_S_ESC_BIAS;
        if (raw < 0 || raw >= (1 << MIN_S_ESC_RAW_BITS)) return 0;
        bitwriter_write(bw, MIN_S_ESC_CODE, MIN_S_ESC_BITS);
        bitwriter_write(bw, (uint32_t)raw, MIN_S_ESC_RAW_BITS);
        return 1;
    }
    const fixed_code_t *entry = &MIN_S_CODE[v - MIN_S_MIN];
    bitwriter_write(bw, entry->code, entry->bits);
    return 1;
}

static int minimal_write_d(bitwriter_t *bw, int32_t v) {
    if (v < MIN_D_MIN || v > MIN_D_MAX) {
        int32_t raw = v + MIN_D_ESC_BIAS;
        if (raw < 0 || raw >= (1 << MIN_D_ESC_RAW_BITS)) return 0;
        bitwriter_write(bw, MIN_D_ESC_CODE, MIN_D_ESC_BITS);
        bitwriter_write(bw, (uint32_t)raw, MIN_D_ESC_RAW_BITS);
        return 1;
    }
    const fixed_code_t *entry = &MIN_D_CODE[v - MIN_D_MIN];
    if (entry->bits == 0) {
        int32_t raw = v + MIN_D_ESC_BIAS;
        if (raw < 0 || raw >= (1 << MIN_D_ESC_RAW_BITS)) return 0;
        bitwriter_write(bw, MIN_D_ESC_CODE, MIN_D_ESC_BITS);
        bitwriter_write(bw, (uint32_t)raw, MIN_D_ESC_RAW_BITS);
        return 1;
    }
    bitwriter_write(bw, entry->code, entry->bits);
    return 1;
}

static int minimal_read_s(bitreader_t *br, int32_t *out) {
    uint32_t bits_read = 0;
    for (int bits = 1; bits <= MIN_S_MAX_BITS; bits++) {
        bits_read = (bits_read << 1) | (uint32_t)bitreader_read_bit(br);
        if (bits == MIN_S_ESC_BITS && bits_read == MIN_S_ESC_CODE) {
            uint32_t raw = 0;
            for (int i = 0; i < MIN_S_ESC_RAW_BITS; i++) {
                raw = (raw << 1) | (uint32_t)bitreader_read_bit(br);
            }
            *out = (int32_t)raw - MIN_S_ESC_BIAS;
            return 1;
        }
        for (int i = 0; i < MIN_S_SYMBOLS; i++) {
            const fixed_code_t *entry = &MIN_S_CODE[i];
            if (entry->bits == bits && entry->code == bits_read) {
                *out = i + MIN_S_MIN;
                return 1;
            }
        }
    }
    return 0;
}

static int minimal_read_d(bitreader_t *br, int32_t *out) {
    uint32_t bits_read = 0;
    for (int bits = 1; bits <= MIN_D_MAX_BITS; bits++) {
        bits_read = (bits_read << 1) | (uint32_t)bitreader_read_bit(br);
        if (bits == MIN_D_ESC_BITS && bits_read == MIN_D_ESC_CODE) {
            uint32_t raw = 0;
            for (int i = 0; i < MIN_D_ESC_RAW_BITS; i++) {
                raw = (raw << 1) | (uint32_t)bitreader_read_bit(br);
            }
            *out = (int32_t)raw - MIN_D_ESC_BIAS;
            return 1;
        }
        for (int i = 0; i < MIN_D_SYMBOLS; i++) {
            const fixed_code_t *entry = &MIN_D_CODE[i];
            if (entry->bits == bits && entry->code == bits_read) {
                *out = i + MIN_D_MIN;
                return 1;
            }
        }
    }
    return 0;
}

static void minimal_perm_fill(uint8_t *buf, size_t buf_len,
                              const uint8_t *seed, size_t seed_len, uint8_t ctr) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    uint8_t ds = 0xA5;
    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, seed, seed_len);
    EVP_DigestUpdate(ctx, &ds, 1);
    EVP_DigestUpdate(ctx, &ctr, 1);
    EVP_DigestFinalXOF(ctx, buf, buf_len);
    EVP_MD_CTX_free(ctx);
}

static void minimal_perm_from_seed(uint8_t perm[N], const uint8_t *seed, size_t seed_len) {
    for (int i = 0; i < N; i++) {
        perm[i] = (uint8_t)i;
    }

    uint8_t buf[1024];
    size_t buf_idx = 0;
    size_t buf_len = sizeof(buf);
    uint8_t ctr = 0;

    minimal_perm_fill(buf, buf_len, seed, seed_len, ctr++);

    for (int i = N - 1; i > 0; i--) {
        uint8_t v = 0;
        do {
            if (buf_idx >= buf_len) {
                minimal_perm_fill(buf, buf_len, seed, seed_len, ctr++);
                buf_idx = 0;
            }
            v = buf[buf_idx++];
        } while (v > (uint8_t)i);
        uint8_t tmp = perm[i];
        perm[i] = perm[v];
        perm[v] = tmp;
    }
}

static int encode_minimal_payload(const ring_t *s_cyc, const ring_t *delta,
                                  const uint8_t perm[N], minimal_sig_t *out) {
    bitwriter_t bw;
    bitwriter_init(&bw, out->s_data, sizeof(out->s_data));

    for (int i = 0; i < N; i++) {
        int32_t v = centered(s_cyc->c[i]);
        if (!minimal_write_s(&bw, v)) return 0;
    }

    for (int i = 0; i < N; i++) {
        int32_t v = centered(delta->c[perm[i]]);
        if (!minimal_write_d(&bw, v)) return 0;
    }

    out->s_len = bitwriter_finish(&bw);
    return 1;
}

typedef struct {
    uint16_t idx;
    int8_t diff;
} hint_pair_t;

static int build_w_hints(hint_pair_t *pairs, int max_pairs,
                         const ring_t *w_round_cyc, const ring_t *w_round_neg,
                         const ring_t *w_round_prime_cyc, const ring_t *w_round_prime_neg,
                         int *out_count) {
    int count = 0;
    for (int i = 0; i < N; i++) {
        int32_t diff = centered_p(mod_p((int32_t)w_round_cyc->c[i] -
                                        (int32_t)w_round_prime_cyc->c[i]));
        if (diff != 0) {
            if (diff < -HINT_DIFF_BIAS || diff >= HINT_DIFF_BIAS) return 0;
            if (count >= max_pairs) return 0;
            pairs[count].idx = (uint16_t)i;
            pairs[count].diff = (int8_t)diff;
            count++;
        }
    }
    for (int i = 0; i < N; i++) {
        int32_t diff = centered_p(mod_p((int32_t)w_round_neg->c[i] -
                                        (int32_t)w_round_prime_neg->c[i]));
        if (diff != 0) {
            if (diff < -HINT_DIFF_BIAS || diff >= HINT_DIFF_BIAS) return 0;
            if (count >= max_pairs) return 0;
            pairs[count].idx = (uint16_t)(i + N);
            pairs[count].diff = (int8_t)diff;
            count++;
        }
    }
    *out_count = count;
    return 1;
}

static int encode_w_hints(uint8_t *out, int out_cap,
                          const ring_t *w_round_cyc, const ring_t *w_round_neg,
                          const ring_t *w_round_prime_cyc, const ring_t *w_round_prime_neg,
                          int *out_len, int *out_count) {
    hint_pair_t pairs[HINT_MAX_COUNT];
    int count = 0;
    if (!build_w_hints(pairs, HINT_MAX_COUNT, w_round_cyc, w_round_neg,
                       w_round_prime_cyc, w_round_prime_neg, &count)) {
        return 0;
    }
    bitwriter_t bw;
    bitwriter_init(&bw, out, out_cap);
    if (!bitwriter_write_bits(&bw, (uint32_t)count, HINT_COUNT_BITS)) return 0;
    for (int i = 0; i < count; i++) {
        uint32_t diff_u = (uint32_t)(pairs[i].diff + HINT_DIFF_BIAS);
        if (!bitwriter_write_bits(&bw, pairs[i].idx, HINT_INDEX_BITS)) return 0;
        if (!bitwriter_write_bits(&bw, diff_u, HINT_DIFF_BITS)) return 0;
    }
    *out_len = bitwriter_finish(&bw);
    if (out_count) {
        *out_count = count;
    }
    return 1;
}

static int apply_w_hints(const uint8_t *data, int data_len,
                         ring_t *w_round_cyc, ring_t *w_round_neg,
                         int *out_count) {
    bitreader_t br;
    bitreader_init(&br, data, data_len);
    uint32_t count = 0;
    if (!bitreader_read_bits(&br, HINT_COUNT_BITS, &count)) return 0;
    if (count > HINT_MAX_COUNT) return 0;
    uint32_t prev_idx = UINT32_MAX;
    for (uint32_t i = 0; i < count; i++) {
        uint32_t idx = 0;
        uint32_t diff_u = 0;
        if (!bitreader_read_bits(&br, HINT_INDEX_BITS, &idx)) return 0;
        if (!bitreader_read_bits(&br, HINT_DIFF_BITS, &diff_u)) return 0;
        if (idx >= (uint32_t)(2 * N)) return 0;
        if (idx <= prev_idx) return 0;
        int32_t diff = (int32_t)diff_u - HINT_DIFF_BIAS;
        if (diff == 0 || diff < -HINT_DIFF_BIAS || diff >= HINT_DIFF_BIAS) return 0;
        if (idx < (uint32_t)N) {
            w_round_cyc->c[idx] = mod_p((int32_t)w_round_cyc->c[idx] + diff);
        } else {
            uint32_t j = idx - (uint32_t)N;
            w_round_neg->c[j] = mod_p((int32_t)w_round_neg->c[j] + diff);
        }
        prev_idx = idx;
    }
    if (out_count) {
        *out_count = (int)count;
    }
    return 1;
}

static int huffman_decode_s(const uint8_t *s_data, int s_len,
                            const uint8_t *perm_seed, size_t perm_seed_len,
                            const uint8_t *is_zeroed,
                            ring_t *s_cyc, ring_t *s_neg) {
#if !SIG_LOSSY_ZERO
    (void)is_zeroed;
#endif
#if SIG_RANGE_S && !SIG_HUFFMAN_DYNAMIC
    rc_dec_t s_rc;
    rc_dec_init(&s_rc, s_data, s_len);

    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            s_cyc->c[i] = 0;
            continue;
        }
#endif
        int sym = 0;
        if (!rc_decode_symbol(&s_rc, S_CYC_SMALL_CUM, S_CYC_SMALL_TOTAL_SYMBOLS,
                              S_CYC_SMALL_TOT, &sym)) {
            return 0;
        }
        int val = 0;
        if (sym == S_CYC_SMALL_ESC) {
            uint32_t raw = 0;
            if (!rc_decode_uniform(&s_rc, (1u << S_CYC_ESC_RAW_BITS), &raw)) {
                return 0;
            }
            val = (int32_t)raw - S_CYC_ESC_BIAS;
        } else {
            val = sym + S_CYC_SMALL_MIN;
        }
        s_cyc->c[i] = mod_q(val);
    }

    // Decode delta and reconstruct s_neg = s_cyc - 2*delta
    uint8_t perm[N];
    minimal_perm_from_seed(perm, perm_seed, perm_seed_len);
    for (int i = 0; i < N; i++) {
        int idx = perm[i];
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[idx]) {
            s_neg->c[idx] = 0;
            continue;
        }
#endif
        int sym = 0;
        if (!rc_decode_symbol(&s_rc, S_DELTA_SMALL_CUM, S_DELTA_SMALL_TOTAL_SYMBOLS,
                              S_DELTA_SMALL_TOT, &sym)) {
            return 0;
        }
        int delta = 0;
        if (sym == S_DELTA_SMALL_ESC) {
            uint32_t raw = 0;
            if (!rc_decode_uniform(&s_rc, (1u << S_DELTA_ESC_RAW_BITS), &raw)) {
                return 0;
            }
            delta = (int32_t)raw - S_DELTA_ESC_BIAS;
        } else {
            delta = sym + S_DELTA_SMALL_MIN;
        }
        // Reconstruct s_neg = s_cyc - 2*delta
        int32_t s_cyc_val = centered(s_cyc->c[idx]);
        int32_t s_neg_val = s_cyc_val - 2 * delta;
        s_neg->c[idx] = mod_q(s_neg_val);
    }

    return s_rc.ok;
#else

    bitreader_t br;
    bitreader_init(&br, s_data, s_len);

#if SIG_HUFFMAN_DYNAMIC
    // Read codebook size
    int codebook_size = 0;
    for (int b = 0; b < 6; b++) {
        codebook_size = (codebook_size << 1) | bitreader_read_bit(&br);
    }

    if (codebook_size == 0 || codebook_size > S_MAX_SYMBOLS) {
        return 0;
    }

    // Build decoding tree from codebook
    huffman_node_t *root = malloc(sizeof(huffman_node_t));
    root->symbol = INT16_MIN;
    root->left = NULL;
    root->right = NULL;

    huffman_entry_t codebook[S_MAX_SYMBOLS];

    for (int i = 0; i < codebook_size; i++) {
        // Read symbol (6 bits)
        int sym = 0;
        for (int b = 0; b < 6; b++) {
            sym = (sym << 1) | bitreader_read_bit(&br);
        }
        codebook[i].symbol = sym - S_SYMBOL_OFFSET;

        // Read code length (4 bits)
        int bits = 0;
        for (int b = 0; b < 4; b++) {
            bits = (bits << 1) | bitreader_read_bit(&br);
        }
        codebook[i].bits = bits;

        // Read code
        uint32_t code = 0;
        for (int b = 0; b < bits; b++) {
            code = (code << 1) | bitreader_read_bit(&br);
        }
        codebook[i].code = code;

        // Build tree node for this code
        huffman_node_t *node = root;
        for (int b = bits - 1; b >= 0; b--) {
            int bit = (code >> b) & 1;
            if (bit == 0) {
                if (!node->left) {
                    node->left = malloc(sizeof(huffman_node_t));
                    node->left->symbol = INT16_MIN;
                    node->left->left = NULL;
                    node->left->right = NULL;
                }
                node = node->left;
            } else {
                if (!node->right) {
                    node->right = malloc(sizeof(huffman_node_t));
                    node->right->symbol = INT16_MIN;
                    node->right->left = NULL;
                    node->right->right = NULL;
                }
                node = node->right;
            }
        }
        node->symbol = codebook[i].symbol;
    }
#endif

    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            s_cyc->c[i] = 0;
            continue;
        }
#endif
#if SIG_HUFFMAN_DYNAMIC
        huffman_node_t *node = root;
        while (node->symbol == INT16_MIN) {
            int bit = bitreader_read_bit(&br);
            node = bit ? node->right : node->left;
            if (!node) {
                free_huffman_tree(root);
                return 0;
            }
        }
        s_cyc->c[i] = mod_q(node->symbol);
#else
        int val = 0;
        if (!decode_fixed_symbol_esc(&br, S_CYC_CODE, S_CYC_SYMBOLS, S_CYC_MIN,
                                     S_CYC_MAX_BITS, S_CYC_ESC_CODE, S_CYC_ESC_BITS,
                                     S_CYC_ESC_RAW_BITS, S_CYC_ESC_BIAS, &val)) {
            return 0;
        }
        s_cyc->c[i] = mod_q(val);
#endif
    }

    uint8_t perm[N];
    minimal_perm_from_seed(perm, perm_seed, perm_seed_len);
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        int idx = perm[i];
        if (is_zeroed && is_zeroed[idx]) {
            s_neg->c[idx] = 0;
            continue;
        }
#endif
#if SIG_HUFFMAN_DYNAMIC
        huffman_node_t *node = root;
        while (node->symbol == INT16_MIN) {
            int bit = bitreader_read_bit(&br);
            node = bit ? node->right : node->left;
            if (!node) {
                free_huffman_tree(root);
                return 0;
            }
        }
        s_neg->c[perm[i]] = mod_q(node->symbol);
#else
        int val = 0;
        if (!decode_fixed_symbol_esc(&br, S_CYC_CODE, S_CYC_SYMBOLS, S_CYC_MIN,
                                     S_CYC_MAX_BITS, S_CYC_ESC_CODE, S_CYC_ESC_BITS,
                                     S_CYC_ESC_RAW_BITS, S_CYC_ESC_BIAS, &val)) {
            return 0;
        }
        s_neg->c[perm[i]] = mod_q(val);
#endif
    }

#if SIG_HUFFMAN_DYNAMIC
    free_huffman_tree(root);
#endif

    return 1;
#endif
}

// Huffman decode signature (s + w)
int huffman_decode_sig(const huffman_sig_t *in, const public_key_t *pk,
                       const uint8_t *msg, size_t msg_len, signature_t *sig) {
    // Decode w (commitment) first so we can derive the permutation seed.
#if SIG_LOSSY_ZERO
    uint8_t zeroed_buf[N];
    derive_zero_positions(zeroed_buf, SIG_LOSSY_ZERO_K, pk->seed, msg, msg_len);
    const uint8_t *is_zeroed = zeroed_buf;
#else
    const uint8_t *is_zeroed = NULL;
#endif
#if SIG_RANGE_W && !SIG_HUFFMAN_DYNAMIC && !SIG_W_CYC_ONLY && (P == 16)
    rc_dec_t w_rc;
    rc_dec_init(&w_rc, in->w_data, in->w_len);
#if SIG_W_DELTA
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            sig->w_cyc.c[i] = 0;
            sig->w_neg.c[i] = 0;
            continue;
        }
#endif
        int w_cyc = 0;
        if (!rc_decode_symbol(&w_rc, W_CYC_CUM, P, W_CYC_TOT, &w_cyc)) {
            return 0;
        }
        if (w_cyc < 0 || w_cyc >= P) {
            return 0;
        }
        int d_sym = 0;
        if (!rc_decode_symbol(&w_rc, W_DELTA_CUM, P, W_DELTA_TOT, &d_sym)) {
            return 0;
        }
        if (d_sym < 0 || d_sym >= P) {
            return 0;
        }
        int32_t delta = d_sym - (P / 2);
        sig->w_cyc.c[i] = (coeff_t)w_cyc;
        sig->w_neg.c[i] = mod_p((int32_t)w_cyc + delta);
    }
#elif SIG_W_COND
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            sig->w_cyc.c[i] = 0;
            sig->w_neg.c[i] = 0;
            continue;
        }
#endif
        int w_cyc = 0;
        if (!rc_decode_symbol(&w_rc, W_CYC_CUM, P, W_CYC_TOT, &w_cyc)) {
            return 0;
        }
        if (w_cyc < 0 || w_cyc >= P) {
            return 0;
        }
        int bucket = (w_cyc == 0 || w_cyc == (P - 1)) ? 0 : 1;
        int w_neg = 0;
        if (!rc_decode_symbol(&w_rc, W_NEG_COND_CUM[bucket], P,
                              W_NEG_COND_TOT[bucket], &w_neg)) {
            return 0;
        }
        if (w_neg < 0 || w_neg >= P) {
            return 0;
        }
        sig->w_cyc.c[i] = (coeff_t)w_cyc;
        sig->w_neg.c[i] = (coeff_t)w_neg;
    }
#else
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            sig->w_cyc.c[i] = 0;
            sig->w_neg.c[i] = 0;
            continue;
        }
#endif
        int pair = 0;
        if (!rc_decode_symbol(&w_rc, W_PAIR_CUM, W_PAIR_SYMBOLS, W_PAIR_TOT, &pair)) {
            return 0;
        }
        if (pair < 0 || pair >= W_PAIR_SYMBOLS) {
            return 0;
        }
        sig->w_cyc.c[i] = (coeff_t)(pair / P);
        sig->w_neg.c[i] = (coeff_t)(pair % P);
    }
#endif
    if (!w_rc.ok) {
        return 0;
    }
#else
    bitreader_t w_br;
    bitreader_init(&w_br, in->w_data, in->w_len);

#if SIG_HUFFMAN_DYNAMIC
    // Read w codebook size (8 bits)
    int w_codebook_size = 0;
    for (int b = 0; b < 8; b++) {
        w_codebook_size = (w_codebook_size << 1) | bitreader_read_bit(&w_br);
    }
    if (w_codebook_size == 0 || w_codebook_size > PK_MAX_SYMBOLS) return 0;

    // Build w decoding tree
    huffman_node_t *w_root = malloc(sizeof(huffman_node_t));
    w_root->symbol = INT16_MIN;
    w_root->left = NULL;
    w_root->right = NULL;

    for (int i = 0; i < w_codebook_size; i++) {
        // Read symbol (8 bits)
        int sym = 0;
        for (int b = 0; b < 8; b++) {
            sym = (sym << 1) | bitreader_read_bit(&w_br);
        }
        // Read code length (5 bits)
        int bits = 0;
        for (int b = 0; b < 5; b++) {
            bits = (bits << 1) | bitreader_read_bit(&w_br);
        }
        // Read code
        uint32_t code = 0;
        for (int b = 0; b < bits; b++) {
            code = (code << 1) | bitreader_read_bit(&w_br);
        }
        // Build tree node
        huffman_node_t *node = w_root;
        for (int b = bits - 1; b >= 0; b--) {
            int bit = (code >> b) & 1;
            if (bit == 0) {
                if (!node->left) {
                    node->left = malloc(sizeof(huffman_node_t));
                    node->left->symbol = INT16_MIN;
                    node->left->left = NULL;
                    node->left->right = NULL;
                }
                node = node->left;
            } else {
                if (!node->right) {
                    node->right = malloc(sizeof(huffman_node_t));
                    node->right->symbol = INT16_MIN;
                    node->right->left = NULL;
                    node->right->right = NULL;
                }
                node = node->right;
            }
        }
        node->symbol = sym;
    }
#endif

    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            sig->w_cyc.c[i] = 0;
#if !SIG_W_CYC_ONLY
            sig->w_neg.c[i] = 0;
#endif
            continue;
        }
#endif
#if SIG_HUFFMAN_DYNAMIC
        huffman_node_t *node = w_root;
        while (node->symbol == INT16_MIN) {
            int bit = bitreader_read_bit(&w_br);
            node = bit ? node->right : node->left;
            if (!node) { free_huffman_tree(w_root); return 0; }
        }
        sig->w_cyc.c[i] = node->symbol;
#else
#if SIG_W_PAIR_HUFF && !SIG_W_CYC_ONLY && (P == 16)
        uint16_t pair = 0;
        if (!w_huff_read_pair(&w_br, &pair)) return 0;
        sig->w_cyc.c[i] = (coeff_t)(pair / P);
        sig->w_neg.c[i] = (coeff_t)(pair % P);
#else
        uint8_t val = 0;
        if (!w_huff_read_cyc(&w_br, &val)) return 0;
        sig->w_cyc.c[i] = val;
#endif
#endif
    }

#if !SIG_W_CYC_ONLY
#if SIG_HUFFMAN_DYNAMIC
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            sig->w_neg.c[i] = 0;
            continue;
        }
#endif
        huffman_node_t *node = w_root;
        while (node->symbol == INT16_MIN) {
            int bit = bitreader_read_bit(&w_br);
            node = bit ? node->right : node->left;
            if (!node) { free_huffman_tree(w_root); return 0; }
        }
        sig->w_neg.c[i] = node->symbol;
    }
#elif !(SIG_W_PAIR_HUFF && (P == 16))
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            sig->w_neg.c[i] = 0;
            continue;
        }
#endif
        uint8_t val = 0;
        if (!w_huff_read_neg(&w_br, &val)) return 0;
        sig->w_neg.c[i] = val;
    }
#endif
#else
    for (int i = 0; i < N; i++) {
#if SIG_LOSSY_ZERO
        if (is_zeroed && is_zeroed[i]) {
            sig->w_neg.c[i] = 0;
            continue;
        }
#endif
        sig->w_neg.c[i] = 0;
    }
#endif

#if SIG_HUFFMAN_DYNAMIC
    free_huffman_tree(w_root);
#endif
#endif

    uint8_t challenge_seed[SIGNATURE_CHALLENGE_BYTES];
    hash_to_challenge(challenge_seed, &sig->w_cyc, &sig->w_neg, pk, msg, msg_len);
    if (!huffman_decode_s(in->s_data, in->s_len,
                          challenge_seed, sizeof(challenge_seed),
                          is_zeroed,
                          &sig->s_cyc, &sig->s_neg)) {
        return 0;
    }

#if SIG_DEHYDRATE_W
    // Rehydrate w: restore the stored values at dehydrated positions
    {
        uint8_t dh_pos_cyc[DEHYDRATE_W_COUNT], dh_pos_neg[DEHYDRATE_W_COUNT];
        derive_w_dehydrate_positions(dh_pos_cyc, pk->seed, msg, msg_len, "DWCY");
        derive_w_dehydrate_positions(dh_pos_neg, pk->seed, msg, msg_len, "DWNG");

        // Unpack stored w values (4 bits each)
        for (int i = 0; i < DEHYDRATE_W_COUNT; i++) {
            uint8_t val_cyc, val_neg;
            if (i % 2 == 0) {
                val_cyc = in->w_dh_cyc[i / 2] & 0xF;
                val_neg = in->w_dh_neg[i / 2] & 0xF;
            } else {
                val_cyc = (in->w_dh_cyc[i / 2] >> 4) & 0xF;
                val_neg = (in->w_dh_neg[i / 2] >> 4) & 0xF;
            }
            sig->w_cyc.c[dh_pos_cyc[i]] = val_cyc;
            sig->w_neg.c[dh_pos_neg[i]] = val_neg;
        }
    }
#endif

#if SIG_DEHYDRATE_S
    // Debug: trace position 2 in both rings
    static int dbg_dec_once = 0;
    if (!dbg_dec_once) {
        dbg_dec_once = 1;
        fprintf(stderr, "DEBUG DECODE: s_cyc[2]=%d, s_neg[2]=%d BEFORE rehydrate\n",
                (int)sig->s_cyc.c[2], (int)sig->s_neg.c[2]);
    }
#endif

#if SIG_DEHYDRATE_S
    // Rehydrate: restore zeroed positions using linear system s * y = target
    // In this Schnorr-like scheme: s * y = unround(w) + c * unround(pk)
    // NOT simply w = s * y as in direct linear schemes

    ring_t y;
    expand_ring(&y, pk->seed, 0);

    // Compute challenge c from w and pk (reusing challenge_seed already computed above)
    master_t c_master;
    expand_sparse_challenge_len(&c_master, challenge_seed, sizeof(challenge_seed), CHALLENGE_WEIGHT);
    ring_t c_cyc, c_neg;
    project_cyclic(&c_master, &c_cyc);
    project_negacyclic(&c_master, &c_neg);

    // Unround w and pk
    ring_t w_unround_cyc, w_unround_neg;
    unround_ring(&w_unround_cyc, &sig->w_cyc);
    unround_ring(&w_unround_neg, &sig->w_neg);

    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    // Compute target = unround(w) + c * unround(pk)
    // This equals s * y for valid signatures
    ring_t cpk_cyc, cpk_neg;
    mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
    mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

    ring_t target_cyc, target_neg;
    add_ring(&target_cyc, &w_unround_cyc, &cpk_cyc);
    add_ring(&target_neg, &w_unround_neg, &cpk_neg);

    // Rehydrate each ring using target = s * y
    int retry = 0;
    int cyc_ok = 0, neg_ok = 0;
    while (retry < 5 && (!cyc_ok || !neg_ok)) {
        if (!cyc_ok) {
            cyc_ok = rehydrate_ring((dehydrate_ring_t*)&sig->s_cyc,
                                    (const dehydrate_ring_t*)&target_cyc,
                                    (const dehydrate_ring_t*)&y,
                                    pk->seed, msg, msg_len, "DCYC", 0, retry, NULL);
        }
        if (!neg_ok) {
            neg_ok = rehydrate_ring((dehydrate_ring_t*)&sig->s_neg,
                                    (const dehydrate_ring_t*)&target_neg,
                                    (const dehydrate_ring_t*)&y,
                                    pk->seed, msg, msg_len, "DNEG", 1, retry, NULL);
        }
        retry++;
    }
    if (!cyc_ok || !neg_ok) {
        return 0;  // Rehydration failed after retries
    }

    // Debug: verify target computation is correct
    static int dbg_reh_once = 0;
    if (!dbg_reh_once) {
        dbg_reh_once = 1;
        // The rehydrated s * y should match target (approximately)
        ring_t sy_check;
        mul_cyclic(&sy_check, &sig->s_cyc, &y);
        int max_diff = 0;
        for (int i = 0; i < N; i++) {
            int diff = abs(centered(mod_q(sy_check.c[i] - target_cyc.c[i])));
            if (diff > max_diff) max_diff = diff;
        }
        fprintf(stderr, "DEBUG: s_cyc * y vs target_cyc max diff: %d\n", max_diff);
    }
#endif

    return 1;
}

static int decode_minimal_s(const minimal_sig_t *in, ring_t *s_cyc, bitreader_t *br) {
    bitreader_init(br, in->s_data, in->s_len);
    for (int i = 0; i < N; i++) {
        int32_t v = 0;
        if (!minimal_read_s(br, &v)) return 0;
        s_cyc->c[i] = mod_q(v);
    }
    return 1;
}

// For pk: values in [0, P-1]
// PK_MAX_SYMBOLS already defined above
#define PK_SYMBOL_OFFSET 0

// Build Huffman tree for pk
static huffman_node_t* build_huffman_tree_pk(int freq[PK_MAX_SYMBOLS], int *num_leaves) {
    huffman_node_t *nodes[PK_MAX_SYMBOLS];
    int node_count = 0;

    for (int i = 0; i < PK_MAX_SYMBOLS; i++) {
        if (freq[i] > 0) {
            huffman_node_t *node = malloc(sizeof(huffman_node_t));
            node->symbol = i;
            node->freq = freq[i];
            node->left = NULL;
            node->right = NULL;
            nodes[node_count++] = node;
        }
    }

    *num_leaves = node_count;

    if (node_count == 0) {
        return NULL;
    }

    if (node_count == 1) {
        return nodes[0];
    }

    while (node_count > 1) {
        qsort(nodes, node_count, sizeof(huffman_node_t*), compare_nodes);
        huffman_node_t *left = nodes[0];
        huffman_node_t *right = nodes[1];
        huffman_node_t *parent = malloc(sizeof(huffman_node_t));
        parent->symbol = INT16_MIN;
        parent->freq = left->freq + right->freq;
        parent->left = left;
        parent->right = right;
        nodes[0] = parent;
        for (int i = 1; i < node_count - 1; i++) {
            nodes[i] = nodes[i + 1];
        }
        node_count--;
    }

    return nodes[0];
}

// Find entry in pk codebook
static huffman_entry_t* find_entry_pk(huffman_entry_t codebook[], int codebook_size, int16_t symbol) {
    for (int i = 0; i < codebook_size; i++) {
        if (codebook[i].symbol == symbol) {
            return &codebook[i];
        }
    }
    return NULL;
}

// Huffman encode public key
int huffman_encode_pk(const public_key_t *pk, huffman_pk_t *out) {
    memcpy(out->seed, pk->seed, SEED_BYTES);

    // Build frequency table from pk_cyc and pk_neg
    int freq[PK_MAX_SYMBOLS] = {0};

    for (int i = 0; i < N; i++) {
        freq[pk->pk_cyc.c[i]]++;
        freq[pk->pk_neg.c[i]]++;
    }

    // Build Huffman tree
    int num_leaves;
    huffman_node_t *root = build_huffman_tree_pk(freq, &num_leaves);
    if (!root) return 0;

    // Generate codebook
    huffman_entry_t codebook[PK_MAX_SYMBOLS];
    int codebook_size;
    generate_codes(root, codebook, &codebook_size);

    // Encode
    bitwriter_t bw;
    bitwriter_init(&bw, out->pk_data, sizeof(out->pk_data));

    // Write codebook size (8 bits, max 256 entries)
    bitwriter_write(&bw, codebook_size, 8);

    // Write codebook entries: symbol (8 bits), length (4 bits), code
    for (int i = 0; i < codebook_size; i++) {
        bitwriter_write(&bw, codebook[i].symbol, 8);
        bitwriter_write(&bw, codebook[i].bits, 4);
        bitwriter_write(&bw, codebook[i].code, codebook[i].bits);
    }

    // Encode pk_cyc
    for (int i = 0; i < N; i++) {
        huffman_entry_t *entry = find_entry_pk(codebook, codebook_size, pk->pk_cyc.c[i]);
        if (!entry) { free_huffman_tree(root); return 0; }
        bitwriter_write(&bw, entry->code, entry->bits);
    }

    // Encode pk_neg
    for (int i = 0; i < N; i++) {
        huffman_entry_t *entry = find_entry_pk(codebook, codebook_size, pk->pk_neg.c[i]);
        if (!entry) { free_huffman_tree(root); return 0; }
        bitwriter_write(&bw, entry->code, entry->bits);
    }

    free_huffman_tree(root);
    out->pk_len = bitwriter_finish(&bw);
    return 1;
}

// Huffman decode public key
int huffman_decode_pk(const huffman_pk_t *in, public_key_t *pk) {
    memcpy(pk->seed, in->seed, SEED_BYTES);

    bitreader_t br;
    bitreader_init(&br, in->pk_data, in->pk_len);

    // Read codebook size
    int codebook_size = 0;
    for (int b = 0; b < 8; b++) {
        codebook_size = (codebook_size << 1) | bitreader_read_bit(&br);
    }

    if (codebook_size == 0 || codebook_size > PK_MAX_SYMBOLS) {
        return 0;
    }

    // Build decoding tree from codebook
    huffman_node_t *root = malloc(sizeof(huffman_node_t));
    root->symbol = INT16_MIN;
    root->left = NULL;
    root->right = NULL;

    for (int i = 0; i < codebook_size; i++) {
        // Read symbol (8 bits)
        int sym = 0;
        for (int b = 0; b < 8; b++) {
            sym = (sym << 1) | bitreader_read_bit(&br);
        }

        // Read code length (4 bits)
        int bits = 0;
        for (int b = 0; b < 4; b++) {
            bits = (bits << 1) | bitreader_read_bit(&br);
        }

        // Read code
        uint32_t code = 0;
        for (int b = 0; b < bits; b++) {
            code = (code << 1) | bitreader_read_bit(&br);
        }

        // Build tree node for this code
        huffman_node_t *node = root;
        for (int b = bits - 1; b >= 0; b--) {
            int bit = (code >> b) & 1;
            if (bit == 0) {
                if (!node->left) {
                    node->left = malloc(sizeof(huffman_node_t));
                    node->left->symbol = INT16_MIN;
                    node->left->left = NULL;
                    node->left->right = NULL;
                }
                node = node->left;
            } else {
                if (!node->right) {
                    node->right = malloc(sizeof(huffman_node_t));
                    node->right->symbol = INT16_MIN;
                    node->right->left = NULL;
                    node->right->right = NULL;
                }
                node = node->right;
            }
        }
        node->symbol = sym;
    }

    // Decode pk_cyc
    for (int i = 0; i < N; i++) {
        huffman_node_t *node = root;
        while (node->symbol == INT16_MIN) {
            int bit = bitreader_read_bit(&br);
            node = bit ? node->right : node->left;
            if (!node) {
                free_huffman_tree(root);
                return 0;
            }
        }
        pk->pk_cyc.c[i] = node->symbol;
    }

    // Decode pk_neg
    for (int i = 0; i < N; i++) {
        huffman_node_t *node = root;
        while (node->symbol == INT16_MIN) {
            int bit = bitreader_read_bit(&br);
            node = bit ? node->right : node->left;
            if (!node) {
                free_huffman_tree(root);
                return 0;
            }
        }
        pk->pk_neg.c[i] = node->symbol;
    }

    free_huffman_tree(root);
    return 1;
}

// ============================================================================
// Signature Compression (Fixed-width, kept for comparison)
// ============================================================================

// Compress signature: s to signed 8-bit, w to unsigned 8-bit
int compress_sig(compressed_sig_t *out, const signature_t *sig) {
    for (int i = 0; i < N; i++) {
        // s values: center and clamp to [-128, 127]
        int32_t s_cyc = centered(sig->s_cyc.c[i]);
        int32_t s_neg = centered(sig->s_neg.c[i]);

        if (s_cyc < -128 || s_cyc > 127 || s_neg < -128 || s_neg > 127) {
            return 0;  // Overflow - signature too large
        }

        out->s_cyc[i] = (int8_t)s_cyc;
        out->s_neg[i] = (int8_t)s_neg;

        // w values: already in [0, P-1], direct cast
        out->w_cyc[i] = (uint8_t)sig->w_cyc.c[i];
        out->w_neg[i] = (uint8_t)sig->w_neg.c[i];
    }
    return 1;
}

// Decompress signature
void decompress_sig(signature_t *sig, const compressed_sig_t *in) {
    for (int i = 0; i < N; i++) {
        // s values: signed 8-bit back to mod Q
        sig->s_cyc.c[i] = mod_q(in->s_cyc[i]);
        sig->s_neg.c[i] = mod_q(in->s_neg[i]);

        // w values: unsigned 8-bit, direct
        sig->w_cyc.c[i] = in->w_cyc[i];
        sig->w_neg.c[i] = in->w_neg[i];
    }
}

// Pack 6-bit signed values into bytes (4 values → 3 bytes)
static void pack_6bit_signed(uint8_t *out, const int8_t *in, int n) {
    for (int i = 0; i < n; i += 4) {
        // Convert signed [-32,31] to unsigned [0,63]
        uint8_t v0 = (in[i] + 32) & 0x3F;
        uint8_t v1 = (in[i+1] + 32) & 0x3F;
        uint8_t v2 = (in[i+2] + 32) & 0x3F;
        uint8_t v3 = (in[i+3] + 32) & 0x3F;
        // Pack 4×6 bits into 3 bytes
        out[0] = (v0 << 2) | (v1 >> 4);
        out[1] = (v1 << 4) | (v2 >> 2);
        out[2] = (v2 << 6) | v3;
        out += 3;
    }
}

// Unpack 6-bit signed values
static void unpack_6bit_signed(int8_t *out, const uint8_t *in, int n) {
    for (int i = 0; i < n; i += 4) {
        out[i]   = (int8_t)((in[0] >> 2) & 0x3F) - 32;
        out[i+1] = (int8_t)(((in[0] << 4) | (in[1] >> 4)) & 0x3F) - 32;
        out[i+2] = (int8_t)(((in[1] << 2) | (in[2] >> 6)) & 0x3F) - 32;
        out[i+3] = (int8_t)(in[2] & 0x3F) - 32;
        in += 3;
    }
}

// Pack 6-bit unsigned values (for pk in [0, P-1])
static void pack_6bit_unsigned(uint8_t *out, const uint8_t *in, int n) {
    for (int i = 0; i < n; i += 4) {
        uint8_t v0 = in[i] & 0x3F;
        uint8_t v1 = in[i+1] & 0x3F;
        uint8_t v2 = in[i+2] & 0x3F;
        uint8_t v3 = in[i+3] & 0x3F;
        out[0] = (v0 << 2) | (v1 >> 4);
        out[1] = (v1 << 4) | (v2 >> 2);
        out[2] = (v2 << 6) | v3;
        out += 3;
    }
}

// Unpack 6-bit unsigned values
static void unpack_6bit_unsigned(uint8_t *out, const uint8_t *in, int n) {
    for (int i = 0; i < n; i += 4) {
        out[i]   = (in[0] >> 2) & 0x3F;
        out[i+1] = ((in[0] << 4) | (in[1] >> 4)) & 0x3F;
        out[i+2] = ((in[1] << 2) | (in[2] >> 6)) & 0x3F;
        out[i+3] = in[2] & 0x3F;
        in += 3;
    }
}

// Pack 5-bit signed values (8 values → 5 bytes)
// Values in [-16, 15] mapped to [0, 31]
static void pack_5bit_signed(uint8_t *out, const int8_t *in, int n) {
    for (int i = 0; i < n; i += 8) {
        uint8_t v0 = (in[i] + 16) & 0x1F;
        uint8_t v1 = (in[i+1] + 16) & 0x1F;
        uint8_t v2 = (in[i+2] + 16) & 0x1F;
        uint8_t v3 = (in[i+3] + 16) & 0x1F;
        uint8_t v4 = (in[i+4] + 16) & 0x1F;
        uint8_t v5 = (in[i+5] + 16) & 0x1F;
        uint8_t v6 = (in[i+6] + 16) & 0x1F;
        uint8_t v7 = (in[i+7] + 16) & 0x1F;
        // Pack 8×5 = 40 bits into 5 bytes
        out[0] = (v0 << 3) | (v1 >> 2);
        out[1] = (v1 << 6) | (v2 << 1) | (v3 >> 4);
        out[2] = (v3 << 4) | (v4 >> 1);
        out[3] = (v4 << 7) | (v5 << 2) | (v6 >> 3);
        out[4] = (v6 << 5) | v7;
        out += 5;
    }
}

// Unpack 5-bit signed values
static void unpack_5bit_signed(int8_t *out, const uint8_t *in, int n) {
    for (int i = 0; i < n; i += 8) {
        out[i]   = (int8_t)((in[0] >> 3) & 0x1F) - 16;
        out[i+1] = (int8_t)(((in[0] << 2) | (in[1] >> 6)) & 0x1F) - 16;
        out[i+2] = (int8_t)((in[1] >> 1) & 0x1F) - 16;
        out[i+3] = (int8_t)(((in[1] << 4) | (in[2] >> 4)) & 0x1F) - 16;
        out[i+4] = (int8_t)(((in[2] << 1) | (in[3] >> 7)) & 0x1F) - 16;
        out[i+5] = (int8_t)((in[3] >> 2) & 0x1F) - 16;
        out[i+6] = (int8_t)(((in[3] << 3) | (in[4] >> 5)) & 0x1F) - 16;
        out[i+7] = (int8_t)(in[4] & 0x1F) - 16;
        in += 5;
    }
}

// Pack 5-bit unsigned values (8 values → 5 bytes)
static void pack_5bit_unsigned(uint8_t *out, const uint8_t *in, int n) {
    for (int i = 0; i < n; i += 8) {
        uint8_t v0 = in[i] & 0x1F;
        uint8_t v1 = in[i+1] & 0x1F;
        uint8_t v2 = in[i+2] & 0x1F;
        uint8_t v3 = in[i+3] & 0x1F;
        uint8_t v4 = in[i+4] & 0x1F;
        uint8_t v5 = in[i+5] & 0x1F;
        uint8_t v6 = in[i+6] & 0x1F;
        uint8_t v7 = in[i+7] & 0x1F;
        out[0] = (v0 << 3) | (v1 >> 2);
        out[1] = (v1 << 6) | (v2 << 1) | (v3 >> 4);
        out[2] = (v3 << 4) | (v4 >> 1);
        out[3] = (v4 << 7) | (v5 << 2) | (v6 >> 3);
        out[4] = (v6 << 5) | v7;
        out += 5;
    }
}

// Unpack 5-bit unsigned values
static void unpack_5bit_unsigned(uint8_t *out, const uint8_t *in, int n) {
    for (int i = 0; i < n; i += 8) {
        out[i]   = (in[0] >> 3) & 0x1F;
        out[i+1] = ((in[0] << 2) | (in[1] >> 6)) & 0x1F;
        out[i+2] = (in[1] >> 1) & 0x1F;
        out[i+3] = ((in[1] << 4) | (in[2] >> 4)) & 0x1F;
        out[i+4] = ((in[2] << 1) | (in[3] >> 7)) & 0x1F;
        out[i+5] = (in[3] >> 2) & 0x1F;
        out[i+6] = ((in[3] << 3) | (in[4] >> 5)) & 0x1F;
        out[i+7] = in[4] & 0x1F;
        in += 5;
    }
}

// Pack 4-bit signed values (2 values → 1 byte)
// Values in [-8, 7] mapped to [0, 15]
static void pack_4bit_signed(uint8_t *out, const int8_t *in, int n) {
    for (int i = 0; i < n; i += 2) {
        uint8_t v0 = (in[i] + 8) & 0x0F;
        uint8_t v1 = (in[i+1] + 8) & 0x0F;
        out[i/2] = (v0 << 4) | v1;
    }
}

// Unpack 4-bit signed values
static void unpack_4bit_signed(int8_t *out, const uint8_t *in, int n) {
    for (int i = 0; i < n; i += 2) {
        out[i]   = (int8_t)((in[i/2] >> 4) & 0x0F) - 8;
        out[i+1] = (int8_t)(in[i/2] & 0x0F) - 8;
    }
}

// Compact compress: coupling-only (s_neg LSB = s_cyc LSB)
// With |s| < 16: s_cyc in 5-bit, s_neg high in 4-bit
int compact_compress_sig(compact_sig_t *out, const signature_t *sig,
                         const uint8_t *challenge_seed) {
    int8_t s_cyc_temp[N];
    int8_t s_neg_high[N];  // s_neg >> 1 (4 bits when |s_neg| < 16)

    for (int i = 0; i < N; i++) {
        int32_t s_cyc = centered(sig->s_cyc.c[i]);
        int32_t s_neg = centered(sig->s_neg.c[i]);

        if (s_cyc < -16 || s_cyc > 15 || s_neg < -16 || s_neg > 15) {
            return 0;  // Overflow - need rejection
        }

        // Coupling-only: LSBs must match
        if ((s_cyc & 1) != (s_neg & 1)) {
            return 0;  // Coupling violated
        }

        s_cyc_temp[i] = (int8_t)s_cyc;
        // Store s_neg >> 1, preserving sign (now 4-bit: [-8, 7])
        s_neg_high[i] = (int8_t)(s_neg >> 1);
    }

    pack_5bit_signed(out->s_cyc_packed, s_cyc_temp, N);
    pack_4bit_signed(out->s_neg_packed, s_neg_high, N);
    memcpy(out->challenge, challenge_seed, CHALLENGE_BYTES);
    return 1;
}

// Compact decompress: reconstruct s_neg LSB from s_cyc
void compact_decompress_s(ring_t *s_cyc, ring_t *s_neg, const compact_sig_t *in) {
    int8_t s_cyc_temp[N];
    int8_t s_neg_high[N];

    unpack_5bit_signed(s_cyc_temp, in->s_cyc_packed, N);
    unpack_4bit_signed(s_neg_high, in->s_neg_packed, N);

    for (int i = 0; i < N; i++) {
        s_cyc->c[i] = mod_q(s_cyc_temp[i]);
        // Reconstruct s_neg: high bits << 1, LSB from s_cyc
        int8_t s_neg_val = (s_neg_high[i] << 1) | (s_cyc_temp[i] & 1);
        s_neg->c[i] = mod_q(s_neg_val);
    }
}

static int compact_huffman_compress(compact_huffman_sig_t *out, const signature_t *sig,
                                    const public_key_t *pk, const uint8_t *msg, size_t msg_len) {
    huffman_sig_t hs;
    if (!huffman_encode_sig(sig, pk, msg, msg_len, &hs)) {
        return 0;
    }
    if (hs.s_len > (int)sizeof(out->s_data)) {
        return 0;
    }
    memcpy(out->s_data, hs.s_data, hs.s_len);
    out->s_len = hs.s_len;

    uint8_t challenge_seed[SIGNATURE_CHALLENGE_BYTES];
    hash_to_challenge(challenge_seed, &sig->w_cyc, &sig->w_neg, pk, msg, msg_len);
    memcpy(out->challenge, challenge_seed, CHALLENGE_FULL_BYTES);

    master_t c_master;
    expand_sparse_challenge_len(&c_master, out->challenge, CHALLENGE_FULL_BYTES, CHALLENGE_WEIGHT);

    ring_t c_cyc, c_neg;
    project_cyclic(&c_master, &c_cyc);
    project_negacyclic(&c_master, &c_neg);

    ring_t y;
    expand_ring(&y, pk->seed, 0);

    ring_t sy_cyc, sy_neg;
    mul_cyclic(&sy_cyc, &sig->s_cyc, &y);
    mul_negacyclic(&sy_neg, &sig->s_neg, &y);

    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    ring_t cpk_cyc, cpk_neg;
    mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
    mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

    ring_t w_prime_cyc, w_prime_neg;
    sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
    sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

    ring_t w_round_prime_cyc, w_round_prime_neg;
    round_ring(&w_round_prime_cyc, &w_prime_cyc);
    round_ring(&w_round_prime_neg, &w_prime_neg);

    if (!encode_w_hints(out->hint_data, sizeof(out->hint_data),
                        &sig->w_cyc, &sig->w_neg,
                        &w_round_prime_cyc, &w_round_prime_neg,
                        &out->hint_len, NULL)) {
        return 0;
    }
    return 1;
}

static int verify_compact_huffman(const compact_huffman_sig_t *sig, const public_key_t *pk,
                                  const uint8_t *msg, size_t msg_len) {
    ring_t s_cyc, s_neg;
#if SIG_LOSSY_ZERO
    uint8_t is_zeroed[N];
    derive_zero_positions(is_zeroed, SIG_LOSSY_ZERO_K, pk->seed, msg, msg_len);
    const uint8_t *zeroed_ptr = is_zeroed;
#else
    const uint8_t *zeroed_ptr = NULL;
#endif
    if (!huffman_decode_s(sig->s_data, sig->s_len,
                          sig->challenge, CHALLENGE_FULL_BYTES,
                          zeroed_ptr, &s_cyc, &s_neg)) {
        return 0;
    }

    if (!verify_coupling(&s_cyc, &s_neg)) {
        return 0;
    }

#if !SIG_LOSSY_ZERO
    master_t s_master;
    if (!crt_lift(&s_cyc, &s_neg, &s_master)) {
        return 0;
    }
    if (!verify_trace_zero(&s_master)) {
        return 0;
    }
#endif

    master_t c_master;
    expand_sparse_challenge_len(&c_master, sig->challenge, CHALLENGE_FULL_BYTES, CHALLENGE_WEIGHT);

    ring_t c_cyc, c_neg;
    project_cyclic(&c_master, &c_cyc);
    project_negacyclic(&c_master, &c_neg);

    ring_t y;
    expand_ring(&y, pk->seed, 0);

    ring_t sy_cyc, sy_neg;
    mul_cyclic(&sy_cyc, &s_cyc, &y);
    mul_negacyclic(&sy_neg, &s_neg, &y);

    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    ring_t cpk_cyc, cpk_neg;
    mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
    mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

    ring_t w_prime_cyc, w_prime_neg;
    sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
    sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

    ring_t w_round_cyc, w_round_neg;
    round_ring(&w_round_cyc, &w_prime_cyc);
    round_ring(&w_round_neg, &w_prime_neg);

    if (!apply_w_hints(sig->hint_data, sig->hint_len, &w_round_cyc, &w_round_neg, NULL)) {
        return 0;
    }

    uint8_t challenge_check[32];
    hash_to_challenge(challenge_check, &w_round_cyc, &w_round_neg, pk, msg, msg_len);
    if (memcmp(challenge_check, sig->challenge, CHALLENGE_FULL_BYTES) != 0) {
        return 0;
    }

    ring_t w_unround_cyc, w_unround_neg;
    unround_ring(&w_unround_cyc, &w_round_cyc);
    unround_ring(&w_unround_neg, &w_round_neg);

    int max_err = 0;
    for (int i = 0; i < N; i++) {
        if (zeroed_ptr && zeroed_ptr[i]) {
            continue;
        }
        int diff = abs(centered(mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
        if (diff > max_err) max_err = diff;
#if !SIG_W_CYC_ONLY
        diff = abs(centered(mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
        if (diff > max_err) max_err = diff;
#endif
    }

#if SIG_W_CYC_ONLY
    if (ring_linf(&w_prime_neg) > W_BOUND) {
        return 0;
    }
#endif
    return max_err <= TAU;
}

// Compress public key: pk values in [0, P-1] as 8-bit
void compress_pk(compressed_pk_t *out, const public_key_t *pk) {
    memcpy(out->seed, pk->seed, SEED_BYTES);

    for (int i = 0; i < N; i++) {
        out->pk_cyc[i] = (uint8_t)pk->pk_cyc.c[i];  // Already in [0, P-1]
        out->pk_neg[i] = (uint8_t)pk->pk_neg.c[i];
    }
}

// Decompress public key
void decompress_pk(public_key_t *pk, const compressed_pk_t *in) {
    memcpy(pk->seed, in->seed, SEED_BYTES);

    for (int i = 0; i < N; i++) {
        pk->pk_cyc.c[i] = in->pk_cyc[i];
        pk->pk_neg.c[i] = in->pk_neg[i];
    }
}

// ============================================================================
// Sampling
// ============================================================================

// Sample master secret with coefficients in {-ETA, ..., ETA}
// Trace-zero constraint: Σx[i] ≡ 0 (mod q)
void sample_small_master(master_t *x) {
    while (1) {
        int64_t sum = 0;
        for (int i = 0; i < N2; i++) {
            uint8_t buf;
            RAND_bytes(&buf, 1);
            int val = (buf % (2 * ETA + 1)) - ETA;
            x->c[i] = mod_q(val);
            sum += val;
        }
        if (mod_q(sum) == 0) return;  // Accept if trace-zero mod q
    }
}

// Sample sparse master with trace-zero: weight/2 are +1, weight/2 are -1
// Requires weight to be even
void sample_sparse_master(master_t *x, int weight) {
    memset(x->c, 0, sizeof(x->c));

    int plus_count = 0, minus_count = 0;
    int half = weight / 2;

    while (plus_count + minus_count < weight) {
        uint8_t buf[3];
        RAND_bytes(buf, 3);
        int pos = ((buf[0] << 8) | buf[1]) % N2;
        if (x->c[pos] == 0) {
            // Assign +1 or -1 based on what we still need
            if (plus_count < half && minus_count < half) {
                x->c[pos] = (buf[2] & 1) ? 1 : Q - 1;
                if (x->c[pos] == 1) plus_count++; else minus_count++;
            } else if (plus_count < half) {
                x->c[pos] = 1;
                plus_count++;
            } else {
                x->c[pos] = Q - 1;
                minus_count++;
            }
        }
    }
}

// Expand public polynomial (deterministic from seed) - uniform version
void expand_ring_uniform(ring_t *r, const uint8_t *seed, int domain_sep) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    uint8_t block[64];
    int block_idx = 64;
    int ctr = 0;

    for (int i = 0; i < N; i++) {
        if (block_idx >= 62) {
            uint8_t in[SEED_BYTES + 2];
            memcpy(in, seed, SEED_BYTES);
            in[SEED_BYTES] = ctr++;
            in[SEED_BYTES + 1] = domain_sep;
            EVP_DigestInit_ex(ctx, EVP_sha3_512(), NULL);
            EVP_DigestUpdate(ctx, in, SEED_BYTES + 2);
            unsigned int len = 64;
            EVP_DigestFinal_ex(ctx, block, &len);
            block_idx = 0;
        }
        uint16_t val = (block[block_idx] << 8) | block[block_idx + 1];
        r->c[i] = val % Q;
        block_idx += 2;
    }
    EVP_MD_CTX_free(ctx);
}

// Expand sparse public polynomial (deterministic from seed)
// Sparse ternary: weight/2 are +1, weight/2 are -1, rest are 0
void expand_ring_sparse(ring_t *r, const uint8_t *seed, int domain_sep, int weight) {
    memset(r->c, 0, sizeof(r->c));

    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    uint8_t buf[1024];

    uint8_t in[SEED_BYTES + 1];
    memcpy(in, seed, SEED_BYTES);
    in[SEED_BYTES] = domain_sep;

    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, in, SEED_BYTES + 1);
    EVP_DigestFinalXOF(ctx, buf, sizeof(buf));
    EVP_MD_CTX_free(ctx);

    int plus_count = 0, minus_count = 0;
    int half = weight / 2;
    int idx = 0;

    while (plus_count + minus_count < weight && idx < 400) {
        int pos = ((buf[idx*2] << 8) | buf[idx*2 + 1]) % N;
        if (r->c[pos] == 0) {
            int sign_bit = buf[512 + plus_count + minus_count] & 1;
            if (plus_count < half && minus_count < half) {
                r->c[pos] = sign_bit ? 1 : Q - 1;
                if (r->c[pos] == 1) plus_count++; else minus_count++;
            } else if (plus_count < half) {
                r->c[pos] = 1;
                plus_count++;
            } else {
                r->c[pos] = Q - 1;
                minus_count++;
            }
        }
        idx++;
    }
}

// Expand bounded uniform: coeffs in [-bound, bound] mod Q
void expand_ring_bounded(ring_t *r, const uint8_t *seed, int domain_sep, int bound) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    uint8_t block[64];
    int block_idx = 64;
    int ctr = 0;
    int range = 2 * bound + 1;  // [-bound, bound] has this many values

    for (int i = 0; i < N; i++) {
        if (block_idx >= 62) {
            uint8_t in[SEED_BYTES + 2];
            memcpy(in, seed, SEED_BYTES);
            in[SEED_BYTES] = ctr++;
            in[SEED_BYTES + 1] = domain_sep;
            EVP_DigestInit_ex(ctx, EVP_sha3_512(), NULL);
            EVP_DigestUpdate(ctx, in, SEED_BYTES + 2);
            unsigned int len = 64;
            EVP_DigestFinal_ex(ctx, block, &len);
            block_idx = 0;
        }
        uint16_t val = (block[block_idx] << 8) | block[block_idx + 1];
        int coeff = (val % range) - bound;  // In [-bound, bound]
        r->c[i] = mod_q(coeff);
        block_idx += 2;
    }
    EVP_MD_CTX_free(ctx);
}

// Wrapper for backward compatibility - uses bounded uniform
void expand_ring(ring_t *r, const uint8_t *seed, int domain_sep) {
    expand_ring_bounded(r, seed, domain_sep, Y_BOUND);
}

// Expand sparse challenge from commitment (deterministic)
// Expand challenge with trace-zero: weight/2 are +1, weight/2 are -1
static void expand_sparse_challenge_len(master_t *c, const uint8_t *commitment,
                                        size_t commitment_len, int weight) {
    memset(c->c, 0, sizeof(c->c));

    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    uint8_t buf[1024];

    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, commitment, commitment_len);
    EVP_DigestFinalXOF(ctx, buf, sizeof(buf));
    EVP_MD_CTX_free(ctx);

    int plus_count = 0, minus_count = 0;
    int half = weight / 2;
    int idx = 0;

    while (plus_count + minus_count < weight && idx < 500) {
        int pos = ((buf[idx*2] << 8) | buf[idx*2 + 1]) % N2;
        if (c->c[pos] == 0) {
            int sign_bit = buf[512 + plus_count + minus_count] & 1;
            if (plus_count < half && minus_count < half) {
                c->c[pos] = sign_bit ? 1 : Q - 1;
                if (c->c[pos] == 1) plus_count++; else minus_count++;
            } else if (plus_count < half) {
                c->c[pos] = 1;
                plus_count++;
            } else {
                c->c[pos] = Q - 1;
                minus_count++;
            }
        }
        idx++;
    }
}

void expand_sparse_challenge(master_t *c, const uint8_t *commitment, int weight) {
    expand_sparse_challenge_len(c, commitment, 32, weight);
}

// ============================================================================
// Hash commitment
// ============================================================================

void hash_to_challenge(uint8_t *out, const ring_t *w_cyc, const ring_t *w_neg,
                       const public_key_t *pk, const uint8_t *msg, size_t msg_len) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
    EVP_DigestUpdate(ctx, w_cyc->c, sizeof(w_cyc->c));
#if !SIG_W_CYC_ONLY
    EVP_DigestUpdate(ctx, w_neg->c, sizeof(w_neg->c));
#endif
    EVP_DigestUpdate(ctx, pk->pk_cyc.c, sizeof(pk->pk_cyc.c));
    EVP_DigestUpdate(ctx, pk->pk_neg.c, sizeof(pk->pk_neg.c));
    EVP_DigestUpdate(ctx, pk->seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, msg, msg_len);
    unsigned int len = 32;
    EVP_DigestFinal_ex(ctx, out, &len);
    EVP_MD_CTX_free(ctx);
}

static void hash_to_challenge_w1(uint8_t *out, const ring_t *w1_cyc,
                                 const public_key_t *pk,
                                 const uint8_t *msg, size_t msg_len) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
    EVP_DigestUpdate(ctx, w1_cyc->c, sizeof(w1_cyc->c));
    EVP_DigestUpdate(ctx, pk->pk_cyc.c, sizeof(pk->pk_cyc.c));
    EVP_DigestUpdate(ctx, pk->pk_neg.c, sizeof(pk->pk_neg.c));
    EVP_DigestUpdate(ctx, pk->seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, msg, msg_len);
    unsigned int len = 32;
    EVP_DigestFinal_ex(ctx, out, &len);
    EVP_MD_CTX_free(ctx);
}

static void expand_nonce_master(master_t *r, const uint8_t *sk_seed,
                                const uint8_t *msg, size_t msg_len,
                                uint32_t attempt) {
    memset(r->c, 0, sizeof(r->c));

    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    uint8_t buf[1024];
    uint8_t ctr[4];
    ctr[0] = (uint8_t)(attempt & 0xFF);
    ctr[1] = (uint8_t)((attempt >> 8) & 0xFF);
    ctr[2] = (uint8_t)((attempt >> 16) & 0xFF);
    ctr[3] = (uint8_t)((attempt >> 24) & 0xFF);

    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, sk_seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, ctr, sizeof(ctr));
    EVP_DigestUpdate(ctx, msg, msg_len);
    EVP_DigestFinalXOF(ctx, buf, sizeof(buf));
    EVP_MD_CTX_free(ctx);

    int plus_count = 0, minus_count = 0;
    int half = NONCE_WEIGHT / 2;
    int idx = 0;

    while (plus_count + minus_count < NONCE_WEIGHT && idx < 500) {
        int pos = ((buf[idx * 2] << 8) | buf[idx * 2 + 1]) % N2;
        if (r->c[pos] == 0) {
            int sign_bit = buf[512 + plus_count + minus_count] & 1;
            if (plus_count < half && minus_count < half) {
                r->c[pos] = sign_bit ? 1 : Q - 1;
                if (r->c[pos] == 1) plus_count++; else minus_count++;
            } else if (plus_count < half) {
                r->c[pos] = 1;
                plus_count++;
            } else {
                r->c[pos] = Q - 1;
                minus_count++;
            }
        }
        idx++;
    }
}

static void hash_to_nonce_seed(uint8_t out[32], const uint8_t *sk_seed,
                               const uint8_t *msg, size_t msg_len,
                               uint32_t attempt) {
    uint8_t ctr[4];
    ctr[0] = (uint8_t)(attempt & 0xFF);
    ctr[1] = (uint8_t)((attempt >> 8) & 0xFF);
    ctr[2] = (uint8_t)((attempt >> 16) & 0xFF);
    ctr[3] = (uint8_t)((attempt >> 24) & 0xFF);

    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
    EVP_DigestUpdate(ctx, sk_seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, ctr, sizeof(ctr));
    EVP_DigestUpdate(ctx, msg, msg_len);
    unsigned int len = 32;
    EVP_DigestFinal_ex(ctx, out, &len);
    EVP_MD_CTX_free(ctx);
}

static void derive_zero_positions(uint8_t *is_zeroed, int k,
                                  const uint8_t *pk_seed,
                                  const uint8_t *msg, size_t msg_len) {
    memset(is_zeroed, 0, N);
    uint8_t buf[512];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, "ZERO", 4);
    EVP_DigestUpdate(ctx, pk_seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, msg, msg_len);
    EVP_DigestFinalXOF(ctx, buf, sizeof(buf));
    EVP_MD_CTX_free(ctx);

    int found = 0;
    int idx = 0;
    while (found < k && idx < 250) {
        int pos = ((buf[idx * 2] << 8) | buf[idx * 2 + 1]) % N;
        if (!is_zeroed[pos]) {
            is_zeroed[pos] = 1;
            found++;
        }
        idx++;
    }
}

#if SIG_DEHYDRATE_W
// Derive positions to dehydrate in w (commitment) rings
// Uses domain sep "DWCY" for w_cyc, "DWNG" for w_neg
static void derive_w_dehydrate_positions(uint8_t positions[DEHYDRATE_W_COUNT],
                                         const uint8_t *pk_seed,
                                         const uint8_t *msg, size_t msg_len,
                                         const char *domain_sep) {
    uint8_t buf[512];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, domain_sep, 4);
    EVP_DigestUpdate(ctx, pk_seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, msg, msg_len);
    EVP_DigestFinalXOF(ctx, buf, sizeof(buf));
    EVP_MD_CTX_free(ctx);

    uint8_t used[N] = {0};
    int found = 0, idx = 0;
    while (found < DEHYDRATE_W_COUNT && idx < 250) {
        int pos = ((buf[idx * 2] << 8) | buf[idx * 2 + 1]) % N;
        if (!used[pos]) {
            positions[found++] = (uint8_t)pos;
            used[pos] = 1;
        }
        idx++;
    }
}

// Dehydrate w ring: zero DEHYDRATE_W_COUNT positions
static void dehydrate_w_ring(ring_t *w, const uint8_t *pk_seed,
                             const uint8_t *msg, size_t msg_len,
                             const char *domain_sep) {
    uint8_t positions[DEHYDRATE_W_COUNT];
    derive_w_dehydrate_positions(positions, pk_seed, msg, msg_len, domain_sep);
    for (int i = 0; i < DEHYDRATE_W_COUNT; i++) {
        w->c[positions[i]] = 0;
    }
}

// Rehydrate w ring: restore from w' = round(s*y - c*unround(pk))
static void rehydrate_w_ring(ring_t *w, const ring_t *w_prime,
                             const uint8_t *pk_seed,
                             const uint8_t *msg, size_t msg_len,
                             const char *domain_sep) {
    uint8_t positions[DEHYDRATE_W_COUNT];
    derive_w_dehydrate_positions(positions, pk_seed, msg, msg_len, domain_sep);
    for (int i = 0; i < DEHYDRATE_W_COUNT; i++) {
        w->c[positions[i]] = w_prime->c[positions[i]];
    }
}
#endif

#if SIG_DEHYDRATE_W_REJECT
// Rejection-based w dehydration: zero positions only where reconstruction is exact
// No hints needed - signer verifies reconstructability before zeroing

// Derive candidate positions for w dehydration (deterministic from pk+msg+retry+ring)
static void derive_w_reject_candidates(uint8_t positions[N], int *count,
                                       const uint8_t *pk_seed,
                                       const uint8_t *msg, size_t msg_len,
                                       int retry,
                                       const char *ring_id) {  // "CYC" or "NEG"
    uint8_t buf[512];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, "WRJC", 4);  // W Reject Candidates
    EVP_DigestUpdate(ctx, ring_id, 3);  // Differentiate rings
    EVP_DigestUpdate(ctx, pk_seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, msg, msg_len);
    EVP_DigestUpdate(ctx, &retry, sizeof(retry));
    EVP_DigestFinalXOF(ctx, buf, sizeof(buf));
    EVP_MD_CTX_free(ctx);

    uint8_t used[N] = {0};
    *count = 0;
    int idx = 0;
    // Generate more candidates than needed (we'll filter to reconstructable ones)
    while (*count < N && idx < 250) {
        int pos = ((buf[idx * 2] << 8) | buf[idx * 2 + 1]) % N;
        if (!used[pos]) {
            positions[(*count)++] = (uint8_t)pos;
            used[pos] = 1;
        }
        idx++;
    }
}

// Find positions where w == w' AND w' != 0 (exact reconstruction, distinguishable from real zeros)
// Only checks first max_check candidates, returns up to max_good positions
static int find_reconstructable_positions(uint8_t *good_positions, int max_good,
                                          const ring_t *w_round,
                                          const ring_t *w_prime,  // round(s*y - c*pk_unround)
                                          const uint8_t *candidates, int num_candidates,
                                          int max_check) {
    int good_count = 0;
    int check_limit = (num_candidates < max_check) ? num_candidates : max_check;
    for (int i = 0; i < check_limit && good_count < max_good; i++) {
        int pos = candidates[i];
        // Only dehydrate if: (1) reconstruction exact, AND (2) w' is non-zero
        // This way, any 0 in transmitted w means "restore from w'" unambiguously
        if (mod_p(w_round->c[pos]) == mod_p(w_prime->c[pos]) &&
            mod_p(w_prime->c[pos]) != 0) {
            good_positions[good_count++] = (uint8_t)pos;
        }
    }
    return good_count;
}

// Check if all first K candidates are "clean" for dehydration
// A candidate is clean if: w == w' (exact recon), including w == w' == 0
// Returns 0 if any candidate has w != w' (problematic natural zero or reconstruction error)
static int check_dehydrate_clean(const ring_t *w_round,
                                 const ring_t *w_prime,
                                 const uint8_t *pk_seed,
                                 const uint8_t *msg, size_t msg_len,
                                 int retry,
                                 const char *ring_id) {
    uint8_t candidates[N];
    int num_candidates;
    derive_w_reject_candidates(candidates, &num_candidates, pk_seed, msg, msg_len, retry, ring_id);

    int check_limit = (num_candidates < DEHYDRATE_W_REJECT_K) ? num_candidates : DEHYDRATE_W_REJECT_K;
    for (int i = 0; i < check_limit; i++) {
        int pos = candidates[i];
        // If w != w', this candidate is problematic
        if (mod_p(w_round->c[pos]) != mod_p(w_prime->c[pos])) {
            return 0;
        }
    }
    return 1;  // All candidates are clean
}

// ============================================================================
// Context-based dehydration: use local neighbors to predict/restore values
// ============================================================================

// Predict value at position i from its neighbors (in P-space)
// Uses simple average of immediate neighbors, wrapped for ring
static int16_t predict_from_context(const ring_t *w, int pos) {
    int prev = (pos - 1 + N) % N;
    int next = (pos + 1) % N;
    // Average of neighbors, rounded
    int sum = mod_p(w->c[prev]) + mod_p(w->c[next]);
    return (int16_t)((sum + 1) / 2);  // Round to nearest
}

// More sophisticated: use 4 neighbors with distance weighting
static int16_t predict_from_context4(const ring_t *w, int pos) {
    int p1 = (pos - 1 + N) % N;
    int p2 = (pos - 2 + N) % N;
    int n1 = (pos + 1) % N;
    int n2 = (pos + 2) % N;
    // Weighted average: closer neighbors have more weight
    // w = 2*near + 1*far, sum weights = 6
    int sum = 2*mod_p(w->c[p1]) + 2*mod_p(w->c[n1]) + mod_p(w->c[p2]) + mod_p(w->c[n2]);
    return (int16_t)((sum + 3) / 6);  // Round to nearest
}

// Check if value at pos matches its contextual prediction
static int matches_context(const ring_t *w, int pos) {
    int16_t actual = mod_p(w->c[pos]);
    int16_t predicted = predict_from_context(w, pos);
    return actual == predicted;
}

// ============================================================================
// 2-bit context hint dehydration
// For each position, 2 bits encode which reconstruction rule to use:
//   Rule 0: value = L (left neighbor)
//   Rule 1: value = R (right neighbor)
//   Rule 2: value = (L + R) / 2 (average, round down)
//   Rule 3: value = (L + R + 1) / 2 (average, round up)
// ============================================================================

// 2-bit hint encoding:
// 00 = no dehydration at this position (skip)
// 01 = value = L (left neighbor)
// 10 = value = R (right neighbor)
// 11 = value = (L + R + 1) / 2 (average, round up - covers most cases)
#define HINT2_SKIP        0
#define HINT2_RULE_LEFT   1
#define HINT2_RULE_RIGHT  2
#define HINT2_RULE_AVG    3
#define HINT2_NO_MATCH    -1

// Apply a 2-bit rule to get reconstructed value
static int16_t apply_hint2_rule(int rule, int16_t L, int16_t R) {
    switch (rule) {
        case HINT2_RULE_LEFT:  return L;
        case HINT2_RULE_RIGHT: return R;
        case HINT2_RULE_AVG:   return (L + R + 1) / 2;  // Round up covers more cases
        case HINT2_SKIP:       return 0;  // No restore
        default: return 0;
    }
}

// Find which 2-bit rule (if any) matches the actual value at position
// Returns rule index (1-3) or HINT2_NO_MATCH if none work
// Note: returns 0 (HINT2_SKIP) is reserved for "don't dehydrate"
static int find_hint2_rule(const ring_t *w, int pos) {
    int16_t actual = mod_p(w->c[pos]);
    int prev = (pos - 1 + N) % N;
    int next = (pos + 1) % N;
    int16_t L = mod_p(w->c[prev]);
    int16_t R = mod_p(w->c[next]);

    // Check each rule - average first (most common), then copy rules
    int16_t avg = (L + R + 1) / 2;
    if (actual == avg)             return HINT2_RULE_AVG;
    if (actual == L)               return HINT2_RULE_LEFT;
    if (actual == R)               return HINT2_RULE_RIGHT;

    return HINT2_NO_MATCH;
}

// Number of positions to dehydrate with 2-bit hints
#define HINT2_POSITIONS 20  // 20 positions × 2 bits = 40 bits = 5 bytes

// Dehydrate using 2-bit context hints
// Returns the hint bits packed into bytes, and count of positions dehydrated
static int dehydrate_w_hint2(ring_t *w_round,
                              const uint8_t *pk_seed,
                              const uint8_t *msg, size_t msg_len,
                              int retry,
                              const char *ring_id,
                              uint8_t *hint_bits,  // Output: packed 2-bit hints
                              int *hint_bytes) {   // Output: number of hint bytes
    uint8_t candidates[N];
    int num_candidates;
    derive_w_reject_candidates(candidates, &num_candidates, pk_seed, msg, msg_len, retry, ring_id);

    int check_limit = (num_candidates < HINT2_POSITIONS) ? num_candidates : HINT2_POSITIONS;

    // Pack 2-bit hints: 4 hints per byte
    memset(hint_bits, 0, (HINT2_POSITIONS + 3) / 4);

    int dehydrated = 0;
    uint8_t skip[N] = {0};  // Track which positions to skip (neighbors of dehydrated)

    for (int i = 0; i < check_limit; i++) {
        int pos = candidates[i];
        int prev = (pos - 1 + N) % N;
        int next = (pos + 1) % N;

        // Skip if position or neighbors already processed
        if (skip[pos] || skip[prev] || skip[next]) {
            // Store "no-op" hint (we'll use rule 0 but not zero the position)
            continue;
        }

        int rule = find_hint2_rule(w_round, pos);
        if (rule != HINT2_NO_MATCH && mod_p(w_round->c[pos]) != 0) {
            // Store the 2-bit rule
            int byte_idx = i / 4;
            int bit_idx = (i % 4) * 2;
            hint_bits[byte_idx] |= (rule << bit_idx);

            // Zero the position
            w_round->c[pos] = 0;
            skip[pos] = 1;
            skip[prev] = 1;  // Don't dehydrate adjacent
            skip[next] = 1;
            dehydrated++;
        }
    }

    *hint_bytes = (check_limit + 3) / 4;  // Round up to bytes
    return dehydrated;
}

// Rehydrate using 2-bit context hints
static void rehydrate_w_hint2(ring_t *w_round,
                               const uint8_t *pk_seed,
                               const uint8_t *msg, size_t msg_len,
                               int retry,
                               const char *ring_id,
                               const uint8_t *hint_bits) {
    uint8_t candidates[N];
    int num_candidates;
    derive_w_reject_candidates(candidates, &num_candidates, pk_seed, msg, msg_len, retry, ring_id);

    int check_limit = (num_candidates < HINT2_POSITIONS) ? num_candidates : HINT2_POSITIONS;

    uint8_t processed[N] = {0};

    for (int i = 0; i < check_limit; i++) {
        int pos = candidates[i];
        int prev = (pos - 1 + N) % N;
        int next = (pos + 1) % N;

        // Skip if position or neighbors already processed
        if (processed[pos] || processed[prev] || processed[next]) {
            continue;
        }

        // If position is 0, apply the hint rule to restore
        if (w_round->c[pos] == 0) {
            // Extract 2-bit rule
            int byte_idx = i / 4;
            int bit_idx = (i % 4) * 2;
            int rule = (hint_bits[byte_idx] >> bit_idx) & 0x3;

            int16_t L = mod_p(w_round->c[prev]);
            int16_t R = mod_p(w_round->c[next]);
            int16_t restored = apply_hint2_rule(rule, L, R);

            // Only restore if the rule gives a non-zero value
            // (otherwise it was a natural zero or rule 0)
            if (restored != 0) {
                w_round->c[pos] = restored;
            }
            processed[pos] = 1;
            processed[prev] = 1;
            processed[next] = 1;
        }
    }
}

// Check if position is in a "flat" region (both neighbors have same non-zero value)
// This is a stronger condition that makes dehydration unambiguous
static int is_flat_region(const ring_t *w, int pos) {
    int prev = (pos - 1 + N) % N;
    int next = (pos + 1) % N;
    int16_t v_prev = mod_p(w->c[prev]);
    int16_t v_next = mod_p(w->c[next]);
    // Both neighbors must be equal and non-zero
    return (v_prev == v_next && v_prev != 0);
}

// Get the flat region value (assumes is_flat_region returned true)
static int16_t get_flat_value(const ring_t *w, int pos) {
    int prev = (pos - 1 + N) % N;
    return mod_p(w->c[prev]);
}

// Dehydrate using flat-region context: only zero positions in flat regions
// A flat region has both neighbors equal and non-zero, and the position matches them
// This is unambiguous: natural zeros can't be in a flat non-zero region
// Returns number of positions dehydrated
static int dehydrate_w_context(ring_t *w_round,
                                const uint8_t *pk_seed,
                                const uint8_t *msg, size_t msg_len,
                                int retry,
                                const char *ring_id) {
    uint8_t candidates[N];
    int num_candidates;
    derive_w_reject_candidates(candidates, &num_candidates, pk_seed, msg, msg_len, retry, ring_id);

    int dehydrated = 0;
    int check_limit = (num_candidates < DEHYDRATE_W_REJECT_K) ? num_candidates : DEHYDRATE_W_REJECT_K;

    // Process candidates in order, but skip adjacent positions (context would be affected)
    uint8_t processed[N] = {0};
    for (int i = 0; i < check_limit; i++) {
        int pos = candidates[i];

        // Skip if this position or neighbors were already processed
        int prev = (pos - 1 + N) % N;
        int next = (pos + 1) % N;
        if (processed[pos] || processed[prev] || processed[next]) {
            continue;
        }

        // Only dehydrate if in a flat region AND value equals the flat value
        if (is_flat_region(w_round, pos)) {
            int16_t flat_val = get_flat_value(w_round, pos);
            if (mod_p(w_round->c[pos]) == flat_val) {
                w_round->c[pos] = 0;
                processed[pos] = 1;
                dehydrated++;
            }
        }
    }
    return dehydrated;
}

// Rehydrate using flat-region context with count: restore exactly `count` zeros in flat regions
// The count tells us how many positions were dehydrated, avoiding natural zero ambiguity
static void rehydrate_w_context(ring_t *w_round,
                                 const uint8_t *pk_seed,
                                 const uint8_t *msg, size_t msg_len,
                                 int retry,
                                 const char *ring_id,
                                 int count) {  // Number of positions that were dehydrated
    uint8_t candidates[N];
    int num_candidates;
    derive_w_reject_candidates(candidates, &num_candidates, pk_seed, msg, msg_len, retry, ring_id);

    int check_limit = (num_candidates < DEHYDRATE_W_REJECT_K) ? num_candidates : DEHYDRATE_W_REJECT_K;

    // Process candidates in same order as dehydration, restore exactly `count` positions
    uint8_t processed[N] = {0};
    int restored = 0;
    for (int i = 0; i < check_limit && restored < count; i++) {
        int pos = candidates[i];

        // Skip if this position or neighbors were already processed
        int prev = (pos - 1 + N) % N;
        int next = (pos + 1) % N;
        if (processed[pos] || processed[prev] || processed[next]) {
            continue;
        }

        // If in a flat region and current value is 0, restore to flat value
        if (w_round->c[pos] == 0 && is_flat_region(w_round, pos)) {
            w_round->c[pos] = get_flat_value(w_round, pos);
            processed[pos] = 1;
            restored++;
        }
    }
}

// Dehydrate w using bitmask: returns bitmask of which candidates were dehydrated
// Each bit i in the mask indicates whether candidate[i] was dehydrated
// A candidate is dehydrated if: w == w' && w' != 0
// Returns the bitmask (0-255 for K=8)
static uint8_t dehydrate_w_bitmask(ring_t *w_round,
                                    const ring_t *w_prime,
                                    const uint8_t *pk_seed,
                                    const uint8_t *msg, size_t msg_len,
                                    int retry,
                                    const char *ring_id) {
    uint8_t candidates[N];
    int num_candidates;
    derive_w_reject_candidates(candidates, &num_candidates, pk_seed, msg, msg_len, retry, ring_id);

    uint8_t mask = 0;
    int check_limit = (num_candidates < DEHYDRATE_W_REJECT_K) ? num_candidates : DEHYDRATE_W_REJECT_K;
    for (int i = 0; i < check_limit; i++) {
        int pos = candidates[i];
        // Dehydrate if w == w' && w' != 0
        if (mod_p(w_round->c[pos]) == mod_p(w_prime->c[pos]) &&
            mod_p(w_prime->c[pos]) != 0) {
            w_round->c[pos] = 0;
            mask |= (1 << i);
        }
    }
    return mask;
}

// Rehydrate w using bitmask: restore positions indicated by the mask
static void rehydrate_w_bitmask(ring_t *w_round,
                                 const ring_t *w_prime,
                                 const uint8_t *pk_seed,
                                 const uint8_t *msg, size_t msg_len,
                                 int retry,
                                 const char *ring_id,
                                 uint8_t mask) {  // Bitmask of which candidates to restore
    uint8_t candidates[N];
    int num_candidates;
    derive_w_reject_candidates(candidates, &num_candidates, pk_seed, msg, msg_len, retry, ring_id);

    int check_limit = (num_candidates < DEHYDRATE_W_REJECT_K) ? num_candidates : DEHYDRATE_W_REJECT_K;
    for (int i = 0; i < check_limit; i++) {
        if (mask & (1 << i)) {
            int pos = candidates[i];
            // Restore from w' (the dehydrated value)
            w_round->c[pos] = mod_p(w_prime->c[pos]);
        }
    }
}
#endif

// ============================================================================
// Component bounds check (no per-index coupling)
// ============================================================================

// Maximum coefficient in valid signature component
#define MAX_MASTER_COEFF (NONCE_WEIGHT + CHALLENGE_WEIGHT * ETA + 10)

int verify_coupling(const ring_t *s_cyc, const ring_t *s_neg) {
    for (int i = 0; i < N; i++) {
        if (abs(centered(s_cyc->c[i])) > MAX_MASTER_COEFF) {
            return 0;
        }
        if (abs(centered(s_neg->c[i])) > MAX_MASTER_COEFF) {
            return 0;
        }
    }
    return 1;
}

// Verify trace-zero constraint: Σx[i] ≡ 0 (mod q)
int verify_trace_zero(const master_t *x) {
    int64_t sum = 0;
    for (int i = 0; i < N2; i++) {
        sum += centered(x->c[i]);
    }
    // Allow sum to be any multiple of q (not just 0)
    return (mod_q(sum) == 0);
}

// Verify trace-zero from projected rings: Σs_master[i] ≡ 0 (mod q)
int verify_trace_zero_projected(const ring_t *s_cyc, const ring_t *s_neg) {
    // Split projection: trace is sum of both halves
    int64_t sum = 0;
    for (int i = 0; i < N; i++) {
        sum += centered(s_cyc->c[i]);
        sum += centered(s_neg->c[i]);
    }
    return (mod_q(sum) == 0);
}

// ============================================================================
// Compute norms
// ============================================================================

void compute_master_norms(stats_t *st, const master_t *x) {
    st->master_linf = 0;
    double sum_sq = 0;
    for (int i = 0; i < N2; i++) {
        int32_t c = centered(x->c[i]);
        if (abs(c) > st->master_linf) st->master_linf = abs(c);
        sum_sq += (double)c * c;
    }
    st->master_l2 = sqrt(sum_sq);
}

void compute_ring_norms(int *linf, double *l2, const ring_t *r) {
    *linf = 0;
    double sum_sq = 0;
    for (int i = 0; i < N; i++) {
        int32_t c = centered(r->c[i]);
        if (abs(c) > *linf) *linf = abs(c);
        sum_sq += (double)c * c;
    }
    *l2 = sqrt(sum_sq);
}

static int ring_linf(const ring_t *r) {
    int linf = 0;
    for (int i = 0; i < N; i++) {
        int32_t c = centered(r->c[i]);
        if (abs(c) > linf) linf = abs(c);
    }
    return linf;
}

static void hist_add(int *hist, int bins, int offset, int value, int *oob) {
    int idx = value + offset;
    if (idx < 0 || idx >= bins) {
        (*oob)++;
        return;
    }
    hist[idx]++;
}

static int hist_sum(const int *hist, int bins) {
    int total = 0;
    for (int i = 0; i < bins; i++) total += hist[i];
    return total;
}

static double hist_entropy(const int *hist, int bins, int total) {
    if (total <= 0) return 0.0;
    double h = 0.0;
    const double inv_log2 = 1.0 / log(2.0);
    for (int i = 0; i < bins; i++) {
        if (hist[i] == 0) continue;
        double p = (double)hist[i] / (double)total;
        h -= p * log(p) * inv_log2;
    }
    return h;
}

static void print_coeffs_centered(const char *label, const coeff_t *vals, int n) {
    printf("  %s:", label);
    for (int i = 0; i < n; i++) {
        if (i % 16 == 0) printf("\n    ");
        printf("%d", centered(vals[i]));
        if (i != n - 1) printf(", ");
    }
    printf("\n");
}

static void print_hist_values(const int *hist, int bins, int offset) {
    printf("    counts (value = index - %d): [", offset);
    for (int i = 0; i < bins; i++) {
        if (i % 16 == 0) printf("\n      ");
        printf("%d", hist[i]);
        if (i != bins - 1) printf(", ");
    }
    printf("\n    ]\n");
}

static void print_index_counts(const char *label, const int *counts, int n) {
    printf("  %s: [", label);
    for (int i = 0; i < n; i++) {
        if (i % 16 == 0) printf("\n    ");
        printf("%d", counts[i]);
        if (i != n - 1) printf(", ");
    }
    printf("\n  ]\n");
}

static void print_hist_summary(const char *label, const int *hist, int bins, int offset, int oob) {
    int total = hist_sum(hist, bins);
    int nonzero = 0;
    int min_bin = -1;
    int max_bin = -1;
    int min_count = 0;
    int max_count = 0;

    for (int i = 0; i < bins; i++) {
        int count = hist[i];
        if (count == 0) continue;
        nonzero++;
        if (min_bin < 0) min_bin = i;
        max_bin = i;
        if (min_count == 0 || count < min_count) min_count = count;
        if (count > max_count) max_count = count;
    }

    printf("  %s: samples=%d, nonzero=%d, entropy=%.3f bits\n",
           label, total, nonzero, hist_entropy(hist, bins, total));
    if (min_bin >= 0) {
        printf("    range=[%d,%d], min_count=%d, max_count=%d, oob=%d\n",
               min_bin - offset, max_bin - offset, min_count, max_count, oob);
    } else {
        printf("    range=[n/a], min_count=0, max_count=0, oob=%d\n", oob);
    }
    print_hist_values(hist, bins, offset);
}

static void print_hist_c_array(const char *name, const int *hist, int bins) {
    printf("static const uint32_t %s[%d] = {", name, bins);
    for (int i = 0; i < bins; i++) {
        if ((i % 16) == 0) printf("\n    ");
        printf("%d,", hist[i]);
    }
    printf("\n};\n");
}

#if SIG_RANGE_TABLES_GEN
static void scale_hist_to_cum(const int *hist, int bins, int min_count, uint32_t total,
                              uint32_t *cum_out) {
    uint64_t sum = 0;
    for (int i = 0; i < bins; i++) {
        sum += (uint64_t)hist[i] + (uint64_t)min_count;
    }
    if (sum == 0) {
        cum_out[0] = 0;
        for (int i = 0; i < bins; i++) {
            cum_out[i + 1] = (uint32_t)(((uint64_t)(i + 1) * total) / bins);
        }
        cum_out[bins] = total;
        return;
    }

    uint32_t *scaled = calloc((size_t)bins, sizeof(uint32_t));
    uint64_t *rem = calloc((size_t)bins, sizeof(uint64_t));
    if (!scaled || !rem) {
        fprintf(stderr, "ERROR: alloc failed for table generation\n");
        free(scaled);
        free(rem);
        return;
    }

    uint32_t scaled_sum = 0;
    for (int i = 0; i < bins; i++) {
        uint64_t freq = (uint64_t)hist[i] + (uint64_t)min_count;
        uint64_t prod = freq * (uint64_t)total;
        uint32_t s = (uint32_t)(prod / sum);
        if (s == 0) s = 1;
        scaled[i] = s;
        rem[i] = prod % sum;
        scaled_sum += s;
    }

    while (scaled_sum > total) {
        int idx = -1;
        uint64_t best = UINT64_MAX;
        for (int i = 0; i < bins; i++) {
            if (scaled[i] > 1 && rem[i] < best) {
                best = rem[i];
                idx = i;
            }
        }
        if (idx < 0) break;
        scaled[idx]--;
        scaled_sum--;
    }

    while (scaled_sum < total) {
        int idx = 0;
        uint64_t best = 0;
        for (int i = 0; i < bins; i++) {
            if (rem[i] > best) {
                best = rem[i];
                idx = i;
            }
        }
        scaled[idx]++;
        scaled_sum++;
    }

    cum_out[0] = 0;
    for (int i = 0; i < bins; i++) {
        cum_out[i + 1] = cum_out[i] + scaled[i];
    }
    cum_out[bins] = total;

    free(scaled);
    free(rem);
}

static void build_small_range_cum(const int *hist, int bins, int offset,
                                  int min_val, int max_val, int min_count,
                                  uint32_t total, uint32_t *cum_out) {
    int symbols = max_val - min_val + 1;
    int total_symbols = symbols + 1;
    int *small_hist = calloc((size_t)total_symbols, sizeof(int));
    if (!small_hist) {
        fprintf(stderr, "ERROR: alloc failed for table generation\n");
        return;
    }

    for (int i = 0; i < bins; i++) {
        int val = i - offset;
        int count = hist[i];
        if (val >= min_val && val <= max_val) {
            small_hist[val - min_val] += count;
        } else {
            small_hist[total_symbols - 1] += count;
        }
    }

    scale_hist_to_cum(small_hist, total_symbols, min_count, total, cum_out);
    free(small_hist);
}

static void print_cum_table(const char *name, const uint32_t *cum, int bins) {
    printf("static const uint32_t %s[%d] = {", name, bins);
    for (int i = 0; i < bins; i++) {
        if ((i % 16) == 0) printf("\n    ");
        printf("%u,", cum[i]);
    }
    printf("\n};\n");
}

static void generate_range_tables(const secret_key_t *sk, const public_key_t *pk,
                                  const uint8_t *msg, size_t msg_len) {
    int hist_s_cyc[S_MAX_SYMBOLS] = {0};
    int hist_s_neg_high[S_MAX_SYMBOLS] = {0};
    int hist_w_cyc[PK_MAX_SYMBOLS] = {0};
    int hist_w_neg[PK_MAX_SYMBOLS] = {0};
#if SIG_W_COND
    int hist_w_neg_cond[W_NEG_COND_BUCKETS][P] = {0};
#endif
#if P <= 16
    int hist_w_pair[P * P] = {0};
#endif
    int oob_s_cyc = 0, oob_s_neg = 0, oob_w_cyc = 0, oob_w_neg = 0;
    int samples = 0;

    for (int t = 0; t < SIG_RANGE_TABLES_SAMPLES; t++) {
        signature_t sig;
        if (!sign(&sig, sk, pk, msg, msg_len)) continue;
        samples++;
        for (int i = 0; i < N; i++) {
            int32_t s_cyc = centered(sig.s_cyc.c[i]);
            int32_t s_neg_high = centered(sig.s_neg.c[i]) >> 1;
            hist_add(hist_s_cyc, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, s_cyc, &oob_s_cyc);
            hist_add(hist_s_neg_high, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, s_neg_high, &oob_s_neg);
            hist_add(hist_w_cyc, PK_MAX_SYMBOLS, 0, sig.w_cyc.c[i], &oob_w_cyc);
            hist_add(hist_w_neg, PK_MAX_SYMBOLS, 0, sig.w_neg.c[i], &oob_w_neg);
#if SIG_W_COND
            if (sig.w_cyc.c[i] >= 0 && sig.w_cyc.c[i] < P &&
                sig.w_neg.c[i] >= 0 && sig.w_neg.c[i] < P) {
                int bucket = (sig.w_cyc.c[i] == 0 || sig.w_cyc.c[i] == (P - 1)) ? 0 : 1;
                hist_w_neg_cond[bucket][sig.w_neg.c[i]]++;
            }
#endif
#if P <= 16
            if (sig.w_cyc.c[i] >= 0 && sig.w_cyc.c[i] < P &&
                sig.w_neg.c[i] >= 0 && sig.w_neg.c[i] < P) {
                int pair = sig.w_cyc.c[i] * P + sig.w_neg.c[i];
                if (pair >= 0 && pair < (P * P)) {
                    hist_w_pair[pair]++;
                }
            }
#endif
        }
    }

    printf("RANGE TABLE GENERATION (%d signatures)\n\n", samples);
#if SIG_RANGE_S && !SIG_HUFFMAN_DYNAMIC
    uint32_t s_cyc_cum[S_CYC_SMALL_TOTAL_SYMBOLS + 1];
    uint32_t s_negh_cum[S_NEGH_SMALL_TOTAL_SYMBOLS + 1];
    build_small_range_cum(hist_s_cyc, S_MAX_SYMBOLS, S_SYMBOL_OFFSET,
                          S_CYC_SMALL_MIN, S_CYC_SMALL_MAX, 1,
                          S_CYC_SMALL_TOT, s_cyc_cum);
    build_small_range_cum(hist_s_neg_high, S_MAX_SYMBOLS, S_SYMBOL_OFFSET,
                          S_NEGH_SMALL_MIN, S_NEGH_SMALL_MAX, 1,
                          S_NEGH_SMALL_TOT, s_negh_cum);

    print_cum_table("S_CYC_SMALL_CUM", s_cyc_cum, S_CYC_SMALL_TOTAL_SYMBOLS + 1);
    print_cum_table("S_NEGH_SMALL_CUM", s_negh_cum, S_NEGH_SMALL_TOTAL_SYMBOLS + 1);
    printf("\n");
#endif

#if SIG_RANGE_W && !SIG_HUFFMAN_DYNAMIC && !SIG_W_CYC_ONLY && (P == 16)
    uint32_t w_cyc_cum[P + 1];
    scale_hist_to_cum(hist_w_cyc, P, 1, W_CYC_TOT, w_cyc_cum);
    print_cum_table("W_CYC_CUM", w_cyc_cum, P + 1);

#if SIG_W_DELTA
    (void)hist_w_neg;
#elif SIG_W_COND
    printf("static const uint32_t W_NEG_COND_TOT[%d] = { %u, %u };\n",
           W_NEG_COND_BUCKETS, W_NEG_COND_TOT[0], W_NEG_COND_TOT[1]);
    printf("static const uint32_t W_NEG_COND_CUM[%d][%d] = {\n", W_NEG_COND_BUCKETS, P + 1);
    for (int b = 0; b < W_NEG_COND_BUCKETS; b++) {
        uint32_t w_neg_cum[P + 1];
        scale_hist_to_cum(hist_w_neg_cond[b], P, 1, W_NEG_COND_TOT[b], w_neg_cum);
        printf("    {");
        for (int i = 0; i < (P + 1); i++) {
            if ((i % 16) == 0) printf("\n        ");
            printf("%u,", w_neg_cum[i]);
        }
        printf("\n    },\n");
    }
    printf("};\n\n");
#else
#if P <= 16
    uint32_t w_pair_cum[W_PAIR_SYMBOLS + 1];
    scale_hist_to_cum(hist_w_pair, W_PAIR_SYMBOLS, 1, W_PAIR_TOT, w_pair_cum);
    print_cum_table("W_PAIR_CUM", w_pair_cum, W_PAIR_SYMBOLS + 1);
#endif
#endif
#endif
}
#endif

// ============================================================================
// Key Generation
// ============================================================================

#define PK_SIZE_TARGET 256

void keygen(public_key_t *pk, secret_key_t *sk) {
    for (int attempt = 0; attempt < 1000; attempt++) {
        RAND_bytes(sk->seed, SEED_BYTES);
        memcpy(pk->seed, sk->seed, SEED_BYTES);

        // Expand public polynomial - SAME y for both rings (shared seed)
        ring_t y;
        expand_ring(&y, sk->seed, 0);

        // Sample sparse master secret (trace-zero by construction: equal +1 and -1)
        sample_sparse_master(&sk->x_master, SECRET_WEIGHT);

        // Project to components for public key computation
        ring_t x_cyc, x_neg;
        project_cyclic(&sk->x_master, &x_cyc);
        project_negacyclic(&sk->x_master, &x_neg);

        // Compute public keys: pk = Round(x * y) with shared y
        ring_t t_cyc, t_neg;
        mul_cyclic(&t_cyc, &x_cyc, &y);
        mul_negacyclic(&t_neg, &x_neg, &y);

        round_ring(&pk->pk_cyc, &t_cyc);
        round_ring(&pk->pk_neg, &t_neg);

        // Check if pk compresses to target size
        huffman_pk_t hpk;
        if (huffman_encode_pk(pk, &hpk)) {
            int pk_size = SEED_BYTES + hpk.pk_len;
            if (pk_size <= PK_SIZE_TARGET) {
                return;  // Success
            }
        }
    }
    // If we get here, use last attempt anyway
}

// ============================================================================
// Signing
// ============================================================================

int sign_with_stats(signature_t *sig, const secret_key_t *sk, const public_key_t *pk,
                    const uint8_t *msg, size_t msg_len, stats_t *st) {

    // SAME y for both rings - shared public polynomial
    ring_t y;
    expand_ring(&y, sk->seed, 0);
#if SIG_LOSSY_ZERO
    uint8_t is_zeroed[N];
    derive_zero_positions(is_zeroed, SIG_LOSSY_ZERO_K, pk->seed, msg, msg_len);
#endif

    for (int attempt = 0; attempt < MAX_ATTEMPTS; attempt++) {
        // Sample master nonce
        master_t r_master;
#if DETERMINISTIC_W
        uint8_t nonce_seed[32];
        hash_to_nonce_seed(nonce_seed, sk->seed, msg, msg_len, (uint32_t)attempt);
        expand_sparse_challenge(&r_master, nonce_seed, NONCE_WEIGHT);
#else
        sample_sparse_master(&r_master, NONCE_WEIGHT);
#endif

        // Project nonce
        ring_t r_cyc, r_neg;
        project_cyclic(&r_master, &r_cyc);
        project_negacyclic(&r_master, &r_neg);

        // Compute commitments - SAME y in both rings
        ring_t w_cyc_full, w_neg_full;
        mul_cyclic(&w_cyc_full, &r_cyc, &y);
        mul_negacyclic(&w_neg_full, &r_neg, &y);

        // Round commitments and store in signature
        round_ring(&sig->w_cyc, &w_cyc_full);
        round_ring(&sig->w_neg, &w_neg_full);

        // Hash to get challenge seed
        ring_t w_cyc_check = sig->w_cyc;
        ring_t w_neg_check = sig->w_neg;
#if SIG_LOSSY_ZERO
        for (int i = 0; i < N; i++) {
            if (is_zeroed[i]) {
                w_cyc_check.c[i] = 0;
                w_neg_check.c[i] = 0;
            }
        }
#endif

        uint8_t challenge_seed[SIGNATURE_CHALLENGE_BYTES];
        hash_to_challenge(challenge_seed, &w_cyc_check, &w_neg_check, pk, msg, msg_len);

        // Expand challenge in master ring
        master_t c_master;
        expand_sparse_challenge(&c_master, challenge_seed, CHALLENGE_WEIGHT);

        // Project challenge to component rings
        ring_t c_cyc, c_neg;
        project_cyclic(&c_master, &c_cyc);
        project_negacyclic(&c_master, &c_neg);

        // Project secret to component rings
        ring_t x_cyc, x_neg;
        project_cyclic(&sk->x_master, &x_cyc);
        project_negacyclic(&sk->x_master, &x_neg);

        // Compute responses: s = r + c * x (in component rings)
        ring_t cx_cyc, cx_neg;
        mul_cyclic(&cx_cyc, &c_cyc, &x_cyc);
        mul_negacyclic(&cx_neg, &c_neg, &x_neg);

        add_ring(&sig->s_cyc, &r_cyc, &cx_cyc);
        add_ring(&sig->s_neg, &r_neg, &cx_neg);

        // Verify component bounds (should always pass for honest signer)
        if (!verify_coupling(&sig->s_cyc, &sig->s_neg)) {
            continue;
        }

        // Check s fits in 5 bits for compression (|s| < 16)
        int s_max = 0;
        for (int i = 0; i < N; i++) {
            int v = abs(centered(sig->s_cyc.c[i]));
            if (v > s_max) s_max = v;
            v = abs(centered(sig->s_neg.c[i]));
            if (v > s_max) s_max = v;
        }
        if (s_max >= 16) {
            continue;  // Reject - s too large for 5-bit
        }

#if SIG_LOSSY_ZERO
        ring_t s_cyc_full = sig->s_cyc;
        ring_t s_neg_full = sig->s_neg;
#endif
        ring_t s_cyc_check = sig->s_cyc;
        ring_t s_neg_check = sig->s_neg;
#if SIG_LOSSY_ZERO
        for (int i = 0; i < N; i++) {
            if (is_zeroed[i]) {
                s_cyc_check.c[i] = 0;
                s_neg_check.c[i] = 0;
            }
        }
#endif

        // Check verification error - SAME y in both rings
        ring_t sy_cyc, sy_neg;
        mul_cyclic(&sy_cyc, &s_cyc_check, &y);
        mul_negacyclic(&sy_neg, &s_neg_check, &y);

        ring_t pk_unround_cyc, pk_unround_neg;
        unround_ring(&pk_unround_cyc, &pk->pk_cyc);
        unround_ring(&pk_unround_neg, &pk->pk_neg);

        ring_t cpk_cyc, cpk_neg;
        mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
        mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

        ring_t w_prime_cyc, w_prime_neg;
        sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
        sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

        // Unround the commitment to compare in Q-domain
        ring_t w_unround_cyc, w_unround_neg;
        unround_ring(&w_unround_cyc, &w_cyc_check);
        unround_ring(&w_unround_neg, &w_neg_check);

        // Check error: w' should be close to unround(w)
        int max_err = 0;
        double err_sum_sq = 0;
        for (int i = 0; i < N; i++) {
            int diff = abs(centered(mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
            if (diff > max_err) max_err = diff;
            err_sum_sq += (double)diff * diff;

            diff = abs(centered(mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
            if (diff > max_err) max_err = diff;
            err_sum_sq += (double)diff * diff;
        }

        int round_match = 1;
#if COMPACT_REQUIRE_ROUND
        // Ensure w' rounds back to the original commitment (needed for compact verification)
        ring_t w_round_check_cyc, w_round_check_neg;
        round_ring(&w_round_check_cyc, &w_prime_cyc);
        round_ring(&w_round_check_neg, &w_prime_neg);
        for (int i = 0; i < N; i++) {
            if (w_round_check_cyc.c[i] != w_cyc_check.c[i] ||
                w_round_check_neg.c[i] != w_neg_check.c[i]) {
                round_match = 0;
                break;
            }
        }
#endif

        // Debug: print only failed attempts (should be rare)
        if (attempt > 0 && attempt < 5) {
            printf("    [retry %d] max_err=%d, TAU=%d\n", attempt, max_err, TAU);
        }

        if (round_match && max_err <= TAU) {
#if SIG_LOSSY_ZERO
            sig->s_cyc = s_cyc_check;
            sig->s_neg = s_neg_check;
            sig->w_cyc = w_cyc_check;
            sig->w_neg = w_neg_check;
#endif
            if (st) {
                // Lift to master for stats
                master_t s_master;
#if SIG_LOSSY_ZERO
                crt_lift(&s_cyc_full, &s_neg_full, &s_master);
#else
                crt_lift(&sig->s_cyc, &sig->s_neg, &s_master);
#endif
                compute_master_norms(st, &s_master);
#if SIG_LOSSY_ZERO
                compute_ring_norms(&st->cyc_linf, &st->cyc_l2, &s_cyc_full);
                compute_ring_norms(&st->neg_linf, &st->neg_l2, &s_neg_full);
#else
                compute_ring_norms(&st->cyc_linf, &st->cyc_l2, &sig->s_cyc);
                compute_ring_norms(&st->neg_linf, &st->neg_l2, &sig->s_neg);
#endif
                st->err_linf = max_err;
                st->err_l2 = sqrt(err_sum_sq);
            }
            return 1;
        }
    }
    return 0;
}

int sign(signature_t *sig, const secret_key_t *sk, const public_key_t *pk,
         const uint8_t *msg, size_t msg_len) {
    return sign_with_stats(sig, sk, pk, msg, msg_len, NULL);
}

// ============================================================================
// Minimal signature (challenge hash + delta + hints)
// ============================================================================

int sign_minimal(minimal_sig_t *msig, const secret_key_t *sk, const public_key_t *pk,
                 const uint8_t *msg, size_t msg_len) {
    ring_t y;
    expand_ring(&y, sk->seed, 0);

    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    for (uint32_t attempt = 0; attempt < MAX_ATTEMPTS; attempt++) {
        master_t r_master;
        expand_nonce_master(&r_master, sk->seed, msg, msg_len, attempt);

        ring_t r_cyc, r_neg;
        project_cyclic(&r_master, &r_cyc);
        project_negacyclic(&r_master, &r_neg);

        ring_t w_full_cyc, w_full_neg;
        mul_cyclic(&w_full_cyc, &r_cyc, &y);
        mul_negacyclic(&w_full_neg, &r_neg, &y);

        ring_t w_round_cyc, w_round_neg;
        round_ring(&w_round_cyc, &w_full_cyc);
        round_ring(&w_round_neg, &w_full_neg);

        uint8_t challenge_full[32];
        hash_to_challenge(challenge_full, &w_round_cyc, &w_round_neg, pk, msg, msg_len);
        memcpy(msig->challenge, challenge_full, CHALLENGE_BYTES);

        master_t c_master;
        expand_sparse_challenge_len(&c_master, msig->challenge, CHALLENGE_BYTES, CHALLENGE_WEIGHT);

        ring_t c_cyc, c_neg;
        project_cyclic(&c_master, &c_cyc);
        project_negacyclic(&c_master, &c_neg);

        // Project secret to component rings
        ring_t x_cyc, x_neg;
        project_cyclic(&sk->x_master, &x_cyc);
        project_negacyclic(&sk->x_master, &x_neg);

        ring_t cx_cyc, cx_neg;
        mul_cyclic(&cx_cyc, &c_cyc, &x_cyc);
        mul_negacyclic(&cx_neg, &c_neg, &x_neg);

        ring_t s_cyc, s_neg;
        add_ring(&s_cyc, &r_cyc, &cx_cyc);
        add_ring(&s_neg, &r_neg, &cx_neg);

        if (!verify_coupling(&s_cyc, &s_neg)) {
            continue;
        }

        if (ring_linf(&s_cyc) > S_BOUND || ring_linf(&s_neg) > S_BOUND) {
            continue;
        }

        ring_t delta;
        int ok = 1;
        for (int i = 0; i < N; i++) {
            int32_t diff = centered(s_cyc.c[i]) - centered(s_neg.c[i]);
            if (diff & 1) {
                ok = 0;
                break;
            }
            delta.c[i] = mod_q(diff / 2);
        }
        if (!ok) {
            continue;
        }

        ring_t sy_cyc, sy_neg;
        mul_cyclic(&sy_cyc, &s_cyc, &y);
        mul_negacyclic(&sy_neg, &s_neg, &y);

        ring_t cpk_cyc, cpk_neg;
        mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
        mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

        ring_t w_prime_cyc, w_prime_neg;
        sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
        sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

        ring_t w_round_prime_cyc, w_round_prime_neg;
        round_ring(&w_round_prime_cyc, &w_prime_cyc);
        round_ring(&w_round_prime_neg, &w_prime_neg);

        ring_t w_unround_cyc, w_unround_neg;
        unround_ring(&w_unround_cyc, &w_round_cyc);
        unround_ring(&w_unround_neg, &w_round_neg);

        int max_err = 0;
        for (int i = 0; i < N; i++) {
            int diff = abs(centered(mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
            if (diff > max_err) max_err = diff;
            diff = abs(centered(mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
            if (diff > max_err) max_err = diff;
        }
        if (max_err > TAU) {
            continue;
        }

        uint8_t c2_full[32];
        // Bind permutation to corrected w (w' + error) rather than raw round(w').
        hash_to_challenge_w1(c2_full, &w_round_cyc, pk, msg, msg_len);
        uint8_t perm[N];
        minimal_perm_from_seed(perm, c2_full, sizeof(c2_full));

        if (!encode_minimal_payload(&s_cyc, &delta, perm, msig)) {
            continue;
        }

        int hint_count = 0;
        if (!encode_w_hints(msig->hint_data, sizeof(msig->hint_data),
                            &w_round_cyc, &w_round_neg,
                            &w_round_prime_cyc, &w_round_prime_neg,
                            &msig->hint_len, &hint_count)) {
            continue;
        }

        int total_size = CHALLENGE_BYTES + msig->s_len + msig->hint_len;
        if (total_size > MIN_SIG_TARGET) {
            continue;
        }

        return 1;
    }
    return 0;
}

int verify_minimal(const minimal_sig_t *msig, const public_key_t *pk,
                   const uint8_t *msg, size_t msg_len) {
    ring_t s_cyc, delta;
    bitreader_t br;
    if (!decode_minimal_s(msig, &s_cyc, &br)) {
        return 0;
    }

    master_t c_master;
    expand_sparse_challenge_len(&c_master, msig->challenge, CHALLENGE_BYTES, CHALLENGE_WEIGHT);

    ring_t c_cyc, c_neg;
    project_cyclic(&c_master, &c_cyc);
    project_negacyclic(&c_master, &c_neg);

    ring_t y;
    expand_ring(&y, pk->seed, 0);

    ring_t sy_cyc;
    mul_cyclic(&sy_cyc, &s_cyc, &y);

    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    ring_t cpk_cyc;
    mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);

    ring_t w_prime_cyc;
    sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);

    ring_t w_round_prime_cyc;
    round_ring(&w_round_prime_cyc, &w_prime_cyc);

    ring_t w_round_cyc = w_round_prime_cyc;
    ring_t w_round_neg_dummy;
    memset(&w_round_neg_dummy, 0, sizeof(w_round_neg_dummy));
    if (!apply_w_hints(msig->hint_data, msig->hint_len,
                       &w_round_cyc, &w_round_neg_dummy, NULL)) {
        return 0;
    }

    uint8_t c2_check[32];
    hash_to_challenge_w1(c2_check, &w_round_cyc, pk, msg, msg_len);
    uint8_t perm[N];
    minimal_perm_from_seed(perm, c2_check, sizeof(c2_check));

    for (int i = 0; i < N; i++) {
        int32_t v = 0;
        if (!minimal_read_d(&br, &v)) return 0;
        delta.c[perm[i]] = mod_q(v);
    }

    ring_t s_neg;
    for (int i = 0; i < N; i++) {
        int32_t s_neg_val = centered(s_cyc.c[i]) - 2 * centered(delta.c[i]);
        s_neg.c[i] = mod_q(s_neg_val);
    }

    if (!verify_coupling(&s_cyc, &s_neg)) {
        return 0;
    }

    if (ring_linf(&s_cyc) > S_BOUND || ring_linf(&s_neg) > S_BOUND) {
        return 0;
    }

    master_t s_master;
    if (!crt_lift(&s_cyc, &s_neg, &s_master)) {
        return 0;
    }
    if (!verify_trace_zero(&s_master)) {
        return 0;
    }

    ring_t sy_neg;
    mul_negacyclic(&sy_neg, &s_neg, &y);

    ring_t cpk_neg;
    mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

    ring_t w_prime_neg;
    sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

    ring_t w_round_prime_neg;
    round_ring(&w_round_prime_neg, &w_prime_neg);

    w_round_cyc = w_round_prime_cyc;
    ring_t w_round_neg = w_round_prime_neg;
    if (!apply_w_hints(msig->hint_data, msig->hint_len,
                       &w_round_cyc, &w_round_neg, NULL)) {
        return 0;
    }

    uint8_t challenge_check[32];
    hash_to_challenge(challenge_check, &w_round_cyc, &w_round_neg, pk, msg, msg_len);
    if (memcmp(challenge_check, msig->challenge, CHALLENGE_BYTES) != 0) {
        return 0;
    }

    ring_t w_unround_cyc, w_unround_neg;
    unround_ring(&w_unround_cyc, &w_round_cyc);
    unround_ring(&w_unround_neg, &w_round_neg);

    int max_err = 0;
    for (int i = 0; i < N; i++) {
        int diff = abs(centered(mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
        if (diff > max_err) max_err = diff;
        diff = abs(centered(mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
        if (diff > max_err) max_err = diff;
    }

#if VERIFY_DEBUG_PRINT
    if (g_verify_debug) {
        printf("  Verify max_err: %d (TAU=%d)\n", max_err, TAU);
    }
#endif

    return max_err <= TAU;
}

// ============================================================================
// Seedless-w signature (nonce_seed + s, verifier reconstructs w)
// ============================================================================

// Expand nonce from public seed (for seedless signatures)
static void expand_nonce_from_seed(master_t *r, const uint8_t *nonce_seed,
                                   uint8_t attempt) {
    uint8_t buf[32];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
    EVP_DigestUpdate(ctx, "NONCE", 5);
    EVP_DigestUpdate(ctx, nonce_seed, NONCE_SEED_BYTES);
    EVP_DigestUpdate(ctx, &attempt, 1);
    unsigned int len = 32;
    EVP_DigestFinal_ex(ctx, buf, &len);
    EVP_MD_CTX_free(ctx);

    expand_sparse_challenge(r, buf, NONCE_WEIGHT);
}

int sign_seedless(seedless_sig_t *sig, const secret_key_t *sk, const public_key_t *pk,
                  const uint8_t *msg, size_t msg_len) {

    // Generate random nonce seed (NOT derived from sk_seed for public verifiability)
    RAND_bytes(sig->nonce_seed, NONCE_SEED_BYTES);

    ring_t y;
    expand_ring(&y, pk->seed, 0);

    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    // Project secret once
    ring_t x_cyc, x_neg;
    project_cyclic(&sk->x_master, &x_cyc);
    project_negacyclic(&sk->x_master, &x_neg);

    for (uint8_t attempt = 0; attempt < 255; attempt++) {
        // Expand nonce from public seed + attempt
        master_t r_master;
        expand_nonce_from_seed(&r_master, sig->nonce_seed, attempt);

        ring_t r_cyc, r_neg;
        project_cyclic(&r_master, &r_cyc);
        project_negacyclic(&r_master, &r_neg);

        // Compute w = round(r * y)
        ring_t w_full_cyc, w_full_neg;
        mul_cyclic(&w_full_cyc, &r_cyc, &y);
        mul_negacyclic(&w_full_neg, &r_neg, &y);

        ring_t w_round_cyc, w_round_neg;
        round_ring(&w_round_cyc, &w_full_cyc);
        round_ring(&w_round_neg, &w_full_neg);

        // Compute challenge c = H(w, pk, msg)
        uint8_t challenge_seed[32];
        hash_to_challenge(challenge_seed, &w_round_cyc, &w_round_neg, pk, msg, msg_len);

        master_t c_master;
        expand_sparse_challenge(&c_master, challenge_seed, CHALLENGE_WEIGHT);

        ring_t c_cyc, c_neg;
        project_cyclic(&c_master, &c_cyc);
        project_negacyclic(&c_master, &c_neg);

        // Compute s = r + c*x
        ring_t cx_cyc, cx_neg;
        mul_cyclic(&cx_cyc, &c_cyc, &x_cyc);
        mul_negacyclic(&cx_neg, &c_neg, &x_neg);

        ring_t s_cyc, s_neg;
        add_ring(&s_cyc, &r_cyc, &cx_cyc);
        add_ring(&s_neg, &r_neg, &cx_neg);

        // Check coupling
        if (!verify_coupling(&s_cyc, &s_neg)) {
            continue;
        }

        // Check s fits in compression bounds
        int s_max = 0;
        for (int i = 0; i < N; i++) {
            int v = abs(centered(s_cyc.c[i]));
            if (v > s_max) s_max = v;
            v = abs(centered(s_neg.c[i]));
            if (v > s_max) s_max = v;
        }
        if (s_max >= 16) continue;

        // Check verification error
        ring_t sy_cyc, sy_neg;
        mul_cyclic(&sy_cyc, &s_cyc, &y);
        mul_negacyclic(&sy_neg, &s_neg, &y);

        ring_t cpk_cyc, cpk_neg;
        mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
        mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

        ring_t w_prime_cyc, w_prime_neg;
        sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
        sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

        ring_t w_unround_cyc, w_unround_neg;
        unround_ring(&w_unround_cyc, &w_round_cyc);
        unround_ring(&w_unround_neg, &w_round_neg);

        int max_err = 0;
        for (int i = 0; i < N; i++) {
            int diff = abs(centered(mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
            if (diff > max_err) max_err = diff;
            diff = abs(centered(mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
            if (diff > max_err) max_err = diff;
        }

        if (max_err > TAU) continue;

        // Success! Encode s using range coder with delta encoding
        sig->attempt = attempt;

        // Store commitment hash c_tilde for binding
        memcpy(sig->c_tilde, challenge_seed, C_TILDE_BYTES);

        // Get permutation from challenge
        uint8_t perm[N];
        minimal_perm_from_seed(perm, challenge_seed, sizeof(challenge_seed));

        // Range-encode s_cyc + delta
        rc_enc_t s_rc;
        rc_enc_init(&s_rc, sig->s_data, sizeof(sig->s_data));

        // Encode s_cyc
        for (int i = 0; i < N; i++) {
            int idx = perm[i];
            int32_t val = centered(s_cyc.c[idx]);
            int sym = (val >= S_CYC_SMALL_MIN && val <= S_CYC_SMALL_MAX)
                ? (val - S_CYC_SMALL_MIN) : S_CYC_SMALL_ESC;
            rc_encode(&s_rc, S_CYC_SMALL_CUM[sym], S_CYC_SMALL_CUM[sym + 1], S_CYC_SMALL_TOT);
            if (sym == S_CYC_SMALL_ESC) {
                int32_t raw = val + S_CYC_ESC_BIAS;
                if (raw < 0 || raw >= (1 << S_CYC_ESC_RAW_BITS)) return 0;
                rc_encode_uniform(&s_rc, (uint32_t)raw, (1u << S_CYC_ESC_RAW_BITS));
            }
        }

        // Encode delta = (s_cyc - s_neg) / 2
        for (int i = 0; i < N; i++) {
            int idx = perm[i];
            int32_t s_cyc_val = centered(s_cyc.c[idx]);
            int32_t s_neg_val = centered(s_neg.c[idx]);
            int32_t diff = s_cyc_val - s_neg_val;
            if (diff & 1) return 0;  // Must be even
            int32_t delta = diff / 2;

            int sym = (delta >= S_DELTA_SMALL_MIN && delta <= S_DELTA_SMALL_MAX)
                ? (delta - S_DELTA_SMALL_MIN) : S_DELTA_SMALL_ESC;
            rc_encode(&s_rc, S_DELTA_SMALL_CUM[sym], S_DELTA_SMALL_CUM[sym + 1], S_DELTA_SMALL_TOT);
            if (sym == S_DELTA_SMALL_ESC) {
                int32_t raw = delta + S_DELTA_ESC_BIAS;
                if (raw < 0 || raw >= (1 << S_DELTA_ESC_RAW_BITS)) return 0;
                rc_encode_uniform(&s_rc, (uint32_t)raw, (1u << S_DELTA_ESC_RAW_BITS));
            }
        }

        sig->s_len = rc_finish(&s_rc);
        if (sig->s_len <= 0) return 0;

        return 1;
    }
    return 0;
}

int verify_seedless(const seedless_sig_t *sig, const public_key_t *pk,
                    const uint8_t *msg, size_t msg_len) {

    ring_t y;
    expand_ring(&y, pk->seed, 0);

    // Reconstruct r from nonce_seed + attempt
    master_t r_master;
    expand_nonce_from_seed(&r_master, sig->nonce_seed, sig->attempt);

    ring_t r_cyc, r_neg;
    project_cyclic(&r_master, &r_cyc);
    project_negacyclic(&r_master, &r_neg);

    // Reconstruct w = round(r * y)
    ring_t w_full_cyc, w_full_neg;
    mul_cyclic(&w_full_cyc, &r_cyc, &y);
    mul_negacyclic(&w_full_neg, &r_neg, &y);

    ring_t w_round_cyc, w_round_neg;
    round_ring(&w_round_cyc, &w_full_cyc);
    round_ring(&w_round_neg, &w_full_neg);

    // Reconstruct challenge and verify c_tilde binding
    uint8_t challenge_seed[32];
    hash_to_challenge(challenge_seed, &w_round_cyc, &w_round_neg, pk, msg, msg_len);

    // Check c_tilde matches - this binds the signature to w
    if (memcmp(sig->c_tilde, challenge_seed, C_TILDE_BYTES) != 0) {
        return 0;  // Commitment binding failed
    }

    // Get permutation
    uint8_t perm[N];
    minimal_perm_from_seed(perm, challenge_seed, sizeof(challenge_seed));

    // Decode s_cyc
    ring_t s_cyc, s_neg;
    rc_dec_t s_rc;
    rc_dec_init(&s_rc, sig->s_data, sig->s_len);

    for (int i = 0; i < N; i++) {
        int idx = perm[i];
        int sym = 0;
        if (!rc_decode_symbol(&s_rc, S_CYC_SMALL_CUM, S_CYC_SMALL_TOTAL_SYMBOLS, S_CYC_SMALL_TOT, &sym)) {
            return 0;
        }
        int32_t val;
        if (sym == S_CYC_SMALL_ESC) {
            uint32_t raw = 0;
            if (!rc_decode_uniform(&s_rc, (1u << S_CYC_ESC_RAW_BITS), &raw)) return 0;
            val = (int32_t)raw - S_CYC_ESC_BIAS;
        } else {
            val = sym + S_CYC_SMALL_MIN;
        }
        s_cyc.c[idx] = mod_q(val);
    }

    // Decode delta and reconstruct s_neg = s_cyc - 2*delta
    for (int i = 0; i < N; i++) {
        int idx = perm[i];
        int sym = 0;
        if (!rc_decode_symbol(&s_rc, S_DELTA_SMALL_CUM, S_DELTA_SMALL_TOTAL_SYMBOLS,
                              S_DELTA_SMALL_TOT, &sym)) {
            return 0;
        }
        int32_t delta;
        if (sym == S_DELTA_SMALL_ESC) {
            uint32_t raw = 0;
            if (!rc_decode_uniform(&s_rc, (1u << S_DELTA_ESC_RAW_BITS), &raw)) return 0;
            delta = (int32_t)raw - S_DELTA_ESC_BIAS;
        } else {
            delta = sym + S_DELTA_SMALL_MIN;
        }
        int32_t s_cyc_val = centered(s_cyc.c[idx]);
        int32_t s_neg_val = s_cyc_val - 2 * delta;
        s_neg.c[idx] = mod_q(s_neg_val);
    }

    // Verify coupling
    if (!verify_coupling(&s_cyc, &s_neg)) {
        return 0;
    }

    // Expand challenge
    master_t c_master;
    expand_sparse_challenge(&c_master, challenge_seed, CHALLENGE_WEIGHT);

    ring_t c_cyc, c_neg;
    project_cyclic(&c_master, &c_cyc);
    project_negacyclic(&c_master, &c_neg);

    // Compute w' = s*y - c*unround(pk)
    ring_t sy_cyc, sy_neg;
    mul_cyclic(&sy_cyc, &s_cyc, &y);
    mul_negacyclic(&sy_neg, &s_neg, &y);

    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    ring_t cpk_cyc, cpk_neg;
    mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
    mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

    ring_t w_prime_cyc, w_prime_neg;
    sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
    sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

    // Check error
    ring_t w_unround_cyc, w_unround_neg;
    unround_ring(&w_unround_cyc, &w_round_cyc);
    unround_ring(&w_unround_neg, &w_round_neg);

    int max_err = 0;
    for (int i = 0; i < N; i++) {
        int diff = abs(centered(mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
        if (diff > max_err) max_err = diff;
        diff = abs(centered(mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
        if (diff > max_err) max_err = diff;
    }

    return max_err <= TAU;
}

// ============================================================================
// Verification
// ============================================================================

int verify(const signature_t *sig, const public_key_t *pk,
           const uint8_t *msg, size_t msg_len) {

    // SAME y for both rings - shared public polynomial
    ring_t y;
    expand_ring(&y, pk->seed, 0);

#if SIG_LOSSY_ZERO
    uint8_t is_zeroed[N];
    const uint8_t *zeroed_ptr = is_zeroed;
    derive_zero_positions(is_zeroed, SIG_LOSSY_ZERO_K, pk->seed, msg, msg_len);
    for (int i = 0; i < N; i++) {
        if (is_zeroed[i]) {
            if (sig->s_cyc.c[i] != 0 || sig->s_neg.c[i] != 0) {
                return 0;
            }
            if (sig->w_cyc.c[i] != 0 || sig->w_neg.c[i] != 0) {
                return 0;
            }
        }
    }
#else
    const uint8_t *zeroed_ptr = NULL;
#endif

    // Verify component bounds first
    if (!verify_coupling(&sig->s_cyc, &sig->s_neg)) {
        return 0;
    }

#if !SIG_LOSSY_ZERO
    // Verify trace-zero constraint (on the lifted master element)
    // Note: This lifts s from the projected rings and checks trace in master
    master_t s_master;
    crt_lift(&sig->s_cyc, &sig->s_neg, &s_master);
    if (!verify_trace_zero(&s_master)) {
        return 0;
    }
#endif

    // Reconstruct challenge
    uint8_t challenge_seed[SIGNATURE_CHALLENGE_BYTES];
    hash_to_challenge(challenge_seed, &sig->w_cyc, &sig->w_neg, pk, msg, msg_len);

    master_t c_master;
    expand_sparse_challenge(&c_master, challenge_seed, CHALLENGE_WEIGHT);

    ring_t c_cyc, c_neg;
    project_cyclic(&c_master, &c_cyc);
    project_negacyclic(&c_master, &c_neg);

    // Compute s * y - SAME y in both rings
    ring_t sy_cyc, sy_neg;
    mul_cyclic(&sy_cyc, &sig->s_cyc, &y);
    mul_negacyclic(&sy_neg, &sig->s_neg, &y);

    // Compute c * unround(pk)
    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    ring_t cpk_cyc, cpk_neg;
    mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
    mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

    // w' = s*y - c*pk
    ring_t w_prime_cyc, w_prime_neg;
    sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
    sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

    // Unround the commitment and check error
    ring_t w_unround_cyc, w_unround_neg;
    unround_ring(&w_unround_cyc, &sig->w_cyc);
    unround_ring(&w_unround_neg, &sig->w_neg);

    int max_err = 0;
    for (int i = 0; i < N; i++) {
        if (zeroed_ptr && zeroed_ptr[i]) {
            continue;
        }
        int diff = abs(centered(mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
        if (diff > max_err) max_err = diff;
        diff = abs(centered(mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
        if (diff > max_err) max_err = diff;
    }

#if VERIFY_DEBUG_PRINT
    if (g_verify_debug) {
        printf("  Verify max_err: %d (TAU=%d)\n", max_err, TAU);
    }
#endif

    return max_err <= TAU;
}

// ============================================================================
// Attack simulation: try to forge with random components
// ============================================================================

int try_forge_uncoupled(signature_t *sig, const public_key_t *pk,
                        const uint8_t *msg, size_t msg_len) {

    // SAME y for both rings
    ring_t y;
    expand_ring(&y, pk->seed, 0);

    // Attacker tries to find valid signatures in each ring INDEPENDENTLY
    for (int attempt = 0; attempt < 10000; attempt++) {
        // Sample independent sparse vectors (NOT from master ring!)
        ring_t r_cyc, r_neg;
        memset(&r_cyc, 0, sizeof(r_cyc));
        memset(&r_neg, 0, sizeof(r_neg));

        for (int i = 0; i < NONCE_WEIGHT/2; i++) {
            uint8_t buf[3];
            RAND_bytes(buf, 3);
            int pos = ((buf[0] << 8) | buf[1]) % N;
            r_cyc.c[pos] = (buf[2] & 1) ? 1 : Q - 1;

            RAND_bytes(buf, 3);
            pos = ((buf[0] << 8) | buf[1]) % N;
            r_neg.c[pos] = (buf[2] & 1) ? 1 : Q - 1;
        }

        // Compute commitments - SAME y
        ring_t w_cyc_full, w_neg_full;
        mul_cyclic(&w_cyc_full, &r_cyc, &y);
        mul_negacyclic(&w_neg_full, &r_neg, &y);

        // Store rounded commitments in signature
        round_ring(&sig->w_cyc, &w_cyc_full);
        round_ring(&sig->w_neg, &w_neg_full);

        // For simplicity, just use r as s (attacker doesn't know secret)
        sig->s_cyc = r_cyc;
        sig->s_neg = r_neg;
#if SIG_LOSSY_ZERO
        uint8_t is_zeroed[N];
        derive_zero_positions(is_zeroed, SIG_LOSSY_ZERO_K, pk->seed, msg, msg_len);
        for (int i = 0; i < N; i++) {
            if (is_zeroed[i]) {
                sig->s_cyc.c[i] = 0;
                sig->s_neg.c[i] = 0;
                sig->w_cyc.c[i] = 0;
                sig->w_neg.c[i] = 0;
            }
        }
#endif

        // Check if bounds are satisfied (almost never!)
        if (verify_coupling(&sig->s_cyc, &sig->s_neg)) {
            return 1;  // Found forgery!
        }
    }
    return 0;
}

// ============================================================================
// Main (compile with -DCRT_LWR_LIB_ONLY=1 to exclude)
// ============================================================================

#ifndef CRT_LWR_LIB_ONLY
int main() {
    printf("╔══════════════════════════════════════════════════════════════════╗\n");
    printf("║  Two-Ring Module-LWR Signature (seedless-w)                      ║\n");
    printf("║  Master: %d coeffs, Q=%d, P=%d, TAU=%d                        ║\n", N2, Q, P, TAU);
    printf("╚══════════════════════════════════════════════════════════════════╝\n\n");

    printf("PARAMETERS:\n");
    printf("  Master dimension: %d\n", N2);
    printf("  Component dimension: %d\n", N);
    printf("  Q=%d, P=%d\n", Q, P);
    printf("  Secret bound (ETA): %d\n", ETA);
    printf("  Nonce weight: %d, Challenge weight: %d\n", NONCE_WEIGHT, CHALLENGE_WEIGHT);
    printf("  Max component coeff bound: %d\n", MAX_MASTER_COEFF);
#if SIG_LOSSY_ZERO
    printf("  Lossy zero positions: %d\n", SIG_LOSSY_ZERO_K);
#endif
    printf("  Minimal s bound: %d, max_err: %d, target sig: %d bytes\n\n", S_BOUND, TAU, MIN_SIG_TARGET);

    // Test projection round-trip
    printf("TEST: Split projection round-trip... ");
    master_t x_test;
    sample_small_master(&x_test);
    ring_t x_cyc, x_neg;
    project_cyclic(&x_test, &x_cyc);
    project_negacyclic(&x_test, &x_neg);
    master_t x_recovered;
    if (crt_lift(&x_cyc, &x_neg, &x_recovered)) {
        int match = 1;
        for (int i = 0; i < N2; i++) {
            if (x_test.c[i] != x_recovered.c[i]) { match = 0; break; }
        }
        printf("%s\n", match ? "OK" : "FAILED");
    } else {
        printf("LIFT FAILED\n");
    }

    // Test that random pairs fail bounds
    printf("TEST: Random pairs fail bounds... ");
    int coupling_failures = 0;
    for (int t = 0; t < 1000; t++) {
        ring_t rand_cyc, rand_neg;
        for (int i = 0; i < N; i++) {
            uint8_t buf[4];
            RAND_bytes(buf, 4);
            rand_cyc.c[i] = ((buf[0] << 8) | buf[1]) % Q;
            rand_neg.c[i] = ((buf[2] << 8) | buf[3]) % Q;
        }
        if (!verify_coupling(&rand_cyc, &rand_neg)) {
            coupling_failures++;
        }
    }
    printf("%d/1000 failed (expected ~1000)\n\n", coupling_failures);

    // Key generation
    public_key_t pk;
    secret_key_t sk;
    printf("KEYGEN:\n");
    keygen(&pk, &sk);
    printf("  Generated keys\n\n");

#if SIG_RANGE_TABLES_GEN
    {
        uint8_t msg[] = "Range table calibration";
        generate_range_tables(&sk, &pk, msg, sizeof(msg));
        return 0;
    }
#endif

#if DUMP_SECRETS
    printf("SECRETS (centered coeffs):\n");
    print_coeffs_centered("x_master", sk.x_master.c, N2);
    ring_t x_cyc_dbg, x_neg_dbg;
    project_cyclic(&sk.x_master, &x_cyc_dbg);
    project_negacyclic(&sk.x_master, &x_neg_dbg);
    print_coeffs_centered("x_cyc", x_cyc_dbg.c, N);
    print_coeffs_centered("x_neg", x_neg_dbg.c, N);
    printf("\n");
#endif

    // Sign
    uint8_t msg[] = "Test message for split-projection signature";
    signature_t sig;
    stats_t st;

    printf("SIGN:\n");
    if (!sign_with_stats(&sig, &sk, &pk, msg, sizeof(msg), &st)) {
        printf("  FAILED\n");
        return 1;
    }
    printf("  Master s norms: L-inf=%d, L2=%.1f\n", st.master_linf, st.master_l2);
    printf("  Cyclic s norms: L-inf=%d, L2=%.1f\n", st.cyc_linf, st.cyc_l2);
    printf("  Negacyclic s norms: L-inf=%d, L2=%.1f\n", st.neg_linf, st.neg_l2);
    printf("  Verification error: L-inf=%d, L2=%.1f\n", st.err_linf, st.err_l2);
#if SIG_LOSSY_ZERO
    master_t s_master_dbg;
    if (crt_lift(&sig.s_cyc, &sig.s_neg, &s_master_dbg)) {
        printf("  Lossy trace-zero: %s\n", verify_trace_zero(&s_master_dbg) ? "OK" : "FAILED");
    } else {
        printf("  Lossy trace-zero: lift failed\n");
    }
#endif
    printf("\n");

    // Test signature compression
    printf("COMPRESSION:\n");

    // Signature encoding for s and w
    huffman_sig_t hsig;
    if (huffman_encode_sig(&sig, &pk, msg, sizeof(msg), &hsig)) {
        int total_size = hsig.s_len + hsig.w_len;
        printf("  %s/%s sig: %d bytes (s) + %d bytes (w) = %d bytes total\n",
               SIG_S_CODEC, SIG_W_CODEC, hsig.s_len, hsig.w_len, total_size);

        // Test round-trip
        signature_t sig_dec;
        if (huffman_decode_sig(&hsig, &pk, msg, sizeof(msg), &sig_dec)) {
            int match = 1;
            int first_diff = -1;
            for (int i = 0; i < N; i++) {
                if (sig_dec.s_cyc.c[i] != sig.s_cyc.c[i] ||
                    sig_dec.s_neg.c[i] != sig.s_neg.c[i] ||
                    sig_dec.w_cyc.c[i] != sig.w_cyc.c[i]
#if !SIG_W_CYC_ONLY
                    || sig_dec.w_neg.c[i] != sig.w_neg.c[i]
#endif
                    ) {
                    if (first_diff < 0) first_diff = i;
                    match = 0;
                }
            }
            printf("  %s/%s round-trip: %s (first_diff=%d)\n", SIG_S_CODEC, SIG_W_CODEC, match ? "OK" : "FAILED", first_diff);
            if (!match && first_diff >= 0) {
                printf("    Diff at %d: s_cyc orig=%d dec=%d, s_neg orig=%d dec=%d\n",
                       first_diff,
                       (int)sig.s_cyc.c[first_diff], (int)sig_dec.s_cyc.c[first_diff],
                       (int)sig.s_neg.c[first_diff], (int)sig_dec.s_neg.c[first_diff]);
                printf("    w at %d: w_cyc orig=%d dec=%d, w_neg orig=%d dec=%d\n",
                       first_diff,
                       (int)sig.w_cyc.c[first_diff], (int)sig_dec.w_cyc.c[first_diff],
                       (int)sig.w_neg.c[first_diff], (int)sig_dec.w_neg.c[first_diff]);
#if SIG_DEHYDRATE_S
                // Print dehydration positions
                uint8_t pos_cyc[DEHYDRATE_COUNT], pos_neg[DEHYDRATE_COUNT];
                derive_dehydrate_positions_ring(pos_cyc, pk.seed, msg, sizeof(msg), "DCYC", 0, NULL);
                derive_dehydrate_positions_ring(pos_neg, pk.seed, msg, sizeof(msg), "DNEG", 0, NULL);
                printf("    DCYC positions[0..9]: ");
                for (int p = 0; p < 10; p++) printf("%d ", pos_cyc[p]);
                printf("\n    DNEG positions[0..9]: ");
                for (int p = 0; p < 10; p++) printf("%d ", pos_neg[p]);
                printf("\n");
#endif
                fflush(stdout);
            }
        } else {
            printf("  %s/%s decode: FAILED (rehydration likely failed)\n", SIG_S_CODEC, SIG_W_CODEC);
        }
    } else {
        printf("  Signature compression: FAILED\n");
    }
    fflush(stdout);

#if !SIG_W_CYC_ONLY
    compact_huffman_sig_t chsig;
    if (compact_huffman_compress(&chsig, &sig, &pk, msg, sizeof(msg))) {
        int total_size = chsig.s_len + chsig.hint_len + CHALLENGE_FULL_BYTES;
        printf("  Compact Huffman sig: %d bytes (s) + %d bytes (challenge) + %d bytes (hints) = %d bytes total\n",
               chsig.s_len, CHALLENGE_FULL_BYTES, chsig.hint_len, total_size);
        if (verify_compact_huffman(&chsig, &pk, msg, sizeof(msg))) {
            printf("  Compact Huffman verify: OK\n");
        } else {
            printf("  Compact Huffman verify: FAILED\n");
        }
    } else {
        printf("  Compact Huffman: FAILED\n");
    }
#endif

#if SIG_DEHYDRATE_W_REJECT
    // Test rejection-based w dehydration
    {
        // Compute w' = round(s*y - c*pk_unround)
        uint8_t challenge_seed_wr[SIGNATURE_CHALLENGE_BYTES];
        hash_to_challenge(challenge_seed_wr, &sig.w_cyc, &sig.w_neg, &pk, msg, sizeof(msg));
        master_t c_master;
        expand_sparse_challenge(&c_master, challenge_seed_wr, CHALLENGE_WEIGHT);
        ring_t c_cyc, c_neg;
        project_cyclic(&c_master, &c_cyc);
        project_negacyclic(&c_master, &c_neg);

        ring_t y;
        expand_ring(&y, pk.seed, 0);

        ring_t sy_cyc, sy_neg;
        mul_cyclic(&sy_cyc, &sig.s_cyc, &y);
        mul_negacyclic(&sy_neg, &sig.s_neg, &y);

        ring_t pk_unround_cyc, pk_unround_neg;
        unround_ring(&pk_unround_cyc, &pk.pk_cyc);
        unround_ring(&pk_unround_neg, &pk.pk_neg);

        ring_t cpk_cyc, cpk_neg;
        mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
        mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

        ring_t w_prime_cyc, w_prime_neg;
        sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
        sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

        ring_t w_round_prime_cyc, w_round_prime_neg;
        round_ring(&w_round_prime_cyc, &w_prime_cyc);
        round_ring(&w_round_prime_neg, &w_prime_neg);

        // Count positions where reconstruction is exact with non-zero w'
        int exact_cyc = 0, exact_neg = 0;
        for (int i = 0; i < N; i++) {
            if (mod_p(sig.w_cyc.c[i]) == mod_p(w_round_prime_cyc.c[i]) &&
                mod_p(w_round_prime_cyc.c[i]) != 0) {
                exact_cyc++;
            }
            if (mod_p(sig.w_neg.c[i]) == mod_p(w_round_prime_neg.c[i]) &&
                mod_p(w_round_prime_neg.c[i]) != 0) {
                exact_neg++;
            }
        }
        int wrong_cyc = 0, wrong_neg = 0;
        for (int i = 0; i < N; i++) {
            if (mod_p(sig.w_cyc.c[i]) != mod_p(w_round_prime_cyc.c[i])) wrong_cyc++;
            if (mod_p(sig.w_neg.c[i]) != mod_p(w_round_prime_neg.c[i])) wrong_neg++;
        }
        printf("  W recon: %d cyc + %d neg wrong (%.1f%%, %.1f%%)\n",
               wrong_cyc, wrong_neg, 100.0*wrong_cyc/N, 100.0*wrong_neg/N);
        printf("  W dehydrate (reject): %d cyc + %d neg positions reconstructable\n", exact_cyc, exact_neg);

        // Test round-trip using bitmask approach
        ring_t w_cyc_copy = sig.w_cyc;
        ring_t w_neg_copy = sig.w_neg;

        // Dehydrate using bitmask
        uint8_t mask_cyc = dehydrate_w_bitmask(&w_cyc_copy, &w_round_prime_cyc, pk.seed, msg, sizeof(msg), 0, "CYC");
        uint8_t mask_neg = dehydrate_w_bitmask(&w_neg_copy, &w_round_prime_neg, pk.seed, msg, sizeof(msg), 0, "NEG");

        // Count bits set in masks
        int dehydrated_cyc = __builtin_popcount(mask_cyc);
        int dehydrated_neg = __builtin_popcount(mask_neg);

        // Count zeros in compressed form
        int zeros_cyc = 0, zeros_neg = 0;
        for (int i = 0; i < N; i++) {
            if (w_cyc_copy.c[i] == 0) zeros_cyc++;
            if (w_neg_copy.c[i] == 0) zeros_neg++;
        }
        printf("  W dehydrated (bitmask): cyc mask=0x%02X (%d bits), neg mask=0x%02X (%d bits)\n",
               mask_cyc, dehydrated_cyc, mask_neg, dehydrated_neg);
        printf("  W zeros: %d cyc + %d neg (overhead: 2 bytes for masks)\n", zeros_cyc, zeros_neg);

        // Rehydrate using bitmask
        rehydrate_w_bitmask(&w_cyc_copy, &w_round_prime_cyc, pk.seed, msg, sizeof(msg), 0, "CYC", mask_cyc);
        rehydrate_w_bitmask(&w_neg_copy, &w_round_prime_neg, pk.seed, msg, sizeof(msg), 0, "NEG", mask_neg);

        // Check round-trip
        int match = 1;
        int first_fail = -1;
        for (int i = 0; i < N; i++) {
            if (mod_p(w_cyc_copy.c[i]) != mod_p(sig.w_cyc.c[i]) ||
                mod_p(w_neg_copy.c[i]) != mod_p(sig.w_neg.c[i])) {
                if (first_fail < 0) first_fail = i;
                match = 0;
            }
        }
        printf("  W dehydrate (bitmask) round-trip: %s\n", match ? "OK" : "FAILED");
        if (!match && first_fail >= 0) {
            printf("    First fail at %d: w_cyc orig=%d got=%d w'=%d, w_neg orig=%d got=%d w'=%d\n",
                   first_fail,
                   mod_p(sig.w_cyc.c[first_fail]), mod_p(w_cyc_copy.c[first_fail]),
                   mod_p(w_round_prime_cyc.c[first_fail]),
                   mod_p(sig.w_neg.c[first_fail]), mod_p(w_neg_copy.c[first_fail]),
                   mod_p(w_round_prime_neg.c[first_fail]));
        }

        // Test context-based dehydration (no extra data needed!)
        ring_t w_cyc_ctx = sig.w_cyc;
        ring_t w_neg_ctx = sig.w_neg;

        // Count positions in flat regions that match the flat value
        int flat_cyc = 0, flat_neg = 0;
        for (int i = 0; i < N; i++) {
            if (is_flat_region(&sig.w_cyc, i) && mod_p(sig.w_cyc.c[i]) == get_flat_value(&sig.w_cyc, i)) flat_cyc++;
            if (is_flat_region(&sig.w_neg, i) && mod_p(sig.w_neg.c[i]) == get_flat_value(&sig.w_neg, i)) flat_neg++;
        }
        printf("  W flat-region dehydratable: %d cyc + %d neg (%.1f%%, %.1f%%)\n",
               flat_cyc, flat_neg, 100.0*flat_cyc/N, 100.0*flat_neg/N);

        // Dehydrate using context
        int ctx_dehy_cyc = dehydrate_w_context(&w_cyc_ctx, pk.seed, msg, sizeof(msg), 0, "CYC");
        int ctx_dehy_neg = dehydrate_w_context(&w_neg_ctx, pk.seed, msg, sizeof(msg), 0, "NEG");

        // Count zeros after context dehydration
        int ctx_zeros_cyc = 0, ctx_zeros_neg = 0;
        for (int i = 0; i < N; i++) {
            if (w_cyc_ctx.c[i] == 0) ctx_zeros_cyc++;
            if (w_neg_ctx.c[i] == 0) ctx_zeros_neg++;
        }
        printf("  W dehydrated (context): %d cyc + %d neg (5 bits overhead for counts)\n", ctx_dehy_cyc, ctx_dehy_neg);

        // Rehydrate using context (pass count to avoid natural zero ambiguity)
        rehydrate_w_context(&w_cyc_ctx, pk.seed, msg, sizeof(msg), 0, "CYC", ctx_dehy_cyc);
        rehydrate_w_context(&w_neg_ctx, pk.seed, msg, sizeof(msg), 0, "NEG", ctx_dehy_neg);

        // Check round-trip
        int ctx_match = 1;
        int ctx_first_fail = -1;
        for (int i = 0; i < N; i++) {
            if (mod_p(w_cyc_ctx.c[i]) != mod_p(sig.w_cyc.c[i]) ||
                mod_p(w_neg_ctx.c[i]) != mod_p(sig.w_neg.c[i])) {
                if (ctx_first_fail < 0) ctx_first_fail = i;
                ctx_match = 0;
            }
        }
        printf("  W dehydrate (context) round-trip: %s\n", ctx_match ? "OK" : "FAILED");
        if (!ctx_match && ctx_first_fail >= 0) {
            int16_t pred_cyc = predict_from_context(&sig.w_cyc, ctx_first_fail);
            int16_t pred_neg = predict_from_context(&sig.w_neg, ctx_first_fail);
            printf("    First fail at %d: w_cyc orig=%d got=%d pred=%d, w_neg orig=%d got=%d pred=%d\n",
                   ctx_first_fail,
                   mod_p(sig.w_cyc.c[ctx_first_fail]), mod_p(w_cyc_ctx.c[ctx_first_fail]), pred_cyc,
                   mod_p(sig.w_neg.c[ctx_first_fail]), mod_p(w_neg_ctx.c[ctx_first_fail]), pred_neg);
        }
    }

    // Test 2-bit context hint dehydration
    {
        ring_t w_cyc_h2 = sig.w_cyc;
        ring_t w_neg_h2 = sig.w_neg;

        // First, count how many positions have a matching 2-bit rule
        int rules_match_cyc = 0, rules_match_neg = 0;
        for (int i = 0; i < N; i++) {
            if (mod_p(sig.w_cyc.c[i]) != 0 && find_hint2_rule(&sig.w_cyc, i) != HINT2_NO_MATCH) rules_match_cyc++;
            if (mod_p(sig.w_neg.c[i]) != 0 && find_hint2_rule(&sig.w_neg, i) != HINT2_NO_MATCH) rules_match_neg++;
        }
        printf("  W 2-bit rule match: %d cyc + %d neg (%.1f%%, %.1f%%) out of 256\n",
               rules_match_cyc, rules_match_neg, 100.0*rules_match_cyc/N, 100.0*rules_match_neg/N);

        // Dehydrate using 2-bit hints
        uint8_t hints_cyc[10], hints_neg[10];  // Max HINT2_POSITIONS/4 bytes each
        int hint_bytes_cyc, hint_bytes_neg;
        int dehy_cyc = dehydrate_w_hint2(&w_cyc_h2, pk.seed, msg, sizeof(msg), 0, "CYC", hints_cyc, &hint_bytes_cyc);
        int dehy_neg = dehydrate_w_hint2(&w_neg_h2, pk.seed, msg, sizeof(msg), 0, "NEG", hints_neg, &hint_bytes_neg);

        printf("  W dehydrated (2-bit hints): %d cyc + %d neg (%d + %d hint bytes = %d total overhead)\n",
               dehy_cyc, dehy_neg, hint_bytes_cyc, hint_bytes_neg, hint_bytes_cyc + hint_bytes_neg);

        // Rehydrate
        rehydrate_w_hint2(&w_cyc_h2, pk.seed, msg, sizeof(msg), 0, "CYC", hints_cyc);
        rehydrate_w_hint2(&w_neg_h2, pk.seed, msg, sizeof(msg), 0, "NEG", hints_neg);

        // Check round-trip
        int h2_match = 1;
        int h2_first_fail = -1;
        for (int i = 0; i < N; i++) {
            if (mod_p(w_cyc_h2.c[i]) != mod_p(sig.w_cyc.c[i]) ||
                mod_p(w_neg_h2.c[i]) != mod_p(sig.w_neg.c[i])) {
                if (h2_first_fail < 0) h2_first_fail = i;
                h2_match = 0;
            }
        }
        printf("  W dehydrate (2-bit hints) round-trip: %s\n", h2_match ? "OK" : "FAILED");
        if (!h2_match && h2_first_fail >= 0) {
            int rule_cyc = find_hint2_rule(&sig.w_cyc, h2_first_fail);
            int rule_neg = find_hint2_rule(&sig.w_neg, h2_first_fail);
            printf("    First fail at %d: w_cyc orig=%d got=%d rule=%d, w_neg orig=%d got=%d rule=%d\n",
                   h2_first_fail,
                   mod_p(sig.w_cyc.c[h2_first_fail]), mod_p(w_cyc_h2.c[h2_first_fail]), rule_cyc,
                   mod_p(sig.w_neg.c[h2_first_fail]), mod_p(w_neg_h2.c[h2_first_fail]), rule_neg);
        }

        // Calculate potential savings
        // Each dehydrated position saves 4 bits (w value), costs 0 bits (hint already allocated)
        int bits_saved = (dehy_cyc + dehy_neg) * 4;
        int bits_cost = (hint_bytes_cyc + hint_bytes_neg) * 8;
        printf("  W 2-bit hint savings: %d bits saved, %d bits cost, net = %d bits (%.1f bytes)\n",
               bits_saved, bits_cost, bits_saved - bits_cost, (bits_saved - bits_cost) / 8.0);
    }
#endif

    // Fixed-width compact encoding (for comparison)
    // Note: compact format uses challenge hash, not w directly
        uint8_t challenge_seed[SIGNATURE_CHALLENGE_BYTES];
    hash_to_challenge(challenge_seed, &sig.w_cyc, &sig.w_neg, &pk, msg, sizeof(msg));
    compact_sig_t csig;
    if (compact_compress_sig(&csig, &sig, challenge_seed)) {
        printf("  Fixed-width: %zu bytes (5-bit s_cyc + 4-bit s_neg + %d-byte challenge)\n", sizeof(csig), CHALLENGE_BYTES);
    } else {
        printf("  Fixed-width: FAILED (s overflow or LSB mismatch)\n");
    }

    // Test seedless signature (no w transmitted, verifier reconstructs)
    printf("\nSEEDLESS SIGNATURE (no w transmitted):\n");
    seedless_sig_t ssig;
    if (sign_seedless(&ssig, &sk, &pk, msg, sizeof(msg))) {
        int total_size = NONCE_SEED_BYTES + C_TILDE_BYTES + 1 + ssig.s_len;
        printf("  Sign: OK\n");
        printf("  Size: %d (nonce) + %d (c_tilde) + 1 (attempt) + %d (s) = %d bytes\n",
               NONCE_SEED_BYTES, C_TILDE_BYTES, ssig.s_len, total_size);
        printf("  Attempt used: %d\n", ssig.attempt);

        if (verify_seedless(&ssig, &pk, msg, sizeof(msg))) {
            printf("  Verify: OK\n");
        } else {
            printf("  Verify: FAILED\n");
        }

        // Test wrong message
        uint8_t wrong_seedless[] = "Wrong message seedless";
        if (!verify_seedless(&ssig, &pk, wrong_seedless, sizeof(wrong_seedless))) {
            printf("  Wrong message rejected: OK\n");
        } else {
            printf("  Wrong message rejected: FAILED\n");
        }
    } else {
        printf("  Sign: FAILED\n");
    }

    // Verify original signature
    printf("\nVERIFY:\n");
#if VERIFY_DEBUG_PRINT
    g_verify_debug = 1;
#endif
    if (verify(&sig, &pk, msg, sizeof(msg))) {
        printf("  Valid signature\n");
    } else {
        printf("  INVALID\n");
        return 1;
    }
#if VERIFY_DEBUG_PRINT
    g_verify_debug = 0;
#endif

    // Wrong message
    uint8_t wrong[] = "Wrong message";
    printf("\nWRONG MESSAGE:\n");
    if (!verify(&sig, &pk, wrong, sizeof(wrong))) {
        printf("  Correctly rejected\n");
    } else {
        printf("  ERROR: accepted wrong message\n");
        //return 1;
    }

    // Statistics over many signatures
    printf("\n══════════════════════════════════════════════════════════════════\n");
    printf("REAL SIGNER STATISTICS (50 signatures):\n");
    printf("══════════════════════════════════════════════════════════════════\n");

    int master_linf_max = 0, cyc_linf_max = 0, neg_linf_max = 0, err_linf_max = 0;
    double master_l2_sum = 0, cyc_l2_sum = 0, neg_l2_sum = 0, err_l2_sum = 0;
    int compact_ok = 0;
    int huffman_ok = 0;
    int huffman_size_sum = 0, huffman_size_min = 9999, huffman_size_max = 0;
    int seedless_ok = 0;
    int seedless_size_sum = 0, seedless_size_min = 9999, seedless_size_max = 0;
#if !SIG_W_CYC_ONLY
    int compact_huff_ok = 0;
    int compact_huff_size_sum = 0, compact_huff_size_min = 9999, compact_huff_size_max = 0;
#endif
    int hist_s_cyc[S_MAX_SYMBOLS] = {0};
    int hist_s_neg_high[S_MAX_SYMBOLS] = {0};
    int hist_delta[S_MAX_SYMBOLS] = {0};
    int hist_w_delta[S_MAX_SYMBOLS] = {0};
    int hist_w_err[S_MAX_SYMBOLS] = {0};
    int hist_w_cyc[PK_MAX_SYMBOLS] = {0};
    int hist_w_neg[PK_MAX_SYMBOLS] = {0};
#if P <= 16
    int hist_w_pair[P * P] = {0};
    int oob_w_pair = 0;
#endif
    int idx_nz_s_cyc[N] = {0};
    int idx_nz_s_neg[N] = {0};
    int idx_nz_w_cyc[N] = {0};
    int idx_nz_w_neg[N] = {0};
    int hist_x_cyc[S_MAX_SYMBOLS] = {0};
    int hist_x_neg[S_MAX_SYMBOLS] = {0};
    int oob_s_cyc = 0, oob_s_neg = 0, oob_delta = 0, oob_w_delta = 0, oob_w_err = 0, oob_w_cyc = 0, oob_w_neg = 0;
    int oob_x_cyc = 0, oob_x_neg = 0;

    // Project secret to component rings for histogram
    ring_t x_cyc_hist, x_neg_hist;
    project_cyclic(&sk.x_master, &x_cyc_hist);
    project_negacyclic(&sk.x_master, &x_neg_hist);
    for (int i = 0; i < N; i++) {
        int32_t x_cyc = centered(x_cyc_hist.c[i]);
        int32_t x_neg = centered(x_neg_hist.c[i]);
        hist_add(hist_x_cyc, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, x_cyc, &oob_x_cyc);
        hist_add(hist_x_neg, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, x_neg, &oob_x_neg);
    }

    for (int t = 0; t < 50; t++) {
        signature_t ts;
        stats_t tst;
        if (!sign_with_stats(&ts, &sk, &pk, msg, sizeof(msg), &tst)) continue;

        if (tst.master_linf > master_linf_max) master_linf_max = tst.master_linf;
        if (tst.cyc_linf > cyc_linf_max) cyc_linf_max = tst.cyc_linf;
        if (tst.neg_linf > neg_linf_max) neg_linf_max = tst.neg_linf;
        if (tst.err_linf > err_linf_max) err_linf_max = tst.err_linf;

        master_l2_sum += tst.master_l2;
        cyc_l2_sum += tst.cyc_l2;
        neg_l2_sum += tst.neg_l2;
        err_l2_sum += tst.err_l2;

        uint8_t cs[32];
        hash_to_challenge(cs, &ts.w_cyc, &ts.w_neg, &pk, msg, sizeof(msg));

        master_t c_master;
        expand_sparse_challenge(&c_master, cs, CHALLENGE_WEIGHT);

        ring_t c_cyc, c_neg;
        project_cyclic(&c_master, &c_cyc);
        project_negacyclic(&c_master, &c_neg);

        ring_t y;
        expand_ring(&y, pk.seed, 0);

        ring_t sy_cyc, sy_neg;
        mul_cyclic(&sy_cyc, &ts.s_cyc, &y);
        mul_negacyclic(&sy_neg, &ts.s_neg, &y);

        ring_t pk_unround_cyc, pk_unround_neg;
        unround_ring(&pk_unround_cyc, &pk.pk_cyc);
        unround_ring(&pk_unround_neg, &pk.pk_neg);

        ring_t cpk_cyc, cpk_neg;
        mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
        mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

        ring_t w_prime_cyc, w_prime_neg;
        sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
        sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

        ring_t w_round_prime_cyc, w_round_prime_neg;
        round_ring(&w_round_prime_cyc, &w_prime_cyc);
        round_ring(&w_round_prime_neg, &w_prime_neg);

        for (int i = 0; i < N; i++) {
            int32_t s_cyc = centered(ts.s_cyc.c[i]);
            int32_t s_neg_high = centered(ts.s_neg.c[i]) >> 1;
            int32_t diff = s_cyc - centered(ts.s_neg.c[i]);
            hist_add(hist_s_cyc, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, s_cyc, &oob_s_cyc);
            hist_add(hist_s_neg_high, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, s_neg_high, &oob_s_neg);
            if ((diff & 1) == 0) {
                int32_t delta = diff / 2;
                hist_add(hist_delta, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, delta, &oob_delta);
            } else {
                oob_delta++;
            }
            hist_add(hist_w_cyc, PK_MAX_SYMBOLS, 0, ts.w_cyc.c[i], &oob_w_cyc);
            hist_add(hist_w_neg, PK_MAX_SYMBOLS, 0, ts.w_neg.c[i], &oob_w_neg);
#if P <= 16
            if (ts.w_cyc.c[i] < P && ts.w_neg.c[i] < P) {
                int pair = ts.w_cyc.c[i] * P + ts.w_neg.c[i];
                if (pair >= 0 && pair < (P * P)) {
                    hist_w_pair[pair]++;
                } else {
                    oob_w_pair++;
                }
            } else {
                oob_w_pair++;
            }
#endif
            int32_t w_diff = centered_p(mod_p((int32_t)ts.w_neg.c[i] - (int32_t)ts.w_cyc.c[i]));
            hist_add(hist_w_delta, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, w_diff, &oob_w_delta);
            int32_t w_err = centered_p(mod_p((int32_t)ts.w_cyc.c[i] -
                                             (int32_t)w_round_prime_cyc.c[i]));
            hist_add(hist_w_err, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, w_err, &oob_w_err);
            w_err = centered_p(mod_p((int32_t)ts.w_neg.c[i] -
                                     (int32_t)w_round_prime_neg.c[i]));
            hist_add(hist_w_err, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, w_err, &oob_w_err);
            if (s_cyc != 0) idx_nz_s_cyc[i]++;
            if (centered(ts.s_neg.c[i]) != 0) idx_nz_s_neg[i]++;
            if (ts.w_cyc.c[i] != 0) idx_nz_w_cyc[i]++;
            if (ts.w_neg.c[i] != 0) idx_nz_w_neg[i]++;
        }

        // Test compressions
        // Fixed-width
        compact_sig_t tc;
        if (compact_compress_sig(&tc, &ts, cs)) compact_ok++;

        // Signature compression (s and w both compressed)
        huffman_sig_t th;
        if (huffman_encode_sig(&ts, &pk, msg, sizeof(msg), &th)) {
            huffman_ok++;
            int total = th.s_len + th.w_len;  // s + w (both compressed)
            huffman_size_sum += total;
            if (total < huffman_size_min) huffman_size_min = total;
            if (total > huffman_size_max) huffman_size_max = total;
        }

#if !SIG_W_CYC_ONLY
        // Compact Huffman (s compressed + challenge hash)
        compact_huffman_sig_t tch;
        if (compact_huffman_compress(&tch, &ts, &pk, msg, sizeof(msg))) {
            compact_huff_ok++;
            int total = tch.s_len + tch.hint_len + CHALLENGE_FULL_BYTES;
            compact_huff_size_sum += total;
            if (total < compact_huff_size_min) compact_huff_size_min = total;
            if (total > compact_huff_size_max) compact_huff_size_max = total;
        }
#endif

        // Seedless signature (nonce_seed + c_tilde + s, no w)
        seedless_sig_t tss;
        if (sign_seedless(&tss, &sk, &pk, msg, sizeof(msg))) {
            seedless_ok++;
            int total = NONCE_SEED_BYTES + C_TILDE_BYTES + 1 + tss.s_len;
            seedless_size_sum += total;
            if (total < seedless_size_min) seedless_size_min = total;
            if (total > seedless_size_max) seedless_size_max = total;
        }

    }

    printf("  Master s: max L-inf=%d, avg L2=%.1f\n", master_linf_max, master_l2_sum/50);
    printf("  Cyclic s: max L-inf=%d, avg L2=%.1f\n", cyc_linf_max, cyc_l2_sum/50);
    printf("  Negacyclic s: max L-inf=%d, avg L2=%.1f\n", neg_linf_max, neg_l2_sum/50);
    printf("  Error: max L-inf=%d, avg L2=%.1f [TAU=%d]\n", err_linf_max, err_l2_sum/50, TAU);
    printf("  Fixed-width compression (coupling-only): %d/50 success (%zu bytes each, s only)\n",
           compact_ok, sizeof(compact_sig_t));
    printf("  Signature compression (%s/%s): %d/50 success\n", SIG_S_CODEC, SIG_W_CODEC, huffman_ok);
    if (huffman_ok > 0) {
        printf("    Size: min=%d, avg=%d, max=%d bytes\n",
               huffman_size_min, huffman_size_sum / huffman_ok, huffman_size_max);
    }
#if !SIG_W_CYC_ONLY
    printf("  Compact Huffman compression: %d/50 success\n", compact_huff_ok);
    if (compact_huff_ok > 0) {
        printf("    Size: min=%d, avg=%d, max=%d bytes\n",
               compact_huff_size_min, compact_huff_size_sum / compact_huff_ok, compact_huff_size_max);
    }
#endif
    printf("  Seedless signature (no w): %d/50 success\n", seedless_ok);
    if (seedless_ok > 0) {
        printf("    Size: min=%d, avg=%d, max=%d bytes\n",
               seedless_size_min, seedless_size_sum / seedless_ok, seedless_size_max);
    }

    char w_label[32];
    char w_label_neg[32];
    snprintf(w_label, sizeof(w_label), "w_cyc (0..%d)", P - 1);
    snprintf(w_label_neg, sizeof(w_label_neg), "w_neg (0..%d)", P - 1);

    printf("\nDISTRIBUTION SUMMARY (50 signatures):\n");
    print_hist_summary("x_cyc (secret, centered)", hist_x_cyc, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, oob_x_cyc);
    print_hist_summary("x_neg (secret, centered)", hist_x_neg, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, oob_x_neg);
    print_hist_summary("s_cyc (centered)", hist_s_cyc, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, oob_s_cyc);
    print_hist_summary("s_neg_high (centered >> 1)", hist_s_neg_high, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, oob_s_neg);
    print_hist_summary("delta (centered)", hist_delta, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, oob_delta);
    print_hist_summary("w_neg - w_cyc (centered)", hist_w_delta, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, oob_w_delta);
    print_hist_summary("w_err (centered)", hist_w_err, S_MAX_SYMBOLS, S_SYMBOL_OFFSET, oob_w_err);
    print_hist_summary(w_label, hist_w_cyc, PK_MAX_SYMBOLS, 0, oob_w_cyc);
    print_hist_summary(w_label_neg, hist_w_neg, PK_MAX_SYMBOLS, 0, oob_w_neg);
#if P <= 16
    if (oob_w_pair) {
        printf("  w_pair oob: %d\n", oob_w_pair);
    }
#endif

#if DUMP_INDEX_COUNTS
    printf("\nINDEX NONZERO COUNTS (50 signatures):\n");
    print_index_counts("s_cyc nonzero per index", idx_nz_s_cyc, N);
    print_index_counts("s_neg nonzero per index", idx_nz_s_neg, N);
    print_index_counts("w_cyc nonzero per index", idx_nz_w_cyc, N);
    print_index_counts("w_neg nonzero per index", idx_nz_w_neg, N);
#endif

#if DUMP_HIST
    printf("\nHIST DUMP (C initializers):\n");
    print_hist_c_array("x_cyc_freq", hist_x_cyc, S_MAX_SYMBOLS);
    print_hist_c_array("x_neg_freq", hist_x_neg, S_MAX_SYMBOLS);
    print_hist_c_array("s_cyc_freq", hist_s_cyc, S_MAX_SYMBOLS);
    print_hist_c_array("s_neg_high_freq", hist_s_neg_high, S_MAX_SYMBOLS);
    print_hist_c_array("delta_freq", hist_delta, S_MAX_SYMBOLS);
    print_hist_c_array("w_delta_freq", hist_w_delta, S_MAX_SYMBOLS);
    print_hist_c_array("w_err_freq", hist_w_err, S_MAX_SYMBOLS);
    print_hist_c_array("w_cyc_freq", hist_w_cyc, PK_MAX_SYMBOLS);
    print_hist_c_array("w_neg_freq", hist_w_neg, PK_MAX_SYMBOLS);
#if P <= 16
    print_hist_c_array("w_pair_freq", hist_w_pair, P * P);
#endif
#endif

    // Wrong message error gap analysis
    printf("\n══════════════════════════════════════════════════════════════════\n");
    printf("WRONG MESSAGE ERROR GAP ANALYSIS:\n");
    printf("══════════════════════════════════════════════════════════════════\n");

    int wrong_err_min = Q, wrong_err_max = 0;
    ring_t y_test;
    expand_ring(&y_test, pk.seed, 0);  // SAME y for both rings

    for (int t = 0; t < 50; t++) {
        // Sign correct message
        signature_t ts;
        if (!sign(&ts, &sk, &pk, msg, sizeof(msg))) continue;

        // Now "verify" with wrong message - compute error
        uint8_t wrong_msg[32];
        RAND_bytes(wrong_msg, 32);

        uint8_t wrong_seed[32];
        hash_to_challenge(wrong_seed, &ts.w_cyc, &ts.w_neg, &pk, wrong_msg, 32);

        master_t c_wrong;
        expand_sparse_challenge(&c_wrong, wrong_seed, CHALLENGE_WEIGHT);

        ring_t c_cyc, c_neg;
        project_cyclic(&c_wrong, &c_cyc);
        project_negacyclic(&c_wrong, &c_neg);

        ring_t sy_cyc, sy_neg;
        mul_cyclic(&sy_cyc, &ts.s_cyc, &y_test);
        mul_negacyclic(&sy_neg, &ts.s_neg, &y_test);

        ring_t pk_unround_cyc, pk_unround_neg;
        unround_ring(&pk_unround_cyc, &pk.pk_cyc);
        unround_ring(&pk_unround_neg, &pk.pk_neg);

        ring_t cpk_cyc, cpk_neg;
        mul_cyclic(&cpk_cyc, &c_cyc, &pk_unround_cyc);
        mul_negacyclic(&cpk_neg, &c_neg, &pk_unround_neg);

        ring_t w_prime_cyc, w_prime_neg;
        sub_ring(&w_prime_cyc, &sy_cyc, &cpk_cyc);
        sub_ring(&w_prime_neg, &sy_neg, &cpk_neg);

        ring_t w_unround_cyc, w_unround_neg;
        unround_ring(&w_unround_cyc, &ts.w_cyc);
        unround_ring(&w_unround_neg, &ts.w_neg);

        int max_err = 0;
        for (int i = 0; i < N; i++) {
            int diff = abs(centered(mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
            if (diff > max_err) max_err = diff;
            diff = abs(centered(mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
            if (diff > max_err) max_err = diff;
        }

        if (max_err < wrong_err_min) wrong_err_min = max_err;
        if (max_err > wrong_err_max) wrong_err_max = max_err;
    }

    printf("  Real signature error: max L-inf = %d\n", err_linf_max);
    printf("  Wrong message error:  min L-inf = %d, max L-inf = %d\n", wrong_err_min, wrong_err_max);
    printf("  TAU = %d\n", TAU);
    printf("  Gap: %d - %d = %d (security margin)\n", wrong_err_min, err_linf_max, wrong_err_min - err_linf_max);

    // Random forgery attack
    printf("\n══════════════════════════════════════════════════════════════════\n");
    printf("RANDOM FORGERY ATTACK (10000 attempts):\n");
    printf("══════════════════════════════════════════════════════════════════\n");

    signature_t fake_sig;
    if (try_forge_uncoupled(&fake_sig, &pk, msg, sizeof(msg))) {
        printf("  WARNING: Found random signature that passes bounds check!\n");
        if (verify(&fake_sig, &pk, msg, sizeof(msg))) {
            printf("  CRITICAL: Forgery verified - scheme is broken!\n");
        }
    } else {
        printf("  No forgery found (bounds check blocks attack)\n");
    }

    // Test pk compression round-trip
    printf("\n══════════════════════════════════════════════════════════════════\n");
    printf("PK COMPRESSION TEST:\n");
    printf("══════════════════════════════════════════════════════════════════\n");

    // Fixed-width pk compression
    compressed_pk_t cpk;
    compress_pk(&cpk, &pk);
    printf("  Fixed-width pk: %zu bytes\n", sizeof(cpk));

    public_key_t pk_restored;
    decompress_pk(&pk_restored, &cpk);

    int pk_match = 1;
    for (int i = 0; i < N; i++) {
        if (pk.pk_cyc.c[i] != pk_restored.pk_cyc.c[i] ||
            pk.pk_neg.c[i] != pk_restored.pk_neg.c[i]) {
            pk_match = 0;
            break;
        }
    }
    printf("  Fixed-width round-trip: %s\n", pk_match ? "OK" : "FAILED");

    // Huffman pk compression
    huffman_pk_t hpk;
    int pk_huffman_size = 0;
    if (huffman_encode_pk(&pk, &hpk)) {
        pk_huffman_size = SEED_BYTES + hpk.pk_len;
        printf("  Huffman pk: %d bytes (%d seed + %d data)\n",
               pk_huffman_size, SEED_BYTES, hpk.pk_len);

        // Test round-trip
        public_key_t pk_huff_restored;
        if (huffman_decode_pk(&hpk, &pk_huff_restored)) {
            int hpk_match = 1;
            for (int i = 0; i < N; i++) {
                if (pk.pk_cyc.c[i] != pk_huff_restored.pk_cyc.c[i] ||
                    pk.pk_neg.c[i] != pk_huff_restored.pk_neg.c[i]) {
                    hpk_match = 0;
                    break;
                }
            }
            printf("  Huffman round-trip: %s\n", hpk_match ? "OK" : "FAILED");

            // Test sign/verify with Huffman-restored pk
            signature_t ver_sig;
            if (sign(&ver_sig, &sk, &pk_huff_restored, msg, sizeof(msg))) {
                if (verify(&ver_sig, &pk_huff_restored, msg, sizeof(msg))) {
                    printf("  Sign/verify with Huffman pk: OK\n");
                } else {
                    printf("  Sign/verify with Huffman pk: VERIFY FAILED\n");
                }
            } else {
                printf("  Sign/verify with Huffman pk: SIGN FAILED\n");
            }
        } else {
            printf("  Huffman decode: FAILED\n");
        }
    } else {
        printf("  Huffman pk encode: FAILED\n");
        pk_huffman_size = COMPRESSED_PK_SIZE;
    }

    // Size calculation
    int pk_fixed = COMPRESSED_PK_SIZE;
    int sig_fixed = COMPACT_SIG_SIZE;
    int sig_huffman_avg = (huffman_ok > 0) ? (huffman_size_sum / huffman_ok) : sig_fixed;
    int sig_seedless_avg = (seedless_ok > 0) ? (seedless_size_sum / seedless_ok) : sig_fixed;
#if !SIG_W_CYC_ONLY
    int sig_compact_huff_avg = (compact_huff_ok > 0) ? (compact_huff_size_sum / compact_huff_ok) : sig_fixed;
#endif

    printf("\n══════════════════════════════════════════════════════════════════\n");
    printf("SUCCESS!\n");
    printf("  pk (fixed):    %d bytes\n", pk_fixed);
    printf("  pk (Huffman):  %d bytes\n", pk_huffman_size);
    printf("  sig (seedless): ~%d bytes  *** BEST ***\n", sig_seedless_avg);
    printf("  sig (with w):  ~%d bytes\n", sig_huffman_avg);
    printf("  Security: %d-dim split-projection Ring-LWR\n", N2);
    printf("  Wrong msg gap: %d (TAU=%d, wrong_min=%d)\n", Q/2 - TAU, TAU, Q/2);
    printf("\n  Comparison (Huffman pk + seedless sig):\n");
    printf("    Seedless:    pk=%d, sig~%d, total~%d  *** RECOMMENDED ***\n",
           pk_huffman_size, sig_seedless_avg, pk_huffman_size + sig_seedless_avg);
    printf("    With w:      pk=%d, sig~%d, total~%d\n", pk_huffman_size, sig_huffman_avg, pk_huffman_size + sig_huffman_avg);
    printf("    Falcon-512:  pk=897, sig=666, total=1563\n");
    printf("    Dilithium2:  pk=1312, sig=2420, total=3732\n");
    printf("══════════════════════════════════════════════════════════════════\n");

    return 0;
}
#endif /* CRT_LWR_LIB_ONLY */

/*
 * =============================================================================
 * Public API Implementation (crt_lwr_sig.h)
 * =============================================================================
 */

int crt_lwr_keygen(crt_lwr_pk_t *pk_out, crt_lwr_sk_t *sk_out) {
    public_key_t internal_pk;
    secret_key_t internal_sk;

    /* Generate keypair (loops until pk fits) */
    keygen(&internal_pk, &internal_sk);

    /* Copy secret key */
    memcpy(sk_out->seed, internal_sk.seed, SEED_BYTES);
    memcpy(sk_out->x_master, internal_sk.x_master.c, N2 * sizeof(int16_t));

    /* Compress public key */
    huffman_pk_t hpk;
    if (!huffman_encode_pk(&internal_pk, &hpk)) {
        return 0;
    }

    /* Serialize: seed + huffman data */
    int total = SEED_BYTES + hpk.pk_len;
    if (total > CRT_LWR_PK_MAX) {
        return 0;  /* Should not happen due to keygen loop */
    }

    memcpy(pk_out->data, hpk.seed, SEED_BYTES);
    memcpy(pk_out->data + SEED_BYTES, hpk.pk_data, hpk.pk_len);
    pk_out->len = total;

    return 1;
}

int crt_lwr_sign(crt_lwr_sig_t *sig_out,
                 const crt_lwr_sk_t *sk,
                 const crt_lwr_pk_t *pk,
                 const uint8_t *msg, size_t msg_len) {

    /* Reconstruct internal secret key */
    secret_key_t internal_sk;
    memcpy(internal_sk.seed, sk->seed, SEED_BYTES);
    memcpy(internal_sk.x_master.c, sk->x_master, N2 * sizeof(int16_t));

    /* Reconstruct internal public key */
    huffman_pk_t hpk;
    memcpy(hpk.seed, pk->data, SEED_BYTES);
    memcpy(hpk.pk_data, pk->data + SEED_BYTES, pk->len - SEED_BYTES);
    hpk.pk_len = pk->len - SEED_BYTES;

    public_key_t internal_pk;
    if (!huffman_decode_pk(&hpk, &internal_pk)) {
        return 0;
    }

    /* Sign */
    seedless_sig_t internal_sig;
    if (!sign_seedless(&internal_sig, &internal_sk, &internal_pk, msg, msg_len)) {
        return 0;
    }

    /* Serialize: nonce_seed + c_tilde + attempt + s_data */
    int total = NONCE_SEED_BYTES + C_TILDE_BYTES + 1 + internal_sig.s_len;
    if (total > CRT_LWR_SIG_MAX) {
        return 0;
    }

    int offset = 0;
    memcpy(sig_out->data + offset, internal_sig.nonce_seed, NONCE_SEED_BYTES);
    offset += NONCE_SEED_BYTES;
    memcpy(sig_out->data + offset, internal_sig.c_tilde, C_TILDE_BYTES);
    offset += C_TILDE_BYTES;
    sig_out->data[offset] = internal_sig.attempt;
    offset += 1;
    memcpy(sig_out->data + offset, internal_sig.s_data, internal_sig.s_len);
    sig_out->len = total;

    return 1;
}

int crt_lwr_verify(const crt_lwr_sig_t *sig,
                   const crt_lwr_pk_t *pk,
                   const uint8_t *msg, size_t msg_len) {

    /* Reconstruct internal public key */
    huffman_pk_t hpk;
    memcpy(hpk.seed, pk->data, SEED_BYTES);
    memcpy(hpk.pk_data, pk->data + SEED_BYTES, pk->len - SEED_BYTES);
    hpk.pk_len = pk->len - SEED_BYTES;

    public_key_t internal_pk;
    if (!huffman_decode_pk(&hpk, &internal_pk)) {
        return 0;
    }

    /* Reconstruct internal signature */
    seedless_sig_t internal_sig;
    int offset = 0;
    memcpy(internal_sig.nonce_seed, sig->data + offset, NONCE_SEED_BYTES);
    offset += NONCE_SEED_BYTES;
    memcpy(internal_sig.c_tilde, sig->data + offset, C_TILDE_BYTES);
    offset += C_TILDE_BYTES;
    internal_sig.attempt = sig->data[offset];
    offset += 1;
    internal_sig.s_len = sig->len - offset;
    memcpy(internal_sig.s_data, sig->data + offset, internal_sig.s_len);

    /* Verify */
    return verify_seedless(&internal_sig, &internal_pk, msg, msg_len);
}
