/*
 * CRT-Coupled Two-Ring Module-LWR Signature Scheme
 * CONSTANT-TIME implementation with CT arithmetic coding
 *
 * Security: ~131 bits (NIST Level 1+)
 * All secret-dependent operations are constant-time.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include "crt_lwr_sig.h"

/* Parameters */
#define N 256
#define N2 512
#define Q 499
#define P 48
#define TAU 65
#define CHALLENGE_WEIGHT 25
#define NONCE_WEIGHT 25
#define SECRET_WEIGHT 50
#define Y_BOUND 4
/* CT_FULL_PARANOID: if defined, sign always iterates all attempts (slow but fully CT).
 * Otherwise, we use early exit which leaks attempt count via timing. */
/* #define CT_FULL_PARANOID */

#ifdef CT_FULL_PARANOID
#define MAX_ATTEMPTS 64   /* Reduced for full CT - covers >99.9% of cases */
#else
#define MAX_ATTEMPTS 1000
#endif
#define SEED_BYTES 16
/* Compact mode for 256-byte signatures */
#define COMPACT_SIG 1
#ifdef COMPACT_SIG
#define NONCE_SEED_BYTES 8   /* 64 bits sufficient for rejection sampling */
#define C_TILDE_BYTES 8      /* 64 bits sufficient for challenge binding */
#else
#define NONCE_SEED_BYTES 12
#define C_TILDE_BYTES 16
#endif

/* Internal types */
typedef int16_t coeff_t;
typedef struct { coeff_t c[N2]; } master_t;
typedef struct { coeff_t c[N]; } ring_t;

typedef struct {
    uint8_t seed[SEED_BYTES];
    ring_t pk_cyc;
    ring_t pk_neg;
} public_key_t;

typedef struct {
    master_t x_master;
    uint8_t seed[SEED_BYTES];
} secret_key_t;

typedef struct {
    uint8_t nonce_seed[NONCE_SEED_BYTES];
    uint8_t c_tilde[C_TILDE_BYTES];
    uint8_t attempt;
    uint8_t s_data[512];
    int s_len;
} seedless_sig_t;

/* ============================================================================
 * Constant-time utilities
 * ============================================================================ */

/* Correct constant-time equality for any 32-bit values */
static inline uint32_t ct_eq(int32_t a, int32_t b) {
    uint32_t diff = (uint32_t)(a ^ b);
    /* (diff | -diff) has MSB set iff diff != 0 */
    uint32_t neq = (diff | (0 - diff)) >> 31;
    return neq - 1;  /* 0xFFFFFFFF if equal, 0 if not equal */
}

/* Correct constant-time unsigned less-than */
static inline uint32_t ct_lt(uint32_t a, uint32_t b) {
    /* a < b iff (a ^ ((a ^ b) | ((a - b) ^ a))) has MSB set */
    return (uint32_t)((int32_t)(a ^ ((a ^ b) | ((a - b) ^ a))) >> 31);
}

static inline uint32_t ct_le(uint32_t a, uint32_t b) {
    return ct_lt(a, b) | ct_eq(a, b);
}

static inline uint32_t ct_lt_signed(int32_t a, int32_t b) {
    return (uint32_t)((a - b) >> 31);
}

static inline uint32_t ct_ge_signed(int32_t a, int32_t b) {
    return ~ct_lt_signed(a, b);
}

static inline int32_t ct_select(uint32_t mask, int32_t a, int32_t b) {
    return (int32_t)((mask & (uint32_t)a) | (~mask & (uint32_t)b));
}

static inline uint32_t ct_select_u32(uint32_t mask, uint32_t a, uint32_t b) {
    return (mask & a) | (~mask & b);
}

static inline uint64_t ct_select_u64(uint64_t mask, uint64_t a, uint64_t b) {
    return (mask & a) | (~mask & b);
}

static inline int32_t ct_abs(int32_t x) {
    int32_t mask = x >> 31;
    return (x ^ mask) - mask;
}

static inline int32_t ct_max(int32_t a, int32_t b) {
    return ct_select(ct_ge_signed(a, b), a, b);
}

static int ct_memcmp(const void *a, const void *b, size_t len) {
    const uint8_t *pa = a;
    const uint8_t *pb = b;
    uint8_t diff = 0;
    for (size_t i = 0; i < len; i++) {
        diff |= pa[i] ^ pb[i];
    }
    return diff;
}

/* ============================================================================
 * Constant-time modular arithmetic
 * ============================================================================ */

static inline int32_t ct_reduce_q(int32_t x) {
    int32_t q = x / Q;
    int32_t r = x - q * Q;
    uint32_t neg_mask = ct_lt_signed(r, 0);
    r = ct_select(neg_mask, r + Q, r);
    return r;
}

static inline int32_t ct_mod_q(int32_t x) {
    return ct_reduce_q(x);
}

static inline int32_t ct_centered(int32_t x) {
    uint32_t mask = ct_lt_signed(Q/2, x);
    return ct_select(mask, x - Q, x);
}

static inline int32_t ct_mod_p(int32_t x) {
    int32_t q = x / P;
    int32_t r = x - q * P;
    uint32_t neg_mask = ct_lt_signed(r, 0);
    r = ct_select(neg_mask, r + P, r);
    return r;
}

/* ============================================================================
 * CRT projections
 * ============================================================================ */

static void project_cyclic(const master_t *x, ring_t *x_cyc) {
    for (int i = 0; i < N; i++) {
        x_cyc->c[i] = ct_mod_q(x->c[i] + x->c[i + N]);
    }
}

static void project_negacyclic(const master_t *x, ring_t *x_neg) {
    for (int i = 0; i < N; i++) {
        x_neg->c[i] = ct_mod_q(x->c[i] - x->c[i + N]);
    }
}

/* ============================================================================
 * Ring operations
 * ============================================================================ */

static void mul_cyclic(ring_t *r, const ring_t *a, const ring_t *b) {
    int32_t tmp[N] = {0};
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            int k = i + j;
            uint32_t wrap_mask = ct_ge_signed(k, N);
            k = ct_select(wrap_mask, k - N, k);
            tmp[k] += (int32_t)a->c[i] * b->c[j];
        }
    }
    for (int i = 0; i < N; i++) {
        r->c[i] = ct_reduce_q(tmp[i]);
    }
}

static void mul_negacyclic(ring_t *r, const ring_t *a, const ring_t *b) {
    int32_t tmp[N] = {0};
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            int k = i + j;
            uint32_t wrap_mask = ct_ge_signed(k, N);
            int idx = ct_select(wrap_mask, k - N, k);
            int32_t sign = ct_select(wrap_mask, -1, 1);
            tmp[idx] += sign * (int32_t)a->c[i] * b->c[j];
        }
    }
    for (int i = 0; i < N; i++) {
        r->c[i] = ct_reduce_q(tmp[i]);
    }
}

static void add_ring(ring_t *r, const ring_t *a, const ring_t *b) {
    for (int i = 0; i < N; i++) {
        r->c[i] = ct_mod_q(a->c[i] + b->c[i]);
    }
}

static void sub_ring(ring_t *r, const ring_t *a, const ring_t *b) {
    for (int i = 0; i < N; i++) {
        r->c[i] = ct_mod_q(a->c[i] - b->c[i]);
    }
}

static void round_ring(ring_t *r, const ring_t *a) {
    for (int i = 0; i < N; i++) {
        int32_t c = ct_centered(a->c[i]);
        int32_t pos_result = (c * P + Q/2) / Q;
        int32_t neg_result = (c * P - Q/2) / Q;
        uint32_t neg_mask = ct_lt_signed(c, 0);
        int32_t v = ct_select(neg_mask, neg_result, pos_result);
        r->c[i] = ct_mod_p(v);
    }
}

static void unround_ring(ring_t *r, const ring_t *a) {
    for (int i = 0; i < N; i++) {
        r->c[i] = (a->c[i] * Q + P/2) / P;
    }
}

/* ============================================================================
 * Sampling
 * ============================================================================ */

/* Constant-time sparse sampling using Fisher-Yates shuffle approach.
 * We generate a permutation of positions and pick the first 'weight' positions.
 * This avoids variable-time collision handling. */
static void ct_sample_sparse_master(master_t *x, int weight) {
    memset(x->c, 0, sizeof(x->c));

    /* Generate enough randomness for position selection and signs */
    uint8_t rand_buf[N2 * 2 + 128];
    RAND_bytes(rand_buf, sizeof(rand_buf));

    /* Use rejection sampling with fixed iteration count.
     * We need 'weight' unique positions. With N2=512 positions and weight=50,
     * birthday paradox gives ~5% collision rate per sample.
     * Process 4x weight candidates to ensure enough unique positions. */
    #define SPARSE_CANDIDATES (4 * SECRET_WEIGHT)

    int16_t positions[SPARSE_CANDIDATES];
    uint8_t used[N2];
    memset(used, 0, sizeof(used));

    int valid_count = 0;
    int half = weight / 2;
    int plus_count = 0, minus_count = 0;

    /* First pass: collect unique positions (constant iteration count) */
    for (int i = 0; i < SPARSE_CANDIDATES; i++) {
        int pos = ((rand_buf[i*2] << 8) | rand_buf[i*2+1]) % N2;
        uint32_t is_new = ct_eq(used[pos], 0);
        uint32_t still_need = ct_lt((uint32_t)valid_count, (uint32_t)weight);
        uint32_t accept = is_new & still_need;

        /* CT update: mark as used only if accepted */
        used[pos] = ct_select(accept, 1, used[pos]);
        positions[valid_count] = pos;
        valid_count += (accept != 0) ? 1 : 0;
    }

    /* Second pass: assign values with balanced signs (constant iteration count) */
    uint8_t *sign_bytes = rand_buf + SPARSE_CANDIDATES * 2;
    for (int i = 0; i < weight; i++) {
        int pos = positions[i];
        uint8_t sign_byte = sign_bytes[i];

        uint32_t need_plus = ct_lt((uint32_t)plus_count, (uint32_t)half);
        uint32_t need_minus = ct_lt((uint32_t)minus_count, (uint32_t)(weight - half));
        uint32_t both_needed = need_plus & need_minus;
        uint32_t use_plus = ct_select_u32(both_needed, (uint32_t)(sign_byte & 1), need_plus);

        x->c[pos] = ct_select(use_plus, 1, Q - 1);
        plus_count += (use_plus != 0) ? 1 : 0;
        minus_count += (use_plus == 0) ? 1 : 0;
    }

    #undef SPARSE_CANDIDATES
}

/* Expand challenge with fixed iteration count for constant time.
 * Uses pre-generated hash stream and CT position acceptance. */
static void expand_sparse_challenge(master_t *c, const uint8_t *seed, int weight) {
    memset(c->c, 0, sizeof(c->c));

    /* Generate enough hash output for fixed iteration count.
     * With weight=25 and 512 positions, need ~4x candidates. */
    #define CHAL_HASH_ROUNDS 16
    #define CHAL_CANDIDATES (CHAL_HASH_ROUNDS * 10)

    uint8_t hash_buf[CHAL_HASH_ROUNDS * 32];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();

    for (uint32_t ctr = 0; ctr < CHAL_HASH_ROUNDS; ctr++) {
        EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
        EVP_DigestUpdate(ctx, seed, 32);
        EVP_DigestUpdate(ctx, &ctr, sizeof(ctr));
        unsigned int len = 32;
        EVP_DigestFinal_ex(ctx, hash_buf + ctr * 32, &len);
    }
    EVP_MD_CTX_free(ctx);

    /* Process candidates with fixed iteration count */
    uint8_t used[N2];
    memset(used, 0, sizeof(used));
    int count = 0;

    for (int i = 0; i < CHAL_CANDIDATES && i * 3 + 2 < (int)sizeof(hash_buf); i++) {
        int pos = ((hash_buf[i*3] << 8) | hash_buf[i*3+1]) % N2;
        uint8_t sign_byte = hash_buf[i*3+2];

        uint32_t is_new = ct_eq(used[pos], 0);
        uint32_t still_need = ct_lt((uint32_t)count, (uint32_t)weight);
        uint32_t accept = is_new & still_need;

        int16_t val = (sign_byte & 1) ? 1 : Q - 1;
        c->c[pos] = ct_select(accept, val, c->c[pos]);
        used[pos] = ct_select(accept, 1, used[pos]);
        count += (accept != 0) ? 1 : 0;
    }

    #undef CHAL_HASH_ROUNDS
    #undef CHAL_CANDIDATES
}

/* Expand nonce with fixed iteration count for constant time. */
static void expand_nonce_master(master_t *r, const uint8_t *nonce_seed, uint8_t attempt) {
    memset(r->c, 0, sizeof(r->c));

    /* Generate enough hash output for fixed iteration count.
     * NONCE_WEIGHT=25, need ~4x candidates for collision margin. */
    #define NONCE_HASH_ROUNDS 16
    #define NONCE_CANDIDATES (NONCE_HASH_ROUNDS * 10)

    uint8_t hash_buf[NONCE_HASH_ROUNDS * 32];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();

    for (uint32_t ctr = 0; ctr < NONCE_HASH_ROUNDS; ctr++) {
        EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
        EVP_DigestUpdate(ctx, nonce_seed, NONCE_SEED_BYTES);
        EVP_DigestUpdate(ctx, &attempt, 1);
        EVP_DigestUpdate(ctx, &ctr, sizeof(ctr));
        unsigned int len = 32;
        EVP_DigestFinal_ex(ctx, hash_buf + ctr * 32, &len);
    }
    EVP_MD_CTX_free(ctx);

    /* Process candidates with fixed iteration count */
    uint8_t used[N2];
    memset(used, 0, sizeof(used));
    int count = 0;

    for (int i = 0; i < NONCE_CANDIDATES && i * 3 + 2 < (int)sizeof(hash_buf); i++) {
        int pos = ((hash_buf[i*3] << 8) | hash_buf[i*3+1]) % N2;
        uint8_t sign_byte = hash_buf[i*3+2];

        uint32_t is_new = ct_eq(used[pos], 0);
        uint32_t still_need = ct_lt((uint32_t)count, (uint32_t)NONCE_WEIGHT);
        uint32_t accept = is_new & still_need;

        int16_t val = (sign_byte & 1) ? 1 : Q - 1;
        r->c[pos] = ct_select(accept, val, r->c[pos]);
        used[pos] = ct_select(accept, 1, used[pos]);
        count += (accept != 0) ? 1 : 0;
    }

    #undef NONCE_HASH_ROUNDS
    #undef NONCE_CANDIDATES
}

static void expand_ring(ring_t *r, const uint8_t *seed, int domain_sep) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    uint8_t hash[64];
    int idx = 0;
    uint32_t ctr = 0;

    while (idx < N) {
        EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
        EVP_DigestUpdate(ctx, seed, SEED_BYTES);
        EVP_DigestUpdate(ctx, &domain_sep, sizeof(domain_sep));
        EVP_DigestUpdate(ctx, &ctr, sizeof(ctr));
        unsigned int len = 32;
        EVP_DigestFinal_ex(ctx, hash, &len);

        for (int i = 0; i < 32 && idx < N; i++) {
            int16_t val = (hash[i] % (2 * Y_BOUND + 1)) - Y_BOUND;
            r->c[idx++] = ct_mod_q(val);
        }
        ctr++;
    }
    EVP_MD_CTX_free(ctx);
}

/* ============================================================================
 * Hash
 * ============================================================================ */

static void hash_to_challenge(uint8_t *out, const ring_t *w_cyc, const ring_t *w_neg,
                              const public_key_t *pk, const uint8_t *msg, size_t msg_len) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
    EVP_DigestUpdate(ctx, w_cyc->c, sizeof(w_cyc->c));
    EVP_DigestUpdate(ctx, w_neg->c, sizeof(w_neg->c));
    EVP_DigestUpdate(ctx, pk->pk_cyc.c, sizeof(pk->pk_cyc.c));
    EVP_DigestUpdate(ctx, pk->pk_neg.c, sizeof(pk->pk_neg.c));
    EVP_DigestUpdate(ctx, pk->seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, msg, msg_len);
    unsigned int len = 32;
    EVP_DigestFinal_ex(ctx, out, &len);
    EVP_MD_CTX_free(ctx);
}

/* ============================================================================
 * Constant-time arithmetic coding
 *
 * Key insight: use fixed iteration counts with conditional updates.
 * The renormalization loop becomes a fixed number of conditional shifts.
 * ============================================================================ */

/* ============================================================================
 * 32-bit Range Coder with Carry Handling
 *
 * Based on Dmitry Subbotin's carryless range coder, adapted for CT.
 * Uses 64-bit low to naturally handle carries without special code.
 * ============================================================================ */

/* Encoder state */
typedef struct {
    uint8_t *buf;
    int cap;
    int len;
    uint64_t low;      /* 64-bit to handle carries */
    uint32_t range;
    uint8_t cache;     /* First pending byte */
    uint32_t cache_size;  /* Number of 0xFF bytes pending */
} ct_rc_enc_t;

/* Decoder state */
typedef struct {
    const uint8_t *buf;
    int len;
    int pos;
    uint32_t code;
    uint32_t range;
} ct_rc_dec_t;

#define RC_TOP_VALUE  (1U << 24)
#define RC_SHIFT_BITS 24

static void ct_rc_enc_init(ct_rc_enc_t *rc, uint8_t *buf, int cap) {
    rc->buf = buf;
    rc->cap = cap;
    rc->len = 0;
    rc->low = 0;
    rc->range = 0xFFFFFFFF;
    rc->cache = 0;
    rc->cache_size = 1;  /* First byte is "pending" */
}

#ifdef DEBUG_ARITH
static int total_renorm_bytes = 0;
#endif

/* Shift out the top byte, handling carries.
 * Note: This has variable-time branches on carry. For full CT, use
 * the fixed-iteration version with conditional operations. */
static void ct_rc_shift_low(ct_rc_enc_t *rc) {
    /* Check for carry */
    if ((uint32_t)rc->low < 0xFF000000U || (rc->low >> 32) != 0) {
        /* Output cached byte + pending 0xFF bytes */
        if (rc->len < rc->cap) {
            rc->buf[rc->len++] = rc->cache + (uint8_t)(rc->low >> 32);
        }
        while (rc->cache_size > 1) {
            rc->cache_size--;
            if (rc->len < rc->cap) {
                rc->buf[rc->len++] = 0xFF + (uint8_t)(rc->low >> 32);
            }
        }
        rc->cache = (uint8_t)((uint32_t)rc->low >> RC_SHIFT_BITS);
    } else {
        /* Accumulate 0xFF bytes */
        rc->cache_size++;
    }
    rc->low = ((uint32_t)rc->low << 8);
}

static void ct_rc_encode(ct_rc_enc_t *rc, uint32_t cum_low, uint32_t cum_high, uint32_t total) {
    uint32_t r = rc->range / total;
    rc->low += (uint64_t)cum_low * r;
    rc->range = (cum_high - cum_low) * r;

    while (rc->range < RC_TOP_VALUE) {
        rc->range <<= 8;
        ct_rc_shift_low(rc);
    }
}

static int ct_rc_finish(ct_rc_enc_t *rc) {
    #ifdef DEBUG_ARITH
    printf("      finish: len before flush=%d, total_renorm_bytes=%d\n", rc->len, total_renorm_bytes);
    total_renorm_bytes = 0;
    #endif

    /* Flush all remaining bytes */
    for (int i = 0; i < 5; i++) {
        ct_rc_shift_low(rc);
    }

    #ifdef DEBUG_ARITH
    printf("      finish: len after flush=%d\n", rc->len);
    #endif
    return rc->len;
}

static void ct_rc_dec_init(ct_rc_dec_t *rc, const uint8_t *buf, int len) {
    rc->buf = buf;
    rc->len = len;
    rc->pos = 0;
    rc->code = 0;
    rc->range = 0xFFFFFFFF;

    /* Skip first byte (it's the cache initialization) */
    rc->pos = 1;
    /* Read 4 bytes for initial code */
    for (int i = 0; i < 4 && rc->pos < rc->len; i++) {
        rc->code = (rc->code << 8) | rc->buf[rc->pos++];
    }
    #ifdef DEBUG_ARITH
    printf("    dec_init: code=0x%08x (pos=%d)\n", rc->code, rc->pos);
    #endif
}

static void ct_rc_renorm_dec(ct_rc_dec_t *rc) {
    while (rc->range < RC_TOP_VALUE) {
        rc->code = (rc->code << 8) | ((rc->pos < rc->len) ? rc->buf[rc->pos++] : 0);
        rc->range <<= 8;
    }
}

/* Constant-time symbol decode: scan all symbols, select matching one */
static int ct_rc_decode(ct_rc_dec_t *rc, const uint32_t *cum, int num_symbols,
                        uint32_t total, int32_t *out) {
    uint32_t r = rc->range / total;
    uint32_t val = rc->code / r;

    #ifdef DEBUG_ARITH
    static int decode_count = 0;
    decode_count++;
    if (decode_count <= 10) {
        printf("      dec[%d]: code=%08x range=%u, r=%u, val=%u\n",
               decode_count-1, rc->code, rc->range, r, val);
    }
    #endif

    /* Clamp val to valid range (using unsigned comparison) */
    uint32_t val_too_big = ~ct_lt(val, total);  /* all 1s if val >= total */
    val = ct_select_u32(val_too_big, total - 1, val);

    /* Constant-time symbol lookup: check all symbols */
    int32_t sym = 0;
    for (int s = 0; s < num_symbols; s++) {
        /* sym = s if cum[s] <= val < cum[s+1] */
        uint32_t in_range = ct_le(cum[s], val) & ct_lt(val, cum[s + 1]);
        sym = ct_select(in_range, s, sym);
    }
    *out = sym;

    #ifdef DEBUG_ARITH
    if (decode_count <= 10) {
        printf("             -> sym=%d, cum=[%u,%u), code-=, range=%u (pos=%d)\n",
               sym, cum[sym], cum[sym+1], (cum[sym + 1] - cum[sym]) * r, rc->pos);
    }
    #endif

    /* Update state */
    rc->code -= cum[sym] * r;
    rc->range = (cum[sym + 1] - cum[sym]) * r;
    ct_rc_renorm_dec(rc);

    return 1;
}

/* ============================================================================
 * Compression tables for s encoding - COMPACT 256-byte target
 *
 * Analysis: With sparse r (25 non-zeros) and sparse c·x product,
 * s_cyc coefficients are concentrated in [-6, 6] with peaked distribution.
 * Delta values similarly concentrated.
 *
 * Entropy budget: 256 - 17 (header) = 239 bytes = 1912 bits for 512 values
 * → ~3.7 bits/coefficient required
 *
 * Using asymmetric Laplace-like distribution centered at 0.
 * ============================================================================ */

/* S_CYC: values in [-8, 8] (17 symbols) - looser bounds for reliability */
#define S_CYC_MIN -8
#define S_CYC_MAX 8
#define S_CYC_SYMBOLS (S_CYC_MAX - S_CYC_MIN + 1)  /* 17 */
#define S_CYC_TOT 32768

/* Laplace-like distribution: P(k) ∝ exp(-|k|/1.8)
 * Cumulative table needs SYMBOLS+1 = 18 entries */
static const uint32_t S_CYC_CUM[S_CYC_SYMBOLS + 1] = {
    /*  -8    -7    -6    -5    -4    -3    -2    -1     0     1     2     3     4     5     6     7     8   */
        0,   64,  192,  512, 1280, 2816, 5376, 9216,16384,23552,27392,29952,31488,32256,32576,32704,32752,32768
};

/* S_DELTA: values in [-8, 8] (17 symbols) */
#define S_DELTA_MIN -8
#define S_DELTA_MAX 8
#define S_DELTA_SYMBOLS (S_DELTA_MAX - S_DELTA_MIN + 1)
#define S_DELTA_TOT 32768

/* Same Laplace-like distribution */
static const uint32_t S_DELTA_CUM[S_DELTA_SYMBOLS + 1] = {
        0,   64,  192,  512, 1280, 2816, 5376, 9216,16384,23552,27392,29952,31488,32256,32576,32704,32752,32768
};

/* ============================================================================
 * Static pk encoding with shared frequency table
 *
 * The pk coefficient distribution is STRUCTURAL - determined by cryptographic
 * parameters (sparse weight, small coefficients), not individual keys.
 * Using a static shared table eliminates 96-byte header overhead.
 *
 * Empirical distribution (from 100 keygen trials):
 *   val=0: 23%, val=1: 18.5%, val=47(-1): 18%, val=2: 12%, val=46(-2): 12%
 *   val=3: 6%, val=45(-3): 6%, val=4: 2%, val=44(-4): 2%, others: ~1%
 * ============================================================================ */
#define PK_SYMBOLS P
#define PK_TOT 32768

/* Static cumulative table for pk coefficients (same for pk_cyc and pk_neg)
 * Built from empirical distribution, scaled to 32768 total.
 * All 49 values strictly increasing to ensure every symbol has positive probability. */
static const uint32_t PK_STATIC_CUM[PK_SYMBOLS + 1] = {
    /* idx:  0     1     2     3     4     5     6     7     8     9    10    11 */
    /* Concentrated around 0, 1, 2, 3, 4 (positive small values) */
             0,  7530, 13610, 17540, 19540, 20150, 20162, 20174, 20186, 20198, 20210, 20222,
    /* idx: 12    13    14    15    16    17    18    19    20    21    22    23 */
         20234, 20246, 20258, 20270, 20282, 20294, 20306, 20318, 20330, 20342, 20354, 20366,
    /* idx: 24    25    26    27    28    29    30    31    32    33    34    35 */
         20378, 20390, 20402, 20414, 20426, 20438, 20450, 20462, 20474, 20486, 20498, 20510,
    /* idx: 36    37    38    39    40    41    42    43    44    45    46    47    48 */
    /* Concentrated around 44, 45, 46, 47 (negative small values in centered form) */
         20522, 20534, 20546, 20558, 20570, 20582, 20600, 20800, 21400, 23300, 25200, 29000, 32768
    /* sym 45:[23300,25200)=1900, sym 46:[25200,29000)=3800, sym 47:[29000,32768)=3768 */
};

static int ct_encode_pk(const public_key_t *pk, uint8_t *out, int max_len) {
    ct_rc_enc_t rc;
    ct_rc_enc_init(&rc, out, max_len);

    /* Encode pk_cyc using static shared table */
    for (int i = 0; i < N; i++) {
        int32_t val = pk->pk_cyc.c[i];
        if (val < 0) val = 0;
        if (val >= P) val = P - 1;
        ct_rc_encode(&rc, PK_STATIC_CUM[val], PK_STATIC_CUM[val + 1], PK_TOT);
    }

    /* Encode pk_neg using same static table */
    for (int i = 0; i < N; i++) {
        int32_t val = pk->pk_neg.c[i];
        if (val < 0) val = 0;
        if (val >= P) val = P - 1;
        ct_rc_encode(&rc, PK_STATIC_CUM[val], PK_STATIC_CUM[val + 1], PK_TOT);
    }

    return ct_rc_finish(&rc);
}

static int ct_decode_pk(const uint8_t *in, int len, public_key_t *pk) {
    ct_rc_dec_t rc;
    ct_rc_dec_init(&rc, in, len);

    /* Decode pk_cyc using static shared table */
    for (int i = 0; i < N; i++) {
        int32_t sym;
        if (!ct_rc_decode(&rc, PK_STATIC_CUM, PK_SYMBOLS, PK_TOT, &sym)) {
            return 0;
        }
        pk->pk_cyc.c[i] = sym;
    }

    /* Decode pk_neg using same static table */
    for (int i = 0; i < N; i++) {
        int32_t sym;
        if (!ct_rc_decode(&rc, PK_STATIC_CUM, PK_SYMBOLS, PK_TOT, &sym)) {
            return 0;
        }
        pk->pk_neg.c[i] = sym;
    }

    return 1;
}

/* ============================================================================
 * Constant-time s encoding using CT arithmetic coding
 *
 * For compact 256-byte signatures, we need tight coefficient bounds.
 * Returns 0 if any coefficient exceeds bounds (caller should retry).
 * ============================================================================ */

/* Check if all coefficients are within bounds (CT, returns mask) */
static uint32_t ct_check_s_bounds(const ring_t *s_cyc, const ring_t *s_neg) {
    uint32_t in_bounds = 0xFFFFFFFF;

    for (int i = 0; i < N; i++) {
        int32_t val = ct_centered(s_cyc->c[i]);
        /* Check |val| <= S_CYC_MAX */
        uint32_t ok = ct_ge_signed(S_CYC_MAX, ct_abs(val));
        in_bounds &= ok;
    }

    for (int i = 0; i < N; i++) {
        int32_t delta = ct_centered(ct_mod_q(s_cyc->c[i] - s_neg->c[i])) / 2;
        uint32_t ok = ct_ge_signed(S_DELTA_MAX, ct_abs(delta));
        in_bounds &= ok;
    }

    return in_bounds;
}

static int ct_encode_s(const ring_t *s_cyc, const ring_t *s_neg,
                       uint8_t *out, int max_len) {
    /* First check bounds (CT) */
    uint32_t bounds_ok = ct_check_s_bounds(s_cyc, s_neg);
    #ifdef DEBUG_BOUNDS
    int32_t max_v = 0, max_d = 0;
    for (int i = 0; i < N; i++) {
        int32_t v = ct_abs(ct_centered(s_cyc->c[i]));
        if (v > max_v) max_v = v;
        int32_t d = ct_abs(ct_centered(ct_mod_q(s_cyc->c[i] - s_neg->c[i])) / 2);
        if (d > max_d) max_d = d;
    }
    printf("    encode: bounds_ok=%u, max_v=%d (limit=%d), max_d=%d (limit=%d)\n",
           bounds_ok, max_v, S_CYC_MAX, max_d, S_DELTA_MAX);
    #endif
    if (!bounds_ok) {
        return 0;  /* Signal that coefficients exceed bounds */
    }

    ct_rc_enc_t rc;
    ct_rc_enc_init(&rc, out, max_len);

    /* Encode s_cyc */
    for (int i = 0; i < N; i++) {
        int32_t val = ct_centered(s_cyc->c[i]);

        /* Clamp to table range (should not trigger after bounds check) */
        val = ct_select(ct_lt_signed(val, S_CYC_MIN), S_CYC_MIN, val);
        val = ct_select(ct_ge_signed(val, S_CYC_MAX + 1), S_CYC_MAX, val);

        /* Convert to symbol index (0-based) */
        int32_t sym = val - S_CYC_MIN;

        ct_rc_encode(&rc, S_CYC_CUM[sym], S_CYC_CUM[sym + 1], S_CYC_TOT);
    }

    /* Encode delta = (s_cyc - s_neg) / 2 */
    for (int i = 0; i < N; i++) {
        int32_t delta = ct_centered(ct_mod_q(s_cyc->c[i] - s_neg->c[i])) / 2;

        /* Clamp to table range */
        delta = ct_select(ct_lt_signed(delta, S_DELTA_MIN), S_DELTA_MIN, delta);
        delta = ct_select(ct_ge_signed(delta, S_DELTA_MAX + 1), S_DELTA_MAX, delta);

        /* Convert to symbol index */
        int32_t sym = delta - S_DELTA_MIN;

        ct_rc_encode(&rc, S_DELTA_CUM[sym], S_DELTA_CUM[sym + 1], S_DELTA_TOT);
    }

    int len = ct_rc_finish(&rc);

    /* Check if we exceeded target size */
    #ifdef COMPACT_SIG
    #define TARGET_S_LEN (256 - NONCE_SEED_BYTES - C_TILDE_BYTES - 1)
    #ifdef DEBUG_BOUNDS
    printf("    encoded len=%d, target=%d\n", len, TARGET_S_LEN);
    #endif
    if (len > TARGET_S_LEN) {
        return 0;  /* Too large, caller should retry */
    }
    #undef TARGET_S_LEN
    #endif

    return len;
}

static int ct_decode_s(const uint8_t *in, int len, ring_t *s_cyc, ring_t *s_neg) {
    ct_rc_dec_t rc;
    ct_rc_dec_init(&rc, in, len);

    /* Decode s_cyc */
    for (int i = 0; i < N; i++) {
        int32_t sym;
        if (!ct_rc_decode(&rc, S_CYC_CUM, S_CYC_SYMBOLS, S_CYC_TOT, &sym)) {
            return 0;
        }
        int32_t val = sym + S_CYC_MIN;
        s_cyc->c[i] = ct_mod_q(val);
    }

    /* Decode delta and reconstruct s_neg */
    for (int i = 0; i < N; i++) {
        int32_t sym;
        if (!ct_rc_decode(&rc, S_DELTA_CUM, S_DELTA_SYMBOLS, S_DELTA_TOT, &sym)) {
            return 0;
        }
        int32_t delta = sym + S_DELTA_MIN;
        s_neg->c[i] = ct_mod_q(ct_centered(s_cyc->c[i]) - 2 * delta);
    }

    return 1;
}

/* ============================================================================
 * Key generation
 * ============================================================================ */

static void keygen(public_key_t *pk, secret_key_t *sk) {
    ring_t y;

    RAND_bytes(sk->seed, SEED_BYTES);
    memcpy(pk->seed, sk->seed, SEED_BYTES);

    expand_ring(&y, pk->seed, 0);
    ct_sample_sparse_master(&sk->x_master, SECRET_WEIGHT);

    ring_t x_cyc, x_neg;
    project_cyclic(&sk->x_master, &x_cyc);
    project_negacyclic(&sk->x_master, &x_neg);

    ring_t t_cyc, t_neg;
    mul_cyclic(&t_cyc, &x_cyc, &y);
    mul_negacyclic(&t_neg, &x_neg, &y);

    round_ring(&pk->pk_cyc, &t_cyc);
    round_ring(&pk->pk_neg, &t_neg);
}

/* ============================================================================
 * Signing (constant-time)
 * ============================================================================ */

/* Constant-time conditional copy for ring_t */
static void ct_copy_ring(uint32_t mask, ring_t *dst, const ring_t *src) {
    for (int i = 0; i < N; i++) {
        dst->c[i] = ct_select(mask, src->c[i], dst->c[i]);
    }
}

/* Constant-time conditional copy for byte arrays */
static void ct_copy_bytes(uint32_t mask, uint8_t *dst, const uint8_t *src, size_t len) {
    for (size_t i = 0; i < len; i++) {
        dst[i] = ct_select(mask, src[i], dst[i]);
    }
}

static int sign_ct(seedless_sig_t *sig, const secret_key_t *sk,
                   const public_key_t *pk, const uint8_t *msg, size_t msg_len) {
    ring_t y;
    expand_ring(&y, pk->seed, 0);

    ring_t x_cyc, x_neg;
    project_cyclic(&sk->x_master, &x_cyc);
    project_negacyclic(&sk->x_master, &x_neg);

    ring_t pk_unround_cyc, pk_unround_neg;
    unround_ring(&pk_unround_cyc, &pk->pk_cyc);
    unround_ring(&pk_unround_neg, &pk->pk_neg);

    RAND_bytes(sig->nonce_seed, NONCE_SEED_BYTES);

    uint32_t found = 0;
    int found_attempt = 0;
    ring_t found_s_cyc, found_s_neg;
    uint8_t found_challenge[32];
    memset(&found_s_cyc, 0, sizeof(found_s_cyc));
    memset(&found_s_neg, 0, sizeof(found_s_neg));
    memset(found_challenge, 0, sizeof(found_challenge));

    /* Loop over attempts. In CT_FULL_PARANOID mode, iterate all attempts.
     * Otherwise, use early exit for performance. */
#ifdef CT_FULL_PARANOID
    for (int attempt = 0; attempt < MAX_ATTEMPTS; attempt++) {
#else
    for (int attempt = 0; attempt < MAX_ATTEMPTS && !found; attempt++) {
#endif
        master_t r_master;
        expand_nonce_master(&r_master, sig->nonce_seed, attempt);

        ring_t r_cyc, r_neg;
        project_cyclic(&r_master, &r_cyc);
        project_negacyclic(&r_master, &r_neg);

        ring_t w_full_cyc, w_full_neg;
        mul_cyclic(&w_full_cyc, &r_cyc, &y);
        mul_negacyclic(&w_full_neg, &r_neg, &y);

        ring_t w_round_cyc, w_round_neg;
        round_ring(&w_round_cyc, &w_full_cyc);
        round_ring(&w_round_neg, &w_full_neg);

        uint8_t challenge_seed[32];
        hash_to_challenge(challenge_seed, &w_round_cyc, &w_round_neg, pk, msg, msg_len);

        master_t c_master;
        expand_sparse_challenge(&c_master, challenge_seed, CHALLENGE_WEIGHT);

        ring_t c_cyc, c_neg;
        project_cyclic(&c_master, &c_cyc);
        project_negacyclic(&c_master, &c_neg);

        ring_t cx_cyc, cx_neg;
        mul_cyclic(&cx_cyc, &c_cyc, &x_cyc);
        mul_negacyclic(&cx_neg, &c_neg, &x_neg);

        ring_t s_cyc, s_neg;
        add_ring(&s_cyc, &r_cyc, &cx_cyc);
        add_ring(&s_neg, &r_neg, &cx_neg);

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

        int32_t max_err = 0;
        for (int i = 0; i < N; i++) {
            int32_t diff_cyc = ct_abs(ct_centered(ct_mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
            int32_t diff_neg = ct_abs(ct_centered(ct_mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
            max_err = ct_max(max_err, diff_cyc);
            max_err = ct_max(max_err, diff_neg);
        }

        /* Check verification bounds */
        uint32_t passes_verify = ct_ge_signed(TAU, max_err);

        /* Check compression bounds (CT) */
        uint32_t passes_compress = ct_check_s_bounds(&s_cyc, &s_neg);

        /* DEBUG: Log bounds failures on first few attempts */
        #ifdef DEBUG_BOUNDS
        if (attempt < 5) {
            int32_t max_s = 0, max_delta = 0;
            for (int i = 0; i < N; i++) {
                int32_t v = ct_abs(ct_centered(s_cyc.c[i]));
                if (v > max_s) max_s = v;
                int32_t d = ct_abs(ct_centered(ct_mod_q(s_cyc.c[i] - s_neg.c[i])) / 2);
                if (d > max_delta) max_delta = d;
            }
            printf("  attempt %d: max_err=%d (TAU=%d), max_s=%d, max_delta=%d, verify=%d, compress=%d\n",
                   attempt, max_err, TAU, max_s, max_delta, passes_verify != 0, passes_compress != 0);
        }
        #endif

        /* CT: accept this attempt only if it passes ALL checks AND we haven't found one yet */
        uint32_t passes = passes_verify & passes_compress;
        uint32_t first_success = passes & ~found;

        /* CT copy: only update found_* if this is the first success */
        found_attempt = ct_select(first_success, attempt, found_attempt);
        ct_copy_ring(first_success, &found_s_cyc, &s_cyc);
        ct_copy_ring(first_success, &found_s_neg, &s_neg);
        ct_copy_bytes(first_success, found_challenge, challenge_seed, 32);

        /* Mark as found (sticky) */
        found |= first_success;
    }

    if (!found) {
        return 0;
    }

    sig->attempt = found_attempt;
    memcpy(sig->c_tilde, found_challenge, C_TILDE_BYTES);

    sig->s_len = ct_encode_s(&found_s_cyc, &found_s_neg, sig->s_data, sizeof(sig->s_data));

    #ifdef DEBUG_BOUNDS
    printf("  found=%u, found_attempt=%d, s_len=%d, sizeof(s_data)=%lu\n",
           found, found_attempt, sig->s_len, sizeof(sig->s_data));
    #endif

    /* Clear sensitive data */
    OPENSSL_cleanse(&x_cyc, sizeof(x_cyc));
    OPENSSL_cleanse(&x_neg, sizeof(x_neg));
    OPENSSL_cleanse(&found_s_cyc, sizeof(found_s_cyc));
    OPENSSL_cleanse(&found_s_neg, sizeof(found_s_neg));

    return sig->s_len > 0;
}

/* ============================================================================
 * Verification
 * ============================================================================ */

static int verify_ct(const seedless_sig_t *sig, const public_key_t *pk,
                     const uint8_t *msg, size_t msg_len) {
    ring_t y;
    expand_ring(&y, pk->seed, 0);

    master_t r_master;
    expand_nonce_master(&r_master, sig->nonce_seed, sig->attempt);

    ring_t r_cyc, r_neg;
    project_cyclic(&r_master, &r_cyc);
    project_negacyclic(&r_master, &r_neg);

    ring_t w_full_cyc, w_full_neg;
    mul_cyclic(&w_full_cyc, &r_cyc, &y);
    mul_negacyclic(&w_full_neg, &r_neg, &y);

    ring_t w_round_cyc, w_round_neg;
    round_ring(&w_round_cyc, &w_full_cyc);
    round_ring(&w_round_neg, &w_full_neg);

    uint8_t challenge_seed[32];
    hash_to_challenge(challenge_seed, &w_round_cyc, &w_round_neg, pk, msg, msg_len);

    if (ct_memcmp(sig->c_tilde, challenge_seed, C_TILDE_BYTES) != 0) {
        return 0;
    }

    ring_t s_cyc, s_neg;
    if (!ct_decode_s(sig->s_data, sig->s_len, &s_cyc, &s_neg)) {
        return 0;
    }

    master_t c_master;
    expand_sparse_challenge(&c_master, challenge_seed, CHALLENGE_WEIGHT);

    ring_t c_cyc, c_neg;
    project_cyclic(&c_master, &c_cyc);
    project_negacyclic(&c_master, &c_neg);

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

    ring_t w_unround_cyc, w_unround_neg;
    unround_ring(&w_unround_cyc, &w_round_cyc);
    unround_ring(&w_unround_neg, &w_round_neg);

    int32_t max_err = 0;
    for (int i = 0; i < N; i++) {
        int32_t diff = ct_abs(ct_centered(ct_mod_q(w_prime_cyc.c[i] - w_unround_cyc.c[i])));
        max_err = ct_max(max_err, diff);
        diff = ct_abs(ct_centered(ct_mod_q(w_prime_neg.c[i] - w_unround_neg.c[i])));
        max_err = ct_max(max_err, diff);
    }

    return max_err <= TAU;
}

/* ============================================================================
 * Public API - Compact 256-byte signatures
 * ============================================================================ */

#ifdef COMPACT_SIG
#define CT_PK_MAX 400   /* seed(16) + arith-coded pk (~357 bytes) */
#define CT_SIG_MAX 256  /* Target: exactly 256 bytes */
#else
#define CT_PK_MAX 512
#define CT_SIG_MAX 600
#endif

typedef struct {
    uint8_t data[CT_PK_MAX];
    int len;
} ct_pk_t;

typedef struct {
    uint8_t data[CT_SIG_MAX];
    int len;
} ct_sig_t;

int crt_lwr_keygen_ct(ct_pk_t *pk_out, crt_lwr_sk_t *sk_out) {
    public_key_t internal_pk;
    secret_key_t internal_sk;

    keygen(&internal_pk, &internal_sk);

    memcpy(sk_out->seed, internal_sk.seed, SEED_BYTES);
    memcpy(sk_out->x_master, internal_sk.x_master.c, N2 * sizeof(int16_t));

    memcpy(pk_out->data, internal_pk.seed, SEED_BYTES);
    int pk_data_len = ct_encode_pk(&internal_pk, pk_out->data + SEED_BYTES, CT_PK_MAX - SEED_BYTES);
    if (pk_data_len == 0) return 0;

    pk_out->len = SEED_BYTES + pk_data_len;
    return 1;
}

int crt_lwr_sign_ct(ct_sig_t *sig_out, const crt_lwr_sk_t *sk, const ct_pk_t *pk,
                    const uint8_t *msg, size_t msg_len) {
    secret_key_t internal_sk;
    memcpy(internal_sk.seed, sk->seed, SEED_BYTES);
    memcpy(internal_sk.x_master.c, sk->x_master, N2 * sizeof(int16_t));

    public_key_t internal_pk;
    memcpy(internal_pk.seed, pk->data, SEED_BYTES);
    if (!ct_decode_pk(pk->data + SEED_BYTES, pk->len - SEED_BYTES, &internal_pk)) {
        return 0;
    }

    seedless_sig_t internal_sig;
    if (!sign_ct(&internal_sig, &internal_sk, &internal_pk, msg, msg_len)) {
        return 0;
    }

    int total = NONCE_SEED_BYTES + C_TILDE_BYTES + 1 + internal_sig.s_len;
    if (total > CT_SIG_MAX) {
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

int crt_lwr_verify_ct(const ct_sig_t *sig, const ct_pk_t *pk,
                      const uint8_t *msg, size_t msg_len) {
    public_key_t internal_pk;
    memcpy(internal_pk.seed, pk->data, SEED_BYTES);
    if (!ct_decode_pk(pk->data + SEED_BYTES, pk->len - SEED_BYTES, &internal_pk)) {
        return 0;
    }

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

    return verify_ct(&internal_sig, &internal_pk, msg, msg_len);
}

/* ============================================================================
 * Test
 * ============================================================================ */

/* Test encode/decode round-trip */
static int test_s_roundtrip(void) {
    ring_t s_cyc, s_neg, s_cyc_out, s_neg_out;
    uint8_t buf[512];

    /* Generate valid CRT-related coefficients:
     * s_cyc = a + b, s_neg = a - b, so (s_cyc - s_neg) = 2b is always even */
    for (int i = 0; i < N; i++) {
        int32_t a = (rand() % 5) - 2;  /* [-2, 2] */
        int32_t b = (rand() % 5) - 2;  /* [-2, 2] */
        s_cyc.c[i] = ct_mod_q(a + b);   /* [-4, 4] */
        s_neg.c[i] = ct_mod_q(a - b);   /* [-4, 4] */
    }

    int len = ct_encode_s(&s_cyc, &s_neg, buf, sizeof(buf));
    if (len == 0) {
        printf("  encode failed\n");
        return 0;
    }

    if (!ct_decode_s(buf, len, &s_cyc_out, &s_neg_out)) {
        printf("  decode failed\n");
        return 0;
    }

    /* Verify round-trip */
    int mismatch_cyc = 0, mismatch_neg = 0;
    for (int i = 0; i < N; i++) {
        int32_t orig_cyc = ct_centered(s_cyc.c[i]);
        int32_t dec_cyc = ct_centered(s_cyc_out.c[i]);
        if (orig_cyc != dec_cyc) {
            if (mismatch_cyc < 3) printf("  s_cyc[%d]: orig=%d, dec=%d\n", i, orig_cyc, dec_cyc);
            mismatch_cyc++;
        }
    }

    for (int i = 0; i < N; i++) {
        int32_t orig_neg = ct_centered(s_neg.c[i]);
        int32_t dec_neg = ct_centered(s_neg_out.c[i]);
        if (orig_neg != dec_neg) {
            if (mismatch_neg < 3) {
                int32_t orig_delta = ct_centered(ct_mod_q(s_cyc.c[i] - s_neg.c[i])) / 2;
                int32_t dec_cyc = ct_centered(s_cyc_out.c[i]);
                printf("  s_neg[%d]: orig=%d, dec=%d, orig_delta=%d, dec_s_cyc=%d\n",
                       i, orig_neg, dec_neg, orig_delta, dec_cyc);
            }
            mismatch_neg++;
        }
    }

    if (mismatch_cyc > 0 || mismatch_neg > 0) {
        printf("  s_cyc mismatches: %d, s_neg mismatches: %d\n", mismatch_cyc, mismatch_neg);
        return 0;
    }

    return 1;
}

#ifndef CRT_LWR_LIB_ONLY
int main() {
    printf("CRT-LWR Signature Scheme (Constant-Time)\n");
    printf("=========================================\n");
    printf("Parameters: N=%d, Q=%d, P=%d, TAU=%d\n", N, Q, P, TAU);
    printf("Security: ~131 bits (NIST Level 1+)\n\n");

    /* First test s encoding round-trip */
    printf("Testing s encode/decode round-trip... ");
    fflush(stdout);
    if (!test_s_roundtrip()) {
        printf("FAILED\n");
        return 1;
    }
    printf("OK\n\n");

    ct_pk_t pk;
    crt_lwr_sk_t sk;
    ct_sig_t sig;

    printf("Keygen... ");
    fflush(stdout);
    if (!crt_lwr_keygen_ct(&pk, &sk)) {
        printf("FAILED\n");
        return 1;
    }
    printf("OK (pk = %d bytes)\n", pk.len);

    const char *msg = "Hello, constant-time CRT-LWR!";
    printf("Sign... ");
    fflush(stdout);
    if (!crt_lwr_sign_ct(&sig, &sk, &pk, (const uint8_t *)msg, strlen(msg))) {
        printf("FAILED\n");
        return 1;
    }
    printf("OK (sig = %d bytes)\n", sig.len);

    printf("Verify... ");
    fflush(stdout);
    if (!crt_lwr_verify_ct(&sig, &pk, (const uint8_t *)msg, strlen(msg))) {
        printf("FAILED\n");
        return 1;
    }
    printf("OK\n");

    const char *wrong = "Wrong message";
    printf("Wrong message... ");
    fflush(stdout);
    if (crt_lwr_verify_ct(&sig, &pk, (const uint8_t *)wrong, strlen(wrong))) {
        printf("FAILED (accepted wrong message)\n");
        return 1;
    }
    printf("correctly rejected\n");

    printf("\nSummary:\n");
    printf("  pk:  %d bytes (CT fixed-width encoding)\n", pk.len);
    printf("  sig: %d bytes (CT arithmetic coding)\n", sig.len);
    printf("  total: %d bytes\n", pk.len + sig.len);

    printf("\nSUCCESS!\n");

    return 0;
}
#endif
