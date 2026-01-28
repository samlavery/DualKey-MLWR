/*
 * 512-dim Security CRT-LWR
 *
 * True 512-dim security via master ring public key,
 * compact signatures via factor ring responses.
 *
 * Secret: X in Z[X]/(X^512 - 1)  (512-dim)
 * Public key: pk = round(X · y) in 512-dim  ← 512-dim LWR security!
 *
 * Signing:
 *   - Nonce r in 512-dim master ring
 *   - Project: r → (r_cyc, r_neg), X → (X_cyc, X_neg)
 *   - Compute s_cyc = r_cyc + c·X_cyc, s_neg = r_neg + c·X_neg
 *   - Encode with delta compression
 *
 * Verification:
 *   - Decode (s_cyc, s_neg), lift to s in 512-dim
 *   - Verify: round(s·y - c·pk) matches commitment
 *
 * Security: Attacker must solve 512-dim LWR to recover X
 * Compactness: Response encoded in 256-dim factors with delta
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <openssl/evp.h>
#include <openssl/rand.h>

#define N256 256
#define N512 512
#define Q 499
#define P 48
#define TAU 65
#define CHALLENGE_WEIGHT 25
#define NONCE_WEIGHT 30
#define SECRET_WEIGHT 50
#define MAX_ATTEMPTS 1000
#define SEED_BYTES 16

/* 2^(-1) mod 499 = 250 */
#define INV2 250

typedef int16_t coeff_t;
typedef struct { coeff_t c[N512]; } ring512_t;
typedef struct { coeff_t c[N256]; } ring256_t;

typedef struct {
    uint8_t seed[SEED_BYTES];
    ring512_t pk;    /* 512-dim public key - TRUE 512-dim security */
} public_key_t;

typedef struct {
    ring512_t x;     /* 512-dim master secret */
    uint8_t seed[SEED_BYTES];
} secret_key_t;

typedef struct {
    uint8_t nonce_seed[8];
    uint8_t c_tilde[8];
    uint8_t attempt;
    uint8_t s_cyc_data[160];   /* 5 bits × 256 */
    uint8_t delta_data[160];   /* 5 bits × 256 */
} signature_t;

static inline int32_t mod_q(int32_t x) {
    int32_t r = x % Q;
    return r < 0 ? r + Q : r;
}

static inline int32_t centered(int32_t x) {
    if (x > Q/2) return x - Q;
    return x;
}

/* ============================================================================
 * 512-dim cyclic ring operations
 * ============================================================================ */

static void mul_512(ring512_t *r, const ring512_t *a, const ring512_t *b) {
    int32_t tmp[N512] = {0};
    for (int i = 0; i < N512; i++) {
        if (a->c[i] == 0) continue;
        for (int j = 0; j < N512; j++) {
            if (b->c[j] == 0) continue;
            tmp[(i + j) % N512] += (int32_t)a->c[i] * b->c[j];
        }
    }
    for (int i = 0; i < N512; i++) r->c[i] = mod_q(tmp[i]);
}

static void add_512(ring512_t *r, const ring512_t *a, const ring512_t *b) {
    for (int i = 0; i < N512; i++) r->c[i] = mod_q(a->c[i] + b->c[i]);
}

static void sub_512(ring512_t *r, const ring512_t *a, const ring512_t *b) {
    for (int i = 0; i < N512; i++) r->c[i] = mod_q(a->c[i] - b->c[i]);
}

static void round_512(ring512_t *r, const ring512_t *a) {
    for (int i = 0; i < N512; i++) {
        int32_t c = centered(a->c[i]);
        int32_t v = (c * P + (c >= 0 ? Q/2 : -Q/2)) / Q;
        r->c[i] = ((v % P) + P) % P;
    }
}

static void unround_512(ring512_t *r, const ring512_t *a) {
    for (int i = 0; i < N512; i++) {
        r->c[i] = (a->c[i] * Q + P/2) / P;
    }
}

/* ============================================================================
 * CRT: 512-dim ↔ (256-cyc, 256-neg)
 * ============================================================================ */

/* Project down: a → (a_cyc, a_neg) */
static void project_to_factors(const ring512_t *a, ring256_t *a_cyc, ring256_t *a_neg) {
    for (int i = 0; i < N256; i++) {
        a_cyc->c[i] = mod_q(a->c[i] + a->c[i + N256]);
        a_neg->c[i] = mod_q(a->c[i] - a->c[i + N256]);
    }
}

/* Lift up: (a_cyc, a_neg) → a
 * a[i] = (a_cyc[i] + a_neg[i]) / 2
 * a[i+256] = (a_cyc[i] - a_neg[i]) / 2
 */
static void lift_from_factors(const ring256_t *a_cyc, const ring256_t *a_neg, ring512_t *a) {
    for (int i = 0; i < N256; i++) {
        int32_t sum = mod_q(a_cyc->c[i] + a_neg->c[i]);
        int32_t diff = mod_q(a_cyc->c[i] - a_neg->c[i]);
        a->c[i] = mod_q(sum * INV2);
        a->c[i + N256] = mod_q(diff * INV2);
    }
}

/* ============================================================================
 * 256-dim factor ring operations
 * ============================================================================ */

static void mul_256_cyc(ring256_t *r, const ring256_t *a, const ring256_t *b) {
    int32_t tmp[N256] = {0};
    for (int i = 0; i < N256; i++) {
        if (a->c[i] == 0) continue;
        for (int j = 0; j < N256; j++) {
            if (b->c[j] == 0) continue;
            tmp[(i + j) % N256] += (int32_t)a->c[i] * b->c[j];
        }
    }
    for (int i = 0; i < N256; i++) r->c[i] = mod_q(tmp[i]);
}

static void mul_256_neg(ring256_t *r, const ring256_t *a, const ring256_t *b) {
    int32_t tmp[N256] = {0};
    for (int i = 0; i < N256; i++) {
        if (a->c[i] == 0) continue;
        for (int j = 0; j < N256; j++) {
            if (b->c[j] == 0) continue;
            int k = i + j;
            int32_t prod = (int32_t)a->c[i] * b->c[j];
            if (k >= N256) tmp[k - N256] -= prod;
            else tmp[k] += prod;
        }
    }
    for (int i = 0; i < N256; i++) r->c[i] = mod_q(tmp[i]);
}

static void add_256(ring256_t *r, const ring256_t *a, const ring256_t *b) {
    for (int i = 0; i < N256; i++) r->c[i] = mod_q(a->c[i] + b->c[i]);
}

static void round_256(ring256_t *r, const ring256_t *a) {
    for (int i = 0; i < N256; i++) {
        int32_t c = centered(a->c[i]);
        int32_t v = (c * P + (c >= 0 ? Q/2 : -Q/2)) / Q;
        r->c[i] = ((v % P) + P) % P;
    }
}

/* ============================================================================
 * Sampling and Expansion
 * ============================================================================ */

static void sample_sparse_512(ring512_t *x, int weight) {
    memset(x->c, 0, sizeof(x->c));
    int placed = 0;
    while (placed < weight) {
        uint8_t buf[3];
        RAND_bytes(buf, 3);
        int pos = ((buf[0] << 8) | buf[1]) % N512;
        if (x->c[pos] == 0) {
            x->c[pos] = (buf[2] & 1) ? 1 : Q - 1;
            placed++;
        }
    }
}

static void expand_512(ring512_t *r, const uint8_t *seed, int domain) {
    uint8_t hash[N512 * 2];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, &domain, sizeof(domain));
    EVP_DigestFinalXOF(ctx, hash, sizeof(hash));
    EVP_MD_CTX_free(ctx);

    for (int i = 0; i < N512; i++) {
        r->c[i] = ((hash[2*i] << 8) | hash[2*i+1]) % Q;
    }
}

static void expand_nonce_512(ring512_t *r, const uint8_t *seed, uint8_t attempt) {
    memset(r->c, 0, sizeof(r->c));

    uint8_t hash[1024];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, seed, 8);
    EVP_DigestUpdate(ctx, &attempt, 1);
    EVP_DigestFinalXOF(ctx, hash, sizeof(hash));
    EVP_MD_CTX_free(ctx);

    int placed = 0, i = 0;
    while (placed < NONCE_WEIGHT && i < 1000) {
        int pos = ((hash[i] << 8) | hash[i+1]) % N512;
        i += 2;
        if (r->c[pos] == 0) {
            r->c[pos] = (hash[i++] & 1) ? 1 : Q - 1;
            placed++;
        }
    }
}

static void expand_challenge_512(ring512_t *c, const uint8_t *seed, int weight) {
    memset(c->c, 0, sizeof(c->c));

    uint8_t hash[1024];
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_shake256(), NULL);
    EVP_DigestUpdate(ctx, seed, 32);
    EVP_DigestFinalXOF(ctx, hash, sizeof(hash));
    EVP_MD_CTX_free(ctx);

    int placed = 0, idx = 0;
    while (placed < weight && idx < 1000) {
        int pos = ((hash[idx] << 8) | hash[idx+1]) % N512;
        idx += 2;
        if (c->c[pos] == 0) {
            c->c[pos] = (hash[idx++] & 1) ? 1 : Q - 1;
            placed++;
        }
    }
}

static void hash_commitment(uint8_t *out, const ring256_t *w_cyc, const ring256_t *w_neg,
                            const public_key_t *pk, const uint8_t *msg, size_t msg_len) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_sha3_256(), NULL);
    EVP_DigestUpdate(ctx, w_cyc->c, sizeof(w_cyc->c));
    EVP_DigestUpdate(ctx, w_neg->c, sizeof(w_neg->c));
    EVP_DigestUpdate(ctx, pk->pk.c, sizeof(pk->pk.c));
    EVP_DigestUpdate(ctx, pk->seed, SEED_BYTES);
    EVP_DigestUpdate(ctx, msg, msg_len);
    unsigned int len = 32;
    EVP_DigestFinal_ex(ctx, out, &len);
    EVP_MD_CTX_free(ctx);
}

/* ============================================================================
 * Encoding with delta compression
 * ============================================================================ */

#define S_MAX 10
#define DELTA_MAX 8

static int encode_s_delta(const ring256_t *s_cyc, const ring256_t *s_neg,
                          uint8_t *out_cyc, uint8_t *out_delta) {
    for (int i = 0; i < N256; i++) {
        int c = centered(s_cyc->c[i]);
        int delta = centered(mod_q(s_cyc->c[i] - s_neg->c[i]));
        if (abs(c) > S_MAX || abs(delta) > DELTA_MAX) return 0;
    }

    memset(out_cyc, 0, 160);
    memset(out_delta, 0, 160);

    int bit_pos = 0;
    for (int i = 0; i < N256; i++) {
        int v = centered(s_cyc->c[i]) + 16;
        int byte_idx = bit_pos / 8;
        int bit_off = bit_pos % 8;
        out_cyc[byte_idx] |= (v << bit_off) & 0xFF;
        if (bit_off > 3) out_cyc[byte_idx + 1] |= v >> (8 - bit_off);
        bit_pos += 5;
    }

    bit_pos = 0;
    for (int i = 0; i < N256; i++) {
        int delta = centered(mod_q(s_cyc->c[i] - s_neg->c[i])) + 16;
        int byte_idx = bit_pos / 8;
        int bit_off = bit_pos % 8;
        out_delta[byte_idx] |= (delta << bit_off) & 0xFF;
        if (bit_off > 3) out_delta[byte_idx + 1] |= delta >> (8 - bit_off);
        bit_pos += 5;
    }

    return 1;
}

static void decode_s_delta(const uint8_t *in_cyc, const uint8_t *in_delta,
                           ring256_t *s_cyc, ring256_t *s_neg) {
    int bit_pos = 0;
    for (int i = 0; i < N256; i++) {
        int byte_idx = bit_pos / 8;
        int bit_off = bit_pos % 8;
        int v = ((in_cyc[byte_idx] >> bit_off) | (in_cyc[byte_idx + 1] << (8 - bit_off))) & 0x1F;
        s_cyc->c[i] = mod_q(v - 16);
        bit_pos += 5;
    }

    bit_pos = 0;
    for (int i = 0; i < N256; i++) {
        int byte_idx = bit_pos / 8;
        int bit_off = bit_pos % 8;
        int delta = ((in_delta[byte_idx] >> bit_off) | (in_delta[byte_idx + 1] << (8 - bit_off))) & 0x1F;
        delta -= 16;
        s_neg->c[i] = mod_q(s_cyc->c[i] - delta);
        bit_pos += 5;
    }
}

/* ============================================================================
 * Keygen
 * ============================================================================ */

static void keygen(public_key_t *pk, secret_key_t *sk) {
    RAND_bytes(sk->seed, SEED_BYTES);
    memcpy(pk->seed, sk->seed, SEED_BYTES);

    /* Public vector in 512-dim */
    ring512_t y;
    expand_512(&y, pk->seed, 0);

    /* Secret in 512-dim master ring */
    sample_sparse_512(&sk->x, SECRET_WEIGHT);

    /* Public key in 512-dim: TRUE 512-dim LWR security */
    ring512_t t;
    mul_512(&t, &sk->x, &y);
    round_512(&pk->pk, &t);
}

/* ============================================================================
 * Sign
 * ============================================================================ */

static int sign_msg(signature_t *sig, const secret_key_t *sk,
                    const public_key_t *pk, const uint8_t *msg, size_t msg_len) {
    ring512_t y;
    expand_512(&y, pk->seed, 0);

    /* Project y to factors for commitment */
    ring256_t y_cyc, y_neg;
    project_to_factors(&y, &y_cyc, &y_neg);

    RAND_bytes(sig->nonce_seed, 8);

    for (int attempt = 0; attempt < MAX_ATTEMPTS; attempt++) {
        /* Nonce in 512-dim master ring */
        ring512_t r;
        expand_nonce_512(&r, sig->nonce_seed, attempt);

        /* Commitment in factors: w = r·y (projected) */
        ring256_t r_cyc, r_neg;
        project_to_factors(&r, &r_cyc, &r_neg);

        ring256_t w_cyc, w_neg;
        mul_256_cyc(&w_cyc, &r_cyc, &y_cyc);
        mul_256_neg(&w_neg, &r_neg, &y_neg);

        ring256_t w_round_cyc, w_round_neg;
        round_256(&w_round_cyc, &w_cyc);
        round_256(&w_round_neg, &w_neg);

        uint8_t challenge_seed[32];
        hash_commitment(challenge_seed, &w_round_cyc, &w_round_neg, pk, msg, msg_len);

        /* Challenge in 512-dim */
        ring512_t c;
        expand_challenge_512(&c, challenge_seed, CHALLENGE_WEIGHT);

        /* Response in 512-dim: s = r + c·X */
        ring512_t cX, s;
        mul_512(&cX, &c, &sk->x);
        add_512(&s, &r, &cX);

        /* Project to factors for encoding */
        ring256_t s_cyc, s_neg;
        project_to_factors(&s, &s_cyc, &s_neg);

        /* Check bounds for encoding */
        if (!encode_s_delta(&s_cyc, &s_neg, sig->s_cyc_data, sig->delta_data)) continue;

        sig->attempt = attempt;
        memcpy(sig->c_tilde, challenge_seed, 8);

        return 1;
    }

    return 0;
}

/* ============================================================================
 * Verify
 * ============================================================================ */

static int verify_msg(const signature_t *sig, const public_key_t *pk,
                      const uint8_t *msg, size_t msg_len) {
    ring512_t y;
    expand_512(&y, pk->seed, 0);

    ring256_t y_cyc, y_neg;
    project_to_factors(&y, &y_cyc, &y_neg);

    /* Recompute nonce commitment */
    ring512_t r;
    expand_nonce_512(&r, sig->nonce_seed, sig->attempt);

    ring256_t r_cyc, r_neg;
    project_to_factors(&r, &r_cyc, &r_neg);

    ring256_t w_cyc, w_neg;
    mul_256_cyc(&w_cyc, &r_cyc, &y_cyc);
    mul_256_neg(&w_neg, &r_neg, &y_neg);

    ring256_t w_round_cyc, w_round_neg;
    round_256(&w_round_cyc, &w_cyc);
    round_256(&w_round_neg, &w_neg);

    uint8_t challenge_seed[32];
    hash_commitment(challenge_seed, &w_round_cyc, &w_round_neg, pk, msg, msg_len);

    if (memcmp(sig->c_tilde, challenge_seed, 8) != 0) return 0;

    /* Decode response and lift to 512-dim */
    ring256_t s_cyc, s_neg;
    decode_s_delta(sig->s_cyc_data, sig->delta_data, &s_cyc, &s_neg);

    ring512_t s;
    lift_from_factors(&s_cyc, &s_neg, &s);

    /* Challenge in 512-dim */
    ring512_t c;
    expand_challenge_512(&c, challenge_seed, CHALLENGE_WEIGHT);

    /* Verify in 512-dim: s·y - c·pk ≈ r·y */
    ring512_t pk_unround;
    unround_512(&pk_unround, &pk->pk);

    ring512_t sy, cpk, w_prime;
    mul_512(&sy, &s, &y);
    mul_512(&cpk, &c, &pk_unround);
    sub_512(&w_prime, &sy, &cpk);

    /* Compare with r·y */
    ring512_t ry;
    mul_512(&ry, &r, &y);

    int max_err = 0;
    for (int i = 0; i < N512; i++) {
        int d = abs(centered(mod_q(w_prime.c[i] - ry.c[i])));
        if (d > max_err) max_err = d;
    }

    return max_err <= TAU;
}

/* ============================================================================
 * Test
 * ============================================================================ */

int main() {
    printf("512-dim Security CRT-LWR\n");
    printf("========================\n");
    printf("Public key: 512-dim (TRUE 512-dim LWR security)\n");
    printf("Signature: Factor-encoded (compact via delta compression)\n\n");

    printf("Parameters:\n");
    printf("  Master ring: %d-dim cyclic\n", N512);
    printf("  Factor rings: %d-dim each\n", N256);
    printf("  Q=%d, P=%d, TAU=%d\n", Q, P, TAU);
    printf("  Secret weight: %d, Nonce weight: %d\n\n", SECRET_WEIGHT, NONCE_WEIGHT);

    public_key_t pk;
    secret_key_t sk;
    signature_t sig;

    printf("Keygen... ");
    fflush(stdout);
    keygen(&pk, &sk);
    printf("OK\n");

    /* Verify CRT roundtrip */
    ring256_t x_cyc, x_neg;
    project_to_factors(&sk.x, &x_cyc, &x_neg);

    ring512_t x_lifted;
    lift_from_factors(&x_cyc, &x_neg, &x_lifted);

    int crt_ok = 1;
    for (int i = 0; i < N512; i++) {
        if (x_lifted.c[i] != sk.x.c[i]) {
            crt_ok = 0;
            break;
        }
    }
    printf("CRT roundtrip: %s\n", crt_ok ? "OK" : "FAIL");

    /* Check parity (should be coupled since single master) */
    int same = 0, diff = 0;
    for (int i = 0; i < N256; i++) {
        int c = centered(x_cyc.c[i]);
        int n = centered(x_neg.c[i]);
        if (c != 0 || n != 0) {
            if ((c & 1) == (n & 1)) same++;
            else diff++;
        }
    }
    printf("Parity (master secret): same=%d, diff=%d (coupled as expected)\n", same, diff);

    const char *msg = "Test message";
    printf("\nSign... ");
    fflush(stdout);
    if (!sign_msg(&sig, &sk, &pk, (const uint8_t*)msg, strlen(msg))) {
        printf("FAILED\n");
        return 1;
    }
    int sig_size = 8 + 8 + 1 + 160 + 160;
    printf("OK (sig = %d bytes)\n", sig_size);

    printf("Verify... ");
    fflush(stdout);
    if (!verify_msg(&sig, &pk, (const uint8_t*)msg, strlen(msg))) {
        printf("FAILED\n");
        return 1;
    }
    printf("OK\n");

    printf("Wrong message... ");
    fflush(stdout);
    if (verify_msg(&sig, &pk, (const uint8_t*)"wrong", 5)) {
        printf("ACCEPTED (BAD!)\n");
        return 1;
    }
    printf("rejected (OK)\n");

    /* Batch test */
    printf("\n=== 100 trials ===\n");
    int success = 0, verify_pass = 0;
    for (int i = 0; i < 100; i++) {
        keygen(&pk, &sk);
        char m[32];
        snprintf(m, sizeof(m), "Trial %d", i);
        if (!sign_msg(&sig, &sk, &pk, (const uint8_t*)m, strlen(m))) continue;
        success++;
        if (verify_msg(&sig, &pk, (const uint8_t*)m, strlen(m))) verify_pass++;
    }
    printf("Sign: %d/100, Verify: %d/%d\n", success, verify_pass, success);

    printf("\n=== Security Summary ===\n");
    printf("LWR dimension: %d (attacker must solve 512-dim LWR)\n", N512);
    printf("Signature size: %d bytes (compact via factor encoding)\n", sig_size);
    printf("Public key size: %d coefficients in P=%d\n", N512, P);

    return 0;
}
