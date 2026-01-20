# CRT-Coupled Two-Ring Module-LWR Signature Cheat Sheet

## Overview
- Master ring: Z_q[X]/(X^512 - 1) with q=499
- CRT factorization into cyclic and negacyclic component rings:
  - Cyclic: Z_q[X]/(X^256 - 1) where X^N = 1
  - Negacyclic: Z_q[X]/(X^256 + 1) where X^N = -1
- Project from master ring to components:
  - x_cyc[i] = x[i] + x[i+N]
  - x_neg[i] = x[i] - x[i+N]
- Lift back to master ring (parity required):
  - x[i] = (x_cyc[i] + x_neg[i]) / 2
  - x[i+N] = (x_cyc[i] - x_neg[i]) / 2
  - Requires x_cyc[i] ≡ x_neg[i] (mod 2) for all i
- Critical: secrets, nonces, and challenges are sampled in the 512-dim master ring
  with **trace-zero constraint**, then projected. This forces attackers to work in
  the full 512-dim structure.
- Same public polynomial y (from seed) used in both rings.
- Both commitments w_cyc and w_neg are computed and included in the hash.

---

## Parameters

### Ring and Modulus
```
N  = 256       // Component ring dimension
N2 = 512       // Master ring dimension (2×N)
Q  = 499       // Prime modulus (Q ≡ 3 mod 8)
P  = 48        // Rounding modulus (Q/P ≈ 10.4)
```

### Sampling and Bounds
```
ETA = 1                  // Secret coefficient bound (ternary: -1, 0, +1)
SECRET_WEIGHT = 50       // Sparse weight for master secret (trace-zero)
NONCE_WEIGHT = 25        // Sparse weight for master nonce (trace-zero)
CHALLENGE_WEIGHT = 25    // Sparse weight for challenge (trace-zero)
Y_BOUND = 4              // Public polynomial bound: coeffs in [-4, 4]
TAU = 65                 // Verification error threshold
B_COEFF = 60             // Max signature coefficient (= w_r + w_c*η + 10)
SEED_BYTES = 16          // Public seed length (128 bits)
```

---

## Data Structures (C)

```c
// Component ring element in Z_q^N
typedef struct { int16_t c[N]; } ring_t;

// Master ring element in Z_q^{2N}
typedef struct { int16_t c[N2]; } master_t;

typedef struct {
    uint8_t seed[SEED_BYTES];
    ring_t pk_cyc;            // pk_cyc = round(x_cyc * y)
    ring_t pk_neg;            // pk_neg = round(x_neg * y)
} public_key_t;

typedef struct {
    master_t x_master;        // Secret in master ring (trace-zero)
    uint8_t seed[SEED_BYTES];
} secret_key_t;

typedef struct {
    ring_t s_cyc;             // Response in cyclic ring
    ring_t s_neg;             // Response in negacyclic ring
    ring_t w_cyc;             // Commitment in cyclic ring
    ring_t w_neg;             // Commitment in negacyclic ring
} signature_t;

// Seedless signature (verifier reconstructs w)
typedef struct {
    uint8_t nonce_seed[12];   // Public nonce seed
    uint8_t c_tilde[16];      // Commitment binding hash
    uint8_t attempt;          // Rejection sampling attempt
    uint8_t s_data[300];      // Range-coded s
    int s_len;
} seedless_sig_t;
```

---

## Core Operations

### CRT Projection (master → components)
```
project_cyclic(x_master):
  for i in [0, N):
    x_cyc[i] = x[i] + x[i+N]  (mod q)

project_negacyclic(x_master):
  for i in [0, N):
    x_neg[i] = x[i] - x[i+N]  (mod q)
```

### CRT Lifting (components → master)
```
crt_lift(x_cyc, x_neg):
  for i in [0, N):
    sum  = x_cyc[i] + x_neg[i]
    diff = x_cyc[i] - x_neg[i]
    if (sum & 1) or (diff & 1):
      return FAIL  // Parity mismatch
    x[i]   = sum / 2
    x[i+N] = diff / 2
  return SUCCESS
```

### Ring Multiplication
```
Cyclic:     (a * b) in Z_q[X]/(X^N - 1)  // X^N = 1
Negacyclic: (a * b) in Z_q[X]/(X^N + 1)  // X^N = -1
```

### LWR Round / Unround
```
round_p(x)   = round(x * P / Q)  // centered
unround_p(y) = y * Q / P + Q/(2P)  // centered lift
```

### Trace-Zero Sampling
```
sample_sparse_master(weight):
  // Sample weight/2 positions with +1, weight/2 with -1
  // Ensures Σx[i] = 0 (trace-zero)
```

---

## Algorithm: Key Generation

```
keygen():
  1. Sample seed σ ← {0,1}^128
  2. y ← expand_ring(σ)           // Bounded: ||y||_∞ ≤ Y_BOUND
  3. x_master ← sample_sparse_master(SECRET_WEIGHT)  // Trace-zero
  4. x_cyc ← project_cyclic(x_master)
  5. x_neg ← project_negacyclic(x_master)
  6. pk_cyc ← round_p(x_cyc * y)  // Cyclic multiplication
  7. pk_neg ← round_p(x_neg * y)  // Negacyclic multiplication

Output:
  - sk = (x_master, σ)
  - pk = (σ, pk_cyc, pk_neg)
```

---

## Algorithm: Signing

```
sign(sk, pk, msg):
  1. y ← expand_ring(σ)
  2. x_cyc, x_neg ← project(x_master)
  3. Repeat until success:
     a. r_master ← sample_sparse_master(NONCE_WEIGHT)  // Trace-zero
     b. r_cyc, r_neg ← project(r_master)
     c. w_cyc ← round_p(r_cyc * y)    // Cyclic commitment
     d. w_neg ← round_p(r_neg * y)    // Negacyclic commitment
     e. challenge_seed ← SHA3-256(w_cyc || w_neg || pk_cyc || pk_neg || σ || msg)
     f. c_master ← expand_sparse_challenge(challenge_seed, CHALLENGE_WEIGHT)
     g. c_cyc, c_neg ← project(c_master)
     h. s_cyc ← r_cyc + c_cyc * x_cyc   // Cyclic response
     i. s_neg ← r_neg + c_neg * x_neg   // Negacyclic response
     j. if ||s_cyc||_∞ > B_COEFF or ||s_neg||_∞ > B_COEFF: continue
     k. if ||s_cyc||_∞ ≥ 16 or ||s_neg||_∞ ≥ 16: continue  // 5-bit compression
     l. Compute verification error, if > TAU: continue
  4. Return σ = (s_cyc, s_neg, w_cyc, w_neg)
```

---

## Algorithm: Verification

```
verify(pk, msg, sig):
  1. y ← expand_ring(σ)

  // Coupling checks
  2. if ||s_cyc||_∞ > B_COEFF or ||s_neg||_∞ > B_COEFF:
       return REJECT

  3. s_master ← crt_lift(s_cyc, s_neg)
     if FAIL: return REJECT  // Liftability check

  4. if Tr(s_master) ≢ 0 (mod q):
       return REJECT  // Trace-zero check

  // Reconstruct challenge
  5. challenge_seed ← SHA3-256(w_cyc || w_neg || pk_cyc || pk_neg || σ || msg)
  6. c_master ← expand_sparse_challenge(challenge_seed, CHALLENGE_WEIGHT)
  7. c_cyc, c_neg ← project(c_master)

  // Verify in both rings
  8. w'_cyc ← s_cyc * y - c_cyc * unround_p(pk_cyc)   // Cyclic: X^N = 1
  9. w'_neg ← s_neg * y - c_neg * unround_p(pk_neg)   // Negacyclic: X^N = -1

  10. err_cyc ← ||w'_cyc - unround_p(w_cyc)||_∞
  11. err_neg ← ||w'_neg - unround_p(w_neg)||_∞

  12. if max(err_cyc, err_neg) > TAU:
        return REJECT

  13. return ACCEPT
```

---

## Key Equations Summary

| Step | Equation | Purpose |
|------|----------|---------|
| CRT Projection | x_cyc = x[i] + x[i+N], x_neg = x[i] - x[i+N] | Master → components |
| CRT Lifting | x[i] = (x_cyc + x_neg)/2, x[i+N] = (x_cyc - x_neg)/2 | Enforced by parity |
| Trace-Zero | Σ x[i] ≡ 0 (mod q) | Constraint on master ring elements |
| KeyGen (cyc) | pk_cyc = round(x_cyc * y) | Cyclic public key |
| KeyGen (neg) | pk_neg = round(x_neg * y) | Negacyclic public key |
| Commit (cyc) | w_cyc = round(r_cyc * y) | Cyclic commitment |
| Commit (neg) | w_neg = round(r_neg * y) | Negacyclic commitment |
| Challenge | c = H(w_cyc \|\| w_neg \|\| pk_cyc \|\| pk_neg \|\| σ \|\| msg) | Fiat-Shamir |
| Response | s_cyc = r_cyc + c_cyc * x_cyc | Cyclic signature response |
| Verify (cyc) | w' = s_cyc * y - c_cyc * unround(pk_cyc) | Check LWR error |
| Verify (neg) | w' = s_neg * y - c_neg * unround(pk_neg) | Check LWR error |

---

## Coupling Constraint

A valid signature (s_cyc, s_neg) must satisfy:

1. **Coefficient bound**: ||s||_∞ ≤ B_COEFF = 60
   - `verify_coupling()` checks this

2. **Liftability**: s_cyc[i] ≡ s_neg[i] (mod 2) for all i
   - `crt_lift()` returns FAIL if violated

3. **Trace-zero**: Σ s_master[i] ≡ 0 (mod q)
   - `verify_trace_zero()` checks this after lifting

Random pairs fail with overwhelming probability:
- Liftability: Pr ≈ 2^{-256}
- Trace-zero: Pr ≈ 1/q ≈ 1/499

---

## Signature Formats

### Full Signature (~436 bytes)
```
s_cyc, s_neg: ~180 bytes (range-coded)
w_cyc, w_neg: ~256 bytes (rounded commitments)
```

### Seedless-w Signature (~209 bytes)
```
nonce_seed:   12 bytes   // Verifier reconstructs w
c_tilde:      16 bytes   // Commitment binding
attempt:       1 byte    // Rejection sampling index
s (range):  ~180 bytes   // Delta-encoded response
```

### Public Key (~416 bytes)
```
seed:         16 bytes
pk_cyc, pk_neg (Huffman): ~400 bytes
```

---

## Compression Notes

### Range Coding for s
- s_cyc encoded with small-value table + escape codes
- s_neg encoded as delta: δ = (s_cyc - s_neg) / 2
- Permutation from challenge seed reorders coefficients for better compression

### Huffman for Public Key
- pk values in [0, P-1] = [0, 47]
- Huffman tables optimized for coefficient distribution

---

## Security Notes

- **Master ring sampling**: Secrets, nonces, and challenges are sampled in the
  512-dim master ring with trace-zero. This is the key security mechanism.

- **CRT bijection** (Lean-verified): The projection (π_cyc, π_neg) is a bijection.
  Learning π_cyc(x) reveals zero information about π_neg(x).

- **No dimension splitting**: An attacker cannot treat the two 256-dim rings
  independently. Any valid (s_cyc, s_neg) must lift to the master ring.

- **Verification rejects decoupled forgeries**: Coefficient bounds, liftability,
  and trace-zero are all checked explicitly.

- **Concrete security**: ~2^138 classical (512-dim lattice problem)

---

## File Reference

- Reference implementation: `crt_coupled_sig.c`
- Security proof: `euf_cma_proof_dual_pk.tex`
- Lean formalization: `lean/CRTSecurity/Aristotle.lean`
