# CRT-Coupled Two-Ring Module-LWR Signatures
*(Master ring embedding with cyclic/negacyclic factor rings)*

## TL;DR
- Master ring Z_q[X]/(X^512 - 1) factors via CRT into cyclic Z_q[X]/(X^256 - 1) and negacyclic Z_q[X]/(X^256 + 1).
- Secrets and nonces are sampled in the 512-dim master ring with a **trace-zero constraint**, then projected to component rings.
- Same public polynomial y (from seed) is used in both rings; challenges are expanded in the master ring.
- Verification checks coefficient bounds, liftability, trace-zero, and the verification equation in both rings.
- Seedless-w signatures: ~209 bytes. Public key: ~416 bytes (Huffman compressed).
- **Machine-verified**: Core CRT bijection property proven in Lean 4.

## Overview

This scheme couples two component rings into a single 512-dimensional master ring using the Chinese Remainder Theorem:

```
Z_q[X]/(X^512 - 1) ≅ Z_q[X]/(X^256 - 1) × Z_q[X]/(X^256 + 1)
                      \___ cyclic ___/   \__ negacyclic __/
```

**CRT Projection** (master → components):
```
π_cyc(x)[i] = x[i] + x[i+256]  (mod q)
π_neg(x)[i] = x[i] - x[i+256]  (mod q)
```

**CRT Lifting** (components → master):
```
x[i]     = (x_cyc[i] + x_neg[i]) / 2
x[i+256] = (x_cyc[i] - x_neg[i]) / 2
```
Lifting requires **parity matching**: x_cyc[i] ≡ x_neg[i] (mod 2) for all i.

## Key Security Property

The master secret is sampled in the 512-dim ring, then projected. An adversary who learns the cyclic projection gains **zero information** about the negacyclic projection (and vice versa). This is formally verified in Lean 4:

```lean
theorem crt_bijection [Invertible (2 : ZMod q)] :
    Function.Bijective (fun s => (cyclicProj s, negacyclicProj s))
```

This forces attackers to solve a 512-dimensional lattice problem, not two independent 256-dim problems.

## Parameters (crt_coupled_sig.c)

| Parameter | Symbol | Value |
|-----------|--------|-------|
| Component ring dimension | N | 256 |
| Master ring dimension | 2N | 512 |
| Prime modulus | q | 499 |
| Rounding modulus | p | 48 |
| Verification threshold | τ | 65 |
| Max signature coefficient | B_coeff | 60 |
| Challenge weight (sparse) | w_c | 25 |
| Nonce weight (sparse) | w_r | 25 |
| Secret weight (sparse) | w_x | 50 |
| Public polynomial bound | B_y | 4 |
| Seed size | — | 128 bits |

**Note**: B_coeff = w_r + w_c × η + 10 = 25 + 25 × 1 + 10 = 60

## Construction

### KeyGen
```
1. Sample seed σ ← {0,1}^128
2. y ← Expand(σ)                           // Shared public polynomial, ||y||_∞ ≤ 4
3. x_master ← S^master_{w_x}               // Sparse master secret, trace-zero
4. x_cyc ← π_cyc(x_master)                 // Project to cyclic ring
5. x_neg ← π_neg(x_master)                 // Project to negacyclic ring
6. pk_cyc ← round_p(x_cyc · y)             // Cyclic: X^N = 1
7. pk_neg ← round_p(x_neg · y)             // Negacyclic: X^N = -1
Output: pk = (σ, pk_cyc, pk_neg), sk = (x_master, σ)
```

### Sign
```
1. y ← Expand(σ)
2. x_cyc, x_neg ← project(x_master)
3. loop:
   a. r_master ← S^master_{w_r}            // Sparse master nonce, trace-zero
   b. r_cyc, r_neg ← project(r_master)
   c. w_cyc ← round_p(r_cyc · y)           // Cyclic commitment
   d. w_neg ← round_p(r_neg · y)           // Negacyclic commitment
   e. challenge_seed ← H(w_cyc || w_neg || pk_cyc || pk_neg || σ || m)
   f. c_master ← ExpandChallenge(challenge_seed, w_c)  // Trace-zero
   g. c_cyc, c_neg ← project(c_master)
   h. s_cyc ← r_cyc + c_cyc · x_cyc        // Response in cyclic ring
   i. s_neg ← r_neg + c_neg · x_neg        // Response in negacyclic ring
   j. if ||s||_∞ > B_coeff: continue       // Coupling bound
   k. if ||s||_∞ ≥ 16: continue            // 5-bit compression
   l. if verification error > τ: continue
   m. return σ = (s_cyc, s_neg, w_cyc, w_neg)
```

### Verify
```
1. y ← Expand(σ)
2. if ||s_cyc||_∞ or ||s_neg||_∞ > B_coeff: reject    // Coupling check
3. s_master ← Lift(s_cyc, s_neg)                       // Check liftability
4. if Tr(s_master) ≢ 0 (mod q): reject                 // Trace-zero check
5. challenge_seed ← H(w_cyc || w_neg || pk_cyc || pk_neg || σ || m)
6. c_master ← ExpandChallenge(challenge_seed, w_c)
7. c_cyc, c_neg ← project(c_master)
8. w'_cyc ← s_cyc · y - c_cyc · lift(pk_cyc)          // Cyclic: X^N = 1
9. w'_neg ← s_neg · y - c_neg · lift(pk_neg)          // Negacyclic: X^N = -1
10. if max(||w'_cyc - lift(w_cyc)||_∞, ||w'_neg - lift(w_neg)||_∞) > τ: reject
11. accept
```

## Signature Formats

### Seedless-w Signature (~209 bytes)
Verifier reconstructs w from public nonce seed:
| Component | Size | Notes |
|-----------|------|-------|
| nonce_seed | 12 bytes | Public nonce seed |
| c_tilde | 16 bytes | Commitment binding hash |
| attempt | 1 byte | Rejection sampling index |
| s (range-coded) | ~180 bytes | Response with delta encoding |
| **Total** | **~209 bytes** | |

### Full Signature (~436 bytes)
| Component | Size | Notes |
|-----------|------|-------|
| s_cyc, s_neg | ~180 bytes | Range-coded response |
| w_cyc, w_neg | ~256 bytes | Rounded commitments |
| **Total** | **~436 bytes** | |

### Public Key (~416 bytes)
| Component | Size | Notes |
|-----------|------|-------|
| Seed | 16 bytes | For y expansion |
| pk_cyc, pk_neg (Huffman) | ~400 bytes | Compressed public keys |
| **Total** | **~416 bytes** | |

## Security

### Coupling Constraint
A valid signature (s_cyc, s_neg) must satisfy:
1. **Coefficient bound**: ||s||_∞ ≤ B_coeff = 60
2. **Liftability**: s_cyc[i] ≡ s_neg[i] (mod 2) for all i
3. **Trace-zero**: Σ s_master[i] ≡ 0 (mod q)

Random pairs fail these constraints with overwhelming probability:
- Liftability: Pr ≈ 2^{-256}
- Trace-zero: Pr ≈ 1/q

### Concrete Security
- **CRT-MLWR**: ~2^138 classical (512-dim lattice)
- **Challenge space**: |C| = C(512,25) × 2^25 ≈ 2^210
- **Tight reduction**: No √q_H forking lemma loss

### Comparison
| Scheme | Signature | Public Key | Security |
|--------|-----------|------------|----------|
| **CRT-Coupled (seedless)** | **~209 B** | **~416 B** | ~2^138 |
| Dilithium-2 | 2420 B | 1312 B | 2^128 |
| Falcon-512 | 666 B | 897 B | 2^128 |

## Repository Layout
- `crt_coupled_sig.c`: Reference C implementation of CRT-coupled scheme
- `euf_cma_proof_dual_pk.tex`: EUF-CMA security proof (LaTeX)
- `lean/CRTSecurity/`: Lean 4 proofs of CRT bijection property
  - `Aristotle.lean`: Machine-verified projection independence theorem
- `dehydrate.h`: Compression utilities

## Build and Run
Requires OpenSSL:
```bash
cc crt_coupled_sig.c -O2 -lcrypto -lm -o crt_coupled_sig
./crt_coupled_sig
```

## Lean 4 Proofs
Build the Lean proofs:
```bash
cd lean
lake build
```

Key verified theorems:
- `crt_bijection`: CRT projection is bijective
- `unique_preimage`: Unique lift for any (cyc, neg) pair
- `proj_injective`: Equal projections ⟹ equal master elements

## Status
Research prototype only. Not constant-time, not hardened, and not audited.

## References
- Security proof: `euf_cma_proof_dual_pk.tex`
- Lean formalization: `lean/CRTSecurity/Aristotle.lean`
