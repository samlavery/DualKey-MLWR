# DualKey Module-LWR Signatures
*(dual public-key MLWR signatures with tight EUF-CMA proof, ~256B pk / ~256B sig)*

## TL;DR
-----

- Dual public-key Module-LWR signature scheme: two independent LWR equations on the same sparse secret (pk1, pk2).
- Aims for ~256-byte public keys and ~256-byte signatures via aggressively tuned Huffman encoding and low-entropy shaping of u.
- A single-constraint instance is estimated to cost around 2^168 classically; the dual-constraint instance (both pk1 and pk2 equations simultaneously) pushes the heuristic cost into the ~2^175 range.
- Full EasyCrypt EUF-CMA script: no `admit` anywhere in the EasyCrypt development; axioms are explicit, localized assumptions (Dual-MLWR, Dual-ZC-MSIS, RO model, algebraic interface).
- Structural knobs: pk-bound zero pattern on S and a small “extended challenge” payload in fixed compressed coordinates, both derived from (pk1 || pk2 || m) rather than u, to avoid forking-style losses and keep the reduction tight.
- Constructive cryptanalysis, parameter tuning, and proof-strengthening PRs are explicitly welcome.


## Overview

This repo contains a **dual public-key Module-LWR signature scheme**, a **fully scripted EasyCrypt proof of EUF-CMA security (no `admit` anywhere)**, and a **reference C implementation** targeting ~256-byte public keys and signatures via Huffman encoding.

The point is a **concrete-security, mechanically checked** treatment of a
non-standard dual-constraint MLWR signature: all game hops and simulation
details live in code, not just in a PDF.

## Security snapshot

- Security notion: EUF-CMA (existential unforgeability under chosen-message attack).
- Concrete bound (model):  
  `Adv_EUF-CMA ≲ 2^-128` up to standard polynomial factors, via a tight
  (non-forking) reduction.
- Assumptions:
  - Dual-MLWR (two Module-LWR constraints on the same sparse secret).
  - Dual-ZC-MSIS (zero-constrained MSIS variant; see paper).
- Challenge space size: `|C| ≈ 2^188`.
- Prototype parameters (N = 128, 4 trees):
  - Public key: ~256 bytes (Huffman-compressed pk1, pk2 + seed).
  - Signature: ~256 bytes (Huffman-compressed u and S).

Sizes are data-dependent: the C code enforces a **low-entropy filter on u**
to keep Huffman output within the 256B budget. The EasyCrypt model abstracts
compression and reasons only about the algebraic checks and bounds.

## Repository layout

- `euf_cma_proof_dual_pk.tex` / `.pdf`  
  Scheme description, security model, reductions, and parameter analysis.
- `module_lwr_256_256.c`  
  Reference C implementation (keygen / sign / verify + Huffman codec + attack harness).
- `DualPKSig.ec`  
  Top-level EasyCrypt EUF-CMA theorem and concrete bound.
- `DualPKSig_SimMain.ec`  
  Main simulation / composition script (hybrid games, inlining, bookkeeping).
- `DualPKSig_Simulation.ec`  
  Detailed game hops, couplings, and statistical distance bounds.
- `DualPKSig_Extraction.ec`  
  G1-forgery -> Dual-ZC-MSIS extractor.
- `DualPKSig_Reductions.ec`  
  Reductions to MLWR / MSIS-type assumptions.
- `dual_pk_verification.sage`  
  Parameter checks, lattice-estimator calls, and bound sanity checks.
- `Makefile`  
  Build / verify entry points.

## Construction sketch

### KeyGen

1. Sample an ultra-sparse ternary secret module `X` over the negacyclic ring
   (N = 128, 4 parallel trees).
2. Expand two matrices `Y1`, `Y2` from a single 32-byte seed using SHAKE256:
   `expand_Y_from_seed_idx(seed, 1)` and `expand_Y_from_seed_idx(seed, 2)`.
3. Compute
   - `pk1 = round_PK(X * Y1)`
   - `pk2 = round_PK(X * Y2)`
   then Huffman-compress `(pk1, pk2, seed)` into the public key.

### Sign

1. Derive a per-signature sparse nonce `R` from a PRF keyed by a secret seed.
2. Compute `u = round_PK(Y1 * R)`. Reject if `u` has more than 2 distinct values  
   (size and distribution shaping).
3. Derive:
   - a **challenge seed** from `(u, pk1, m)`,
   - a **zero seed** from `(pk1, pk2, m)`.
4. Hash the challenge seed to a sparse ternary challenge vector `c`, then set  
   `S = R + c * X (mod q)`.
5. Enforce **D-min** bounds on `D = c * X`:
   - `||D||_inf >= D_MIN_INF`,
   - `||D||_2 >= D_MIN_L2`.
6. From the zero seed `(pk1, pk2, m)`, derive a deterministic zero pattern and
   force `ZERO_COUNT` coordinates of `S` to 0 in each tree.
7. Derive a short **extended challenge** `e` with entries in `[-3, 3]` from the
   same zero seed and write it into a subset of the zeroed positions of `S`
   *after* LWR compression (so it survives the codec).
8. Huffman-encode `u_rounded` and the compressed `S` into the signature.

### Verify

1. Huffman-decode `u_rounded` and `S_compressed`.
2. Recompute the zero pattern from `(pk1, pk2, m)` and check:
   - all required zero positions in `S` are 0, and
   - the embedded extended-challenge slots match the recomputed `e`.
3. Lift `u_rounded`, `S_compressed`, `pk1`, `pk2` back to q.
4. Check the **Y1 equation** (u-linked residual):
   - `S_tilde * Y1 - u_tilde - c * pk1_tilde` is small in:
     - `L_inf`,
     - projected bands pi8 and pi9.
5. Check the **Y2 equation** (hidden-nonce residual):
   - `S_tilde * Y2 - c * pk2_tilde` is small on its own, again under raw and
     projected bounds. With `S = R + c * X`, this constrains `R * Y2`.

A valid forgery has to satisfy both LWR-style checks, the pk-bound zero pattern,
the embedded extended challenge, and the D-min constraints.

## What is structurally non-standard

This is not a vanilla Dilithium-style scheme.

### 1. Dual-constraint public key on one sparse secret

The public key encodes **two noisy equations on the same X**:

- `pk1 = round(X * Y1)`
- `pk2 = round(X * Y2)`

with `Y1` and `Y2` independently derived from a common seed. A forger has to
work in the **intersection of two noisy module lattices**. 

For the prototype (N = 128, 4 trees, ultra-sparse X), the in-repo estimator and
combinatorial bounds suggest:

- A single-constraint instance is estimated to cost around 2^168 classically; the dual-constraint instance (both pk1 and pk2 equations simultaneously) pushes the heuristic cost into the ~2^175 range.

### 2. Pk-bound, message-dependent zero pattern

The signer zeros `ZERO_COUNT` coordinates of `S` using only `(pk1, pk2, m)`,
and the verifier recomputes the same pattern. This:

- decouples the information loss from `u` (no circular dependency on `u`),
- makes the missing information a **public, verifiable function** of the key
  and message,
- is the structural knob the EasyCrypt proof uses to avoid a forking lemma
  and keep the reduction tight.

### 3. Extended challenge embedded after compression

A small vector `e` with entries in `[-3, 3]` is derived from `(pk1, pk2, m)`
and written into fixed, zeroed slots of `S` **after** LWR compression.
Verification recomputes `e` and checks those positions.

Any forged `S` must therefore:

- satisfy both LWR equations and all norm/projection bounds, and
- preserve this structured low-amplitude tag in specific coordinates.

This materially shrinks the forging surface in a way that the EasyCrypt
script can quantify.

### 4. Enforced non-degenerate challenge–secret interaction (D-min)

The implementation enforces explicit lower bounds on `D = c * X`:

- prevents `D = 0` and “almost-zero” flat directions where the dual-MLWR
  instance becomes weak,
- leaves honest signatures essentially unaffected under the chosen parameters,
- forces forgeries to pay the full MLWR/MSIS cost.

### 5. Aggressive u-entropy shaping

Rejecting any `u` with more than two distinct values:

- keeps `u` Huffman codes near the 256B target, and
- pushes `u` into an **extremely low-entropy regime** tuned to the codec and
  the EasyCrypt model.

Combined with the pk-bound zero pattern and extended challenge, this gives a
rigid “signature shape” that is hard to emulate without approximating the
honest distribution.

### 6. Dual residual checks

Verification enforces two distinct residuals:

1. **Y1 (u-linked) residual**  
   `S_tilde * Y1 - u_tilde - c * pk1_tilde`  
   bounded in `L_inf`, pi8, pi9.

2. **Y2 (hidden-nonce) residual**  
   `S_tilde * Y2 - c * pk2_tilde`  
   small on its own, effectively constraining `R * Y2`.

A forger must pass both residual tests plus all structural checks; this is where the empirical `~2^175` hardness estimate is coming from.

## Proof status (EasyCrypt)

- There are no `admit` tactics anywhere in the EasyCrypt development.
- Remaining axioms fall into:
  - abstract algebra interface (vector/matrix identities), and
  - explicit cryptographic assumptions (Dual-MLWR, Dual-ZC-MSIS, RO model, etc.).
- A separate “concrete algebra” module discharges the interface axioms.
- `DualPKSig.ec` and `DualPKSig_SimMain.ec` script the full reduction with
  explicit accounting for rounding and simulation losses.

If you care about the reduction graph, start from these two files and follow
the game hops.

## C prototype and attack harness

`module_lwr_256_256.c` is a **research prototype**, not a hardened library:

- schoolbook negacyclic multiplication (no NTT),
- OpenSSL SHAKE256 and `RAND_bytes`,
- not constant-time, no masking.

It includes a basic **attack harness** that:

- samples “honest-looking” `(u, S)` under the same constraints,
- enforces the pk-bound zero pattern and embedded extended challenge,
- measures how often the dual residual checks and projections accept by accident.

Instrumentation tracks:

- norms of `S` and `D` (`L_inf`, `L_2`),
- residual norms (raw, pi8, pi9),
- pk and signature size distributions and compression ratios.

## Build and run

- `make ec-check`  
  Run EasyCrypt and emit `.ok` stamps for the proof entry points.
- `make module_lwr_256_256`  
  Build the C prototype.
- `./module_lwr_256_256`  
  Run a keygen / sign / verify cycle and basic forgery experiments.
- `make paper`  
  Build the LaTeX proof document.
- `make clean`  
  Remove `.ok` stamps, `.eco` caches, and the C binary.

## Notes on use and disclosure

- This code and the associated proof may fall under **dual-use / export-control**
  regimes depending on jurisdiction. See `export-control.md` and `LICENSE.md`.
- The EasyCrypt development is intentionally modular:
  - swapping parameters,
  - tightening bounds,
  - or attacking the dual-constraint structure
  should be possible with local changes.


License
-------
Copyright (c) 2024-2026 Samuel Lavery <sam.lavery@gmail.com>
See LICENSE.md for terms.
