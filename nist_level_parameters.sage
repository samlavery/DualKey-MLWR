#!/usr/bin/env sage
"""
NIST Level Parameter Derivation for Module-LWR Signature
Based on actual implementation: module_lwr_256_256.c

Key insight: Huffman compression achieves ~256B PK / ~256B sig
"""

from sage.all import *

# ============================================================================
# CURRENT LEVEL I PARAMETERS (from module_lwr_256_256.c)
# ============================================================================

LEVEL_I = {
    'name': 'Level I (Current)',
    'n': 128,           # Ring dimension
    'k': 4,             # Module rank (NUM_TREES)
    'N': 512,           # Total dimension (n × k)
    'q': 4099,          # Base modulus (Q7)
    'p_pk': 128,        # PK compression (7 bits)
    'p_s': 2048,        # Signature compression (11 bits)
    'w_X': 48,          # Secret weight
    'w_R': 32,          # Nonce weight
    'w_c': 64,          # Challenge weight
    'z_pos': 64,        # Zero positions (ZERO_COUNT)
    'tau': 525,         # Verification bound
    # Actual compressed sizes (from implementation)
    'pk_bytes': 256,    # Huffman compressed
    'sig_bytes': 256,   # Huffman compressed (rejected if larger)
    'seed_bits': 256,
}

# ============================================================================
# PROPOSED NIST LEVEL III PARAMETERS
# Scale: ~1.5x dimension for ~192-bit security
# ============================================================================

LEVEL_III = {
    'name': 'Level III',
    'n': 192,           # Ring dimension (1.5× Level I)
    'k': 5,             # Module rank
    'N': 960,           # Total dimension
    'q': 4099,          # Keep same modulus
    'p_pk': 128,        # Same compression
    'p_s': 2048,
    'w_X': 72,          # Scale secret weight (1.5×48)
    'w_R': 48,          # Scale nonce weight (1.5×32)
    'w_c': 96,          # Scale challenge weight (1.5×64)
    'z_pos': 96,        # Scale zero positions (1.5×64)
    'tau': 787,         # Scale tau (1.5×525)
    # Estimated compressed sizes (Huffman scales sub-linearly)
    'pk_bytes': 384,    # ~1.5× Level I
    'sig_bytes': 384,   # ~1.5× Level I
    'seed_bits': 384,
}

# ============================================================================
# PROPOSED NIST LEVEL V PARAMETERS
# Scale: 2x dimension for ~256-bit security
# ============================================================================

LEVEL_V = {
    'name': 'Level V',
    'n': 256,           # Ring dimension (2× Level I)
    'k': 6,             # Module rank
    'N': 1536,          # Total dimension
    'q': 8191,          # Larger prime for bigger tau headroom
    'p_pk': 256,        # Adjusted for larger q
    'p_s': 4096,
    'w_X': 96,          # Scale secret weight (2×48)
    'w_R': 64,          # Scale nonce weight (2×32)
    'w_c': 128,         # Scale challenge weight (2×64)
    'z_pos': 128,       # Scale zero positions (2×64)
    'tau': 1050,        # Scale tau (2×525) - now fits with larger q
    # Estimated compressed sizes
    'pk_bytes': 512,    # ~2× Level I
    'sig_bytes': 512,   # ~2× Level I
    'seed_bits': 512,
}

# ============================================================================
# SECURITY ESTIMATION
# ============================================================================

def estimate_security(params):
    """
    Estimate security from combinatorial hardness of sparse secrets.

    Attack complexity: C(n, w_X) × 2^w_X per tree, times k trees
    This is the binding complexity for forging without knowing X.
    """
    n = params['n']
    k = params['k']
    w_X = params['w_X']
    w_c = params['w_c']
    z_pos = params['z_pos']

    # Per-tree combinatorial complexity: C(n, w_X) × 2^w_X
    per_tree_bits = float(log(binomial(n, w_X), 2)) + w_X

    # Total for k trees (independence amplification)
    total_combinatorial = per_tree_bits  # Conservative: single tree attack

    # Challenge space
    challenge_bits = float(log(binomial(n, w_c), 2)) + w_c

    # Zero-position constraint security
    # Forger must hit z_pos zeros per tree without knowing positions
    # Probability per coefficient: z_pos/n
    # For k trees: (z_pos/n)^(k*z_pos) ≈ negligible
    zero_barrier = k * z_pos * float(log(n/z_pos, 2))

    # Effective security: minimum of all bounds
    effective = min(total_combinatorial, challenge_bits)

    return {
        'combinatorial_per_tree': per_tree_bits,
        'total_combinatorial': total_combinatorial,
        'challenge_space': challenge_bits,
        'zero_barrier': zero_barrier,
        'effective': effective,
    }

# ============================================================================
# DUAL BARRIER CALCULATION
# ============================================================================

def compute_dual_barrier(params):
    """
    Compute dual amplification barrier.

    For Y2 constraint: ||Δ·Y2||_∞ ≤ 2τ for random Y2
    Probability: ((4τ+1)/q)^N
    """
    n = params['n']
    k = params['k']
    q = params['q']
    tau = params['tau']

    prob_per_coeff = float(RR(4*tau + 1) / RR(q))
    dim = k * n

    if prob_per_coeff < 1:
        barrier_bits = -dim * float(log(prob_per_coeff, 2))
    else:
        barrier_bits = 0

    return {
        'prob_per_coeff': prob_per_coeff,
        'dimension': dim,
        'barrier_bits': barrier_bits,
    }

# ============================================================================
# SIZE ANALYSIS
# ============================================================================

def analyze_sizes(params):
    """
    Analyze compressed sizes.

    Implementation uses Huffman compression to achieve target sizes.
    Raw sizes are much larger but compress well due to:
    1. Sparse structure (many zeros from z_pos)
    2. Small coefficient range after LWR rounding
    3. Rejection sampling ensures compressible signatures
    """
    n = params['n']
    k = params['k']
    p_pk = params['p_pk']
    p_s = params['p_s']
    z_pos = params['z_pos']

    bits_pk = int(ceil(log(p_pk, 2)))
    bits_s = int(ceil(log(p_s, 2)))

    # Raw sizes (uncompressed)
    pk_raw_bits = 2 * k * n * bits_pk  # pk1 + pk2
    sig_raw_bits = k * n * bits_pk + k * n * bits_s  # u_rounded + S

    pk_raw_bytes = pk_raw_bits // 8
    sig_raw_bytes = sig_raw_bits // 8

    # Compressed sizes (from params or estimated)
    pk_compressed = params['pk_bytes']
    sig_compressed = params['sig_bytes']

    # Compression ratios
    pk_ratio = pk_raw_bytes / pk_compressed if pk_compressed > 0 else 0
    sig_ratio = sig_raw_bytes / sig_compressed if sig_compressed > 0 else 0

    # Zero ratio in signature
    zero_ratio = z_pos / n

    return {
        'pk_raw_bytes': pk_raw_bytes,
        'pk_compressed_bytes': pk_compressed,
        'pk_compression_ratio': pk_ratio,
        'sig_raw_bytes': sig_raw_bytes,
        'sig_compressed_bytes': sig_compressed,
        'sig_compression_ratio': sig_ratio,
        'zero_ratio': zero_ratio,
    }

# ============================================================================
# ANALYSIS OUTPUT
# ============================================================================

def analyze_parameters(params):
    """Full analysis of a parameter set."""

    print("=" * 80)
    print(f"  {params['name']}")
    print("=" * 80)

    print(f"\n{'PARAMETERS':=^60}")
    print(f"  Ring dimension (n):      {params['n']}")
    print(f"  Module rank (k):         {params['k']}")
    print(f"  Total dimension (N):     {params['N']}")
    print(f"  Modulus (q):             {params['q']}")
    print(f"  Secret weight (w_X):     {params['w_X']}/{params['n']}")
    print(f"  Challenge weight (w_c):  {params['w_c']}/{params['n']}")
    print(f"  Zero positions:          {params['z_pos']}/{params['n']}")

    sec = estimate_security(params)
    print(f"\n{'SECURITY ESTIMATE':=^60}")
    print(f"  Combinatorial (per tree): ~2^{sec['combinatorial_per_tree']:.0f} bits")
    print(f"  Challenge space:          ~2^{sec['challenge_space']:.0f} bits")
    print(f"  Zero barrier:             ~2^{sec['zero_barrier']:.0f} bits")
    print(f"  EFFECTIVE SECURITY:       ~2^{sec['effective']:.0f} bits classical")

    barrier = compute_dual_barrier(params)
    print(f"\n{'DUAL AMPLIFICATION BARRIER':=^60}")
    print(f"  Per-coefficient prob:     {barrier['prob_per_coeff']:.4f}")
    print(f"  Barrier:                  2^-{barrier['barrier_bits']:.0f}")

    sizes = analyze_sizes(params)
    print(f"\n{'SIZE ANALYSIS':=^60}")
    print(f"  Public Key (raw):         {sizes['pk_raw_bytes']} bytes")
    print(f"  Public Key (Huffman):     {sizes['pk_compressed_bytes']} bytes")
    print(f"  PK compression ratio:     {float(sizes['pk_compression_ratio']):.1f}x")
    print(f"  Signature (raw):          {sizes['sig_raw_bytes']} bytes")
    print(f"  Signature (Huffman):      {sizes['sig_compressed_bytes']} bytes")
    print(f"  Sig compression ratio:    {float(sizes['sig_compression_ratio']):.1f}x")
    print(f"  Zero ratio in sig:        {float(sizes['zero_ratio'])*100:.0f}%")

    return {
        'params': params,
        'security': sec,
        'barrier': barrier,
        'sizes': sizes,
    }

# ============================================================================
# COMPARISON TABLE
# ============================================================================

def print_comparison():
    """Print comparison table."""

    results = []
    for params in [LEVEL_I, LEVEL_III, LEVEL_V]:
        results.append(analyze_parameters(params))

    print("\n")
    print("=" * 90)
    print("  COMPARISON TABLE")
    print("=" * 90)

    print(f"\n{'Parameter':<25} {'Level I':<20} {'Level III':<20} {'Level V':<20}")
    print("-" * 85)

    for key in ['n', 'k', 'N']:
        vals = [r['params'][key] for r in results]
        print(f"{key:<25} {vals[0]:<20} {vals[1]:<20} {vals[2]:<20}")

    print("-" * 85)

    # Security
    sec_vals = [f"~2^{int(r['security']['effective'])}" for r in results]
    print(f"{'Effective Security':<25} {sec_vals[0]:<20} {sec_vals[1]:<20} {sec_vals[2]:<20}")
    print(f"{'NIST Target':<25} 128 bits{'':<12} 192 bits{'':<12} 256 bits")

    print("-" * 85)

    # Sizes (compressed)
    pk_vals = [f"{r['sizes']['pk_compressed_bytes']} bytes" for r in results]
    sig_vals = [f"{r['sizes']['sig_compressed_bytes']} bytes" for r in results]
    print(f"{'Public Key (Huffman)':<25} {pk_vals[0]:<20} {pk_vals[1]:<20} {pk_vals[2]:<20}")
    print(f"{'Signature (Huffman)':<25} {sig_vals[0]:<20} {sig_vals[1]:<20} {sig_vals[2]:<20}")

    print("-" * 85)

    # Barrier
    barrier_vals = [f"2^-{int(r['barrier']['barrier_bits'])}" for r in results]
    print(f"{'Dual Barrier':<25} {barrier_vals[0]:<20} {barrier_vals[1]:<20} {barrier_vals[2]:<20}")

    print("\n")
    print("=" * 90)
    print("  COMPARISON WITH DILITHIUM (NIST STANDARD)")
    print("=" * 90)

    print(f"\n{'Scheme':<30} {'PK Size':<15} {'Sig Size':<15} {'Security':<15}")
    print("-" * 75)
    print("Dilithium2 (Level I)           1312 B          2420 B          ~128 bits")
    print("Dilithium3 (Level III)         1952 B          3293 B          ~192 bits")
    print("Dilithium5 (Level V)           2592 B          4595 B          ~256 bits")
    print("-" * 75)

    for i, r in enumerate(results):
        name = ['DualPK Level I', 'DualPK Level III', 'DualPK Level V'][i]
        pk = r['sizes']['pk_compressed_bytes']
        sig = r['sizes']['sig_compressed_bytes']
        sec = int(r['security']['effective'])
        print(f"{name:<30} {pk} B{'':<10} {sig} B{'':<10} ~{sec} bits")

    print("-" * 75)

    # Size improvement
    dil_pk = [1312, 1952, 2592]
    dil_sig = [2420, 3293, 4595]

    print(f"\nSize Improvement:")
    for i, level in enumerate(['Level I', 'Level III', 'Level V']):
        our_pk = results[i]['sizes']['pk_compressed_bytes']
        our_sig = results[i]['sizes']['sig_compressed_bytes']
        pk_ratio = float(dil_pk[i]) / float(our_pk)
        sig_ratio = float(dil_sig[i]) / float(our_sig)
        print(f"  {level}: PK {pk_ratio:.1f}x smaller, Sig {sig_ratio:.1f}x smaller")

    return results

# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    results = print_comparison()

    print("\n" + "=" * 90)
    print("  NOTES")
    print("=" * 90)
    print("""
    1. Sizes are HUFFMAN COMPRESSED (matching actual implementation)
       Raw sizes are 3-4x larger but compress well due to sparse structure.

    2. Security comes from:
       - Combinatorial hardness of sparse ternary secrets
       - Challenge space unpredictability
       - Zero-position barrier (dual amplification)

    3. Level III/V parameters are PROPOSED and need:
       - Implementation testing (Huffman compression ratios)
       - Rejection rate tuning (tau bounds)
       - Security verification (lattice-estimator)

    4. Compression achieved via:
       - 50% zeros per polynomial (z_pos/n)
       - Rejection sampling ensures small symbols
       - Huffman coding of remaining coefficients
    """)
