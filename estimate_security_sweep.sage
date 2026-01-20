#!/usr/bin/env sage
"""
Security parameter sweep for CRT-LWR Signature Scheme
"""

import sys
sys.path.insert(0, '/Users/samuellavery/work/lattice-estimator')

from estimator import LWE, ND
from sage.all import sqrt, floor, ceil, oo, log

# Practical bound on signatures attacker can collect
M_SAMPLES = 2**70  # ~10^21 signatures is very conservative

def estimate_params(N2, Q, P, SECRET_WEIGHT, tag=""):
    """Estimate security for given parameters"""

    # LWR -> LWE error conversion
    error_bound = Q / (2*P)
    a = -floor(error_bound)
    b = ceil(error_bound) - 1

    # Create LWE parameters
    try:
        params = LWE.Parameters(
            n=N2,
            q=Q,
            Xs=ND.SparseTernary(N2, p=SECRET_WEIGHT//2, m=SECRET_WEIGHT//2),
            Xe=ND.Uniform(a, b),
            m=M_SAMPLES,
            tag=tag
        )

        # Quick estimation
        result = LWE.estimate.rough(params, jobs=1, catch_exceptions=True)

        min_rop = float('inf')
        best_attack = None
        for attack, res in result.items():
            if 'rop' in res:
                rop = float(res['rop'])
                if rop < min_rop:
                    min_rop = rop
                    best_attack = attack

        sec_bits = float(log(min_rop, 2)) if min_rop < float('inf') else 0
        return sec_bits, best_attack, float(error_bound)

    except Exception as e:
        print(f"  Error: {e}")
        return 0, "error", 0.0

print("="*80)
print("CRT-LWR Security Parameter Sweep")
print("="*80)

# Current parameters
print("\n--- Current Parameters ---")
sec, attack, err = estimate_params(512, 251, 32, 50, "current")
print(f"N2=512, Q=251, P=32, h=50: {sec:.1f} bits ({attack}), err_bound={err:.2f}")

# Try larger Q values (must be prime ≡ 3 mod 8)
# Primes ≡ 3 mod 8: 251, 499, 1019, 2027, 3307, 4091, 8179, ...
print("\n--- Trying larger Q ---")
for Q in [499, 1019, 2027, 3307]:
    P = 32  # Keep P fixed
    sec, attack, err = estimate_params(512, Q, P, 50, f"Q={Q}")
    print(f"N2=512, Q={Q}, P=32, h=50: {sec:.1f} bits ({attack}), err_bound={err:.2f}")

# Try larger N2
print("\n--- Trying larger N2 ---")
for N2 in [768, 1024]:
    Q = 251
    P = 32
    h = int(N2 * 50 / 512)  # Scale secret weight
    sec, attack, err = estimate_params(N2, Q, P, h, f"N2={N2}")
    print(f"N2={N2}, Q=251, P=32, h={h}: {sec:.1f} bits ({attack}), err_bound={err:.2f}")

# Try larger Q with larger N2
print("\n--- Trying larger Q with larger N2 ---")
for Q in [1019, 2027]:
    for N2 in [512, 768]:
        P = 64  # Larger P for smaller error
        h = int(N2 * 50 / 512)
        sec, attack, err = estimate_params(N2, Q, P, h, f"Q={Q},N2={N2}")
        print(f"N2={N2}, Q={Q}, P=64, h={h}: {sec:.1f} bits ({attack}), err_bound={err:.2f}")

print("\n" + "="*80)
print("Target: 128 bits (NIST Level 1)")
print("="*80)
