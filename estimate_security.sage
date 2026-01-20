#!/usr/bin/env sage
"""
Security estimation for CRT-LWR Signature Scheme using lattice-estimator

CRT-LWR Parameters:
- Master ring dimension N2 = 512
- Component ring dimension N = 256
- Modulus Q = 251
- Rounding modulus P = 32
- Secret: sparse ternary, weight ~50 in 512 coefficients
- LWR error: uniform in [-Q/(2P), Q/(2P)] ≈ [-3.9, 3.9]

For LWR -> LWE conversion:
The rounding operation b = round(a*s * P/Q) creates error e ≈ Uniform(-Q/(2P), Q/(2P))
"""

import sys
sys.path.insert(0, '/Users/samuellavery/work/lattice-estimator')

from estimator import LWE, ND
from sage.all import sqrt, floor, ceil

# CRT-LWR Parameters
N2 = 512        # Master ring dimension (attack surface)
N = 256         # Component ring dimension
Q = 251         # Prime modulus
P = 32          # Rounding modulus
SECRET_WEIGHT = 50  # Sparse secret Hamming weight

# LWR -> LWE error conversion
# Rounding error is approximately uniform in [-Q/(2P), Q/(2P)]
# For Q=251, P=32: error range = [-3.92, 3.92], roughly [-4, 4]
error_bound = Q / (2*P)
print(f"LWR error bound: Q/(2P) = {float(error_bound):.2f}")

# Uniform error in [-4, 3] (integer bounds)
a = -floor(error_bound)
b = ceil(error_bound) - 1  # Conservative bound
print(f"Error distribution: Uniform({a}, {b})")

# Secret distribution: sparse ternary in {-1, 0, 1}
# Weight ~50 means ~50 non-zero positions out of 512
print(f"Secret distribution: SparseTernary(n={N2}, weight={SECRET_WEIGHT})")

# Number of samples available to attacker
# For signature scheme: attacker can collect arbitrary number of signatures
# Each signature provides one LWE sample (the commitment w = round(r*y))
# Conservative assumption: attacker can collect many signatures
# Use infinity for unbounded, or a practical limit
from sage.all import oo
m = oo  # Attacker can observe arbitrary signatures

print("\n" + "="*70)
print("CRT-LWR Security Estimation")
print("="*70)
print(f"Parameters: n={N2}, q={Q}, P={P}")
print(f"Secret: SparseTernary(n={N2}, h={SECRET_WEIGHT})")
print(f"Error: Uniform({a}, {b})")
print(f"Samples: m={m}")
print("="*70)

# Create LWE parameters
# SparseTernary(n, p, m): n=dim, p=+1 count, m=-1 count
# For symmetric ternary with weight h: p = m = h/2
params = LWE.Parameters(
    n=N2,
    q=Q,
    Xs=ND.SparseTernary(N2, p=SECRET_WEIGHT//2, m=SECRET_WEIGHT//2),
    Xe=ND.Uniform(a, b),
    m=m,
    tag="CRT-LWR-512"
)

print(f"\nLWE Parameters: {params}")
print()

# Run security estimation
print("Running security estimation (this may take a moment)...")
print()

try:
    result = LWE.estimate(params, jobs=1)

    print("\n" + "="*70)
    print("Summary")
    print("="*70)

    # Find minimum security level
    min_rop = float('inf')
    best_attack = None
    for attack, res in result.items():
        if 'rop' in res and float(res['rop']) < min_rop:
            min_rop = float(res['rop'])
            best_attack = attack

    from sage.all import log
    if best_attack:
        print(f"Best attack: {best_attack}")
        print(f"Security level: {float(log(min_rop, 2)):.1f} bits")
    else:
        print("No successful attacks found")

except Exception as e:
    print(f"Error during estimation: {e}")
    import traceback
    traceback.print_exc()

print("\n" + "="*70)
print("Comparison with NIST schemes")
print("="*70)
print("Kyber-512:  ~118 bits (n=512, q=3329)")
print("Dilithium2: ~118 bits (MSIS, n=1024, q=8380417)")
print("Falcon-512: ~108 bits (NTRU, n=512, q=12289)")
