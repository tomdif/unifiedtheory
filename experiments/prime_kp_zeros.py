#!/usr/bin/env python3
"""
Combine the prime sum with K/P decomposition.

Compute A(k) = Σ_{p prime, p ≤ N} p^{ik} = Σ_p e^{ik log p}

K(k) = Re(A(k)) = Σ_p cos(k log p)
P(k) = Im(A(k)) = Σ_p sin(k log p)

K·P = Re(A) · Im(A) = the Berry-Keating observable of the prime sum

Questions:
1. Where does K·P = 0 as a function of k?
2. Where does |A(k)|² = K² + P² have minima?
3. Do either of these relate to the Riemann zeros γ_n?

Also compute the WEIGHTED version:
A_w(k) = Σ_n n^{-1/2} e^{ik log n} = ζ̄(1/2 - ik)
where the zeros of A_w are EXACTLY the Riemann zeros.
"""

import numpy as np
from sympy import primerange

# Known Riemann zeros
ZEROS = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
    67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
    79.337375, 82.910381, 84.735493, 87.425275, 88.809111,
    92.491899, 94.651344, 95.870634, 98.831194, 101.317851,
]


def compute_prime_kp(k_values, N_prime_max):
    """Compute the prime amplitude sum and its K/P decomposition."""
    primes = list(primerange(2, N_prime_max + 1))
    log_primes = np.log(np.array(primes, dtype=float))

    K = np.zeros(len(k_values))
    P = np.zeros(len(k_values))

    for j, k in enumerate(k_values):
        phases = k * log_primes
        K[j] = np.sum(np.cos(phases))
        P[j] = np.sum(np.sin(phases))

    return K, P


def compute_weighted_sum(k_values, N_max):
    """Compute A_w(k) = Σ_{n=1}^{N} n^{-1/2} e^{ik log n}.
    This is ζ̄(1/2 - ik) (conjugate of zeta on the critical line).
    Its zeros are at k = γ_n (Riemann zeros)."""
    ns = np.arange(1, N_max + 1, dtype=float)
    weights = ns ** (-0.5)
    log_ns = np.log(ns)

    K = np.zeros(len(k_values))
    P = np.zeros(len(k_values))

    for j, k in enumerate(k_values):
        phases = k * log_ns
        K[j] = np.sum(weights * np.cos(phases))
        P[j] = np.sum(weights * np.sin(phases))

    return K, P


def find_sign_changes(f, k_values):
    """Find k values where f changes sign."""
    changes = []
    for i in range(len(f) - 1):
        if f[i] * f[i+1] < 0:
            # Linear interpolation
            k0 = k_values[i] - f[i] * (k_values[i+1] - k_values[i]) / (f[i+1] - f[i])
            changes.append(k0)
    return np.array(changes)


def main():
    print("=" * 65)
    print("PRIME SUM + K/P DECOMPOSITION")
    print("=" * 65)

    # Fine k grid
    k_values = np.linspace(10, 105, 100000)

    # --- Test 1: Weighted sum (should give exact Riemann zeros) ---
    print("\n--- Weighted sum: A_w(k) = Σ n^{-1/2} e^{ik log n} ---")
    print("This IS ζ on the critical line. Zeros = Riemann zeros.")

    for N in [1000, 10000]:
        K_w, P_w = compute_weighted_sum(k_values, N)
        KP_w = K_w * P_w
        modulus2_w = K_w**2 + P_w**2

        # Find minima of |A_w|²
        from scipy.signal import argrelmin
        mins = argrelmin(modulus2_w, order=50)[0]
        min_k = k_values[mins]

        # Find K·P sign changes
        kp_zeros = find_sign_changes(KP_w, k_values)

        # Find K=0 crossings
        k_zeros = find_sign_changes(K_w, k_values)
        # Find P=0 crossings
        p_zeros = find_sign_changes(P_w, k_values)

        print(f"\n  N = {N}:")
        print(f"  |A_w|² minima (first 15):  {min_k[:15].round(3)}")
        print(f"  Riemann zeros (first 15):  {np.array(ZEROS[:15]).round(3)}")

        # Check matches
        matched = 0
        for z in ZEROS[:15]:
            if any(abs(min_k - z) < 0.5):
                matched += 1
        print(f"  Matches (within 0.5): {matched}/15")

    # --- Test 2: Unweighted prime sum ---
    print("\n\n--- Unweighted prime sum: A(k) = Σ_p e^{ik log p} ---")

    for N in [1000, 10000]:
        K_p, P_p = compute_prime_kp(k_values, N)
        KP_p = K_p * P_p
        modulus2_p = K_p**2 + P_p**2

        mins = argrelmin(modulus2_p, order=50)[0]
        min_k = k_values[mins]

        kp_zeros = find_sign_changes(KP_p, k_values)

        print(f"\n  N = {N} (π(N) = {len(list(primerange(2, N+1)))} primes):")
        print(f"  |A|² minima (first 15):    {min_k[:15].round(3)}")
        print(f"  K·P zeros (first 15):      {kp_zeros[:15].round(3)}")
        print(f"  Riemann zeros (first 15):  {np.array(ZEROS[:15]).round(3)}")

        # Check |A|² minima against zeros
        matched_mod = 0
        for z in ZEROS[:15]:
            if any(abs(min_k - z) < 1.0):
                matched_mod += 1

        # Check K·P zeros against Riemann zeros
        matched_kp = 0
        for z in ZEROS[:15]:
            if len(kp_zeros) > 0 and any(abs(kp_zeros - z) < 1.0):
                matched_kp += 1

        print(f"  |A|² minima matching zeros (±1.0): {matched_mod}/15")
        print(f"  K·P zeros matching Riemann zeros (±1.0): {matched_kp}/15")

    # --- Test 3: The K·P product specifically ---
    print("\n\n--- K·P = Re(A)·Im(A) analysis ---")
    print("K·P = 0 when either K=0 or P=0.")
    print("K=0: the cosine sum over primes vanishes")
    print("P=0: the sine sum over primes vanishes")
    print("These are the 'real' and 'imaginary' nodes of the prime sum.")

    K_p, P_p = compute_prime_kp(k_values, 10000)

    k_only = find_sign_changes(K_p, k_values)
    p_only = find_sign_changes(P_p, k_values)

    print(f"\n  K=0 crossings (first 20): {k_only[:20].round(3)}")
    print(f"  P=0 crossings (first 20): {p_only[:20].round(3)}")
    print(f"  Riemann zeros (first 20): {np.array(ZEROS[:20]).round(3)}")

    # Do K=0 or P=0 crossings correlate with Riemann zeros?
    matched_k = sum(1 for z in ZEROS[:20] if len(k_only) > 0 and min(abs(k_only - z)) < 0.5)
    matched_p = sum(1 for z in ZEROS[:20] if len(p_only) > 0 and min(abs(p_only - z)) < 0.5)

    print(f"\n  K=0 crossings near Riemann zeros (±0.5): {matched_k}/20")
    print(f"  P=0 crossings near Riemann zeros (±0.5): {matched_p}/20")

    # --- Test 4: The K·P zeros as a function (not just sign changes) ---
    # The argument of A(k) = arctan(P/K)
    # arg(A) changes by π at each zero of ζ (on the critical line)
    # For the prime sum, arg(A_p) might have similar behavior

    arg_p = np.arctan2(P_p, K_p)
    # Unwrap to get continuous phase
    arg_p_unwrapped = np.unwrap(arg_p)

    # The derivative of arg gives the "instantaneous frequency"
    # which should have spikes at the Riemann zeros
    darg = np.diff(arg_p_unwrapped) / np.diff(k_values)

    # Find peaks of |darg|
    from scipy.signal import find_peaks
    peaks, _ = find_peaks(np.abs(darg), height=np.std(darg)*3, distance=50)
    peak_k = k_values[peaks]

    print(f"\n  Phase jumps of prime sum (first 20): {peak_k[:20].round(3)}")
    print(f"  Riemann zeros (first 20):            {np.array(ZEROS[:20]).round(3)}")
    matched_phase = sum(1 for z in ZEROS[:20]
                        if len(peak_k) > 0 and min(abs(peak_k - z)) < 1.0)
    print(f"  Phase jumps near Riemann zeros (±1.0): {matched_phase}/20")

    print("\n" + "=" * 65)
    print("SUMMARY")
    print("=" * 65)


if __name__ == "__main__":
    main()
