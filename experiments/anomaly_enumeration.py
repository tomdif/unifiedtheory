#!/usr/bin/env python3
"""
Enumerate anomaly-free generation structures for SU(3) × SU(2) × U(1).

For each combination of SU(3) × SU(2) representations forming a
"generation" (5 fermion types), check whether anomaly cancellation
has nontrivial hypercharge solutions.

Anomaly conditions (all left-handed Weyl fermions):
1. SU(3)³:          Σ_i A3_i · d2_i = 0            (Y-independent)
2. SU(3)² × U(1):   Σ_i T3_i · d2_i · Y_i = 0
3. SU(2)² × U(1):   Σ_i d3_i · T2_i · Y_i = 0
4. Gravitational:    Σ_i d3_i · d2_i · Y_i = 0
5. U(1)³:           Σ_i d3_i · d2_i · Y_i³ = 0

Representation data for SU(3):
  Rep     dim  Dynkin_index  Cubic_anomaly
  1       1    0             0
  3       3    1/2           1
  3̄       3    1/2           -1
  6       6    5/2           7
  6̄       6    5/2           -7
  8       8    3             0
  10      10   15/2          27
  10̄      10   15/2          -27
  15      15   10            35    (symmetric tensor)
  15̄      15   10            -35

Representation data for SU(2):
  Rep  dim  Dynkin_index
  1    1    0
  2    2    1/2
  3    3    2
  4    4    5
  5    5    10
"""

from fractions import Fraction
from itertools import product as cartprod
import numpy as np
from numpy.polynomial import polynomial as P

# SU(3) representations: (name, dim, dynkin_index, cubic_anomaly)
SU3_REPS = [
    ("1",   1,  Fraction(0),    0),
    ("3",   3,  Fraction(1,2),  1),
    ("3b",  3,  Fraction(1,2),  -1),
    ("6",   6,  Fraction(5,2),  7),
    ("6b",  6,  Fraction(5,2),  -7),
    ("8",   8,  Fraction(3),    0),
]

# SU(2) representations: (name, dim, dynkin_index)
SU2_REPS = [
    ("1",  1, Fraction(0)),
    ("2",  2, Fraction(1,2)),
    ("3",  3, Fraction(2)),
]

def check_generation(species_list):
    """Check if a generation structure admits anomaly-free hypercharges.

    species_list: list of (su3_rep, su2_rep) tuples, each being
                  (name3, d3, T3, A3, name2, d2, T2)

    Returns: (is_anomaly_free, n_solutions, solutions_description)
    """
    n = len(species_list)

    # Extract data
    d3 = [s[1] for s in species_list]
    T3 = [s[2] for s in species_list]
    A3 = [s[3] for s in species_list]
    d2 = [s[5] for s in species_list]
    T2 = [s[6] for s in species_list]

    # Condition 1: SU(3)³ (Y-independent)
    su3_cubic = sum(A3[i] * d2[i] for i in range(n))
    if su3_cubic != 0:
        return False, 0, "SU(3)³ fails"

    # The remaining conditions are linear/cubic in Y_i.
    # Coefficients for the linear conditions:
    # Cond 2: SU(3)²×U(1): coeff_i = T3_i * d2_i
    c2 = [float(T3[i] * d2[i]) for i in range(n)]
    # Cond 3: SU(2)²×U(1): coeff_i = d3_i * T2_i
    c3 = [float(d3[i] * T2[i]) for i in range(n)]
    # Cond 4: gravitational: coeff_i = d3_i * d2_i
    c4 = [float(d3[i] * d2[i]) for i in range(n)]
    # Cond 5: U(1)³: coeff_i = d3_i * d2_i (multiplied by Y_i³)
    c5 = [float(d3[i] * d2[i]) for i in range(n)]

    # Build the linear constraint matrix (conditions 2,3,4)
    A_mat = np.array([c2, c3, c4])

    # Check rank — how many Y_i are determined?
    rank = np.linalg.matrix_rank(A_mat, tol=1e-12)

    if rank >= n:
        # Only trivial solution Y = 0
        return False, 0, "Only trivial solution"

    # Find null space of the linear conditions
    # Using SVD
    U, S, Vt = np.linalg.svd(A_mat, full_matrices=True)
    null_dim = n - rank
    null_space = Vt[rank:]  # rows of Vt corresponding to zero singular values

    if null_dim == 0:
        return False, 0, "Only trivial solution"

    # Now check the cubic condition on the null space.
    # If Y = Σ_k t_k * v_k where v_k span the null space,
    # the cubic condition becomes a cubic polynomial in the t_k.

    if null_dim == 1:
        # Y = t * v for some vector v
        v = null_space[0]
        # Cubic: Σ c5_i * (t*v_i)³ = t³ * Σ c5_i * v_i³ = 0
        cubic_coeff = sum(c5[i] * v[i]**3 for i in range(n))
        if abs(cubic_coeff) < 1e-10:
            # Cubic is automatically satisfied for all t!
            return True, float('inf'), f"1-param family (null_dim=1, cubic auto)"
        else:
            # Only t=0 satisfies cubic
            return False, 0, f"Cubic forces t=0 (coeff={cubic_coeff:.6f})"

    elif null_dim == 2:
        # Y = s*u + t*v
        u_vec, v_vec = null_space[0], null_space[1]
        # Cubic: Σ c5_i * (s*u_i + t*v_i)³ = 0
        # Expand: s³·Σc5·u³ + 3s²t·Σc5·u²v + 3st²·Σc5·uv² + t³·Σc5·v³ = 0
        # This is a homogeneous cubic in (s,t).
        coeff_s3 = sum(c5[i] * u_vec[i]**3 for i in range(n))
        coeff_s2t = 3 * sum(c5[i] * u_vec[i]**2 * v_vec[i] for i in range(n))
        coeff_st2 = 3 * sum(c5[i] * u_vec[i] * v_vec[i]**2 for i in range(n))
        coeff_t3 = sum(c5[i] * v_vec[i]**3 for i in range(n))

        # If all coefficients are ~0, cubic is automatically satisfied
        if all(abs(c) < 1e-10 for c in [coeff_s3, coeff_s2t, coeff_st2, coeff_t3]):
            return True, float('inf'), f"2-param family (cubic auto)"

        # Otherwise, the cubic defines a curve in (s,t) space.
        # Check if it has nontrivial real solutions.
        # Set t=1: coeff_s3·s³ + coeff_s2t·s² + coeff_st2·s + coeff_t3 = 0
        if abs(coeff_s3) > 1e-10:
            coeffs = [coeff_t3, coeff_st2, coeff_s2t, coeff_s3]
            roots = np.roots([coeff_s3, coeff_s2t, coeff_st2, coeff_t3])
            real_roots = [r.real for r in roots if abs(r.imag) < 1e-8]
            if real_roots:
                return True, len(real_roots), f"2-param null, {len(real_roots)} cubic branches"
            else:
                # Also check s=0 (t arbitrary) or t=0 (s arbitrary)
                if abs(coeff_t3) < 1e-10:
                    return True, 1, "2-param null, t=0 branch"
                return False, 0, "No real roots of cubic"
        else:
            # coeff_s3 ≈ 0, so it's at most quadratic in s
            return True, 1, f"2-param null, degenerate cubic"

    else:
        # null_dim >= 3: many free parameters, likely has solutions
        return True, float('inf'), f"{null_dim}-param family"


def enumerate_sm_like():
    """Enumerate SM-like generation structures.

    SM-like: 5 species types with the structure
    Q: (R3_Q, R2_Q)  — "quark doublet" analog
    u: (R3_u, 1)     — "up singlet" analog (SU(2) singlet)
    d: (R3_d, 1)     — "down singlet" analog (SU(2) singlet)
    L: (1, R2_L)     — "lepton doublet" analog (SU(3) singlet)
    e: (1, 1)        — "charged lepton" analog (both singlets)

    This structure ensures:
    - "Quarks" carry color charge, "leptons" don't
    - The SU(2) structure has doublets and singlets
    """

    results = []

    # SU(3) reps for quarks (non-trivial)
    su3_color = [(n,d,T,A) for (n,d,T,A) in SU3_REPS if d > 1]
    # SU(2) reps for doublets (non-trivial)
    su2_weak = [(n,d,T) for (n,d,T) in SU2_REPS if d > 1]

    for r3Q in su3_color:
        for r2Q in su2_weak:
            for r3u in su3_color:
                for r3d in su3_color:
                    for r2L in su2_weak:
                        # Build the 5 species
                        # Q: (r3Q, r2Q)
                        # u: (r3u, singlet)
                        # d: (r3d, singlet)
                        # L: (singlet, r2L)
                        # e: (singlet, singlet)
                        su3_singlet = SU3_REPS[0]  # (1, 1, 0, 0)
                        su2_singlet = SU2_REPS[0]  # (1, 1, 0)

                        species = [
                            (*r3Q, *r2Q),      # Q
                            (*r3u, *su2_singlet),  # u
                            (*r3d, *su2_singlet),  # d
                            (*su3_singlet, *r2L),  # L
                            (*su3_singlet, *su2_singlet),  # e
                        ]

                        ok, nsol, desc = check_generation(species)

                        label = (f"Q=({r3Q[0]},{r2Q[0]}) "
                                f"u=({r3u[0]},1) "
                                f"d=({r3d[0]},1) "
                                f"L=(1,{r2L[0]}) "
                                f"e=(1,1)")

                        if ok:
                            results.append((label, nsol, desc))

    return results


def main():
    print("=" * 70)
    print("ANOMALY-FREE GENERATION ENUMERATION")
    print("SU(3) × SU(2) × U(1), SM-like structure")
    print("SU(3) reps: 1, 3, 3b, 6, 6b, 8")
    print("SU(2) reps: 1, 2, 3")
    print("=" * 70)

    results = enumerate_sm_like()

    print(f"\nTotal anomaly-free structures found: {len(results)}")
    print()

    # Group by whether they use only fundamentals
    fund_only = []
    higher_reps = []

    for label, nsol, desc in results:
        uses_higher = any(r in label for r in ["6", "6b", "8", "10"])
        # Check if it uses only fundamentals (3, 3b for SU(3); 2 for SU(2))
        is_fundamental = not uses_higher

        if is_fundamental:
            fund_only.append((label, nsol, desc))
        else:
            higher_reps.append((label, nsol, desc))

    print(f"Using only fundamental reps: {len(fund_only)}")
    for label, nsol, desc in fund_only:
        print(f"  {label}")
        print(f"    → {desc}")

    print(f"\nUsing higher representations: {len(higher_reps)}")
    for label, nsol, desc in higher_reps[:20]:
        print(f"  {label}")
        print(f"    → {desc}")
    if len(higher_reps) > 20:
        print(f"  ... and {len(higher_reps) - 20} more")

    print()
    print("=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    if len(fund_only) > 0 and len(higher_reps) > 0:
        print(f"Anomaly cancellation alone does NOT select fundamentals.")
        print(f"There are {len(higher_reps)} anomaly-free structures with higher reps.")
        print(f"A minimality/elementary-defect hypothesis IS needed on top.")
    elif len(higher_reps) == 0:
        print(f"Only fundamental representations are anomaly-free!")
        print(f"This would be a strong uniqueness result.")

    # Now check: among fundamental-only structures, how many are there?
    print()
    print("=" * 70)
    print("FUNDAMENTAL-ONLY ANALYSIS")
    print("=" * 70)
    print(f"Fundamental-only anomaly-free structures: {len(fund_only)}")
    if len(fund_only) <= 10:
        for label, nsol, desc in fund_only:
            print(f"  {label}: {desc}")

    # The SM is Q=(3,2) u=(3b,1) d=(3b,1) L=(1,2) e=(1,1)
    sm_label = "Q=(3,2) u=(3b,1) d=(3b,1) L=(1,2) e=(1,1)"
    print(f"\nSM structure: {sm_label}")
    sm_found = any(sm_label in label for label, _, _ in fund_only)
    print(f"SM found in catalog: {sm_found}")


if __name__ == "__main__":
    main()
