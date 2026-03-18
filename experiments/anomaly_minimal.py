#!/usr/bin/env python3
"""
Find ALL anomaly-free sets of left-handed Weyl fermions using only
fundamental/trivial representations of SU(3) × SU(2).

Species types (fundamentals + trivial + conjugates):
  Type    SU(3)  SU(2)   d3  d2  T3    T2    A3
  (3,2)     3      2      3   2  1/2   1/2    1
  (3b,2)    3b     2      3   2  1/2   1/2   -1
  (3,1)     3      1      3   1  1/2    0     1
  (3b,1)    3b     1      3   1  1/2    0    -1
  (1,2)     1      2      1   2   0    1/2    0
  (1,1)     1      1      1   1   0     0     0

A "generation" is a multiset specifying how many of each type,
plus U(1) hypercharges satisfying all 5 anomaly conditions.

Enumerate all multisets with total species count ≤ MAX_SPECIES.
For each, check if anomaly conditions have nontrivial Y solutions.
"""

import numpy as np
from itertools import product as cartprod
from fractions import Fraction

# Species types: (label, d3, d2, T3, T2, A3)
TYPES = [
    ("(3,2)",   3, 2, 0.5, 0.5,  1),
    ("(3b,2)",  3, 2, 0.5, 0.5, -1),
    ("(3,1)",   3, 1, 0.5, 0.0,  1),
    ("(3b,1)",  3, 1, 0.5, 0.0, -1),
    ("(1,2)",   1, 2, 0.0, 0.5,  0),
    ("(1,1)",   1, 1, 0.0, 0.0,  0),
]

def check_anomaly(counts):
    """Given counts = [n1, n2, ..., n6] for each species type,
    check if anomaly conditions have nontrivial Y solutions.

    Each species type i appears counts[i] times, each instance
    with the SAME hypercharge Y_i (all instances of a type have
    the same quantum numbers, hence same Y).

    Returns (has_nontrivial, null_dim, cubic_info)
    """
    # Number of distinct Y variables = number of types with nonzero count
    active = [(i, counts[i]) for i in range(6) if counts[i] > 0]
    n_vars = len(active)

    if n_vars == 0:
        return False, 0, "empty"

    # Build anomaly coefficients for each active type
    # For type i appearing n_i times with hypercharge Y_i:
    # Each instance contributes the same amount, so we get n_i × (contribution per instance)

    # Condition 1: SU(3)³ (Y-independent)
    # Σ_i n_i * A3_i * d2_i = 0
    su3_cubic = sum(counts[i] * TYPES[i][5] * TYPES[i][2] for i in range(6))
    if abs(su3_cubic) > 1e-10:
        return False, 0, "SU(3)³ fails"

    # Linear conditions on Y:
    # Cond 2: SU(3)²×U(1): Σ_i n_i * T3_i * d2_i * Y_i = 0
    # Cond 3: SU(2)²×U(1): Σ_i n_i * d3_i * T2_i * Y_i = 0
    # Cond 4: Gravitational: Σ_i n_i * d3_i * d2_i * Y_i = 0

    c2 = [counts[i] * TYPES[i][3] * TYPES[i][2] for i in range(6)]  # n*T3*d2
    c3 = [counts[i] * TYPES[i][1] * TYPES[i][4] for i in range(6)]  # n*d3*T2
    c4 = [counts[i] * TYPES[i][1] * TYPES[i][2] for i in range(6)]  # n*d3*d2

    # Only keep active variables
    active_indices = [i for i, _ in active]
    c2_active = [c2[i] for i in active_indices]
    c3_active = [c3[i] for i in active_indices]
    c4_active = [c4[i] for i in active_indices]

    A_mat = np.array([c2_active, c3_active, c4_active])

    rank = np.linalg.matrix_rank(A_mat, tol=1e-10)
    null_dim = n_vars - rank

    if null_dim <= 0:
        return False, 0, "only trivial"

    # Find null space
    U, S, Vt = np.linalg.svd(A_mat, full_matrices=True)
    null_vecs = Vt[rank:]

    # Cubic condition: Σ_i n_i * d3_i * d2_i * Y_i³ = 0
    c5 = [counts[i] * TYPES[i][1] * TYPES[i][2] for i in active_indices]

    if null_dim == 1:
        v = null_vecs[0]
        # Cubic: t³ * Σ c5_i * v_i³ = 0
        cubic_coeff = sum(c5[j] * v[j]**3 for j in range(n_vars))
        if abs(cubic_coeff) < 1e-10:
            return True, 1, "1-param, cubic auto"
        else:
            return False, 0, "cubic kills it"

    elif null_dim == 2:
        u_v, v_v = null_vecs[0], null_vecs[1]
        # Cubic in (s,t): homogeneous degree 3
        c_s3 = sum(c5[j] * u_v[j]**3 for j in range(n_vars))
        c_s2t = 3*sum(c5[j] * u_v[j]**2 * v_v[j] for j in range(n_vars))
        c_st2 = 3*sum(c5[j] * u_v[j] * v_v[j]**2 for j in range(n_vars))
        c_t3 = sum(c5[j] * v_v[j]**3 for j in range(n_vars))

        if all(abs(c) < 1e-10 for c in [c_s3, c_s2t, c_st2, c_t3]):
            return True, 2, "2-param, cubic auto"

        # Check for real solutions of cubic in s/t
        if abs(c_s3) > 1e-10:
            roots = np.roots([c_s3, c_s2t, c_st2, c_t3])
            real_roots = sum(1 for r in roots if abs(r.imag) < 1e-6)
            if real_roots > 0:
                return True, 2, f"2-param, {real_roots} branches"
        # Check t=0 branch
        if abs(c_s3) < 1e-10:
            return True, 2, "2-param, degenerate"
        if abs(c_t3) < 1e-10:
            return True, 2, "2-param, t=0 branch"
        return False, 0, "no real cubic roots"

    else:
        return True, null_dim, f"{null_dim}-param"


def total_species(counts):
    """Total number of fermion species (counting multiplicities from SU(3)×SU(2) dims)."""
    return sum(counts[i] * TYPES[i][1] * TYPES[i][2] for i in range(6))


def total_types(counts):
    """Number of distinct nonzero types."""
    return sum(1 for c in counts if c > 0)


def main():
    MAX_PER_TYPE = 5  # Max instances of each type
    MAX_TOTAL = 20    # Max total species (weighted by d3*d2)

    print("=" * 70)
    print("ANOMALY-FREE FERMION SETS: FUNDAMENTALS ONLY")
    print(f"Species types: {[t[0] for t in TYPES]}")
    print(f"Max per type: {MAX_PER_TYPE}, Max total species: {MAX_TOTAL}")
    print("=" * 70)

    results = []

    # Enumerate all multisets
    for n1 in range(MAX_PER_TYPE + 1):
        for n2 in range(MAX_PER_TYPE + 1):
            for n3 in range(MAX_PER_TYPE + 1):
                for n4 in range(MAX_PER_TYPE + 1):
                    for n5 in range(MAX_PER_TYPE + 1):
                        for n6 in range(MAX_PER_TYPE + 1):
                            counts = [n1, n2, n3, n4, n5, n6]

                            # Skip trivial
                            if all(c == 0 for c in counts):
                                continue

                            # Skip if total species too large
                            ts = total_species(counts)
                            if ts > MAX_TOTAL or ts == 0:
                                continue

                            # Must have at least one colored AND one uncolored
                            # to be physically interesting (otherwise no
                            # quark-lepton structure)
                            has_color = any(counts[i] > 0 for i in [0,1,2,3])
                            has_uncolor = any(counts[i] > 0 for i in [4,5])

                            ok, nd, info = check_anomaly(counts)

                            if ok:
                                label = " + ".join(
                                    f"{counts[i]}×{TYPES[i][0]}"
                                    for i in range(6) if counts[i] > 0
                                )
                                results.append({
                                    'counts': counts,
                                    'label': label,
                                    'total': ts,
                                    'n_types': total_types(counts),
                                    'null_dim': nd,
                                    'info': info,
                                    'has_color': has_color,
                                    'has_uncolor': has_uncolor,
                                })

    # Sort by total species count
    results.sort(key=lambda r: (r['total'], r['n_types']))

    print(f"\nTotal anomaly-free sets found: {len(results)}")

    # Filter to physically interesting: both colored and uncolored matter
    physical = [r for r in results if r['has_color'] and r['has_uncolor']]
    print(f"With both colored + uncolored matter: {len(physical)}")

    print(f"\n--- All anomaly-free sets (sorted by size) ---")
    for r in results[:50]:
        marker = ""
        if r['counts'] == [1, 0, 0, 2, 1, 1]:
            marker = " ← SM GENERATION"
        phys = "  [Q+L]" if (r['has_color'] and r['has_uncolor']) else ""
        print(f"  {r['total']:2d} species: {r['label']}{marker}{phys}")
        print(f"           {r['info']}")
    if len(results) > 50:
        print(f"  ... and {len(results) - 50} more")

    # Find the SM
    print(f"\n--- SM generation ---")
    # SM: 1×(3,2) + 2×(3b,1) + 1×(1,2) + 1×(1,1)
    sm_counts = [1, 0, 0, 2, 1, 1]
    sm_total = total_species(sm_counts)
    sm_ok, sm_nd, sm_info = check_anomaly(sm_counts)
    print(f"SM counts: {sm_counts}")
    print(f"SM total species: {sm_total}")
    print(f"SM anomaly-free: {sm_ok}, null_dim={sm_nd}, {sm_info}")

    # Find minimal anomaly-free sets with both color and uncolored matter
    print(f"\n--- Minimal anomaly-free sets with quark+lepton structure ---")
    if physical:
        min_total = physical[0]['total']
        minimal = [r for r in physical if r['total'] == min_total]
        print(f"Minimum species count: {min_total}")
        print(f"Number of minimal sets: {len(minimal)}")
        for r in minimal:
            marker = " ← SM" if r['counts'] == sm_counts else ""
            print(f"  {r['label']}{marker}")
            print(f"    {r['info']}")

    # Is the SM the unique minimal?
    print(f"\n--- Is the SM the unique minimal anomaly-free set? ---")
    if physical:
        min_total = physical[0]['total']
        if min_total == sm_total:
            minimal_sm = [r for r in physical if r['total'] == min_total]
            if len(minimal_sm) == 1 and minimal_sm[0]['counts'] == sm_counts:
                print("YES — the SM is the unique minimal anomaly-free set!")
            else:
                print(f"NO — there are {len(minimal_sm)} minimal sets at size {min_total}")
        elif min_total < sm_total:
            print(f"NO — there are smaller anomaly-free sets (size {min_total} < SM size {sm_total})")
        else:
            print(f"The SM (size {sm_total}) is smaller than all others (min {min_total})")

    print()
    print("=" * 70)


if __name__ == "__main__":
    main()
