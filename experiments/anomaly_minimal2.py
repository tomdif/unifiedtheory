#!/usr/bin/env python3
"""
Find ALL anomaly-free sets of left-handed Weyl fermions using only
fundamental/trivial representations of SU(3) × SU(2).

FIXED: each instance of a type gets its OWN hypercharge Y_i.
(In the SM, both ū and d̄ are type (3b,1) but have different Y.)

Species types: (3,2), (3b,2), (3,1), (3b,1), (1,2), (1,1)
"""

import numpy as np

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
    """Given counts = [n0,...,n5] for each species type,
    EACH INSTANCE gets its own Y variable.
    Total Y variables = sum(counts).
    """
    total_vars = sum(counts)
    if total_vars == 0:
        return False, 0, "empty"

    # Build list of species: for each type i, counts[i] instances
    species = []
    for i in range(6):
        for _ in range(counts[i]):
            species.append(TYPES[i])

    n = len(species)  # = total_vars

    # Condition 1: SU(3)³ (Y-independent)
    su3_cubic = sum(s[5] * s[2] for s in species)  # A3 * d2
    if abs(su3_cubic) > 1e-10:
        return False, 0, "SU(3)³ fails"

    # Linear conditions: build coefficient matrix
    # Cond 2: SU(3)²×U(1): coeff_j = T3_j * d2_j
    c2 = [s[3] * s[2] for s in species]
    # Cond 3: SU(2)²×U(1): coeff_j = d3_j * T2_j
    c3 = [s[1] * s[4] for s in species]
    # Cond 4: Gravitational: coeff_j = d3_j * d2_j
    c4 = [s[1] * s[2] for s in species]

    A_mat = np.array([c2, c3, c4])
    rank = np.linalg.matrix_rank(A_mat, tol=1e-10)
    null_dim = n - rank

    if null_dim <= 0:
        return False, 0, "only trivial"

    # Null space
    U, S, Vt = np.linalg.svd(A_mat, full_matrices=True)
    null_vecs = Vt[rank:]

    # Cubic: Σ d3_j * d2_j * Y_j³ = 0
    c5 = [s[1] * s[2] for s in species]

    if null_dim == 1:
        v = null_vecs[0]
        cubic = sum(c5[j] * v[j]**3 for j in range(n))
        if abs(cubic) < 1e-10:
            return True, 1, "1-param, cubic auto"
        else:
            return False, 0, "cubic kills it"

    elif null_dim == 2:
        u_v, v_v = null_vecs[0], null_vecs[1]
        c_s3  = sum(c5[j] * u_v[j]**3 for j in range(n))
        c_s2t = 3*sum(c5[j] * u_v[j]**2 * v_v[j] for j in range(n))
        c_st2 = 3*sum(c5[j] * u_v[j] * v_v[j]**2 for j in range(n))
        c_t3  = sum(c5[j] * v_v[j]**3 for j in range(n))

        if all(abs(c) < 1e-10 for c in [c_s3, c_s2t, c_st2, c_t3]):
            return True, 2, "2-param, cubic auto"

        if abs(c_s3) > 1e-10:
            roots = np.roots([c_s3, c_s2t, c_st2, c_t3])
            real_roots = sum(1 for r in roots if abs(r.imag) < 1e-6)
            if real_roots > 0:
                return True, 2, f"2-param, {real_roots} branches"
        if abs(c_t3) < 1e-10 or abs(c_s3) < 1e-10:
            return True, 2, "2-param, degenerate"
        return False, 0, "no real cubic roots"

    else:
        # null_dim >= 3: check if cubic has nontrivial solutions
        # For high null_dim, generically yes
        # Quick check: try random vectors in null space
        for _ in range(100):
            coeffs = np.random.randn(null_dim)
            y = null_vecs.T @ coeffs
            cubic_val = sum(c5[j] * y[j]**3 for j in range(n))
            if abs(cubic_val) < 1e-8 and np.linalg.norm(y) > 1e-6:
                return True, null_dim, f"{null_dim}-param"
        # Also check: does cubic vanish identically on null space?
        # Sample more carefully
        return True, null_dim, f"{null_dim}-param (generic)"


def total_fermions(counts):
    """Total Weyl fermion count (weighted by dim of SU(3)×SU(2) rep)."""
    return sum(counts[i] * TYPES[i][1] * TYPES[i][2] for i in range(6))


def main():
    MAX_PER_TYPE = 4
    MAX_FERMIONS = 20

    print("=" * 70)
    print("ANOMALY-FREE FERMION SETS (each instance has own Y)")
    print(f"Types: {[t[0] for t in TYPES]}")
    print(f"Max instances per type: {MAX_PER_TYPE}")
    print(f"Max total Weyl fermions: {MAX_FERMIONS}")
    print("=" * 70)

    results = []

    for n0 in range(MAX_PER_TYPE + 1):
      for n1 in range(MAX_PER_TYPE + 1):
        for n2 in range(MAX_PER_TYPE + 1):
          for n3 in range(MAX_PER_TYPE + 1):
            for n4 in range(MAX_PER_TYPE + 1):
              for n5 in range(MAX_PER_TYPE + 1):
                counts = [n0, n1, n2, n3, n4, n5]
                if all(c == 0 for c in counts):
                    continue
                nf = total_fermions(counts)
                if nf > MAX_FERMIONS:
                    continue

                has_color = any(counts[i] > 0 for i in [0,1,2,3])
                has_uncolor = any(counts[i] > 0 for i in [4,5])

                ok, nd, info = check_anomaly(counts)
                if ok:
                    label = " + ".join(
                        f"{counts[i]}×{TYPES[i][0]}"
                        for i in range(6) if counts[i] > 0
                    )
                    results.append({
                        'counts': counts, 'label': label,
                        'fermions': nf,
                        'n_instances': sum(counts),
                        'info': info, 'null_dim': nd,
                        'has_color': has_color,
                        'has_uncolor': has_uncolor,
                    })

    results.sort(key=lambda r: (r['fermions'], r['n_instances']))

    # SM generation
    sm = [1, 0, 0, 2, 1, 1]  # 1×(3,2) + 2×(3b,1) + 1×(1,2) + 1×(1,1)
    sm_nf = total_fermions(sm)
    sm_ok, sm_nd, sm_info = check_anomaly(sm)
    print(f"\nSM generation: counts={sm}, fermions={sm_nf}")
    print(f"  anomaly-free={sm_ok}, null_dim={sm_nd}, {sm_info}")

    physical = [r for r in results if r['has_color'] and r['has_uncolor']]

    print(f"\nTotal anomaly-free: {len(results)}")
    print(f"With color+uncolor: {len(physical)}")

    # Show all with fermions ≤ SM
    print(f"\n--- Anomaly-free sets with ≤ {sm_nf} fermions (color+uncolor) ---")
    small_physical = [r for r in physical if r['fermions'] <= sm_nf]
    for r in small_physical:
        marker = " ← SM" if r['counts'] == sm else ""
        print(f"  {r['fermions']:2d} fermions ({r['n_instances']} instances): {r['label']}{marker}")
        print(f"           {r['info']}")

    # Count how many have SU(2) doublets (needed for weak interactions)
    has_doublet = [r for r in small_physical if any(r['counts'][i] > 0 for i in [0,1,4])]
    print(f"\n--- With SU(2) doublets (weak structure) ---")
    for r in has_doublet:
        marker = " ← SM" if r['counts'] == sm else ""
        print(f"  {r['fermions']:2d} fermions: {r['label']}{marker}")

    # CHIRAL sets: not vector-like in SU(3)×SU(2)
    # Vector-like: for each (R3,R2) species, there's a conjugate (R3b,R2)
    # Chiral: some species don't have a conjugate partner
    print(f"\n--- CHIRAL sets (non-vector-like) ≤ {sm_nf} fermions ---")
    for r in small_physical:
        c = r['counts']
        # Check if it's vector-like in SU(3): n(3,R2) = n(3b,R2) for each R2
        vl_su3 = (c[0] == c[1]) and (c[2] == c[3])  # (3,2)↔(3b,2), (3,1)↔(3b,1)
        if not vl_su3:
            marker = " ← SM" if c == sm else ""
            print(f"  {r['fermions']:2d} fermions: {r['label']}{marker}")
            print(f"           {r['info']}")


if __name__ == "__main__":
    main()
