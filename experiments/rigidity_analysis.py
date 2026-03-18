#!/usr/bin/env python3
"""
Rigidity analysis: which chiral theories have fully determined charge ratios?

KEY INSIGHT:
- 3 linear anomaly conditions (SU(3)², SU(2)², gravitational)
- 1 cubic anomaly condition
- k species types → k hypercharge unknowns
- Linear null space dimension = k - rank(linear) ≤ k - 3

For the cubic to FULLY determine charge ratios (up to normalization):
- Need null_dim = 2 (so cubic on 2D gives finitely many lines)
- Need the cubic to be NON-DEGENERATE (not identically zero on null space)

This requires k = 5 species types (generically).
With k < 5: cubic is redundant (null_dim ≤ 1).
With k > 5: cubic leaves continuous moduli (null_dim ≥ 3).

QUESTION: Is the SM the minimal CHIRAL theory with 5 species types?
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


def analyze(counts):
    """Analyze a multiset of species types."""
    total_vars = sum(counts)
    if total_vars == 0:
        return None

    species = []
    for i in range(6):
        for _ in range(counts[i]):
            species.append(TYPES[i])

    n = len(species)

    # SU(3)³
    su3_cubic = sum(s[5] * s[2] for s in species)
    if abs(su3_cubic) > 1e-10:
        return None  # SU(3)³ fails

    # Linear constraint matrix
    c2 = [s[3] * s[2] for s in species]
    c3 = [s[1] * s[4] for s in species]
    c4 = [s[1] * s[2] for s in species]
    A_mat = np.array([c2, c3, c4])
    rank = np.linalg.matrix_rank(A_mat, tol=1e-10)
    null_dim = n - rank

    if null_dim <= 0:
        return {'null_dim': 0, 'rigid': False, 'reason': 'trivial'}

    # Get null space
    U, S, Vt = np.linalg.svd(A_mat, full_matrices=True)
    null_vecs = Vt[rank:]

    # Cubic coefficients on null space
    c5 = [s[1] * s[2] for s in species]

    cubic_zero = True  # Is cubic identically zero on null space?

    if null_dim == 1:
        v = null_vecs[0]
        cubic_coeff = sum(c5[j] * v[j]**3 for j in range(n))
        cubic_zero = abs(cubic_coeff) < 1e-10
        return {
            'null_dim': 1,
            'cubic_zero': cubic_zero,
            'rigid': True,  # 1-dim: ratios determined by linears
            'reason': 'linears fix ratios' + (' (cubic redundant)' if cubic_zero else ' (cubic gives isolated)')
        }

    elif null_dim == 2:
        u_v, v_v = null_vecs[0], null_vecs[1]
        c_s3  = sum(c5[j] * u_v[j]**3 for j in range(n))
        c_s2t = 3*sum(c5[j] * u_v[j]**2 * v_v[j] for j in range(n))
        c_st2 = 3*sum(c5[j] * u_v[j] * v_v[j]**2 for j in range(n))
        c_t3  = sum(c5[j] * v_v[j]**3 for j in range(n))

        cubic_zero = all(abs(c) < 1e-10 for c in [c_s3, c_s2t, c_st2, c_t3])

        if cubic_zero:
            return {
                'null_dim': 2,
                'cubic_zero': True,
                'rigid': False,
                'reason': 'cubic degenerate — continuous moduli'
            }

        # Cubic is nontrivial on 2D null space
        # Homogeneous cubic in (s,t) → ≤ 3 lines through origin
        if abs(c_s3) > 1e-10:
            roots = np.roots([c_s3, c_s2t, c_st2, c_t3])
            real_roots = [r.real for r in roots if abs(r.imag) < 1e-6]
            n_branches = len(real_roots) + (1 if abs(c_t3) < 1e-10 else 0)
        else:
            n_branches = 99  # degenerate

        return {
            'null_dim': 2,
            'cubic_zero': False,
            'rigid': True,
            'n_branches': n_branches,
            'reason': f'RIGID: cubic gives {n_branches} discrete branches'
        }

    else:
        return {
            'null_dim': null_dim,
            'rigid': False,
            'reason': f'null_dim={null_dim} ≥ 3 — underdetermined'
        }


def total_fermions(counts):
    return sum(counts[i] * TYPES[i][1] * TYPES[i][2] for i in range(6))


def is_chiral(counts):
    """Not vector-like in SU(3)."""
    return not (counts[0] == counts[1] and counts[2] == counts[3])


def main():
    MAX = 4
    MAX_FERMIONS = 20

    print("=" * 70)
    print("RIGIDITY ANALYSIS")
    print("=" * 70)

    rigid_chiral = []
    nonrigid_chiral = []

    for n0 in range(MAX+1):
      for n1 in range(MAX+1):
        for n2 in range(MAX+1):
          for n3 in range(MAX+1):
            for n4 in range(MAX+1):
              for n5 in range(MAX+1):
                counts = [n0,n1,n2,n3,n4,n5]
                if all(c==0 for c in counts): continue
                nf = total_fermions(counts)
                if nf > MAX_FERMIONS: continue
                if not is_chiral(counts): continue

                # Must have both color and uncolor
                has_color = any(counts[i] > 0 for i in [0,1,2,3])
                has_uncolor = any(counts[i] > 0 for i in [4,5])
                if not (has_color and has_uncolor): continue

                result = analyze(counts)
                if result is None: continue

                label = " + ".join(
                    f"{counts[i]}×{TYPES[i][0]}"
                    for i in range(6) if counts[i] > 0
                )

                entry = {
                    'counts': counts, 'label': label,
                    'fermions': nf, 'n_species': sum(counts),
                    **result
                }

                if result['rigid']:
                    rigid_chiral.append(entry)
                else:
                    nonrigid_chiral.append(entry)

    rigid_chiral.sort(key=lambda r: r['fermions'])
    nonrigid_chiral.sort(key=lambda r: r['fermions'])

    sm = [1, 0, 0, 2, 1, 1]

    print(f"\nRIGID chiral theories (discrete charge ratios): {len(rigid_chiral)}")
    for r in rigid_chiral:
        marker = " ← SM" if r['counts'] == sm else ""
        print(f"  {r['fermions']:2d} fermions ({r['n_species']} species): {r['label']}{marker}")
        print(f"           null_dim={r['null_dim']}, {r['reason']}")

    print(f"\nNon-rigid chiral theories (continuous moduli): {len(nonrigid_chiral)}")
    for r in nonrigid_chiral[:15]:
        print(f"  {r['fermions']:2d} fermions ({r['n_species']} species): {r['label']}")
        print(f"           null_dim={r['null_dim']}, {r['reason']}")
    if len(nonrigid_chiral) > 15:
        print(f"  ... and {len(nonrigid_chiral) - 15} more")

    print(f"\n{'='*70}")
    print("KEY FINDING:")
    print(f"{'='*70}")
    if rigid_chiral:
        min_rigid = rigid_chiral[0]['fermions']
        min_rigid_set = [r for r in rigid_chiral if r['fermions'] == min_rigid]
        print(f"Smallest rigid chiral theory: {min_rigid} fermions")
        for r in min_rigid_set:
            marker = " ← SM" if r['counts'] == sm else ""
            print(f"  {r['label']}{marker}")
        sm_is_minimal = any(r['counts'] == sm for r in min_rigid_set)
        print(f"\nSM is the minimal rigid chiral theory: {sm_is_minimal}")

    print(f"\nThe rigidity argument:")
    print(f"  - 3 linear conditions + 1 cubic = 4 effective constraints")
    print(f"  - k species types → k-3 dim null space from linears")
    print(f"  - Cubic on 2D null space → ≤ 3 discrete branches (rigidity)")
    print(f"  - Cubic on 1D null space → either redundant or 1 point")
    print(f"  - Cubic on ≥3D null space → surface (not discrete)")
    print(f"  - SWEET SPOT: k=5 species (null_dim=2)")


if __name__ == "__main__":
    main()
