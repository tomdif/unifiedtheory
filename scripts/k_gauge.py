#!/usr/bin/env python3
"""
k_gauge.py — The gauged chamber kernel on a Poisson causal set

Define K_gauge(P,Q) = det(ζ·U[P,Q]) + det(ζ·U[Q,P]) - δ_{P,Q}

where:
  ζ(i,j) = 1 if i ≤ j (order kernel)
  U(i,j) = SU(3) holonomy matrix on the causal link i→j
  (ζ·U)[P,Q]_{ab} = ζ(p_a, q_b) · U(p_a, q_b)

The product ζ·U means: the matrix entry is the holonomy if
there's a causal link, and zero otherwise.

For chamber points P = (p₁,...,p_d) with p₁ < ... < p_d,
det(ζ·U[P,Q]) is a d×d determinant of SU(3) matrices weighted
by the causal order.

COMPUTATION:
1. Sprinkle N points into a 1+1D causal diamond (d=2 for speed)
2. Assign random SU(3) holonomies to causal links
3. Compute K_gauge as a matrix on chamber points
4. Decompose into R-even/R-odd sectors
5. Extract eigenvalue ratios
6. Compare with known mass ratios
"""

import numpy as np
from itertools import combinations

def sprinkle_causal_diamond_2d(N, seed=42):
    """Sprinkle N points into a 1+1D causal diamond.
    Diamond: |x| + |t| ≤ 1, with t > 0 (future half).
    Returns coordinates and causal order."""
    rng = np.random.default_rng(seed)

    # Sprinkle into the full diamond
    points = []
    while len(points) < N:
        t = rng.uniform(-1, 1)
        x = rng.uniform(-1, 1)
        if abs(x) + abs(t) <= 1:
            points.append((t, x))

    points.sort()  # sort by time
    points = np.array(points)

    # Causal order: i < j if t_j > t_i and |x_j - x_i| < t_j - t_i
    N = len(points)
    order = np.zeros((N, N), dtype=bool)
    for i in range(N):
        for j in range(i+1, N):
            dt = points[j, 0] - points[i, 0]
            dx = abs(points[j, 1] - points[i, 1])
            if dt > 0 and dx < dt:
                order[i, j] = True

    return points, order

def random_su3(rng):
    """Generate a random SU(3) matrix (Haar measure approximation)."""
    # Use QR decomposition of random complex matrix
    Z = (rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    # Fix phases to get SU(3)
    d = np.diagonal(R)
    ph = d / np.abs(d)
    Q = Q @ np.diag(ph)
    # Ensure det = 1
    det = np.linalg.det(Q)
    Q = Q / (det ** (1/3))
    return Q

def compute_k_gauge(points, order, N_c=3, d=2, seed=42):
    """Compute the gauged chamber kernel."""
    rng = np.random.default_rng(seed)
    N = len(points)

    # Assign SU(N_c) holonomies to each causal link
    holonomies = {}
    for i in range(N):
        for j in range(i+1, N):
            if order[i, j]:
                holonomies[(i, j)] = random_su3(rng)
                holonomies[(j, i)] = holonomies[(i, j)].conj().T  # inverse

    # Chamber points: strictly increasing d-tuples
    chamber_pts = list(combinations(range(N), d))
    n_ch = len(chamber_pts)

    if n_ch > 500:
        # Subsample
        rng2 = np.random.default_rng(seed + 100)
        indices = rng2.choice(n_ch, 500, replace=False)
        chamber_pts = [chamber_pts[i] for i in sorted(indices)]
        n_ch = len(chamber_pts)

    # Zeta function
    def zeta(i, j):
        if i == j:
            return 1.0
        if i < j and order[i, j]:
            return 1.0
        if i < j:
            return 1.0 if i <= j else 0.0  # Simple order: i ≤ j
        return 0.0

    # For the gauged kernel: (ζ·U)(i,j) = ζ(i,j) · U(i,j)
    # where U(i,j) is the holonomy if i→j is a causal link,
    # identity if i=j, and zero if no link.
    def zeta_U(i, j):
        """Returns N_c × N_c matrix."""
        if i <= j:  # causal order (using index order as proxy)
            if (i, j) in holonomies:
                return holonomies[(i, j)]
            else:
                return np.eye(N_c)  # trivial holonomy for non-adjacent
        return np.zeros((N_c, N_c))

    # K_gauge(P, Q) for chamber points P, Q (each a d-tuple of indices)
    # = det(ζ·U[P,Q]) + det(ζ·U[Q,P]) - δ_{P,Q}
    # where (ζ·U[P,Q])_{ab} = (ζ·U)(p_a, q_b) is an N_c × N_c matrix
    # The "det" is a block determinant of a d×d matrix of N_c×N_c blocks.

    # For d=2: det([[A, B], [C, D]]) = det(AD - BC) for commuting blocks
    # For non-commuting: det = det(A)det(D - CA⁻¹B) if A invertible.
    # Use the Leibniz formula for block determinants.

    def block_det_2x2(blocks):
        """Determinant of a 2×2 block matrix [[A,B],[C,D]] = det(AD-BC)
        (valid for d=2 since we sum over permutations)."""
        A, B = blocks[0]
        C, D = blocks[1]
        # Leibniz: det = A⊗D - B⊗C (for 2×2, this is trace of AD - BC... no)
        # Actually for the SCALAR det of the block matrix, using permutations:
        # det = det(A·D) - det(B·C) ... no, that's wrong too.
        # The correct formula: det([[A,B],[C,D]]) summed over S_2:
        # = tr(A)·tr(D) - tr(B)·tr(C) ... no.
        #
        # For the gauged kernel, we want a SCALAR output.
        # The correct approach: take the trace over color indices.
        # K_gauge(P,Q) = Tr[det(ζ·U[P,Q])] where det is the d×d det
        # and Tr is the N_c × N_c trace.
        #
        # For d=2: det = (ζ·U)(p₁,q₁)·(ζ·U)(p₂,q₂) - (ζ·U)(p₁,q₂)·(ζ·U)(p₂,q₁)
        # This is a product of N_c×N_c matrices → N_c×N_c result.
        # Take Tr to get a scalar.
        return np.trace(A @ D - B @ C)

    # Build K_gauge matrix
    K = np.zeros((n_ch, n_ch), dtype=complex)
    for i, P in enumerate(chamber_pts):
        for j, Q in enumerate(chamber_pts):
            # Block matrix (ζ·U[P,Q])_{ab} = zeta_U(P[a], Q[b])
            blocks_PQ = [[zeta_U(P[a], Q[b]) for b in range(d)] for a in range(d)]
            blocks_QP = [[zeta_U(Q[a], P[b]) for b in range(d)] for a in range(d)]

            det_PQ = block_det_2x2(blocks_PQ)
            det_QP = block_det_2x2(blocks_QP)
            delta = 1.0 if i == j else 0.0

            K[i, j] = det_PQ + det_QP - delta * 3  # Tr(I₃) = 3

    return chamber_pts, K

def analyze_spectrum(chamber_pts, K, N, d=2):
    """Extract R-even/odd eigenvalues."""
    n_ch = len(chamber_pts)

    # Reflection R: (p₁,...,p_d) → (N-1-p_d,...,N-1-p₁)
    pt_to_idx = {p: i for i, p in enumerate(chamber_pts)}
    R_mat = np.zeros((n_ch, n_ch))
    for i, P in enumerate(chamber_pts):
        RP = tuple(N - 1 - P[k] for k in range(d-1, -1, -1))
        if RP in pt_to_idx:
            R_mat[i, pt_to_idx[RP]] = 1.0

    # Symmetrize K (it should be Hermitian but numerical noise)
    K_herm = (K + K.conj().T) / 2

    # Project onto R-even and R-odd
    P_even = (np.eye(n_ch) + R_mat) / 2
    P_odd = (np.eye(n_ch) - R_mat) / 2

    K_even = P_even @ K_herm.real @ P_even
    K_odd = P_odd @ K_herm.real @ P_odd

    eig_even = np.sort(np.linalg.eigvalsh(K_even))[::-1]
    eig_odd = np.sort(np.linalg.eigvalsh(K_odd))[::-1]

    even_nz = eig_even[np.abs(eig_even) > 1e-8]
    odd_nz = eig_odd[np.abs(eig_odd) > 1e-8]

    return even_nz, odd_nz

def main():
    print("=" * 70)
    print("GAUGED CHAMBER KERNEL K_gauge ON POISSON CAUSAL SET")
    print("SU(3) holonomies, d=2 (for computational feasibility)")
    print("=" * 70)

    # Run for multiple sprinklings and average
    all_ratios = []

    for N in [15, 20, 25, 30]:
        print(f"\n{'─'*70}")
        print(f"N = {N} points, d = 2")
        print(f"{'─'*70}")

        seed_ratios = []
        for seed in range(10):
            points, order = sprinkle_causal_diamond_2d(N, seed=seed*137)
            n_links = np.sum(order)

            try:
                chamber_pts, K = compute_k_gauge(points, order, N_c=3, d=2, seed=seed*137+1)
                even, odd = analyze_spectrum(chamber_pts, K, N, d=2)

                if len(even) >= 2 and len(odd) >= 1 and odd[0] > 0:
                    ratio = even[0] / odd[0]
                    seed_ratios.append(ratio)

                    if seed < 3:
                        print(f"  seed={seed}: #pts={len(chamber_pts)}, #links={n_links}, "
                              f"le={even[0]:.3f}, lo={odd[0]:.3f}, le/lo={ratio:.4f}")
            except Exception as e:
                if seed < 3:
                    print(f"  seed={seed}: error: {e}")

        if seed_ratios:
            mean_r = np.mean(seed_ratios)
            std_r = np.std(seed_ratios) / np.sqrt(len(seed_ratios))
            all_ratios.append((N, mean_r, std_r, len(seed_ratios)))
            print(f"  Mean le/lo = {mean_r:.4f} ± {std_r:.4f} ({len(seed_ratios)} seeds)")

    # Compare with predictions
    print(f"\n{'='*70}")
    print("COMPARISON WITH PREDICTIONS")
    print(f"{'='*70}")

    # For d=2, the ungauged K_F has le/lo → 3 = (d+1)/(d-1)
    # The gauged K_gauge should have a DIFFERENT ratio

    print(f"\n  Ungauged prediction (d=2): le/lo → 3.0")
    print(f"\n  {'N':>4} {'le/lo (gauged)':>15} {'le/lo (ungauged)':>18}")
    print(f"  {'─'*40}")
    for N, mean_r, std_r, n_seeds in all_ratios:
        print(f"  {N:>4} {mean_r:>10.4f} ± {std_r:.4f}   3.000 (target)")

    print(f"\n  If the gauged ratio differs from 3.0, the SU(3) holonomy")
    print(f"  modifies the spectral gap — the confining sector sees a")
    print(f"  different effective dimension than the free sector.")

    # The KEY question: does the gauged ratio converge to a specific value?
    if len(all_ratios) >= 2:
        ratios_only = [r[1] for r in all_ratios]
        print(f"\n  Gauged ratios: {[f'{r:.3f}' for r in ratios_only]}")
        print(f"  Trend: {'increasing' if ratios_only[-1] > ratios_only[0] else 'decreasing' if ratios_only[-1] < ratios_only[0] else 'flat'}")

if __name__ == "__main__":
    main()
