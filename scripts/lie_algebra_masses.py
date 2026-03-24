#!/usr/bin/env python3
"""
Lie algebra mass ratios: sum connections instead of multiplying holonomies.

THE SYSTEMATIC BIAS:
  Current pipeline: U_chain = Π exp(iA_link), K = |U[0,0]|
  Problem: U ∈ SU(N), so |K|²+|P|²=1. Long chains compress K toward
  the Haar average ~1/√N, introducing nonlinear distortion.

THE FIX:
  Sum connections in the Lie algebra: A_chain = Σ A_link ∈ su(N)
  K/P decomposition is LINEAR: K = tr(A)/N, P = A - K·I
  No norm constraint. K and P are genuinely independent.
  Long chains contribute linearly, not through compressed projection.

TEST:
  Run BOTH pipelines on the same causal sets. Compare mass ratios.
  If Lie algebra gives closer-to-experiment results with less scatter,
  the unitarity compression was a systematic bias.

Usage:
  python lie_algebra_masses.py --quick    # 3 seeds
  python lie_algebra_masses.py            # 5 seeds
"""

import sys, os
import numpy as np
import time
import torch

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lepton_gpu import (build_causet, forward_dp_numpy, sample_chains_numpy,
                         count_paths_gpu, random_su2_gpu, DEVICE)

EXP_MU_TAU = 0.0595


def generate_su2_connections(n_links, seed, beta=4.0):
    """Generate su(2) Lie algebra elements (the connections A_link).

    For SU(2): su(2) = {i(a₁σ₁ + a₂σ₂ + a₃σ₃)} = traceless anti-Hermitian 2×2.
    We parameterize as A = i·H where H is traceless Hermitian:
      H = a₁σ₁ + a₂σ₂ + a₃σ₃

    The distribution: each aᵢ ~ N(0, 1/β), giving connections concentrated
    near zero for large β (weak field / continuum limit).

    Returns: (n_links, 2, 2) complex64 tensor of su(2) elements.
    """
    rng = torch.Generator(device=DEVICE).manual_seed(seed)
    # Random coefficients for Pauli matrices
    a = torch.randn(n_links, 3, device=DEVICE, generator=rng, dtype=torch.float32) / beta

    # Build traceless Hermitian matrices H = a₁σ₁ + a₂σ₂ + a₃σ₃
    # σ₁ = [[0,1],[1,0]], σ₂ = [[0,-i],[i,0]], σ₃ = [[1,0],[0,-1]]
    H = torch.zeros(n_links, 2, 2, dtype=torch.complex64, device=DEVICE)
    H[:, 0, 0] = torch.complex(a[:, 2], torch.zeros_like(a[:, 2]))   # a₃
    H[:, 0, 1] = torch.complex(a[:, 0], -a[:, 1])                     # a₁ - ia₂
    H[:, 1, 0] = torch.complex(a[:, 0], a[:, 1])                      # a₁ + ia₂
    H[:, 1, 1] = torch.complex(-a[:, 2], torch.zeros_like(a[:, 2]))   # -a₃

    # Connection A = iH (anti-Hermitian, traceless)
    A = 1j * H
    return A


def compute_holonomy_lepton(chains, key_to_link, max_id, Us, s_ref):
    """ORIGINAL: multiply holonomies, project onto s_ref[0]. Returns c_weighted."""
    n_chains = len(chains)
    if n_chains == 0:
        return torch.zeros(2, dtype=torch.complex64, device=DEVICE)

    chain_len = len(chains[0])
    n_links_per = chain_len - 1

    W = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(n_chains, -1, -1).clone()
    eye2 = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(n_chains, -1, -1)

    for li in range(n_links_per):
        link_idx = torch.zeros(n_chains, dtype=torch.long, device=DEVICE)
        valid = torch.zeros(n_chains, dtype=torch.bool, device=DEVICE)
        for ci, chain in enumerate(chains):
            k = chain[li] * max_id + chain[li + 1]
            if isinstance(key_to_link, np.ndarray):
                idx = key_to_link[k] if k < len(key_to_link) else -1
            else:
                idx = -1
            if idx >= 0:
                link_idx[ci] = idx
                valid[ci] = True
        mats = Us[link_idx]
        mask = valid.view(-1, 1, 1).expand_as(mats)
        mats = torch.where(mask, mats, eye2)
        W = torch.bmm(mats, W)

    result = torch.matmul(W, s_ref)  # (n_chains, 2)
    return result.mean(dim=0)


def compute_algebra_lepton(chains, key_to_link, max_id, As, s_ref):
    """NEW: sum connections in su(2), project onto s_ref[0]. Returns c_weighted."""
    n_chains = len(chains)
    if n_chains == 0:
        return torch.zeros(2, dtype=torch.complex64, device=DEVICE)

    chain_len = len(chains[0])
    n_links_per = chain_len - 1

    # Accumulate A_chain = Σ A_link (in the Lie algebra, a vector space)
    A_sum = torch.zeros(n_chains, 2, 2, dtype=torch.complex64, device=DEVICE)
    zero2 = torch.zeros(n_chains, 2, 2, dtype=torch.complex64, device=DEVICE)

    for li in range(n_links_per):
        link_idx = torch.zeros(n_chains, dtype=torch.long, device=DEVICE)
        valid = torch.zeros(n_chains, dtype=torch.bool, device=DEVICE)
        for ci, chain in enumerate(chains):
            k = chain[li] * max_id + chain[li + 1]
            if isinstance(key_to_link, np.ndarray):
                idx = key_to_link[k] if k < len(key_to_link) else -1
            else:
                idx = -1
            if idx >= 0:
                link_idx[ci] = idx
                valid[ci] = True
        conns = As[link_idx]
        mask = valid.view(-1, 1, 1).expand_as(conns)
        conns = torch.where(mask, conns, zero2)
        A_sum += conns  # LINEAR sum in su(2)

    # Project: apply A_sum to s_ref as a matrix
    # The "effective state" is A_sum @ s_ref (in the algebra, not the group)
    result = torch.matmul(A_sum, s_ref)  # (n_chains, 2)
    return result.mean(dim=0)


def run_comparison(rho=10000, n_sample=300, seed=42, beta=4.0):
    """Run both holonomy and algebra pipelines on the same causal set."""
    t0 = time.time()

    N, pi, pj, n_pairs = build_causet(rho, seed=seed)
    if n_pairs == 0:
        return None

    dp_fwd, L_max, adj_starts, adj_targets = forward_dp_numpy(N, pi, pj)
    path_counts = count_paths_gpu(N, pi, pj, L_max)

    max_id = int(max(N, 1))
    edge_keys = pi.astype(np.int64) * max_id + pj.astype(np.int64)
    unique_keys, _ = np.unique(edge_keys, return_inverse=True)
    n_links = len(unique_keys)

    key_to_link = np.full(max_id * max_id, -1, dtype=np.int64) if max_id <= 50000 else None
    if key_to_link is not None:
        key_to_link[unique_keys] = np.arange(n_links, dtype=np.int64)

    # Generate BOTH group elements and algebra elements from SAME seed
    Us = random_su2_gpu(n_links, seed + 9000, beta=beta)
    As = generate_su2_connections(n_links, seed + 9000, beta=beta)
    torch.cuda.synchronize()

    s_ref = torch.tensor([1, 0], dtype=torch.complex64, device=DEVICE)
    rng = np.random.default_rng(seed + 5000)

    # Holonomy pipeline
    hol_weighted = torch.zeros(2, dtype=torch.complex64, device=DEVICE)
    hol_total_weight = 0.0

    # Algebra pipeline
    alg_weighted = torch.zeros(2, dtype=torch.complex64, device=DEVICE)
    alg_total_weight = 0.0

    for L in range(2, L_max + 1):
        true_count = path_counts.get(L, 0.0)
        if true_count == 0:
            continue

        chains = sample_chains_numpy(adj_starts, adj_targets, dp_fwd, N,
                                      L, n_sample, rng)
        if not chains:
            continue

        # Holonomy
        c_hol = compute_holonomy_lepton(chains, key_to_link, max_id, Us, s_ref)
        hol_weighted += true_count * c_hol
        hol_total_weight += true_count

        # Algebra
        c_alg = compute_algebra_lepton(chains, key_to_link, max_id, As, s_ref)
        alg_weighted += true_count * c_alg
        alg_total_weight += true_count

    if hol_total_weight == 0:
        return None

    # Holonomy ratio
    c_hol = (hol_weighted / hol_total_weight).cpu().numpy()
    hol_norm = np.abs(c_hol)
    hol_masses = np.sort(hol_norm)[::-1]
    r_hol = float(hol_masses[1] / hol_masses[0]) if hol_masses[0] > 0 else 0

    # Algebra ratio
    c_alg = (alg_weighted / alg_total_weight).cpu().numpy()
    alg_norm = np.abs(c_alg)
    alg_masses = np.sort(alg_norm)[::-1]
    r_alg = float(alg_masses[1] / alg_masses[0]) if alg_masses[0] > 0 else 0

    return {
        'r_holonomy': r_hol,
        'r_algebra': r_alg,
        'hol_mags': (float(hol_masses[0]), float(hol_masses[1])),
        'alg_mags': (float(alg_masses[0]), float(alg_masses[1])),
        'L_max': L_max,
        'N': N,
        'time': time.time() - t0,
    }


if __name__ == "__main__":
    rho = 10000
    n_seeds = 5
    n_sample = 300

    if "--quick" in sys.argv:
        n_seeds = 3
        n_sample = 200

    print("=" * 70)
    print("  HOLONOMY vs LIE ALGEBRA MASS RATIOS")
    print(f"  rho={rho}, {n_seeds} seeds, {n_sample} samples/length, beta=4.0")
    print("=" * 70)

    all_hol, all_alg = [], []

    for seed in range(n_seeds):
        r = run_comparison(rho=rho, n_sample=n_sample, seed=seed * 137)
        if r is None:
            print(f"  seed={seed}: FAILED", flush=True)
            continue

        all_hol.append(r['r_holonomy'])
        all_alg.append(r['r_algebra'])

        print(f"  seed={seed}: "
              f"HOL r={r['r_holonomy']:.5f} ({r['hol_mags'][0]:.4f},{r['hol_mags'][1]:.4f})  "
              f"ALG r={r['r_algebra']:.5f} ({r['alg_mags'][0]:.4f},{r['alg_mags'][1]:.4f})  "
              f"L_max={r['L_max']}  t={r['time']:.0f}s", flush=True)

    if all_hol:
        hol_mean, hol_std = np.mean(all_hol), np.std(all_hol)
        alg_mean, alg_std = np.mean(all_alg), np.std(all_alg)
        hol_err = abs(hol_mean - EXP_MU_TAU) / EXP_MU_TAU * 100
        alg_err = abs(alg_mean - EXP_MU_TAU) / EXP_MU_TAU * 100

        print(f"\n{'='*70}")
        print(f"  COMPARISON ({len(all_hol)} seeds)")
        print(f"{'='*70}")
        print(f"  Experiment: m_mu/m_tau = {EXP_MU_TAU}")
        print(f"")
        print(f"  HOLONOMY (group elements, |K|²+|P|²=1):")
        print(f"    r = {hol_mean:.5f} +/- {hol_std:.5f}  ({hol_err:.1f}% off)")
        print(f"")
        print(f"  LIE ALGEBRA (connections, unconstrained):")
        print(f"    r = {alg_mean:.5f} +/- {alg_std:.5f}  ({alg_err:.1f}% off)")
        print(f"")

        if alg_err < hol_err:
            print(f"  >> ALGEBRA IS CLOSER TO EXPERIMENT by {hol_err-alg_err:.1f} percentage points")
            print(f"  >> The unitarity compression WAS a systematic bias")
        elif hol_err < alg_err:
            print(f"  >> HOLONOMY IS CLOSER TO EXPERIMENT by {alg_err-hol_err:.1f} percentage points")
            print(f"  >> The unitarity compression was NOT the dominant error")
        else:
            print(f"  >> COMPARABLE: difference is within noise")

        if alg_std < hol_std:
            print(f"  >> ALGEBRA HAS LESS SCATTER ({alg_std:.5f} vs {hol_std:.5f})")
        elif hol_std < alg_std:
            print(f"  >> HOLONOMY HAS LESS SCATTER ({hol_std:.5f} vs {alg_std:.5f})")
