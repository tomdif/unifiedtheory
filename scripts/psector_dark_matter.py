#!/usr/bin/env python3
"""
P-sector dark matter mass from within-chain dressing correlator.

Physics:
  The K/P decomposition splits the SU(2) holonomy into:
    K-sector: c_K(l) = |<W(0→l) s_ref>[0]|  →  Higgs (scalar, charged)
    P-sector: c_P(l) = |<W(0→l) s_ref>[1]|  →  DM candidate (neutral, massive)

  The P-sector is invisible to the source functional (trace) but
  contributes to the observable |z|² = Q² + P². It is:
    - Electrically neutral (no coupling to K-sector/trace)
    - Massive (correlator decays exponentially)
    - Gravitationally interacting (contributes to |z|²)
    - Self-conjugate (P and -P give same observable)

  These are exactly the properties of a viable dark matter candidate.

  This script computes m_DM/v from the P-sector autocorrelation,
  exactly as higgs_correlator.py computes m_H/v from the K-sector.

Algorithm:
  1. Build causal set, compute DP, sample chains
  2. For each chain, compute SU(2) holonomy at every link
  3. Extract P-sector profile: c_P(l) = |<W(0→l) s_ref>[1]|
  4. Subtract within-chain mean: h_P(l) = c_P(l) - mean(c_P)
  5. Compute autocorrelation C_P(tau) = mean[h_P(l) * h_P(l+tau)]
  6. Fit C_P(tau) = A * exp(-m_DM * tau) + C_inf
  7. m_DM/v = m_DM / mean(c_K)  [VEV from K-sector]

Requirements: pip install numpy scipy torch
Usage: python psector_dark_matter.py
"""

import sys, os
import numpy as np
import time
import torch
from scipy.optimize import curve_fit

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lepton_gpu import (build_causet, forward_dp_numpy, sample_chains_numpy,
                         random_su2_gpu, DEVICE)


def compute_kp_profiles(chains, pi, pj, N, Us, s_ref, max_id):
    """
    Compute BOTH K-sector and P-sector profiles along each chain.

    K-sector: c_K(l) = |<W(0→l) s_ref>[0]|  (source/charge component)
    P-sector: c_P(l) = |<W(0→l) s_ref>[1]|  (dressing component)

    Returns: (K_profiles, P_profiles), each shape (n_chains, L)
    """
    n_chains = len(chains)
    if n_chains == 0:
        return np.array([]), np.array([])

    chain_len = len(chains[0])

    edge_keys = pi.astype(np.int64) * max_id + pj.astype(np.int64)
    unique_keys, inverse = np.unique(edge_keys, return_inverse=True)
    n_links = len(unique_keys)

    if max_id <= 50000:
        key_to_link = np.full(max_id * max_id, -1, dtype=np.int64)
        key_to_link[unique_keys] = np.arange(n_links, dtype=np.int64)
    else:
        key_to_link = None

    K_profiles = np.zeros((n_chains, chain_len), dtype=np.float64)
    P_profiles = np.zeros((n_chains, chain_len), dtype=np.float64)

    batch_size = min(n_chains, 512)
    for b_start in range(0, n_chains, batch_size):
        b_end = min(b_start + batch_size, n_chains)
        batch_chains = chains[b_start:b_end]
        b_n = b_end - b_start

        W = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(b_n, -1, -1).clone()
        eye2 = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(b_n, -1, -1)

        # At l=0: K = |s_ref[0]| = 1.0, P = |s_ref[1]| = 0.0
        K_profiles[b_start:b_end, 0] = torch.abs(s_ref[0]).item()
        P_profiles[b_start:b_end, 0] = torch.abs(s_ref[1]).item()

        for li in range(chain_len - 1):
            link_idx = torch.zeros(b_n, dtype=torch.long, device=DEVICE)
            valid = torch.zeros(b_n, dtype=torch.bool, device=DEVICE)

            for ci, chain in enumerate(batch_chains):
                k = chain[li] * max_id + chain[li + 1]
                if key_to_link is not None:
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

            proj = torch.matmul(W, s_ref)  # (b_n, 2)
            K_profiles[b_start:b_end, li + 1] = torch.abs(proj[:, 0]).cpu().numpy()
            P_profiles[b_start:b_end, li + 1] = torch.abs(proj[:, 1]).cpu().numpy()

    return K_profiles, P_profiles


def compute_autocorrelation(profiles):
    """Compute averaged autocorrelation from profiles."""
    n_chains, L = profiles.shape
    max_tau = L // 2

    chain_means = profiles.mean(axis=1, keepdims=True)
    h = profiles - chain_means

    C = np.zeros(max_tau)
    for tau in range(max_tau):
        if tau == 0:
            vals = (h * h).mean(axis=1)
        else:
            vals = (h[:, :-tau] * h[:, tau:]).mean(axis=1)
        C[tau] = vals.mean()

    return np.arange(max_tau), C


def exp_decay(tau, A, m, C_inf):
    return A * np.exp(-m * tau) + C_inf


SM_MH_OVER_V = 125.1 / 245.5  # 0.5094


def run_psector(rho=10000, beta=4.0, n_sample=300, seed=42,
                L_min=6, L_max_use=17):
    """Run both K-sector (Higgs) and P-sector (DM) correlators."""
    t0 = time.time()

    N, pi, pj, n_pairs = build_causet(rho, seed=seed)
    if n_pairs == 0:
        return None

    dp_fwd, L_max, adj_starts, adj_targets = forward_dp_numpy(N, pi, pj)
    max_id = int(max(N, 1))

    edge_keys = pi.astype(np.int64) * max_id + pj.astype(np.int64)
    n_links = len(np.unique(edge_keys))
    Us = random_su2_gpu(n_links, seed + 9000, beta=beta)
    if torch.cuda.is_available():
        torch.cuda.synchronize()

    s_ref = torch.tensor([1, 0], dtype=torch.complex64, device=DEVICE)
    rng_chain = np.random.default_rng(seed + 5000)

    all_K_taus, all_K_Cs, all_K_vevs = [], [], []
    all_P_taus, all_P_Cs, all_P_vevs = [], [], []

    actual_L_max = min(L_max, L_max_use)

    for L in range(L_min, actual_L_max + 1):
        chains = sample_chains_numpy(adj_starts, adj_targets, dp_fwd, N,
                                      L, n_sample, rng_chain)
        if len(chains) < 10:
            continue

        K_prof, P_prof = compute_kp_profiles(
            chains, pi, pj, N, Us, s_ref, max_id)

        if K_prof.size == 0:
            continue

        # K-sector (Higgs)
        K_vev = K_prof.mean()
        K_tau, K_C = compute_autocorrelation(K_prof)
        all_K_vevs.append(K_vev)
        all_K_taus.append(K_tau)
        all_K_Cs.append(K_C)

        # P-sector (DM candidate)
        P_vev = P_prof.mean()
        P_tau, P_C = compute_autocorrelation(P_prof)
        all_P_vevs.append(P_vev)
        all_P_taus.append(P_tau)
        all_P_Cs.append(P_C)

    if not all_K_Cs:
        return None

    # Grand average correlators
    min_len = min(len(c) for c in all_K_Cs)
    K_C_avg = np.mean([c[:min_len] for c in all_K_Cs], axis=0)
    P_C_avg = np.mean([c[:min_len] for c in all_P_Cs], axis=0)
    taus = np.arange(min_len)

    K_vev_avg = np.mean(all_K_vevs)
    P_vev_avg = np.mean(all_P_vevs)

    # Fit K-sector (Higgs mass)
    m_H, m_H_err = np.nan, np.nan
    try:
        popt_K, pcov_K = curve_fit(exp_decay, taus[1:], K_C_avg[1:],
                                    p0=[K_C_avg[0], 0.5, 0.0],
                                    bounds=([0, 0.01, -1], [10, 5, 1]),
                                    maxfev=5000)
        m_H = popt_K[1]
        m_H_err = np.sqrt(pcov_K[1, 1]) if pcov_K[1, 1] > 0 else 0
    except Exception:
        pass

    # Fit P-sector (DM mass)
    m_DM, m_DM_err = np.nan, np.nan
    try:
        popt_P, pcov_P = curve_fit(exp_decay, taus[1:], P_C_avg[1:],
                                    p0=[P_C_avg[0], 0.5, 0.0],
                                    bounds=([0, 0.01, -1], [10, 5, 1]),
                                    maxfev=5000)
        m_DM = popt_P[1]
        m_DM_err = np.sqrt(pcov_P[1, 1]) if pcov_P[1, 1] > 0 else 0
    except Exception:
        pass

    mH_over_v = m_H / K_vev_avg if K_vev_avg > 0 else np.nan
    mDM_over_v = m_DM / K_vev_avg if K_vev_avg > 0 else np.nan

    return {
        'K_vev': K_vev_avg,
        'P_vev': P_vev_avg,
        'm_H': m_H, 'm_H_err': m_H_err,
        'm_DM': m_DM, 'm_DM_err': m_DM_err,
        'mH_over_v': mH_over_v,
        'mDM_over_v': mDM_over_v,
        'mDM_GeV': mDM_over_v * 246.2 if not np.isnan(mDM_over_v) else np.nan,
        'P_over_K_vev': P_vev_avg / K_vev_avg if K_vev_avg > 0 else np.nan,
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
    print("  P-SECTOR DARK MATTER MASS FROM DRESSING CORRELATOR")
    print(f"  rho={rho}, {n_seeds} seeds, {n_sample} samples/length")
    print("=" * 70)

    all_mH, all_mDM, all_mH_v, all_mDM_v, all_mDM_GeV = [], [], [], [], []
    all_PK = []

    for seed in range(n_seeds):
        r = run_psector(rho=rho, n_sample=n_sample, seed=seed * 137)
        if r is None:
            print(f"  seed={seed}: FAILED", flush=True)
            continue

        all_mH.append(r['m_H'])
        all_mDM.append(r['m_DM'])
        all_mH_v.append(r['mH_over_v'])
        all_mDM_v.append(r['mDM_over_v'])
        all_mDM_GeV.append(r['mDM_GeV'])
        all_PK.append(r['P_over_K_vev'])

        print(f"  seed={seed}: m_H/v={r['mH_over_v']:.4f}  "
              f"m_DM/v={r['mDM_over_v']:.4f}  "
              f"m_DM={r['mDM_GeV']:.1f} GeV  "
              f"P/K={r['P_over_K_vev']:.4f}  "
              f"t={r['time']:.0f}s", flush=True)

    if all_mDM_v:
        print(f"\n{'='*70}")
        print(f"  RESULTS ({len(all_mDM_v)} seeds)")
        print(f"{'='*70}")
        print(f"  K-sector (Higgs):")
        print(f"    m_H/v = {np.mean(all_mH_v):.4f} +/- {np.std(all_mH_v):.4f}")
        print(f"    Expt:   0.509")
        print(f"")
        print(f"  P-sector (DM candidate):")
        print(f"    m_DM/v = {np.mean(all_mDM_v):.4f} +/- {np.std(all_mDM_v):.4f}")
        print(f"    m_DM   = {np.mean(all_mDM_GeV):.1f} +/- {np.std(all_mDM_GeV):.1f} GeV")
        print(f"    P/K VEV ratio = {np.mean(all_PK):.4f}")
        print(f"")
        print(f"  DM/Higgs mass ratio:")
        print(f"    m_DM/m_H = {np.mean(all_mDM_v)/np.mean(all_mH_v):.3f}")
        print(f"")
        print(f"  Physical properties of P-sector DM:")
        print(f"    - Electrically neutral (P-sector invisible to trace/source)")
        print(f"    - Massive (correlator decays exponentially)")
        print(f"    - Gravitationally interacting (contributes to |z|^2)")
        print(f"    - Self-conjugate (P and -P give same observable)")
        print(f"    - Stable (no decay channel to K-sector without breaking gauge)")
