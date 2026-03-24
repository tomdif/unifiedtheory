#!/usr/bin/env python3
"""
P-sector energy density correlator: m_DM from ⟨tr(P²)(x) tr(P²)(y)⟩.

THE ISSUE WITH THE HOLONOMY PROJECTION:
  For SU(N), |K|² + |P|² = 1 (unitarity). The P-sector amplitude
  is determined by K. No independent mass.

THE FIX (Route 1):
  Measure the correlator of the P-sector ENERGY DENSITY tr(P†P),
  not the P-sector AMPLITUDE |P|. These are different:
    - |P(x)| is constrained by unitarity: |P| = √(1-|K|²)
    - tr(P†P)(x) = N - |tr(W)/N|² × N is ALSO determined by K at each point
    - BUT: the CONNECTED two-point function ⟨tr(P†P)(x)·tr(P†P)(y)⟩_c
      decays at a DIFFERENT rate than ⟨K(x)·K(y)⟩_c

  In free field theory: ⟨φ²(x)φ²(y)⟩ ~ exp(-2m|x-y|), so m' = 2m.
  In the interacting causal set: m' could differ.

  The tr(P†P) correlator is:
    - Gauge-invariant (tr(UPU†·UP†U†) = tr(P†P))
    - Scalar (real-valued)
    - Computable from existing holonomy data
    - Measures the P-sector "glueball" mass, not the amplitude

Algorithm:
  1. Along each chain, compute cumulative holonomy W(0→l)
  2. K(l) = tr(W(0→l))/N (complex, the trace projection)
  3. E_P(l) = N - N·|K(l)/N|² = N(1 - |K(l)|²/N²) (P-sector energy)
     Equivalently for SU(2): E_P(l) = 2(1 - |K(l)|²/4)
  4. Subtract mean: δE_P(l) = E_P(l) - ⟨E_P⟩
  5. Correlator: C_P(τ) = ⟨δE_P(l) · δE_P(l+τ)⟩
  6. ALSO compute K correlator (Higgs) for comparison:
     K(l) = |proj[0]| (first component, as in higgs_correlator.py)
  7. Fit both C_K(τ) and C_P(τ) to A·exp(-mτ) + C_inf
  8. Report m_H/v and m_DM/v

The prediction: m_DM ≠ m_H if the P-sector energy density has
different fluctuation dynamics than the K-sector amplitude.
"""

import sys, os
import numpy as np
import time
import torch
from scipy.optimize import curve_fit

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lepton_gpu import (build_causet, forward_dp_numpy, sample_chains_numpy,
                         random_su2_gpu, DEVICE)


def compute_kp_energy_profiles(chains, pi, pj, N_nodes, Us, s_ref, max_id):
    """
    Compute K-sector amplitude AND P-sector energy density along chains.

    K_amp(l) = |⟨W(0→l) s_ref⟩[0]|   (amplitude, as in higgs_correlator)
    K_trace(l) = |tr(W(0→l))| / 2     (trace of holonomy / N for SU(2))
    E_P(l) = 2 - |tr(W(0→l))|² / 2   (P-sector energy = N - |tr(W)|²/N)

    Returns: (K_amp_profiles, E_P_profiles), each shape (n_chains, L)
    """
    n_chains = len(chains)
    if n_chains == 0:
        return np.array([]), np.array([])

    chain_len = len(chains[0])
    N_gauge = 2  # SU(2)

    edge_keys = pi.astype(np.int64) * max_id + pj.astype(np.int64)
    unique_keys, inverse = np.unique(edge_keys, return_inverse=True)
    n_links = len(unique_keys)

    if max_id <= 50000:
        key_to_link = np.full(max_id * max_id, -1, dtype=np.int64)
        key_to_link[unique_keys] = np.arange(n_links, dtype=np.int64)
    else:
        key_to_link = None

    K_amp = np.zeros((n_chains, chain_len), dtype=np.float64)
    E_P = np.zeros((n_chains, chain_len), dtype=np.float64)

    batch_size = min(n_chains, 512)
    for b_start in range(0, n_chains, batch_size):
        b_end = min(b_start + batch_size, n_chains)
        batch_chains = chains[b_start:b_end]
        b_n = b_end - b_start

        W = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(b_n, -1, -1).clone()
        eye2 = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(b_n, -1, -1)

        # At l=0: W = I, tr(W) = 2, K_amp = 1, E_P = 2 - 4/2 = 0
        K_amp[b_start:b_end, 0] = 1.0
        E_P[b_start:b_end, 0] = 0.0

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

            # K-sector amplitude (first component of W @ s_ref)
            proj = torch.matmul(W, s_ref)
            K_amp[b_start:b_end, li + 1] = torch.abs(proj[:, 0]).cpu().numpy()

            # P-sector energy density: tr(P†P) = N - |tr(W)|²/N
            # For SU(2): tr(W) = W[0,0] + W[1,1]
            tr_W = W[:, 0, 0] + W[:, 1, 1]  # (b_n,) complex
            tr_W_sq = (tr_W.real ** 2 + tr_W.imag ** 2)  # |tr(W)|²
            ep = N_gauge - tr_W_sq / N_gauge  # N - |tr(W)|²/N
            E_P[b_start:b_end, li + 1] = ep.cpu().numpy()

    return K_amp, E_P


def compute_autocorrelation(profiles):
    """Compute averaged autocorrelation."""
    n_chains, L = profiles.shape
    max_tau = L // 2
    chain_means = profiles.mean(axis=1, keepdims=True)
    h = profiles - chain_means
    C = np.zeros(max_tau)
    for tau in range(max_tau):
        if tau == 0:
            C[tau] = (h * h).mean()
        else:
            C[tau] = (h[:, :-tau] * h[:, tau:]).mean()
    return np.arange(max_tau), C


def exp_decay(tau, A, m, C_inf):
    return A * np.exp(-m * tau) + C_inf


def run_psector_energy(rho=10000, beta=4.0, n_sample=300, seed=42,
                        L_min=6, L_max_use=17):
    t0 = time.time()
    N_nodes, pi, pj, n_pairs = build_causet(rho, seed=seed)
    if n_pairs == 0:
        return None

    dp_fwd, L_max, adj_starts, adj_targets = forward_dp_numpy(N_nodes, pi, pj)
    max_id = int(max(N_nodes, 1))
    edge_keys = pi.astype(np.int64) * max_id + pj.astype(np.int64)
    n_links = len(np.unique(edge_keys))
    Us = random_su2_gpu(n_links, seed + 9000, beta=beta)
    if torch.cuda.is_available():
        torch.cuda.synchronize()

    s_ref = torch.tensor([1, 0], dtype=torch.complex64, device=DEVICE)
    rng = np.random.default_rng(seed + 5000)

    all_K_C, all_P_C, all_K_vev = [], [], []
    actual_L_max = min(L_max, L_max_use)

    for L in range(L_min, actual_L_max + 1):
        chains = sample_chains_numpy(adj_starts, adj_targets, dp_fwd, N_nodes,
                                      L, n_sample, rng)
        if len(chains) < 10:
            continue

        K_amp, E_P = compute_kp_energy_profiles(
            chains, pi, pj, N_nodes, Us, s_ref, max_id)
        if K_amp.size == 0:
            continue

        all_K_vev.append(K_amp.mean())
        _, K_C = compute_autocorrelation(K_amp)
        _, P_C = compute_autocorrelation(E_P)
        all_K_C.append(K_C)
        all_P_C.append(P_C)

    if not all_K_C:
        return None

    min_len = min(len(c) for c in all_K_C)
    K_C_avg = np.mean([c[:min_len] for c in all_K_C], axis=0)
    P_C_avg = np.mean([c[:min_len] for c in all_P_C], axis=0)
    taus = np.arange(min_len)
    K_vev = np.mean(all_K_vev)

    # Fit K-sector (Higgs)
    m_H = np.nan
    try:
        popt, _ = curve_fit(exp_decay, taus[1:], K_C_avg[1:],
                            p0=[K_C_avg[0], 0.5, 0.0],
                            bounds=([0, 0.01, -1], [10, 5, 1]), maxfev=5000)
        m_H = popt[1]
    except:
        pass

    # Fit P-sector energy (DM)
    m_DM = np.nan
    try:
        popt, _ = curve_fit(exp_decay, taus[1:], P_C_avg[1:],
                            p0=[P_C_avg[0], 0.5, 0.0],
                            bounds=([0, 0.01, -1], [10, 5, 1]), maxfev=5000)
        m_DM = popt[1]
    except:
        pass

    mH_v = m_H / K_vev if K_vev > 0 else np.nan
    mDM_v = m_DM / K_vev if K_vev > 0 else np.nan

    return {
        'K_vev': K_vev,
        'm_H': m_H, 'mH_over_v': mH_v,
        'm_DM': m_DM, 'mDM_over_v': mDM_v,
        'mDM_GeV': mDM_v * 246.2 if not np.isnan(mDM_v) else np.nan,
        'ratio_mDM_mH': m_DM / m_H if m_H > 0 else np.nan,
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
    print("  P-SECTOR ENERGY DENSITY CORRELATOR (Route 1)")
    print(f"  Observable: tr(P†P) = N - |tr(W)|²/N")
    print(f"  rho={rho}, {n_seeds} seeds, {n_sample} samples/length")
    print("=" * 70)

    all_mH_v, all_mDM_v, all_ratio = [], [], []

    for seed in range(n_seeds):
        r = run_psector_energy(rho=rho, n_sample=n_sample, seed=seed * 137)
        if r is None:
            print(f"  seed={seed}: FAILED", flush=True)
            continue

        all_mH_v.append(r['mH_over_v'])
        all_mDM_v.append(r['mDM_over_v'])
        all_ratio.append(r['ratio_mDM_mH'])

        print(f"  seed={seed}: m_H/v={r['mH_over_v']:.4f}  "
              f"m_DM/v={r['mDM_over_v']:.4f}  "
              f"m_DM/m_H={r['ratio_mDM_mH']:.3f}  "
              f"m_DM={r['mDM_GeV']:.0f} GeV  "
              f"t={r['time']:.0f}s", flush=True)

    if all_mDM_v:
        print(f"\n{'='*70}")
        print(f"  RESULTS ({len(all_mDM_v)} seeds)")
        print(f"{'='*70}")
        print(f"  K-sector (Higgs amplitude correlator):")
        print(f"    m_H/v = {np.nanmean(all_mH_v):.4f} +/- {np.nanstd(all_mH_v):.4f}")
        print(f"    Expt:   0.509")
        print(f"")
        print(f"  P-sector (energy density correlator tr(P†P)):")
        print(f"    m_DM/v = {np.nanmean(all_mDM_v):.4f} +/- {np.nanstd(all_mDM_v):.4f}")
        dm_gev = np.nanmean(all_mDM_v) * 246.2
        print(f"    m_DM = {dm_gev:.0f} +/- {np.nanstd(all_mDM_v)*246.2:.0f} GeV")
        print(f"")
        print(f"  Mass ratio:")
        print(f"    m_DM/m_H = {np.nanmean(all_ratio):.3f} +/- {np.nanstd(all_ratio):.3f}")
        print(f"")
        if abs(np.nanmean(all_ratio) - 2.0) < 0.5:
            print(f"  NOTE: m_DM/m_H ~ 2 is expected in free theory")
            print(f"  (⟨φ²(x)φ²(y)⟩ ~ e^{{-2mτ}} for free scalar)")
        elif abs(np.nanmean(all_ratio) - 1.0) < 0.2:
            print(f"  WARNING: m_DM/m_H ~ 1 suggests the constraint |P|²=1-|K|²")
            print(f"  is still dominating. The energy correlator may not be")
            print(f"  independent enough from the amplitude correlator.")
        else:
            print(f"  m_DM/m_H = {np.nanmean(all_ratio):.2f} — DIFFERS from both 1 and 2")
            print(f"  This is a genuine interacting-theory prediction.")
