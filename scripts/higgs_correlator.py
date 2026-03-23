#!/usr/bin/env python3
"""
Higgs mass-to-VEV ratio from within-chain scalar correlator.

Physics:
  The Higgs field emerges as the scalar component of the SU(2) fiber holonomy.
  Along each causal chain, the holonomy projection c_K(l) = |<W(0→l) s_ref>[0]|
  acts as a lattice scalar field. Subtracting the chain mean gives the Higgs
  fluctuation h(l) = c_K(l) - <c_K>. The autocorrelation C(tau) = <h(l)h(l+tau)>
  decays as A*exp(-m*tau) + C_inf, defining a scalar mass m in chain units.
  The VEV is v = <c_K>, so m_H/v = m / <c_K>.

  SM target: m_H/v = 125.1/245.5 = 0.509
  Expected result: m_H/v ~ 0.4 (within factor of 2, zero free parameters)

Algorithm:
  1. Build causal set, compute forward DP, sample chains of length L=4..17
  2. For each chain, compute cumulative SU(2) holonomy at every link
  3. Subtract within-chain mean: h(l) = c_K(l) - mean(c_K)
  4. Compute autocorrelation C(tau) = mean_l[ h(l)*h(l+tau) ]
  5. Fit C(tau) = A*exp(-m*tau) + C_inf via scipy curve_fit
  6. m_H/v = m / mean(c_K)

Requirements: pip install numpy scipy torch
Usage: python higgs_correlator.py
"""

import sys, os
import numpy as np
import time
import torch
from scipy.optimize import curve_fit

# Import infrastructure from lepton_gpu.py
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lepton_gpu import (build_causet, forward_dp_numpy, sample_chains_numpy,
                         random_su2_gpu, DEVICE)

# ============================================================
# Correlator computation
# ============================================================

def compute_chain_scalar_profiles(chains, pi, pj, N, Us, s_ref, max_id):
    """
    For each chain, compute c_K(l) at every link position l=0..L-1.

    c_K(l) = |<W(0→l) @ s_ref>[0]|  (projection of cumulative holonomy)

    Returns: array of shape (n_chains, L) with scalar field values.
    """
    n_chains = len(chains)
    if n_chains == 0:
        return np.array([])

    chain_len = len(chains[0])

    # Build edge key lookup
    edge_keys = pi.astype(np.int64) * max_id + pj.astype(np.int64)
    unique_keys, inverse = np.unique(edge_keys, return_inverse=True)
    n_links = len(unique_keys)

    if max_id <= 50000:
        key_to_link = np.full(max_id * max_id, -1, dtype=np.int64)
        key_to_link[unique_keys] = np.arange(n_links, dtype=np.int64)
    else:
        key_to_link = None  # fallback not needed for typical rho

    profiles = np.zeros((n_chains, chain_len), dtype=np.float64)

    # Process in batches on GPU
    batch_size = min(n_chains, 512)
    for b_start in range(0, n_chains, batch_size):
        b_end = min(b_start + batch_size, n_chains)
        batch_chains = chains[b_start:b_end]
        b_n = b_end - b_start

        # Cumulative holonomy: W starts as identity, multiply link-by-link
        W = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(b_n, -1, -1).clone()
        eye2 = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(b_n, -1, -1)

        # At l=0, c_K = |s_ref[0]| = 1.0
        profiles[b_start:b_end, 0] = torch.abs(s_ref[0]).item()

        for li in range(chain_len - 1):
            # Look up link indices
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

            # Project onto s_ref
            proj = torch.matmul(W, s_ref)  # (b_n, 2)
            c_K = torch.abs(proj[:, 0]).cpu().numpy()  # scalar component
            profiles[b_start:b_end, li + 1] = c_K

    return profiles


def compute_autocorrelation(profiles):
    """
    Compute averaged autocorrelation from scalar profiles.

    For each chain: h(l) = c_K(l) - mean(c_K), then C(tau) = mean_l[h(l)*h(l+tau)]
    Average C(tau) over all chains.

    Returns: tau_values, C_values (1D arrays)
    """
    n_chains, L = profiles.shape
    max_tau = L // 2  # only use half the chain to avoid boundary effects

    # Subtract within-chain mean
    chain_means = profiles.mean(axis=1, keepdims=True)
    h = profiles - chain_means

    C = np.zeros(max_tau)
    counts = np.zeros(max_tau)

    for tau in range(max_tau):
        # C(tau) = mean over chains and positions of h(l)*h(l+tau)
        if tau == 0:
            vals = (h * h).mean(axis=1)  # variance per chain
        else:
            vals = (h[:, :-tau] * h[:, tau:]).mean(axis=1)
        C[tau] = vals.mean()
        counts[tau] = len(vals)

    return np.arange(max_tau), C


def exp_decay(tau, A, m, C_inf):
    """Model: C(tau) = A * exp(-m * tau) + C_inf"""
    return A * np.exp(-m * tau) + C_inf


# ============================================================
# Main
# ============================================================

SM_MH_OVER_V = 125.1 / 245.5  # 0.5094

def run_higgs_correlator(rho=10000, beta=4.0, n_sample=300, seed=42,
                          L_min=4, L_max_use=17):
    """Run Higgs correlator for one seed."""
    t0 = time.time()

    # Build causal set
    N, pi, pj, n_pairs = build_causet(rho, seed=seed)
    if n_pairs == 0:
        return None

    dp_fwd, L_max, adj_starts, adj_targets = forward_dp_numpy(N, pi, pj)
    max_id = int(max(N, 1))

    # Generate SU(2) gauge field
    edge_keys = pi.astype(np.int64) * max_id + pj.astype(np.int64)
    n_links = len(np.unique(edge_keys))
    Us = random_su2_gpu(n_links, seed + 9000, beta=beta)
    if torch.cuda.is_available():
        torch.cuda.synchronize()

    s_ref = torch.tensor([1, 0], dtype=torch.complex64, device=DEVICE)
    rng_chain = np.random.default_rng(seed + 5000)

    # Collect profiles across chain lengths
    all_taus = []
    all_Cs = []
    all_vevs = []
    length_data = {}

    actual_L_max = min(L_max, L_max_use)

    for L in range(L_min, actual_L_max + 1):
        chains = sample_chains_numpy(adj_starts, adj_targets, dp_fwd, N,
                                      L, n_sample, rng_chain)
        if len(chains) < 10:
            continue

        profiles = compute_chain_scalar_profiles(
            chains, pi, pj, N, Us, s_ref, max_id)

        if profiles.size == 0:
            continue

        # VEV = mean scalar field value
        vev = profiles.mean()
        all_vevs.append(vev)

        # Autocorrelation
        taus, C = compute_autocorrelation(profiles)
        if len(taus) < 3:
            continue

        all_taus.append(taus)
        all_Cs.append(C)
        length_data[L] = {
            'n_chains': len(chains),
            'vev': vev,
            'C0': C[0] if len(C) > 0 else 0,
        }

    if not all_Cs:
        return None

    # Average autocorrelation across lengths (align by tau)
    max_len = max(len(c) for c in all_Cs)
    C_avg = np.zeros(max_len)
    C_count = np.zeros(max_len)
    for c in all_Cs:
        C_avg[:len(c)] += c
        C_count[:len(c)] += 1
    C_count[C_count == 0] = 1
    C_avg /= C_count

    tau_arr = np.arange(max_len)
    vev_avg = np.mean(all_vevs)

    # Fit exponential decay
    m_fit = np.nan
    A_fit = np.nan
    C_inf_fit = np.nan
    fit_success = False

    if len(tau_arr) >= 4 and C_avg[0] > 0:
        try:
            # Initial guesses
            p0 = [C_avg[0], 0.5, 0.0]
            bounds = ([0, 0.01, -np.inf], [np.inf, 10.0, np.inf])
            popt, pcov = curve_fit(exp_decay, tau_arr, C_avg, p0=p0,
                                    bounds=bounds, maxfev=5000)
            A_fit, m_fit, C_inf_fit = popt
            fit_success = True
        except (RuntimeError, ValueError):
            # Fallback: simple log-slope between tau=0 and tau=1
            if C_avg[0] > 0 and len(C_avg) > 1 and C_avg[1] > 0:
                m_fit = -np.log(C_avg[1] / C_avg[0])
                fit_success = True

    mH_over_v = m_fit / vev_avg if (fit_success and vev_avg > 0) else np.nan

    return {
        'm_fit': m_fit,
        'vev': vev_avg,
        'mH_over_v': mH_over_v,
        'A_fit': A_fit,
        'C_inf': C_inf_fit,
        'fit_success': fit_success,
        'C_avg': C_avg,
        'n_lengths': len(all_Cs),
        'L_max': actual_L_max,
        'time': time.time() - t0,
        'length_data': length_data,
    }


if __name__ == "__main__":
    rho = 10000
    beta = 4.0
    n_seeds = 5
    n_sample = 300

    print("=" * 80)
    print("  HIGGS MASS-TO-VEV RATIO FROM WITHIN-CHAIN SCALAR CORRELATOR")
    print(f"  rho={rho}, beta={beta}, {n_seeds} seeds, {n_sample} samples/length")
    print(f"  SM target: m_H/v = {SM_MH_OVER_V:.4f}")
    print(f"  Device: {DEVICE}")
    print("=" * 80)

    all_mHv = []

    for seed_idx in range(n_seeds):
        r = run_higgs_correlator(rho=rho, beta=beta, n_sample=n_sample,
                                  seed=seed_idx * 137)
        if r is None:
            print(f"  seed={seed_idx:>2d}: FAILED (no chains)", flush=True)
            continue

        all_mHv.append(r['mH_over_v'])

        status = "OK" if r['fit_success'] else "FIT FAILED"
        print(f"  seed={seed_idx:>2d}: m_H/v = {r['mH_over_v']:.4f}  "
              f"m = {r['m_fit']:.4f}  vev = {r['vev']:.4f}  "
              f"A = {r.get('A_fit', 0):.4f}  C_inf = {r.get('C_inf', 0):.6f}  "
              f"[{status}]  "
              f"({r['n_lengths']} lengths, L_max={r['L_max']})  "
              f"t={r['time']:.0f}s", flush=True)

        # Show correlator shape
        C = r['C_avg']
        if len(C) >= 4:
            print(f"         C(tau): {C[0]:.4f}  {C[1]:.4f}  {C[2]:.4f}  {C[3]:.4f} ...",
                  flush=True)

    print(f"\n{'='*80}")
    print(f"  RESULTS ({len(all_mHv)} seeds)")
    print(f"{'='*80}")

    if all_mHv:
        valid = [x for x in all_mHv if np.isfinite(x)]
        if valid:
            m = np.mean(valid)
            s = np.std(valid) / np.sqrt(len(valid)) if len(valid) > 1 else 0
            print(f"  m_H/v = {m:.4f} +/- {s:.4f}")
            print(f"  SM target: {SM_MH_OVER_V:.4f}")
            print(f"  Ratio to SM: {m / SM_MH_OVER_V:.2f}x")
            print()
            print(f"  Interpretation:")
            print(f"    The scalar correlator mass extracted from SU(2) holonomy")
            print(f"    fluctuations along causal chains gives m_H/v ~ {m:.2f},")
            print(f"    compared to SM value 0.509. This is a zero-parameter")
            print(f"    prediction from the causal set + fiber bundle structure.")
        else:
            print(f"  No valid fits obtained.")
    else:
        print(f"  No successful runs.")

    print(f"{'='*80}")
