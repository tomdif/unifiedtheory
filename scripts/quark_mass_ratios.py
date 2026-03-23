#!/usr/bin/env python3
"""
Quark mass ratios from Casimir scaling + hypercharge + generation phase.

Physics:
  The inter-sector mass ratio m_t/m_b relates to the lepton ratio r_mu_tau
  via the gauge Casimir invariants and hypercharge assignments:

    m_t/m_b = (1/r_mu_tau) * (C2(SU3)/C2(SU2)) * |Y(t_R)/Y(b_R)|

  where:
    C2(SU3) = 4/3  (fundamental rep quadratic Casimir)
    C2(SU2) = 3/4  (fundamental rep quadratic Casimir)
    Y(t_R)  = +4/3 (right-handed top hypercharge)
    Y(b_R)  = -2/3 (right-handed bottom hypercharge)

  So: m_t/m_b = (1/r_mu_tau) * (16/9) * 2 = 32 / (9 * r_mu_tau)

  This is proved in CasimirScaling.lean and requires no new simulation --
  it reuses the lepton r_mu_tau.

  For intra-sector ratios (m_u/m_t, m_c/m_t, m_d/m_b, m_s/m_b), we apply
  the generation phase mechanism from generation_phase.py, but now to SU(3)
  holonomy for the quark sector.

  Experimental values:
    m_t/m_b = 173.0/4.18  = 41.4
    m_c/m_t = 1.27/173.0  = 0.00734
    m_u/m_t = 0.00216/173.0 = 1.25e-5
    m_s/m_b = 0.093/4.18  = 0.0222
    m_d/m_b = 0.0047/4.18 = 0.00112

Requirements: pip install numpy scipy torch
Usage: python quark_mass_ratios.py
"""

import sys, os
import numpy as np
import time
import torch

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lepton_gpu import (build_causet, forward_dp_numpy, count_paths_gpu,
                         sample_chains_numpy, random_su2_gpu, DEVICE)
from cabibbo_gpu import random_su3_fast, random_su2_fast

# ============================================================
# Constants
# ============================================================

# Quadratic Casimir invariants (fundamental representation)
C2_SU3 = 4.0 / 3.0   # SU(3) fundamental
C2_SU2 = 3.0 / 4.0    # SU(2) fundamental

# Hypercharges (SM normalization)
Y_tR = 4.0 / 3.0      # right-handed top
Y_bR = -2.0 / 3.0     # right-handed bottom
Y_uR = 4.0 / 3.0      # right-handed up (same as top)
Y_dR = -2.0 / 3.0     # right-handed down (same as bottom)

# Casimir + hypercharge ratio
CASIMIR_RATIO = C2_SU3 / C2_SU2       # 16/9
HYPERCHARGE_RATIO = abs(Y_tR / Y_bR)   # 2

# Experimental quark masses (PDG 2024, MS-bar at respective scales)
M_TOP = 173.0     # GeV
M_BOTTOM = 4.18   # GeV
M_CHARM = 1.27    # GeV
M_UP = 0.00216    # GeV
M_STRANGE = 0.093 # GeV
M_DOWN = 0.0047   # GeV

EXP_MT_MB = M_TOP / M_BOTTOM       # 41.4
EXP_MC_MT = M_CHARM / M_TOP        # 0.00734
EXP_MU_MT = M_UP / M_TOP           # 1.25e-5
EXP_MS_MB = M_STRANGE / M_BOTTOM   # 0.0222
EXP_MD_MB = M_DOWN / M_BOTTOM      # 0.00112
EXP_MU_TAU = 0.0595                # m_mu/m_tau

# Generation phase
ALPHA_PLANCK = 3.0 / (32.0 * np.pi)  # ~ 0.02984

# ============================================================
# Compute r_mu_tau from lepton sector
# ============================================================

def compute_r_mu_tau(rho, n_sample=300, seed=42, beta=4.0):
    """
    Compute the lepton mass ratio r = m_mu/m_tau from count-weighted SU(2) holonomy.
    Same algorithm as lepton_gpu.py.
    """
    from lepton_gpu import compute_holonomy_gpu

    N, pi, pj, n_pairs = build_causet(rho, seed=seed)
    if n_pairs == 0:
        return 0.0, {}

    dp_fwd, L_max, adj_starts, adj_targets = forward_dp_numpy(N, pi, pj)
    path_counts = count_paths_gpu(N, pi, pj, L_max)

    max_id = int(max(N, 1))
    edge_keys = pi.astype(np.int64) * max_id + pj.astype(np.int64)
    unique_keys, _ = np.unique(edge_keys, return_inverse=True)
    n_links = len(unique_keys)

    if max_id <= 50000:
        key_to_link = np.full(max_id * max_id, -1, dtype=np.int64)
        key_to_link[unique_keys] = np.arange(n_links, dtype=np.int64)
    else:
        sort_order = np.argsort(unique_keys)
        sorted_keys = unique_keys[sort_order]
        key_to_link = (sorted_keys, sort_order)

    Us = random_su2_gpu(n_links, seed + 9000, beta=beta)
    if torch.cuda.is_available():
        torch.cuda.synchronize()

    s_ref = torch.tensor([1, 0], dtype=torch.complex64, device=DEVICE)
    rng_chain = np.random.default_rng(seed + 5000)

    c_weighted = torch.zeros(2, dtype=torch.complex64, device=DEVICE)
    total_weight = 0.0
    length_data = {}

    for L in range(2, L_max + 1):
        count = path_counts.get(L, 0.0)
        if count == 0:
            continue
        chains = sample_chains_numpy(adj_starts, adj_targets, dp_fwd, N,
                                      L, n_sample, rng_chain)
        if not chains:
            continue
        n_found = len(chains)
        c_sum = compute_holonomy_gpu(chains, key_to_link, max_id, Us, s_ref)
        c_avg = c_sum / n_found
        c_weighted += count * c_avg
        total_weight += count
        length_data[L] = count

    if total_weight == 0:
        return 0.0, length_data

    c_weak = (c_weighted / total_weight).cpu().numpy()
    c_norm = np.abs(c_weak)
    masses = np.sort(c_norm)[::-1]
    r = float(masses[1] / masses[0]) if masses[0] > 0 else 0

    return r, length_data


def compute_quark_generation_ratios(length_data, alpha, beta_color=6.0, seed=42):
    """
    Compute intra-sector quark mass ratios using generation phase + SU(3) holonomy.

    For each chain length L, the SU(3) holonomy weight w_L enters a 3x3 Yukawa:
      Y[a,b] = sum_L n(L) * exp(2*pi*i*(a-b)*alpha*L) * w_L

    Returns (m_1/m_3, m_2/m_3) for the sector.
    """
    if not length_data:
        return 0.0, 0.0

    # For SU(3) holonomy weights, we use the path count structure
    # and compute average SU(3) projection at each length.
    # At this level of approximation, w_L ~ 1/sqrt(L) (random walk on SU(3))
    # The generation phase does the heavy lifting.
    Y = np.zeros((3, 3), dtype=np.complex128)

    for L, count in length_data.items():
        # SU(3) holonomy average projection decays as 1/sqrt(L) for random walk
        w_L = 1.0 / np.sqrt(float(L))
        for a in range(3):
            for b in range(3):
                phase = np.exp(2j * np.pi * (a - b) * alpha * L)
                Y[a, b] += count * phase * w_L

    M = Y.conj().T @ Y
    eigvals = np.sort(np.abs(np.linalg.eigvalsh(M)))[::-1]

    if eigvals[0] <= 0:
        return 0.0, 0.0

    masses = np.sqrt(eigvals)
    r_12 = masses[2] / masses[0] if masses[0] > 0 else 0  # lightest/heaviest
    r_22 = masses[1] / masses[0] if masses[0] > 0 else 0  # middle/heaviest

    return r_12, r_22


# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    rho = 10000
    beta = 4.0
    n_seeds = 5
    n_sample = 300

    print("=" * 80)
    print("  QUARK MASS RATIOS: CASIMIR SCALING + GENERATION PHASE")
    print(f"  rho={rho}, beta={beta}, {n_seeds} seeds, {n_sample} samples/length")
    print(f"  Device: {DEVICE}")
    print("=" * 80)

    # ----------------------------------------------------------
    # Part 1: Casimir formula for m_t/m_b
    # ----------------------------------------------------------
    print(f"\n  CASIMIR + HYPERCHARGE FORMULA (proved in CasimirScaling.lean):")
    print(f"    m_t/m_b = (1/r_mu_tau) * (C2(SU3)/C2(SU2)) * |Y(t_R)/Y(b_R)|")
    print(f"            = (1/r_mu_tau) * ({CASIMIR_RATIO:.4f}) * ({HYPERCHARGE_RATIO:.1f})")
    print(f"            = {32.0/9.0:.4f} / r_mu_tau")
    print(f"    Expt: m_t/m_b = {EXP_MT_MB:.1f}")

    all_r_mu_tau = []
    all_mt_mb = []
    all_r_up_light = []
    all_r_up_mid = []

    for seed_idx in range(n_seeds):
        t0 = time.time()
        r_mu_tau, length_data = compute_r_mu_tau(rho, n_sample=n_sample,
                                                   seed=seed_idx * 137, beta=beta)
        if r_mu_tau <= 0:
            print(f"  seed={seed_idx:>2d}: FAILED", flush=True)
            continue

        mt_mb = 32.0 / (9.0 * r_mu_tau)
        all_r_mu_tau.append(r_mu_tau)
        all_mt_mb.append(mt_mb)

        # Generation phase for up-type sector
        r_light, r_mid = compute_quark_generation_ratios(
            length_data, ALPHA_PLANCK, seed=seed_idx * 137)
        all_r_up_light.append(r_light)
        all_r_up_mid.append(r_mid)

        dt = time.time() - t0
        print(f"  seed={seed_idx:>2d}: r_mu_tau = {r_mu_tau:.5f}  "
              f"m_t/m_b = {mt_mb:.1f}  "
              f"(m_u/m_t ~ {r_light:.6f}, m_c/m_t ~ {r_mid:.5f})  "
              f"t={dt:.0f}s", flush=True)

    # ----------------------------------------------------------
    # Summary
    # ----------------------------------------------------------
    print(f"\n{'='*80}")
    print(f"  RESULTS ({len(all_r_mu_tau)} seeds)")
    print(f"{'='*80}")

    if all_r_mu_tau:
        n = len(all_r_mu_tau)

        # r_mu_tau
        m_r = np.mean(all_r_mu_tau)
        s_r = np.std(all_r_mu_tau) / np.sqrt(n) if n > 1 else 0
        print(f"\n  Input:")
        print(f"    r_mu_tau = {m_r:.5f} +/- {s_r:.5f}  (expt: {EXP_MU_TAU})")

        # m_t/m_b (Casimir formula)
        m_tb = np.mean(all_mt_mb)
        s_tb = np.std(all_mt_mb) / np.sqrt(n) if n > 1 else 0
        print(f"\n  Inter-sector (Casimir + hypercharge):")
        print(f"    m_t/m_b = {m_tb:.1f} +/- {s_tb:.1f}  "
              f"(expt: {EXP_MT_MB:.1f}, ratio: {m_tb/EXP_MT_MB:.2f}x)")

        # Generation phase ratios
        if all_r_up_light:
            m_ul = np.mean(all_r_up_light)
            s_ul = np.std(all_r_up_light) / np.sqrt(n) if n > 1 else 0
            m_um = np.mean(all_r_up_mid)
            s_um = np.std(all_r_up_mid) / np.sqrt(n) if n > 1 else 0

            print(f"\n  Intra-sector (generation phase, alpha = 3/(32*pi)):")
            print(f"    Up-type sector:")
            print(f"      m_u/m_t = {m_ul:.6f} +/- {s_ul:.6f}  "
                  f"(expt: {EXP_MU_MT:.6f})")
            print(f"      m_c/m_t = {m_um:.5f} +/- {s_um:.5f}  "
                  f"(expt: {EXP_MC_MT:.5f})")

        print(f"\n  Formula summary:")
        print(f"    C2(SU3)/C2(SU2) = (4/3)/(3/4) = {CASIMIR_RATIO:.4f}")
        print(f"    |Y(t_R)/Y(b_R)| = |(+4/3)/(-2/3)| = {HYPERCHARGE_RATIO:.1f}")
        print(f"    m_t/m_b = 32/(9 * r_mu_tau) = 32/(9 * {m_r:.5f}) = {m_tb:.1f}")
    else:
        print(f"  No successful runs.")

    print(f"{'='*80}")
