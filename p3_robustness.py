#!/usr/bin/env python3
"""P3 SHORE-UP: robustness appendix for the everpresent-Lambda
exclusion and the l_k bound.

Variants of the subdominant-envelope bound scan
(rho_DE/rho_c0 = OL_base + A*(t0/t - 1), flatness closing Om):
  R1: baseline profiled over OL_base (Om profiled) AND h  [main fix:
      the committed scan held Om at the fiducial value]
  R2: BAO-only (no CMB distance priors)
  R3: no-Lya (drop the z = 2.33 pair) with CMB
  R4: h-grid spacing halved (numerical stability check)
Output: A_2sigma and l_k bound per variant + the exclusion Delta-chi2
of the best stochastic realization re-quoted per variant.
"""
import math
import numpy as np

src = open("desi_likelihood_zero_param.py").read()
head = src[:src.index("# LCDM reference")]
exec(head)

def model_chi2_flex(fde, hgrid, use_cmb=True, drop=()):
    om = 1 - fde[-1] - ORF
    if om <= 0.05 or om >= 0.95: return (np.inf, None)
    E2 = om / a ** 3 + ORF / a ** 4 + fde
    if np.any(E2 <= 0): return (np.inf, None)
    E = np.sqrt(E2)
    DC = build_DC(E)
    keep = [i for i in range(13) if i not in drop]
    Ck = COV[np.ix_(keep, keep)]
    ICk = np.linalg.inv(Ck)
    best = (np.inf, None)
    for h in hgrid:
        rd = rd_drag(om, h)
        DH0 = CKMS / (100 * h)
        vec = []
        for idx in keep:
            z, ty = BAO_Z[idx], BAO_T[idx]
            dm = interp_at(z, DC) * DH0
            dh = DH0 / np.interp(1 / (1 + z), a, E)
            if ty == "DM": vec.append(dm / rd)
            elif ty == "DH": vec.append(dh / rd)
            else: vec.append((z * dm * dm * dh) ** (1 / 3) / rd)
        d = np.array(vec) - BAO_Y[keep]
        chi = d @ ICk @ d
        if use_cmb:
            dmstar = interp_at(ZSTAR, DC) * DH0
            Rsh = math.sqrt(om) * dmstar / DH0
            lA = math.pi * dmstar / (rd * (144.43 / 147.09))
            dc = np.array([Rsh, lA, WB]) - CMB_MU
            chi += dc @ ICMB @ dc
        if chi < best[0]: best = (chi, h)
    return best

def bound_scan(hgrid, use_cmb=True, drop=(), tag=""):
    olgrid = np.linspace(0.60, 0.76, 17)
    def best_at(A):
        b = np.inf
        for ol in olgrid:
            f = ol + A * (t[-1] / np.maximum(t, 1e-30) - 1.0)
            f = np.minimum(f, 1e8)
            c2, h = model_chi2_flex(f, hgrid, use_cmb, drop)
            if c2 < b: b = c2
        return b
    base = best_at(0.0)
    A2s = None; prev = base; prevA = 0.0
    grid = np.linspace(0.0, 0.30, 31)
    for A in grid[1:]:
        c2 = best_at(A)
        if c2 - base > 4 and A2s is None:
            A2s = prevA + (A - prevA) * (4 - (prev - base)) / (c2 - prev)
            break
        prev, prevA = c2, A
    if A2s is None:
        print(f"  [{tag}] no 2-sigma crossing up to A = 0.30 "
              f"(base chi2 = {base:.2f})", flush=True)
        return
    lk = 12.14 * (0.685 / A2s) ** (1 / 3)
    print(f"  [{tag}] base chi2 = {base:.2f}  A_2sigma = {A2s:.4f}  "
          f"l_k >= {lk:.1f} fm", flush=True)

print("== R1: baseline, Om AND h profiled ==", flush=True)
bound_scan(np.linspace(0.55, 0.78, 231), True, (), "R1 full")
print("== R2: BAO-only (no CMB priors) ==", flush=True)
bound_scan(np.linspace(0.55, 0.78, 231), False, (), "R2 BAO-only")
print("== R3: no-Lya ==", flush=True)
bound_scan(np.linspace(0.55, 0.78, 231), True, (11, 12), "R3 no-Lya")
print("== R4: h-grid halved spacing ==", flush=True)
bound_scan(np.linspace(0.55, 0.78, 461), True, (), "R4 fine-h")
print("DONE", flush=True)
