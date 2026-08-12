#!/usr/bin/env python3
"""THE ZERO-PARAMETER DESI LIKELIHOOD RUN.

The dark-energy sector is now fully pinned (EVERPRESENT_LAMBDA_DERIVED
+ CN_DEEP_DAMPING): amplitude dLambda sqrt(V) = kappa sqrt(v_eff)
(parameter-free), edge channel Lambda ~ 1/T with the anchoring
RMS dLambda(T0) = Lambda_obs (equivalently l_k = 12.1 fm - ONE observed
number absorbed), floor channel harmless.  Everything else - the full
z-shape of rho_DE at every BAO redshift and the CMB-era behavior - is
PREDICTION.  This script confronts it with real data:

  DATA: DESI DR2 BAO official mean vector + covariance (13 entries:
  BGS DV, LRG1/LRG2/LRG3+ELG1/ELG2/QSO DM+DH, Lya DH+DM; from
  CobayaSampler/bao_data desi_bao_dr2, i.e. the numbers of
  arXiv:2503.14738) + Planck-2018 compressed distance priors
  (R, l_A, omega_b) = (1.7502, 301.471, 0.02236), sigma = (0.0046,
  0.090, 0.00015), corr(R,lA) = 0.46, corr(R,wb) = -0.66,
  corr(lA,wb) = -0.34 (arXiv:1808.05724).

  MODEL: 400 realizations of the action-law process
  rho_DE(V) = amp * y4(V)/V^{1/4} (independent increments in V^{3/2};
  the July machinery of everpresent_desi.py) with amp FIXED by
  std(f(today)) = 0.685; overlay shape computed on the fiducial
  background [PHYS, perturbative]; per realization flatness closes
  Omega_m,i = 1 - f_i(1) - Omega_r; h profiled over a grid; r_d from
  the standard early-universe fitting formula (the model's DE is
  ~1e-4 at recombination, so the early universe is standard).

  REFERENCES on identical data: flat LCDM (scan Omega_m, h) and
  w0waCDM (scan Omega_m, h, w0, wa - the DESI-preferred class).

Registered readings (BEFORE the run):
  (i)   COMPETITIVE/PREFERRED: conditioned (f_today > 0) median
        Delta-chi2 vs LCDM <= +5, or best quartile <= 0.  If the
        median is NEGATIVE the parameter-free law FITS DESI BETTER
        than Lambda - headline result.
  (ii)  DEAD: conditioned median Delta-chi2 > 25 AND best realization
        > +10: the sector is falsified in its perturbative form.
  (iii) INTERMEDIATE: report; data-limited.
"""
import math
import numpy as np

rng = np.random.default_rng(20260811)

# ---------------- data ------------------------------------------------------
BAO_Z = [0.295, 0.510, 0.510, 0.706, 0.706, 0.934, 0.934,
         1.321, 1.321, 1.484, 1.484, 2.330, 2.330]
BAO_T = ["DV", "DM", "DH", "DM", "DH", "DM", "DH",
         "DM", "DH", "DM", "DH", "DH", "DM"]
BAO_Y = np.array([7.94167639, 13.58758434, 21.86294686, 17.35069094,
                  19.45534918, 21.57563956, 17.64149464, 27.60085612,
                  14.17602155, 30.51190063, 12.81699964,
                  8.631545674846294, 38.988973961958784])
COV = np.zeros((13, 13))
diag = [5.78998687e-03, 2.83473742e-02, 1.83928040e-01, 3.23752442e-02,
        1.11469198e-01, 2.61732816e-02, 4.04183878e-02, 1.05336516e-01,
        5.04233092e-02, 5.83020277e-01, 2.68336193e-01, 1.02136194e-02,
        2.82685779e-01]
for i, d in enumerate(diag): COV[i, i] = d
for (i, j, v) in [(1, 2, -3.26062007e-02), (3, 4, -2.37445646e-02),
                  (5, 6, -1.12938006e-02), (7, 8, -2.90308418e-02),
                  (9, 10, -1.95215562e-01), (11, 12, -2.31395216e-02)]:
    COV[i, j] = COV[j, i] = v
ICOV = np.linalg.inv(COV)

CMB_MU = np.array([1.7502, 301.471, 0.02236])
sR, sLA, sWB = 0.0046, 0.090, 0.00015
CC = np.array([[1, 0.46, -0.66], [0.46, 1, -0.34], [-0.66, -0.34, 1.0]])
CMB_COV = CC * np.outer([sR, sLA, sWB], [sR, sLA, sWB])
ICMB = np.linalg.inv(CMB_COV)
ZSTAR, ZD = 1089.9, 1059.9
WB = 0.02236

def rd_drag(om_m, h):
    # standard fitting formula (Aubourg+15), Mpc
    wm = om_m * h * h
    return 147.05 * (wm / 0.1432) ** -0.23 * (WB / 0.02236) ** -0.13

# ---------------- fiducial background + process -----------------------------
OMF, ORF = 0.315, 4.15e-5 / 0.674 ** 2
n = 6000
a = np.geomspace(1e-9, 1.0, n)
Hf = np.sqrt(OMF / a ** 3 + ORF / a ** 4 + (1 - OMF - ORF))
t = np.zeros(n); eta = np.zeros(n)
t[0] = a[0] ** 2 / (2 * math.sqrt(ORF)); eta[0] = a[0] / math.sqrt(ORF)
for i in range(1, n):
    da = a[i] - a[i - 1]
    t[i] = t[i - 1] + da / (0.5 * (a[i] * Hf[i] + a[i - 1] * Hf[i - 1]))
    eta[i] = eta[i - 1] + da / (0.5 * (a[i] ** 2 * Hf[i] +
                                       a[i - 1] ** 2 * Hf[i - 1]))
I0 = np.concatenate([[0], np.cumsum(0.5 * (a[1:] ** 3 + a[:-1] ** 3)
                                    * np.diff(t))])
I1 = np.concatenate([[0], np.cumsum(0.5 * (a[1:] ** 3 * eta[1:] +
                                    a[:-1] ** 3 * eta[:-1]) * np.diff(t))])
I2 = np.concatenate([[0], np.cumsum(0.5 * (a[1:] ** 3 * eta[1:] ** 2 +
                                    a[:-1] ** 3 * eta[:-1] ** 2)
                                    * np.diff(t))])
I3 = np.concatenate([[0], np.cumsum(0.5 * (a[1:] ** 3 * eta[1:] ** 3 +
                                    a[:-1] ** 3 * eta[:-1] ** 3)
                                    * np.diff(t))])
V = (4 * np.pi / 3) * (eta ** 3 * I0 - 3 * eta ** 2 * I1 + 3 * eta * I2 - I3)
V = np.maximum.accumulate(np.maximum(V, 1e-300))

NREAL = 400
W = V ** 1.5
dW = np.diff(W, prepend=0.0)
F = np.zeros((NREAL, n))
for r in range(NREAL):
    xi = rng.normal(size=n)
    B = np.cumsum(np.sqrt(np.maximum(dW, 0)) * xi)
    F[r] = (B / np.sqrt(W)) / V ** 0.25
F *= 0.685 / F[:, -1].std()          # FIXED amplitude: std f(today) = 0.685
print(f"realizations: {NREAL}; std f(1) = {F[:, -1].std():.3f}; "
      f"f(1)>0: {(F[:, -1] > 0).mean():.2f}", flush=True)

# ---------------- distances and chi2 ----------------------------------------
CKMS = 2.99792458e5

def build_DC(E):
    integ = 1.0 / (a ** 2 * E)
    # cumulative from a=1 downward
    seg = 0.5 * (integ[1:] + integ[:-1]) * np.diff(a)
    DCrev = np.concatenate([[0], np.cumsum(seg[::-1])])[::-1]
    return DCrev            # DC[i] = int_{a_i}^{1} da/(a^2 E)  (units c/H0)

def interp_at(z, arr):
    az = 1.0 / (1 + z)
    return np.interp(az, a, arr)

def model_chi2(fde, hgrid, ret=False):
    om = 1 - fde[-1] - ORF
    if om <= 0.05 or om >= 0.95: return (np.inf, None) if not ret else None
    E2 = om / a ** 3 + ORF / a ** 4 + fde
    if np.any(E2 <= 0): return (np.inf, None) if not ret else None
    E = np.sqrt(E2)
    DC = build_DC(E)
    best = (np.inf, None)
    for h in hgrid:
        rd = rd_drag(om, h)
        DH0 = CKMS / (100 * h)               # c/H0 in Mpc
        vec = []
        for z, ty in zip(BAO_Z, BAO_T):
            dm = interp_at(z, DC) * DH0
            dh = DH0 / np.interp(1 / (1 + z), a, E)
            if ty == "DM": vec.append(dm / rd)
            elif ty == "DH": vec.append(dh / rd)
            else: vec.append((z * dm * dm * dh) ** (1 / 3) / rd)
        vec = np.array(vec)
        dbao = vec - BAO_Y
        chi_bao = dbao @ ICOV @ dbao
        # CMB
        dmstar = interp_at(ZSTAR, DC) * DH0
        Rsh = math.sqrt(om) * dmstar / DH0 * 1.0   # sqrt(om) H0 DM / c
        rs_star = rd * (144.43 / 147.09)
        lA = math.pi * dmstar / rs_star
        dc = np.array([Rsh, lA, WB]) - CMB_MU
        chi = chi_bao + dc @ ICMB @ dc
        if chi < best[0]: best = (chi, h)
    return best

hgrid = np.linspace(0.55, 0.78, 231)

# LCDM reference
bestL = (np.inf, None, None)
for omx in np.linspace(0.26, 0.36, 41):
    fconst = np.full(n, 1 - omx - ORF)
    c2, h = model_chi2(fconst, hgrid)
    if c2 < bestL[0]: bestL = (c2, omx, h)
print(f"LCDM: chi2 = {bestL[0]:.2f} at Om = {bestL[1]:.3f}, "
      f"h = {bestL[2]:.3f}", flush=True)

# w0waCDM reference (coarse)
bestW = (np.inf, None)
for omx in np.linspace(0.28, 0.36, 17):
    for w0 in np.linspace(-1.1, -0.5, 13):
        for wa in np.linspace(-1.6, 0.4, 11):
            f_w = (1 - omx - ORF) * a ** (-3 * (1 + w0 + wa)) * \
                np.exp(-3 * wa * (1 - a))
            c2, h = model_chi2(f_w, hgrid)
            if c2 < bestW[0]: bestW = (c2, (omx, w0, wa, h))
print(f"w0waCDM: chi2 = {bestW[0]:.2f} at (Om, w0, wa, h) = "
      f"{tuple(round(x, 3) for x in bestW[1])}", flush=True)

# everpresent realizations
res = []
for r in range(NREAL):
    if F[r, -1] <= 0:
        res.append((np.inf, r, None)); continue
    c2, h = model_chi2(F[r], hgrid)
    res.append((c2, r, h))
chis = np.array([x[0] for x in res])
cond = np.isfinite(chis)
cc = np.sort(chis[cond])
dchi = cc - bestL[0]
print(f"\neverpresent action law ({cond.sum()} realizations with "
      f"f(1)>0 and viable background):", flush=True)
print(f"  chi2: min = {cc[0]:.2f}  16% = {np.percentile(cc, 16):.2f}  "
      f"median = {np.percentile(cc, 50):.2f}  84% = "
      f"{np.percentile(cc, 84):.2f}")
print(f"  Delta-chi2 vs LCDM: min = {dchi[0]:+.2f}  median = "
      f"{np.median(dchi):+.2f}  best quartile <= {np.percentile(dchi,25):+.2f}")
print(f"  fraction of realizations beating LCDM: {(dchi < 0).mean():.3f}")
print(f"  (w0waCDM beats LCDM by {bestL[0]-bestW[0]:.2f} on this data)")
ibest = int(np.argmin(chis))
print(f"  best realization: idx {ibest}, chi2 = {chis[ibest]:.2f}, "
      f"h = {res[ibest][2]:.3f}, f(1) = {F[ibest, -1]:.3f}, "
      f"Om = {1 - F[ibest, -1] - ORF:.3f}")
# marginal (anthropic-caveat) factor over ALL realizations
Lmarg = np.mean(np.exp(-0.5 * np.minimum(chis - bestL[0], 200)))
print(f"  ensemble-marginal factor <exp(-dchi2/2)> = {Lmarg:.3e} "
      f"(includes wrong-sign/wrong-size realizations; anthropic caveat)")

# ---------------- deterministic drift law (self-tuning channel) -------------
# The lambda-bridge arc's deterministic alternative: sign-coherent
# Lambda ~ 1/T (the envelope followed smoothly; <S>/n self-tuning drift),
# amplitude anchored at 0.685 today.  Zero free parameters beyond h.
f_det = 0.685 * (t[-1] / np.maximum(t, 1e-30))
f_det = np.minimum(f_det, 1e8)
c2d, hd = model_chi2(f_det, hgrid)
print(f"\ndeterministic drift law rho_DE = 0.685 rho_c0 (t0/t):")
print(f"  chi2 = {c2d:.2f} at h = {hd}, Delta vs LCDM = {c2d-bestL[0]:+.2f},"
      f" vs w0waCDM = {c2d-bestW[0]:+.2f}")
# effective CPL of the deterministic law for reporting
sel = a >= 0.5
w_eff = -1 - np.gradient(np.log(f_det[sel]), np.log(a[sel])) / 3
X = np.vstack([np.ones(sel.sum()), 1 - a[sel]]).T
w0d, wad = np.linalg.lstsq(X, w_eff, rcond=None)[0]
print(f"  effective (w0, wa) over z<1: ({w0d:+.3f}, {wad:+.3f})")

# ---------------- the derived bound on l_k ----------------------------------
# Exclusion -> bound: a subdominant everpresent envelope atop a constant
# Lambda (total pinned to 0.685 today):
#   rho_DE(a)/rho_c0 = 0.685 + A ((t0/t) - 1)
# Delta-chi2(A) = 4 defines A_2sigma; amplitude ~ l_k^-3 gives
#   l_k >= 12.14 fm * (0.685/A_2sigma)^{1/3}.
print("\nbound scan: subdominant envelope atop constant Lambda:")
prev = None
A2s = None
for A in np.linspace(0.0, 0.12, 25):
    f_mix = 0.685 + A * (t[-1] / np.maximum(t, 1e-30) - 1.0)
    f_mix = np.minimum(f_mix, 1e8)
    c2m, hm = model_chi2(f_mix, hgrid)
    if A in (0.0, 0.02, 0.05, 0.1) or True:
        pass
    if prev is None: base = c2m
    if c2m - base > 4 and A2s is None and prev is not None:
        # linear interpolation in A
        A2s = prevA + (A - prevA) * (4 - (prev - base)) / (c2m - prev)
    prev, prevA = c2m, A
    if abs(A - round(A, 2)) < 1e-9 and round(A * 100) % 2 == 0:
        print(f"  A = {A:.3f}: chi2 = {c2m:.2f} (Delta = {c2m - base:+.2f})")
if A2s is not None:
    lk_bound = 12.14 * (0.685 / A2s) ** (1 / 3)
    print(f"  A_2sigma = {A2s:.4f}  ->  l_k >= {lk_bound:.1f} fm "
          f"(gravitational nonlocality, DESI-derived)")
else:
    print("  no 2-sigma crossing in scan range")
print("DONE")
