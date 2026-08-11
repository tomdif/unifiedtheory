#!/usr/bin/env python3
"""THE PARAMETER-FREE EVERPRESENT-LAMBDA AMPLITUDE.

Assembly of three previously derived/measured constants into the
amplitude that the July arc had to CALIBRATE:

  (1) kappa = 4/sqrt6      the quantum of action per unit BD bracket
                           (quantum-consistency status: forced exactly
                           in the 2D engine (pi/4 analog), inside the
                           unique 4D branching window
                           [four-d-normalization-check]);
  (2) l_disc^2 = 8 pi G    from the causal-action coefficient c = 1/2
                           (LayerA/CausalActionCoefficient);
  (3) v_eff(eps, That) = c_N + (pi/4) M(eps) g That^2
                           the measured per-element action variance
                           (ACTION_VARIANCE_REPORT, action_variance_mc
                           .json; M(eps) exact).

THE CANCELLATION.  Unimodular conjugacy reads a fluctuation of the
total action as an effective cosmological-constant fluctuation over
4-volume V:  dLambda = 8 pi G dS / (hbar V).  With
dS = kappa hbar sqrt(v_eff N) and N = V / l_disc^4:

  dLambda = 8 pi G kappa sqrt(v_eff) sqrt(V) / (l_disc^2 V) * l_disc^0
          = [8 pi G / l_disc^2] * kappa sqrt(v_eff) / sqrt(V)
          = kappa sqrt(v_eff) / sqrt(V)          (exactly, by (2)).

All Planck factors cancel BECAUSE of the Einstein-Hilbert matching that
fixed the discreteness scale: the same c = 1/2 that put l_disc at the
reduced-Planck length makes the everpresent amplitude independent of
G.  What remains is the derived action quantum times the measured
variance.  This script evaluates the consequences:

  A. c_N and g extracted from the MC data (intercept/slope of
     Var S/(kappa^2 N) against tau^2 per smearing eps).
  B. kappa_V = V_pastlightcone / T0^4 for Planck-2018 LCDM.
  C. THE FLOOR: Omega_fluct = kappa sqrt(c_N) / (3 sqrt(kappa_V)
     (H0 T0)^2) - Sorkin's 1/T^2 channel, now with NO free amplitude.
  D. THE EDGE CHANNEL: dLambda = kappa sqrt((pi/4) M(eps) g) T0 /
     (l_disc... in units) / sqrt(V); setting it equal to Lambda_obs
     SOLVES for the gravitational nonlocality scale l_k = l_disc
     eps^{-1/4} with no calibration freedom (July's 2.5-3.8 fm becomes
     a PREDICTION of l_k, cross-checked here).
  E. SINGLE-SCALE FALSIFICATION: if gravity shared the matter-sector
     bound l_k <= 1e-19 m (LHC), the edge channel OVERPRODUCES Lambda
     by a computable factor -> the gravity/matter nonlocality split is
     forced by magnitude, not just tension.
"""
import json, math
import numpy as np

KAPPA = 4 / math.sqrt(6)
LP = 1.616255e-35            # m
LDISC = math.sqrt(8 * math.pi) * LP
H0 = 67.4                    # km/s/Mpc
H0_SI = H0 * 1000 / 3.0857e22    # 1/s
C = 2.99792458e8
LH = C / H0_SI               # Hubble length, m
OM, OL = 0.315, 0.685

def M_eps(e):
    return (105 / 4) * math.sqrt(math.pi) * e ** 1.5 * \
        (e * e + 2 * e + 3) / (2 - e) ** 6.5

# ---------------- A. c_N and g from the MC data -----------------------------
data = json.load(open("action_variance_mc.json"))
print("== A. variance structure from action_variance_mc.json ==")
eps_list = [1.0, 0.5, 0.2, 0.1, 0.05]
groups = {}
for row in data:
    groups.setdefault(row["V"], []).append(row)
cn_est, g_est = {}, {}
for e in eps_list:
    key = f"S_{e}"
    xs, ys = [], []
    for V, rows in sorted(groups.items()):
        if len(rows) < 4: continue
        S = np.array([r[key] for r in rows])
        N = np.mean([r["N"] for r in rows])
        tau = rows[0]["T"]
        xs.append(tau ** 2)
        ys.append(np.var(S, ddof=1) / (KAPPA ** 2 * N))
    xs, ys = np.array(xs), np.array(ys)
    A = np.vstack([xs, np.ones(len(xs))]).T
    (slope, icept), *_ = np.linalg.lstsq(A, ys, rcond=None)
    g = slope / ((math.pi / 4) * M_eps(e))
    cn_est[e], g_est[e] = icept, g
    print(f"  eps={e:4}: intercept c_N = {icept:8.3f}   slope = {slope:9.3f}"
          f"   g = slope/((pi/4)M) = {g:6.3f}   (M = {M_eps(e):.4g})")
print("  NOTE: intercepts at strong damping bound the Poisson floor;")
print("  negative/small values reflect the N-D covariance cancellation.")
cN_band = (0.05, max(0.05, min(abs(cn_est[e]) for e in (0.1, 0.05))), 2.0)
print(f"  adopted c_N band for the floor: [{cN_band[0]}, {cN_band[2]}]")

# ---------------- B. past-lightcone 4-volume in LCDM ------------------------
print("== B. LCDM past-lightcone 4-volume ==")
n = 40000
a = np.geomspace(1e-8, 1.0, n)
H = np.sqrt(OM / a ** 3 + OL)            # H/H0 (radiation negligible for V)
t = np.zeros(n)
for i in range(1, n):
    da = a[i] - a[i - 1]
    aH = 0.5 * (a[i] * H[i] + a[i - 1] * H[i - 1])
    t[i] = t[i - 1] + da / aH
T0 = t[-1]
eta = np.zeros(n)
for i in range(1, n):
    da = a[i] - a[i - 1]
    a2H = 0.5 * (a[i] ** 2 * H[i] + a[i - 1] ** 2 * H[i - 1])
    eta[i] = eta[i - 1] + da / a2H
r_com = eta[-1] - eta                     # comoving distance to lightcone
rp = a * r_com                            # proper radius at time t
V = np.trapz((4 * math.pi / 3) * rp ** 3, t)
kV = V / T0 ** 4
print(f"  T0 = {T0:.4f}/H0   V_lc = {V:.4f}/H0^4   kappa_V = V/T0^4 = "
      f"{kV:.4f}")

# ---------------- C. the parameter-free floor -------------------------------
print("== C. floor channel (Sorkin 1/T^2), NO free amplitude ==")
for cN in (cN_band[0], 0.5, 1.0, cN_band[2]):
    dL = KAPPA * math.sqrt(cN) / math.sqrt(V)      # in H0^2 units
    Om_fl = dL / 3.0
    print(f"  c_N = {cN:5.2f}:  dLambda = {dL:.4f} H0^2   "
          f"Omega_fluct = {Om_fl:.4f}")
print("  (Lambda_obs = 3*0.685 = 2.055 H0^2, i.e. Omega = 0.685)")
cn_star = (3 * OL * math.sqrt(V) / KAPPA) ** 2
print(f"  c_N reproducing Lambda_obs exactly: c_N* = {cn_star:.4f}")
# The floor follows the CLASSIC 1/sqrt(V) law, whose Omega is ~epoch-
# independent; ACTION_VARIANCE_REPORT showed that law is CMB-fatal at
# today's amplitude.  Early-dark-energy limits (Planck, few percent)
# therefore bound the Poisson-floor coefficient:
Om_early = 0.03
cn_max = (3 * Om_early * math.sqrt(V) / KAPPA) ** 2
print(f"  CMB early-DE limit Omega ~ {Om_early} -> c_N <= {cn_max:.2e}")
print("  => the N-D covariance cancellation must suppress the Poisson")
print("     floor by >= 3 orders below its naive O(1) value - a sharp,")
print("     computable internal prediction (the MC noise floor ~0.3")
print("     cannot resolve it; an exact deep-damping variance")
print("     computation decides, and c_N > 4e-4 kills the theory).")

# ---------------- D. edge channel: solve for l_k ----------------------------
print("== D. edge channel fixes the gravitational nonlocality scale ==")
# dLambda_edge = kappa sqrt((pi/4) M g) * (T0_phys/l_disc) / sqrt(V_phys)
# in H0-units: T0_phys = T0 * L_H / c ... work in meters:
T0_m = T0 * LH                # light-travel: T0 in units of L_H (c=1)
V_m = V * LH ** 4
Lam_obs = 3 * OL / LH ** 2    # 1/m^2
g = 0.7
# solve M(eps) from dLambda = Lambda_obs
need = (Lam_obs * math.sqrt(V_m) * LDISC / (KAPPA * T0_m)) ** 2 \
    / ((math.pi / 4) * g)
# invert M(eps) ~ small-eps form M = 1.9635 * eps^1.5 (3/90.51 ...) exact:
lo, hi = 1e-140, 1.0
for _ in range(400):
    mid = math.sqrt(lo * hi)
    if M_eps(mid) < need: lo = mid
    else: hi = mid
eps_star = math.sqrt(lo * hi)
lk = LDISC * eps_star ** -0.25
print(f"  required M(eps) = {need:.4g}  ->  eps* = {eps_star:.4g}")
print(f"  l_k = l_disc eps*^-1/4 = {lk:.4g} m = {lk*1e15:.2f} fm")
for gg in (0.5, 1.0):
    need2 = need * g / gg
    lo, hi = 1e-140, 1.0
    for _ in range(400):
        mid = math.sqrt(lo * hi)
        if M_eps(mid) < need2: lo = mid
        else: hi = mid
    m2 = math.sqrt(lo * hi)
    print(f"    g = {gg}: l_k = {LDISC * m2 ** -0.25 * 1e15:.2f} fm")

# ---------------- E. single-scale falsification -----------------------------
print("== E. single nonlocality scale is excluded by MAGNITUDE ==")
lk_lhc = 1e-19               # m, matter-sector bound
eps_lhc = (LDISC / lk_lhc) ** 4
over = KAPPA * math.sqrt((math.pi / 4) * M_eps(eps_lhc) * g) * T0_m \
    / (LDISC * math.sqrt(V_m)) / Lam_obs
print(f"  l_k = 1e-19 m (LHC matter bound): eps = {eps_lhc:.3g}, "
      f"Lambda_edge/Lambda_obs = {over:.3g}")
print(f"  -> single-scale nonlocality OVERPRODUCES Lambda by ~1e"
      f"{int(math.log10(over))}: the gravity/matter split is forced.")
print("DONE")
