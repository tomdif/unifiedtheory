"""Decisive end-effect test of the framework's coupling story.

Framework claims (LayerA/CouplingUnification, FineStructure, AlphaGUT):
  * all gauge couplings start equal at the discreteness scale (~M_P),
  * sin^2 theta_W = 3/8 there (i.e. alpha_1 = alpha_2 in GUT normalisation),
  * matter = 3 SM generations + 1 Higgs doublet,
  * reading A: g^2 = 1          -> alpha_U = 1/(4 pi)
  * reading B: alpha_U = 3/(32 pi)   (AlphaGUT reinterpretation)
  * separately: alpha(0) = ln(5/3)/70  (FineStructureIRFromGap)

Standard 2-loop SM gauge RGEs (Machacek-Vaughn; top Yukawa at 1 loop in the
2-loop gauge term) are run from the boundary scale down to M_Z, then alpha_em
is taken to q^2 = 0 with the measured SM threshold shift.  Nothing is fitted.
"""
import json
import math

import numpy as np
from scipy.integrate import solve_ivp

MZ = 91.1876
MP = 1.22089e19          # Planck mass
MP_RED = 2.435e18        # reduced Planck mass
# PDG 2024 inputs at M_Z (MSbar)
ALPHA_S = 0.1180
ALPHA_S_ERR = 0.0009
ALPHA_EM_INV_MZ = 127.951
SIN2_MZ = 0.23122
INV_ALPHA0 = 137.035999177
DELTA_0_TO_MZ = INV_ALPHA0 - ALPHA_EM_INV_MZ   # measured leptonic+hadronic+top shift, MSbar
YT_MZ = 0.97                                    # MSbar top Yukawa near M_Z

B1 = np.array([41 / 10, -19 / 6, -7.0])
B2 = np.array([[199 / 50, 27 / 10, 44 / 5],
               [9 / 10, 35 / 6, 12.0],
               [11 / 10, 9 / 2, -26.0]])
CT = np.array([17 / 10, 3 / 2, 2.0])   # top-Yukawa coefficients in 2-loop gauge betas


def rhs(t, y):
    """y = (1/alpha_1, 1/alpha_2, 1/alpha_3, y_t); t = ln(mu)."""
    inv = y[:3]
    if np.any(inv <= 0):
        return np.zeros(4)
    a = 1 / inv
    yt = y[3]
    # d(1/a_i)/dt = -b_i/(2 pi) - sum_j b_ij a_j/(8 pi^2) + c_i y_t^2/(32 pi^3)
    dinv =-B1 / (2 * math.pi) - (B2 @ a) / (8 * math.pi ** 2) + CT * yt ** 2 / (32 * math.pi ** 3)
    g3sq, g2sq, g1sq = 4 * math.pi * a[2], 4 * math.pi * a[1], 4 * math.pi * a[0]
    dyt = yt / (16 * math.pi ** 2) * (4.5 * yt ** 2 - 8 * g3sq - 2.25 * g2sq - 17 / 20 * g1sq)
    return np.concatenate([dinv, [dyt]])


def measured_inv():
    inv_em = ALPHA_EM_INV_MZ
    inv2 = inv_em * SIN2_MZ
    inv1 = 3 / 5 * inv_em * (1 - SIN2_MZ)
    inv3 = 1 / ALPHA_S
    return np.array([inv1, inv2, inv3])


def run(y0, t0, t1):
    pole = lambda t, y: min(y[0], y[1], y[2]) - 0.05
    pole.terminal = True
    sol = solve_ivp(rhs, (t0, t1), y0, rtol=1e-10, atol=1e-12, events=pole, dense_output=True)
    return sol


def yt_at(mu):
    """1-loop-consistent top Yukawa at mu, obtained by running up from M_Z."""
    y0 = np.concatenate([measured_inv(), [YT_MZ]])
    sol = run(y0, math.log(MZ), math.log(mu))
    return sol.y[3, -1]


def from_boundary(inv_u, M):
    """Run down from equal couplings at M; return dict of M_Z values or pole scale."""
    y0 = np.array([inv_u, inv_u, inv_u, yt_at(M)])
    sol = run(y0, math.log(M), math.log(MZ))
    if sol.status == 1:   # pole hit
        mu_pole = math.exp(sol.t_events[0][0])
        which = ["alpha_1", "alpha_2", "alpha_3"][int(np.argmin(sol.y_events[0][0][:3]))]
        return {"landau_pole_GeV": mu_pole, "coupling": which}
    inv1, inv2, inv3 = sol.y[:3, -1]
    inv_em = inv2 + 5 / 3 * inv1
    return {
        "inv_alpha1_MZ": inv1, "inv_alpha2_MZ": inv2, "inv_alpha3_MZ": inv3,
        "alpha_s_MZ": 1 / inv3,
        "sin2_MZ": inv2 / inv_em,
        "inv_alpha_em_MZ": inv_em,
        "inv_alpha0_pred": inv_em + DELTA_0_TO_MZ,
    }


def best_free_unification():
    """Two-coupling unification (alpha_1 = alpha_2 meet point) and the alpha_3 mismatch."""
    y0 = np.concatenate([measured_inv(), [YT_MZ]])
    sol = run(y0, math.log(MZ), math.log(MP))
    ts = np.linspace(math.log(MZ), sol.t[-1], 20000)
    Y = sol.sol(ts)
    d12 = Y[0] - Y[1]
    k = int(np.argmax(d12 < 0))
    t12 = ts[k]
    inv12 = Y[1, k]
    inv3 = Y[2, k]
    # sigma of 1/alpha_3 at that scale from alpha_s error (propagated ~ constant shift at 1-loop)
    sig3 = ALPHA_S_ERR / ALPHA_S ** 2
    return {"M_12_GeV": math.exp(t12), "inv_alpha_12": inv12, "inv_alpha_3_there": inv3,
            "alpha3_mismatch_in_inv": inv3 - inv12, "mismatch_sigma_from_alpha_s": (inv3 - inv12) / sig3}


def main():
    out = {"inputs": {"alpha_s": ALPHA_S, "inv_alpha_em_MZ": ALPHA_EM_INV_MZ, "sin2_MZ": SIN2_MZ,
                      "delta_0_to_MZ": DELTA_0_TO_MZ},
           "targets": {"inv_alpha0_CODATA": INV_ALPHA0, "inv_alpha0_ln53_over_70": 70 / math.log(5 / 3)}}
    for name, inv_u in [("A_g2_eq_1", 4 * math.pi), ("B_alpha_3_over_32pi", 32 * math.pi / 3)]:
        for mname, M in [("M_P", MP), ("M_P_reduced", MP_RED)]:
            out[f"{name}@{mname}"] = from_boundary(inv_u, M)
    out["free_scale_unification"] = best_free_unification()
    # Best case for the framework: choose M and alpha_U freely to hit alpha_s and alpha_em(M_Z) exactly,
    # then see what sin^2(M_Z) and alpha_2 come out.
    best = None
    for logM in np.linspace(13, 19.5, 261):
        M = 10 ** logM
        lo, hi = 5.0, 80.0
        for _ in range(60):
            mid = (lo + hi) / 2
            r = from_boundary(mid, M)
            if "alpha_s_MZ" not in r or r["alpha_s_MZ"] > ALPHA_S:
                lo = mid
            else:
                hi = mid
        r = from_boundary((lo + hi) / 2, M)
        if "inv_alpha_em_MZ" in r:
            miss = abs(r["inv_alpha_em_MZ"] - ALPHA_EM_INV_MZ)
            if best is None or miss < best[0]:
                best = (miss, logM, (lo + hi) / 2, r)
    out["best_fit_free_M_alphaU_matching_alpha_s"] = {"log10_M": best[1], "inv_alpha_U": best[2], **best[3]}
    print(json.dumps(out, indent=1))
    with open("unification_running_test.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
