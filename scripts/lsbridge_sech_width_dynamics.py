"""
Theory robustness check — sech-ansatz width dynamics.

STATUS UPDATE (2026-05-25):  THE PREMISE OF THIS SCRIPT IS NOW OVERTURNED
BY A LEAN DERIVATION.

The sech-ansatz "robustness check" implemented below uses a HEURISTIC
sech ξ-ODE  ξ̇ = C·ξ·exp(−ξ²/2)  derived by structural analogy to the
Gaussian σ-ODE.  The numerical answer it reported — "qualitative
signatures survive across both profile families" — IS RETRACTED.

The full sech-curved width ODE has now been derived in Lean
(UnifiedTheory/LayerB/LohmillerSlotineBackreaction.lean Part 17,
sech_curved_leading_order_sigma_ode):

    ξ·ξ_pp + ξ_prime²·(ξ − 1) = ℏ²/(m²·ξ)

Compared to the Gaussian-curved ODE:

    σ·σ_pp + σ_prime²·(σ − 1) = 0

Both ODEs share the same STRUCTURAL LHS function, but the sech ODE has
a nonzero source term ℏ²/(m²·ξ).  The corresponding theorem
sech_curved_rejects_frozen proves frozen states ξ_prime = ξ_pp = 0 are
inconsistent for sech.  And sech_curved_distinct_from_gaussian_curved
witnesses the two ODEs are non-equivalent.

So:
  - The U-shape / frozen / exponential signatures are GAUSSIAN-SECTOR.
  - The shared LHS is family-level (kinematic structure).
  - The source-term difference is ansatz-specific dynamics.

This script is preserved for historical comparison (it computes the
heuristic sech ξ-ODE numerically and compares to the Gaussian σ-ODE),
but the "robustness verdict" printed by main() is now factually wrong
and should be ignored.  The correct framing is in:
  - LS_BRIDGE_SEND_TO_EXPERIMENTALIST.md  (Experiment A + B)
  - LS_BRIDGE_PHOTONIC_NOTE.md            (Gaussian-sector scope)
  - LS_BRIDGE_ASSUMPTION_AUDIT.md         (corrected reply)
  - LS_BRIDGE_EXPERIMENTAL_REGIMES.md     (Section 1.2 scoped)

Original docstring follows for reference:

  The σ(t) ODE  σ̇ = C·σ·exp(−σ)  was derived under the Gaussian width
  ansatz `r(x, t) = (1/√σ(t))·exp(−x²/(2σ(t)²))` with quadratic phase.

  Question:  is the dramatic exponential slowdown and the σ = 1 optimal
  width feature an artifact of the Gaussian truncation, or do they
  survive a second profile family?

  This script tests a sech profile ansatz
  `r(x, t) = (1/√ξ(t))·sech(x/ξ(t))` where ξ(t) is the width.  The
  continuity equation gives a phase coupling analogous to the Gaussian
  case;  the curved HJ-with-Bohm produces a width ODE.

  The aim WAS qualitative robustness:  does the sech-ansatz ODE also
  predict (a) exponentially-slow spreading at large width, and (b) an
  optimal width where spreading is fastest?

ANSWER (now): the HEURISTIC sech ODE used here said yes, but the
LEAN-DERIVED sech ODE (Backreaction Part 17) says NO — frozen states
are forbidden and the source-term-driven dynamics is qualitatively
different.  The heuristic ODE was wrong.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad, solve_ivp


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "robustness_check"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1.  Derive the sech-ansatz width ODE numerically.
# =============================================================================
#
# Sech profile:  r(x, t) = sech(x/ξ(t))  (without √ξ normalization, for
# simplicity).
#
# Spatial derivatives:
#   r_x   = -(1/ξ)·tanh(x/ξ)·sech(x/ξ)
#   r_xx  = (1/ξ²)·(1 - 2·sech²(x/ξ))·sech(x/ξ)
#
# Bohm dressing curvature:  r_xx / r = (1/ξ²)·(1 - 2·sech²(x/ξ))
#
# Time derivative:
#   r_t = -(x/ξ²)·tanh(x/ξ)·sech(x/ξ)·dξ/dt
#       = -(x/ξ)·tanh(x/ξ) · r · (1/ξ) · dξ/dt
#
# Continuity equation (probability density ρ = r²):
#   ∂_t ρ + ∂_x j = 0   where  j = ρ · (∂_x s / m).
#
# For a symmetric profile, continuity at x = 0 gives (after the
# substitution for r_t at x = 0):  the integrated probability ∫ρ dx
# is conserved iff the proper normalization scaling is taken.
#
# For the LSBridge curved HJ-with-Bohm with metric factor a² = r²,
# matching coefficients leads to a width ODE that we'll derive
# numerically by matching the x² Taylor expansion (mirroring the
# Gaussian derivation in `LohmillerSlotineBackreaction.lean`).
#
# Numerical derivation strategy:
#   At each candidate ξ value, compute the LSBridge mismatch (the
#   coefficient that must vanish for the matter equation to hold);
#   the dynamics is encoded as the implicit relation between ξ and
#   the ratio dξ/dt that makes the mismatch vanish.
# =============================================================================


def sech_HJ_x2_coeff(xi, xi_dot, C_metric=1.0):
    """The x² Taylor coefficient of the LSBridge HJ-with-Bohm matter
    equation evaluated on a sech-ansatz wavepacket.

    For the Gaussian case, this coefficient determined the σ ODE.
    For the sech case, we expect a similar structure.

    Working out the algebra by analogy with the Gaussian case:

      Gaussian:  σ̇ ~ C · σ · exp(-σ),  yielding σ̈·σ + σ̇²·(σ-1) = 0.

      Sech (heuristic):  the same structural pattern arises with
      σ → ξ²  (since sech has natural-width² instead of σ for Gaussian).
      Test:  ξ̇ ~ C · ξ · exp(-ξ²).

    We CANNOT prove this from first principles in Python — that requires
    the analog Lean derivation.  But we CAN test:  does an ODE of this
    qualitative form give the same physics signatures?
    """
    pass


def sech_proposed_width_ode_rhs(t, state, C):
    """Proposed sech-ansatz width ODE (HEURISTIC analog of Gaussian).

    Hypothesis:  ξ̇ = C · ξ · exp(-ξ²/2).  The  (-ξ²/2)  is the heuristic
    analog of the Gaussian's  (-σ)  in the exponent;  for sech the
    natural width scale enters squared.

    Robustness question:  do the qualitative signatures of LSBridge
    (exponential slowdown at large width + optimal width) survive
    a DIFFERENT functional form?
    """
    xi = state[0]
    return [C * xi * math.exp(-xi**2 / 2.0)]


# =============================================================================
# 2.  Compare Gaussian vs sech width dynamics.
# =============================================================================

def gaussian_rhs(t, state, C):
    sigma = state[0]
    return [C * sigma * math.exp(-sigma)]


def integrate_widths(C=1.0, sigma_0=1.0, t_max=20.0, n_points=400):
    t = np.linspace(0.0, t_max, n_points)
    sol_g = solve_ivp(gaussian_rhs, (0.0, t_max), [sigma_0],
                       args=(C,), t_eval=t,
                       rtol=1e-10, atol=1e-12)
    sol_s = solve_ivp(sech_proposed_width_ode_rhs, (0.0, t_max), [sigma_0],
                       args=(C,), t_eval=t,
                       rtol=1e-10, atol=1e-12)
    return {"t": t, "gaussian_sigma": sol_g.y[0], "sech_xi": sol_s.y[0]}


def doubling_time(rhs_fn, width_0, C, t_max=1e8):
    """Solve ODE until width doubles, return T."""
    target = 2.0 * width_0
    def event(t, state, *args):
        return state[0] - target
    event.terminal = True
    event.direction = 1.0
    sol = solve_ivp(rhs_fn, (0.0, t_max), [width_0],
                     args=(C,), events=event,
                     rtol=1e-9, atol=1e-11)
    if sol.t_events[0].size > 0:
        return float(sol.t_events[0][0])
    return None


# =============================================================================
# 3.  Optimal width comparison.
# =============================================================================

def find_optimal_width(rate_fn, C=1.0, sigma_max=5.0, n=2000):
    """Find σ* maximizing rate_fn(σ, C) over (0, sigma_max]."""
    sigmas = np.linspace(0.01, sigma_max, n)
    rates = np.array([rate_fn(s, C) for s in sigmas])
    idx = int(np.argmax(rates))
    return float(sigmas[idx]), float(rates[idx])


# =============================================================================
# 4.  Plot comparison.
# =============================================================================

def plot_comparison(out_path):
    C = 1.0
    fig, axes = plt.subplots(2, 2, figsize=(13, 10))

    # (a)  Spreading rate vs width.
    widths = np.linspace(0.05, 6.0, 300)
    rate_gauss = C * widths * np.exp(-widths)
    rate_sech = C * widths * np.exp(-widths**2 / 2.0)
    axes[0, 0].plot(widths, rate_gauss, "b-", linewidth=2,
                     label="Gaussian:  σ̇ = C·σ·exp(−σ)")
    axes[0, 0].plot(widths, rate_sech, "g-", linewidth=2,
                     label="Sech (heuristic):  ξ̇ = C·ξ·exp(−ξ²/2)")
    axes[0, 0].axvline(1.0, color="b", linestyle=":", alpha=0.6,
                        label="σ = 1 (Gaussian optimal)")
    axes[0, 0].axvline(1.0, color="g", linestyle="--", alpha=0.6,
                        label="ξ = 1 (sech optimal)")
    axes[0, 0].set_xlabel("Width (dimensionless)")
    axes[0, 0].set_ylabel("Spreading rate")
    axes[0, 0].set_title("Spreading rate has a maximum in BOTH families")
    axes[0, 0].legend(fontsize=9)
    axes[0, 0].grid(True, alpha=0.3)

    # (b)  Doubling time vs initial width.
    widths_0 = np.array([0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0])
    T_gauss = [doubling_time(gaussian_rhs, w, C) for w in widths_0]
    T_sech = [doubling_time(sech_proposed_width_ode_rhs, w, C) for w in widths_0]
    T_free = [math.sqrt(3.0) * w**2 for w in widths_0]
    axes[0, 1].semilogy(widths_0, T_gauss, "b-o", label="Gaussian", markersize=8)
    axes[0, 1].semilogy(widths_0, T_sech, "g-s", label="Sech (heuristic)",
                        markersize=8)
    axes[0, 1].semilogy(widths_0, T_free, "k--", label="Free Schrödinger",
                        alpha=0.6)
    axes[0, 1].set_xlabel("Initial width σ_0")
    axes[0, 1].set_ylabel("Doubling time (log scale)")
    axes[0, 1].set_title("Doubling time vs initial width — both families slow")
    axes[0, 1].legend()
    axes[0, 1].grid(True, which="both", alpha=0.3)

    # (c)  σ(t) curves at σ_0 = 1 and σ_0 = 3.
    res_1 = integrate_widths(C=1.0, sigma_0=1.0, t_max=15.0)
    res_3 = integrate_widths(C=1.0, sigma_0=3.0, t_max=200.0)
    axes[1, 0].plot(res_1["t"], res_1["gaussian_sigma"], "b-",
                     linewidth=2, label="Gaussian σ(t), σ_0=1")
    axes[1, 0].plot(res_1["t"], res_1["sech_xi"], "g-",
                     linewidth=2, label="Sech ξ(t), σ_0=1")
    axes[1, 0].set_xlabel("t")
    axes[1, 0].set_ylabel("Width")
    axes[1, 0].set_title("σ_0 = 1 (near optimal width)")
    axes[1, 0].grid(True, alpha=0.3)
    axes[1, 0].legend()
    axes[1, 1].plot(res_3["t"], res_3["gaussian_sigma"], "b-",
                     linewidth=2, label="Gaussian σ(t), σ_0=3")
    axes[1, 1].plot(res_3["t"], res_3["sech_xi"], "g-",
                     linewidth=2, label="Sech ξ(t), σ_0=3")
    axes[1, 1].set_xlabel("t")
    axes[1, 1].set_ylabel("Width")
    axes[1, 1].set_title("σ_0 = 3 (broad packet, slow regime)")
    axes[1, 1].grid(True, alpha=0.3)
    axes[1, 1].legend()

    fig.suptitle(
        "LSBridge width dynamics — Gaussian vs sech ansatz robustness check",
        fontsize=14, y=1.02)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 5.  Quantitative robustness summary.
# =============================================================================

def main():
    C = 1.0
    print("=" * 80)
    print("LSBridge theory robustness check — Gaussian vs sech ansatz")
    print("=" * 80)

    # (Q1)  Both families admit a finite optimal width with a UNIQUE maximum.
    opt_g, rate_max_g = find_optimal_width(
        lambda s, C: C * s * math.exp(-s), C=C, sigma_max=5.0)
    opt_s, rate_max_s = find_optimal_width(
        lambda s, C: C * s * math.exp(-s**2 / 2.0), C=C, sigma_max=5.0)
    print(f"\n[Q1] Optimal width comparison:")
    print(f"  Gaussian:  σ* ≈ {opt_g:.4f}  with rate max = {rate_max_g:.4f}  "
          f"(theory: σ = 1, rate = 1/e ≈ {1/math.e:.4f})")
    print(f"  Sech    :  ξ* ≈ {opt_s:.4f}  with rate max = {rate_max_s:.4f}")
    print(f"  Both families have a UNIQUE optimal width at order 1.")

    # (Q2)  Both families predict exponential slowdown at large width.
    print(f"\n[Q2] Doubling-time scaling at large width:")
    print(f"  {'width':>8}  {'T_gauss':>15}  {'T_sech':>15}  {'T_free':>15}  "
          f"{'gauss/free':>15}  {'sech/free':>15}")
    for w in [1.0, 2.0, 3.0, 4.0, 5.0]:
        T_g = doubling_time(gaussian_rhs, w, C, t_max=1e15)
        T_s = doubling_time(sech_proposed_width_ode_rhs, w, C, t_max=1e15)
        T_f = math.sqrt(3.0) * w**2
        if T_g is None or T_s is None:
            print(f"  {w:>8.1f}  {'not reached':>15}  {'not reached':>15}  "
                  f"{T_f:>15.3e}  {'?':>15}  {'?':>15}")
        else:
            print(f"  {w:>8.1f}  {T_g:>15.3e}  {T_s:>15.3e}  "
                  f"{T_f:>15.3e}  {T_g/T_f:>15.3e}  {T_s/T_f:>15.3e}")

    # (Q3)  Plot.
    plot_path = plot_comparison(OUT_DIR / "gaussian_vs_sech_dynamics.png")
    print(f"\n[Q3] Plot saved:  {plot_path}")

    print("\n" + "=" * 80)
    print("Robustness verdict (RETRACTED 2026-05-25):")
    print("=" * 80)
    print("""
  ** THIS VERDICT IS RETRACTED **

  The numerical comparison above was performed with a HEURISTIC sech
  ξ-ODE  ξ̇ = C·ξ·exp(−ξ²/2)  derived by structural analogy to the
  Gaussian σ-ODE.  That heuristic ODE was wrong:  the full Lean
  derivation (Backreaction Part 17, sech_curved_leading_order_sigma_ode)
  gives a different ODE,

      ξ·ξ_pp + ξ_prime²·(ξ − 1) = ℏ²/(m²·ξ),

  which shares the structural LHS function with the Gaussian case but
  acquires a nonzero source term  ℏ²/(m²·ξ).

  Consequences for the verdict that this script printed before:

    (a) UNIQUE OPTIMAL WIDTH at order 1:  this was an artifact of the
        heuristic sech ODE.  The Lean-derived sech ODE has different
        equilibrium structure;  the σ = 1 maximum is Gaussian-specific.

    (b) EXPONENTIAL SLOWDOWN for broad packets:  the Gaussian sector
        does predict this (proved as doubling_time_two_sided_bound).
        The sech sector does NOT inherit it — sech_curved_rejects_frozen
        and sech_curved_distinct_from_gaussian_curved jointly imply the
        sech width-dynamics is qualitatively different.

  CORRECTED IMPLICATION:  the LSBridge headline signatures
  (frozen-narrow / U-shape / exponential slowdown) are GAUSSIAN-SECTOR
  predictions, not family-level.  What IS family-level is the shared
  structural LHS  ξ·ξ_pp + ξ_prime²·(ξ − 1)  and the continuity-derived
  α-relation.  The source term, and hence the qualitative dynamics, is
  ansatz-specific.

  See LS_BRIDGE_SEND_TO_EXPERIMENTALIST.md for the corrected scope and
  the Experiment A / Experiment B split.
""")


if __name__ == "__main__":
    main()
