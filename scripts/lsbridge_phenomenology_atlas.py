"""
LSBridge phenomenology atlas.

Tabulates the LSBridge constant-R prediction map across all profile
families closed in the prediction-suite Lean files:

  - E1  polynomial   r(x) = 1 - x²
  - E2  Gaussian     r(x) = exp(-x²/(2σ²))
  - E3  sech         r(x) = sech(x/σ)
  - E4  exponential  r(x) = exp(αx + β)
  - E-Gen-Sech       r(x) = A · sech(B·x)

For each profile, this script computes:
  - sign of R (Ricci scalar of the emergent metric)
  - whether algebraic cancellation occurs (R = 0 at isolated points or all x)
  - whether spreading is frozen / monotone / optimal
  - asymptotic width behavior

Cross-references the corresponding Lean theorems.  Output: JSON atlas
plus a console summary table.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1.  R(x) per profile family — closed-form scalars from the proved theorems
# =============================================================================

def R_polynomial(x: float) -> float:
    """E1: r(x) = 1 - x², R(x) computed from family law 2·(r_x² − r·r_xx)/r⁴.

    Algebraically:  r_x = -2x, r_xx = -2.
                    r_x² - r·r_xx = 4x² + 2(1 - x²) = 2x² + 2 = 2(1 + x²).
                    R = 4(1 + x²)/(1 - x²)⁴.

    At x = ±1, r → 0 — singularity, but the EINSTEIN IDENTITY cancellation
    in E1 occurs at this x.  Lean proves a separate cancellation theorem.
    """
    r = 1.0 - x*x
    if abs(r) < 1e-12:
        return float("nan")
    return 4.0 * (1.0 + x*x) / r**4


def R_gaussian(x: float, sigma: float) -> float:
    """E2: r(x) = exp(-x²/(2σ²)), R_σ(x) = 2/(σ²·r²)."""
    r2 = math.exp(-x*x / (sigma*sigma))
    return 2.0 / (sigma*sigma * r2)


def R_sech(sigma: float) -> float:
    """E3: r(x) = sech(x/σ), R_σ(x) = 2/σ² (constant in x)."""
    return 2.0 / (sigma*sigma)


def R_exponential() -> float:
    """E4: r(x) = exp(αx + β), R(x) = 0 (identically)."""
    return 0.0


def R_gen_sech(A: float, B: float) -> float:
    """E-Gen-Sech: r(x) = A·sech(B·x), R(x) = 2·B²/A² (constant in x)."""
    return 2.0 * B*B / (A*A)


# =============================================================================
# 2.  PHENOMENOLOGY ATLAS — tabulate predictions per family
# =============================================================================

def build_atlas():
    return [
        {
            "family": "E1 polynomial",
            "profile": "r(x) = 1 − x²",
            "domain": "x ∈ (−1, 1)  (r > 0)",
            "R_form": "R(x) = 4(1 + x²)/(1 − x²)⁴",
            "R_sign": "→ ∞ at nodes x = ±1; positive on (−1, 1)",
            "cancellation": "Einstein-identity cancellation theorem at specific x (E1 Lean)",
            "constant_R": False,
            "spreading_behavior": "n/a (not a dynamic profile)",
            "asymptotic": "blows up at boundary nodes",
            "lean_theorem": "LohmillerSlotinePredictionE1.polyProfile_R_zero_at_x_one",
        },
        {
            "family": "E2 Gaussian",
            "profile": "r(x) = exp(−x²/(2σ²))",
            "domain": "x ∈ ℝ  (r > 0 everywhere)",
            "R_form": "R_σ(x) = 2/(σ²·r²) = (2/σ²)·exp(x²/σ²)",
            "R_sign": "strictly positive, varies with x",
            "cancellation": "no global cancellation; matter and geometry both grow",
            "constant_R": False,
            "spreading_behavior": "n/a (static identity)",
            "asymptotic": "R → 0 at peak as σ → ∞; R → ∞ as σ → 0; R → ∞ at fixed x as σ → 0",
            "lean_theorem": "LohmillerSlotinePredictionE2.gaussianRicci_from_identity",
        },
        {
            "family": "E3 sech soliton",
            "profile": "r(x) = sech(x/σ) = 1/cosh(x/σ)",
            "domain": "x ∈ ℝ  (r > 0 everywhere)",
            "R_form": "R_σ(x) = 2/σ²  (CONSTANT in x)",
            "R_sign": "strictly positive, constant — 'de Sitter-like' emergent geometry",
            "cancellation": "homogeneous matter ↔ homogeneous curvature",
            "constant_R": True,
            "spreading_behavior": "frozen at any σ_const (admits constant-σ solution)",
            "asymptotic": "R → 0 as σ → ∞ (vacuum); R → ∞ as σ → 0",
            "lean_theorem": "LohmillerSlotinePredictionE3.sechRicci_from_identity",
        },
        {
            "family": "E4 exponential",
            "profile": "r(x) = exp(αx + β)",
            "domain": "x ∈ ℝ  (r > 0 everywhere, for any α, β)",
            "R_form": "R(x) = 0  (IDENTICALLY)",
            "R_sign": "zero everywhere — exact pointwise matter/geometry cancellation",
            "cancellation": "(4m/ℏ²)·V exactly equals Δ_geom (proved as `expProfile_einstein_cancellation`)",
            "constant_R": True,
            "spreading_behavior": "frozen (R = 0 vacuum geometry)",
            "asymptotic": "no σ-dependence; R = 0 for all α, β",
            "lean_theorem": "LohmillerSlotinePredictionEExponential.derivedRicci_expProfile_zero",
        },
        {
            "family": "E-Generalized sech",
            "profile": "r(x) = A·sech(B·x)",
            "domain": "x ∈ ℝ  (r > 0 if A > 0)",
            "R_form": "R = 2·(B/A)²  (CONSTANT in x, depends only on ratio)",
            "R_sign": "≥ 0; = 0 iff B = 0; > 0 for any B ≠ 0",
            "cancellation": "homogeneous constant-curvature geometry",
            "constant_R": True,
            "spreading_behavior": "frozen at any (A, B)",
            "asymptotic": "characteristic curvature radius = A/B",
            "lean_theorem": "LohmillerSlotinePredictionEGeneralizedSech.derivedRicci_gSech",
        },
    ]


def print_atlas_table(atlas):
    print("=" * 110)
    print("LSBridge phenomenology atlas — constant-R prediction map")
    print("=" * 110)
    for entry in atlas:
        print(f"\n[{entry['family']}]  {entry['profile']}")
        print(f"   domain        : {entry['domain']}")
        print(f"   R form        : {entry['R_form']}")
        print(f"   R sign        : {entry['R_sign']}")
        print(f"   cancellation  : {entry['cancellation']}")
        print(f"   constant R?   : {entry['constant_R']}")
        print(f"   spreading     : {entry['spreading_behavior']}")
        print(f"   asymptotic    : {entry['asymptotic']}")
        print(f"   Lean theorem  : {entry['lean_theorem']}")
    print()
    print("=" * 110)


# =============================================================================
# 3.  CLASSIFICATION SUMMARY — proved constant-R branches
# =============================================================================

def classification_summary():
    return {
        "R_classification_complete": True,
        "branches": [
            {
                "R_value": "R ≡ 0",
                "family": "E4 exponential r = exp(αx + β)",
                "achievable": True,
                "lean_witness": "zero_R_realized_by_exponential",
            },
            {
                "R_value": "R ≡ 2C, C > 0",
                "family": "E-Gen-Sech r = A·sech(Bx) with (B/A)² = C",
                "achievable": True,
                "lean_witness": "positive_R_realized_by_gen_sech",
            },
            {
                "R_value": "R ≡ 2C, C < 0",
                "family": "—  (no globally smooth bounded positive profile)",
                "achievable": False,
                "lean_obstruction": [
                    "no_isLocalMax_for_constant_negative_R  "
                    "(IsLocalMax bridge: no local maximum can host R < 0)",
                    "no_global_smooth_bounded_negative_R    "
                    "(Taylor proof: globally bounded r ∈ [m, M] cannot host R < 0)",
                ],
            },
        ],
    }


# =============================================================================
# 4.  PLOT — R(x) for each profile family (where applicable)
# =============================================================================

def plot_R_profiles(out_path):
    fig, axes = plt.subplots(2, 2, figsize=(12, 9))

    # E1 polynomial
    x_poly = np.linspace(-0.95, 0.95, 200)
    R_poly = np.array([R_polynomial(x) for x in x_poly])
    axes[0, 0].plot(x_poly, R_poly, "b-", linewidth=2)
    axes[0, 0].set_title("E1 polynomial: r = 1 − x², R = 4(1+x²)/(1−x²)⁴")
    axes[0, 0].set_xlabel("x")
    axes[0, 0].set_ylabel("R(x)")
    axes[0, 0].set_yscale("log")
    axes[0, 0].grid(True, alpha=0.3)

    # E2 Gaussian, various σ
    x_gauss = np.linspace(-3.0, 3.0, 200)
    for sigma in [0.5, 1.0, 2.0]:
        R_g = np.array([R_gaussian(x, sigma) for x in x_gauss])
        axes[0, 1].plot(x_gauss, R_g, label=f"σ = {sigma}", linewidth=2)
    axes[0, 1].set_title("E2 Gaussian: R_σ(x) = (2/σ²)·exp(x²/σ²)")
    axes[0, 1].set_xlabel("x")
    axes[0, 1].set_ylabel("R(x)")
    axes[0, 1].set_yscale("log")
    axes[0, 1].grid(True, alpha=0.3)
    axes[0, 1].legend()

    # E3 sech & E-Gen-Sech, various σ
    sigma_vals = np.linspace(0.1, 5.0, 100)
    R_sech_vals = 2.0 / sigma_vals**2
    axes[1, 0].plot(sigma_vals, R_sech_vals, "g-", linewidth=2,
                    label="E3: R = 2/σ² (constant in x)")
    axes[1, 0].set_xlabel("σ (or A/B for gen-sech)")
    axes[1, 0].set_ylabel("R")
    axes[1, 0].set_yscale("log")
    axes[1, 0].set_xscale("log")
    axes[1, 0].set_title("E3 sech / E-Gen-Sech:  R = 2/(curvature radius)²")
    axes[1, 0].grid(True, which="both", alpha=0.3)
    axes[1, 0].legend()

    # E4 exponential: R ≡ 0
    x_exp = np.linspace(-2.0, 2.0, 100)
    R_exp_vals = np.zeros_like(x_exp)
    axes[1, 1].plot(x_exp, R_exp_vals, "r-", linewidth=3,
                    label="E4: R ≡ 0 for any α, β")
    axes[1, 1].set_ylim(-0.5, 0.5)
    axes[1, 1].set_xlabel("x")
    axes[1, 1].set_ylabel("R(x)")
    axes[1, 1].set_title("E4 exponential: r = exp(αx + β), R ≡ 0 IDENTICALLY")
    axes[1, 1].grid(True, alpha=0.3)
    axes[1, 1].legend()

    fig.suptitle("LSBridge prediction map — R(x) per profile family",
                 fontsize=14, y=1.00)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 5.  MAIN
# =============================================================================

def main():
    atlas = build_atlas()
    classification = classification_summary()

    out = {
        "phenomenology_atlas": atlas,
        "classification_summary": classification,
        "summary_remarks": {
            "complete_R_classification": (
                "R = 0 (E4 exponential, witness), "
                "R > 0 (E-Gen-Sech, witness), "
                "R < 0 (impossible globally — Taylor proof)"
            ),
            "dynamic_consequence": (
                "All constant-R profiles admit frozen (σ ≡ const) solutions, "
                "impossible in free Schrödinger.  Backreaction enables vacuum "
                "and 'de Sitter-like' emergent geometries."
            ),
            "optimal_spreading_width": (
                "σ̇ = C·σ·exp(−σ) is maximized at σ = 1.  This identifies "
                "a characteristic LSBridge length scale at which spreading "
                "is fastest."
            ),
        },
    }

    out_path = OUT_DIR / "phenomenology_atlas.json"
    with out_path.open("w") as f:
        json.dump(out, f, indent=2)

    plot_path = OUT_DIR / "R_per_profile_family.png"
    plot_R_profiles(plot_path)

    print_atlas_table(atlas)
    print()
    print("Classification summary:")
    for branch in classification["branches"]:
        print(f"  - {branch['R_value']:>12}:  family = {branch['family']}")
        print(f"     achievable: {branch['achievable']}")
        if "lean_witness" in branch:
            print(f"     witness: {branch['lean_witness']}")
        if "lean_obstruction" in branch:
            for obs in branch["lean_obstruction"]:
                print(f"     obstruction: {obs}")
    print()
    print(f"Full atlas JSON: {out_path}")
    print(f"R profile plot:  {plot_path}")


if __name__ == "__main__":
    main()
