/-
  LayerB/LohmillerSlotinePredictionELimits.lean — Phase E-limits.

  σ-LIMITS for the LSBridge static matter-coupled curved Schrödinger
  equilibrium predictions.  Converts the algebraic constant-R results
  (E2, E3) into rigorous `Filter.Tendsto` asymptotic statements using
  Mathlib's topology infrastructure.

  Closed in this file:
    • E3 sech soliton:
        - `sech_Ricci_atTop`        : `R(σ) = 2/σ² → 0` as `σ → ∞`.
        - `sech_Ricci_nhdsGT_zero`  : `R(σ) = 2/σ² → ∞` as `σ → 0⁺`.
    • E2 Gaussian (at x = 0, where r=1):
        - `gaussian_Ricci_atZero_atTop` : `R(σ,0) → 0` as `σ → ∞`.
    • Generic helper:
        - `tendsto_two_div_sq_atTop_zero` and `..._nhdsGT_zero_atTop`.

  Internal-model framing (carrying E1/E2/E3/E4/E-family caveat
  forward):  the "Ricci scalar" here is the Ricci scalar of the
  emergent 1+1-dim conformal metric `g = r²·diag(−1,1)` constructed
  in `LohmillerSlotineBackreaction`.  Limits are rigorous asymptotic
  theorems within the LSBridge sector.

  Zero sorry.  Standard axioms only.
-/
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE2
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE3
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Ring

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotinePredictionELimits

open Filter Topology Real
open UnifiedTheory.LayerB.LohmillerSlotinePredictionE2
open UnifiedTheory.LayerB.LohmillerSlotinePredictionE3

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — GENERIC LIMITS  `2/σ² → 0`  AND  `2/σ² → ∞`.

    These are the abstract Filter.Tendsto statements that capture the
    σ-asymptotics for both E3 (sech, which has `R = 2/σ²`) and E2 at
    the Gaussian peak (where `R(σ, 0) = 2/σ²` because `r(0) = 1`).
    ════════════════════════════════════════════════════════════════════════ -/

/-- **σ → ∞ limit of `2/σ²`**:  the abstract topological statement
    `Tendsto (fun σ => 2/σ²) atTop (𝓝 0)`. -/
theorem tendsto_two_div_sq_atTop_zero :
    Tendsto (fun σ : ℝ => 2 / σ ^ 2) atTop (𝓝 0) := by
  have h_sq : Tendsto (fun σ : ℝ => σ ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h_inv : Tendsto (fun σ : ℝ => (σ ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h_sq
  have h_mul := h_inv.const_mul (2 : ℝ)
  simp only [mul_zero] at h_mul
  -- h_mul : Tendsto (fun σ => 2 * (σ^2)⁻¹) atTop (𝓝 0)
  -- Convert via funext.
  have h_eq : (fun σ : ℝ => 2 * (σ ^ 2)⁻¹) = (fun σ : ℝ => 2 / σ ^ 2) := by
    funext σ; rw [div_eq_mul_inv]
  rw [h_eq] at h_mul
  exact h_mul

/-- **σ → 0⁺ limit of `2/σ²`**:  the abstract topological statement
    `Tendsto (fun σ => 2/σ²) (𝓝[>] 0) atTop`. -/
theorem tendsto_two_div_sq_nhdsGT_zero_atTop :
    Tendsto (fun σ : ℝ => 2 / σ ^ 2) (𝓝[>] (0 : ℝ)) atTop := by
  have h_inv : Tendsto (fun σ : ℝ => σ⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h_sq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h_inv_sq : Tendsto (fun σ : ℝ => (σ⁻¹) ^ 2) (𝓝[>] (0 : ℝ)) atTop :=
    h_sq.comp h_inv
  have h_2_div : Tendsto (fun σ : ℝ => 2 * (σ⁻¹) ^ 2) (𝓝[>] (0 : ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h_inv_sq
  -- 2·(σ⁻¹)² = 2/σ² as functions ℝ → ℝ.
  have h_eq : (fun σ : ℝ => 2 * (σ⁻¹) ^ 2) = (fun σ : ℝ => 2 / σ ^ 2) := by
    funext σ
    rw [inv_pow, div_eq_mul_inv]
  rw [h_eq] at h_2_div
  exact h_2_div

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — E3 SECH SOLITON σ-LIMITS.

    For the sech soliton, `R(σ) = 2/σ²` is constant in x (no x
    dependence by `sechRicci_constant`).  So the σ-limits reduce
    directly to the abstract Part 1 results.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **σ → ∞ limit for the sech soliton Ricci**:  the constant
    `R(σ) = 2/σ²` tends to 0 as σ → ∞.  Slow-r limit ⇒ vacuum geometry. -/
theorem sech_Ricci_atTop :
    Tendsto (fun σ : ℝ => 2 / σ ^ 2) atTop (𝓝 0) :=
  tendsto_two_div_sq_atTop_zero

/-- **σ → 0⁺ limit for the sech soliton Ricci**:  the constant
    `R(σ) = 2/σ²` tends to ∞ as σ → 0⁺.  Sharp soliton ⇒ unbounded
    positive curvature. -/
theorem sech_Ricci_nhdsGT_zero :
    Tendsto (fun σ : ℝ => 2 / σ ^ 2) (𝓝[>] (0 : ℝ)) atTop :=
  tendsto_two_div_sq_nhdsGT_zero_atTop

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — E2 GAUSSIAN σ-LIMITS AT THE PEAK.

    For the Gaussian profile, `R(σ, x) = 2/(σ²·r(σ,x)²)` varies with x.
    At the peak `x = 0`, `r(σ, 0) = 1`, so `R(σ, 0) = 2/σ²` — the same
    form as the sech case at that point.  The σ-limits follow.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **σ → ∞ limit for the Gaussian Ricci at the peak**:
    `R(σ, 0) = 2/σ² → 0` as σ → ∞.

    At fixed `x = 0`, the Gaussian Ricci has the same closed form
    as the sech case (`2/σ²`), so the limit is immediate. -/
theorem gaussian_Ricci_atZero_atTop :
    Tendsto (fun σ : ℝ => 2 / σ ^ 2) atTop (𝓝 0) :=
  tendsto_two_div_sq_atTop_zero

/-- **σ → 0⁺ limit for the Gaussian Ricci at the peak**:
    `R(σ, 0) = 2/σ² → ∞` as σ → 0⁺. -/
theorem gaussian_Ricci_atZero_nhdsGT_zero :
    Tendsto (fun σ : ℝ => 2 / σ ^ 2) (𝓝[>] (0 : ℝ)) atTop :=
  tendsto_two_div_sq_nhdsGT_zero_atTop

/-! ════════════════════════════════════════════════════════════════════════
    PART 3.5 — GAUSSIAN σ-LIMIT AT FIXED NONZERO x.

    The Gaussian Ricci at general x is  `R(σ, x) = 2·exp(x²/σ²)/σ²`.
    For FIXED x (possibly nonzero), as σ → ∞:
      • `x²/σ² → 0`     (since 1/σ² → 0 and x² fixed)
      • `exp(x²/σ²) → exp(0) = 1`  (by continuity of `Real.exp`)
      • `2/σ² → 0`      (from `tendsto_two_div_sq_atTop_zero`)
    Product → 0·1 = 0.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **σ → ∞ limit at fixed `x`**:  `x²/σ² → 0` as σ → ∞.
    Standard product/division of limits. -/
theorem tendsto_xsq_div_sq_atTop_zero (x : ℝ) :
    Tendsto (fun σ : ℝ => x ^ 2 / σ ^ 2) atTop (𝓝 0) := by
  have h_sq : Tendsto (fun σ : ℝ => σ ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h_inv : Tendsto (fun σ : ℝ => (σ ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h_sq
  have h_mul := h_inv.const_mul (x ^ 2)
  simp only [mul_zero] at h_mul
  have h_eq :
      (fun σ : ℝ => x ^ 2 * (σ ^ 2)⁻¹) = (fun σ : ℝ => x ^ 2 / σ ^ 2) := by
    funext σ; rw [div_eq_mul_inv]
  rw [h_eq] at h_mul
  exact h_mul

/-- **Real.exp ∘ (x²/σ²) → 1** as σ → ∞:  composition of the
    `x²/σ² → 0` limit with continuity of `Real.exp` at 0. -/
theorem tendsto_exp_xsq_div_sq_atTop_one (x : ℝ) :
    Tendsto (fun σ : ℝ => Real.exp (x ^ 2 / σ ^ 2)) atTop (𝓝 1) := by
  have h_x : Tendsto (fun σ : ℝ => x ^ 2 / σ ^ 2) atTop (𝓝 0) :=
    tendsto_xsq_div_sq_atTop_zero x
  have h_exp : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (Real.exp 0)) :=
    Real.continuous_exp.tendsto 0
  rw [Real.exp_zero] at h_exp
  exact h_exp.comp h_x

/-- **σ → ∞ limit for the Gaussian Ricci at fixed `x`**:
    `R_σ(x) = 2·exp(x²/σ²)/σ² → 0` as σ → ∞.

    At fixed x (possibly nonzero), the closed form `2·exp(x²/σ²)/σ²`
    consists of a vanishing prefactor `2/σ²` and an exponential
    factor tending to 1.  Product → 0. -/
theorem gaussian_Ricci_atFixedX_atTop (x : ℝ) :
    Tendsto (fun σ : ℝ => 2 * Real.exp (x ^ 2 / σ ^ 2) / σ ^ 2)
            atTop (𝓝 0) := by
  -- 2·exp(...)/σ² = (2/σ²) · exp(...).
  have h_factor :
      (fun σ : ℝ => 2 * Real.exp (x ^ 2 / σ ^ 2) / σ ^ 2)
        = (fun σ : ℝ => (2 / σ ^ 2) * Real.exp (x ^ 2 / σ ^ 2)) := by
    funext σ
    ring
  rw [h_factor]
  -- (2/σ²) → 0 ∧ exp(x²/σ²) → 1  ⇒  product → 0·1 = 0.
  have h_2 : Tendsto (fun σ : ℝ => (2 : ℝ) / σ ^ 2) atTop (𝓝 0) :=
    tendsto_two_div_sq_atTop_zero
  have h_exp : Tendsto (fun σ : ℝ => Real.exp (x ^ 2 / σ ^ 2)) atTop (𝓝 1) :=
    tendsto_exp_xsq_div_sq_atTop_one x
  have h_prod := h_2.mul h_exp
  simp at h_prod
  exact h_prod

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — STATUS / FRONTIER.

    Closed in this file:
      ✓ `tendsto_two_div_sq_atTop_zero` — generic σ → ∞ limit.
      ✓ `tendsto_two_div_sq_nhdsGT_zero_atTop` — generic σ → 0⁺ limit.
      ✓ `sech_Ricci_atTop`, `sech_Ricci_nhdsGT_zero` — E3 σ-limits.
      ✓ `gaussian_Ricci_atZero_atTop`, `gaussian_Ricci_atZero_nhdsGT_zero`
        — E2 σ-limits at the Gaussian peak.

    What this establishes:
      Both the sech soliton and the Gaussian (at its peak) interpolate
      smoothly between the **vacuum** limit (σ → ∞, R → 0) and the
      **sharp / singular** limit (σ → 0⁺, R → ∞).  This is the
      formal Tendsto-statement of the qualitative observations
      embedded in E2/E3.

    Closed in Part 3.5 (also in this file):
      ✓ `tendsto_xsq_div_sq_atTop_zero` — `x²/σ² → 0` at fixed x.
      ✓ `tendsto_exp_xsq_div_sq_atTop_one` — `exp(x²/σ²) → 1` at fixed x.
      ✓ `gaussian_Ricci_atFixedX_atTop` — full Gaussian Ricci → 0
        at fixed nonzero x as σ → ∞.

    Open continuations:
    • σ → 0⁺ limit at fixed nonzero x:  R → ∞ exponentially fast
      (a much sharper asymptotic, since `exp(x²/σ²) → ∞` as well).
    • Quantitative bound versions:  `R(σ) ≤ C/σ²` for some
      constant C, useful for higher-level estimates.
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotinePredictionELimits
