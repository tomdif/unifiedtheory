/- Inverse powers of a shrinking mesh dominate logarithmic coupling growth.
These elementary bounds keep the geometric path arbitrary. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.LogarithmicUltravioletGrowth
noncomputable section
open Filter
open scoped Topology

/-- A polynomial bound suffices; no asymptotic expansion of the logarithm is used. -/
theorem inverse_square_lower (a β b : ℝ) (ha : 0 < a) (hβ : 0 < β) (hb : 0 < b)
    (hupper : β ≤ b * Real.log a⁻¹) :
    a⁻¹ ^ 2 / b ^ 2 ≤ (a ^ 4)⁻¹ / β ^ 2 := by
  have ht : 0 < a⁻¹ := inv_pos.mpr ha
  have hl : Real.log a⁻¹ ≤ a⁻¹ := by
    have h := Real.log_le_sub_one_of_pos ht
    linarith
  have hc : β ≤ b * a⁻¹ := hupper.trans (mul_le_mul_of_nonneg_left hl hb.le)
  have hs := pow_le_pow_left₀ hβ.le hc 2
  rw [← inv_pow]
  apply (div_le_div_iff₀ (pow_pos hb 2) (pow_pos hβ 2)).mpr
  have h := mul_le_mul_of_nonneg_left hs (sq_nonneg a⁻¹)
  nlinarith

/-- A positive mesh tending to zero has reciprocal tending to infinity. -/
theorem reciprocal_tendsto {ι : Type*} (l : Filter ι) (a : ι → ℝ)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => (a i)⁻¹) l atTop := by
  have h : Tendsto a l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha0, ha⟩
  exact h.inv_tendsto_nhdsGT_zero

/-- Uniform logarithmic upper brackets force divergence of the actual
inverse-fourth-power noise prefactor on every shrinking positive mesh. -/
theorem inverse_fourth_div_square_tendsto {ι : Type*} (l : Filter ι) (a β : ι → ℝ)
    (b : ℝ) (hb : 0 < b) (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hβ : ∀ᶠ i in l, 0 < β i)
    (hupper : ∀ᶠ i in l, β i ≤ b * Real.log (a i)⁻¹) :
    Tendsto (fun i => ((a i) ^ 4)⁻¹ / (β i) ^ 2) l atTop := by
  have h := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp
    (reciprocal_tendsto l a ha ha0)).const_mul_atTop (show 0 < (b ^ 2)⁻¹ by positivity)
  have hl : Tendsto (fun i => (a i)⁻¹ ^ 2 / b ^ 2) l atTop := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_comm] using h
  apply tendsto_atTop_mono' l _ hl
  filter_upwards [ha, hβ, hupper] with i hai hβi hui
  exact inverse_square_lower (a i) (β i) b hai hβi hb hui

end
end UnifiedTheory.Clay.YangMills.LogarithmicUltravioletGrowth
