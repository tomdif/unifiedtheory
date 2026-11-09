/- A locally Lipschitz Hilbert-valued curve with weak scalar derivatives
has the expected derivative for every bounded symmetric quadratic form.
The proof controls the quadratic increment directly; it does not assume
strong differentiability of the curve. -/
import UnifiedTheory.Audit.KFCausalMassGram
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeakQuadraticDerivative
noncomputable section
open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def energy (P : E →L[ℂ] E) (x : E) : ℝ := (inner ℂ x (P x)).re

theorem energy_increment (P : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) (x d : E) :
    energy P (x+d)-energy P x = 2*(inner ℂ d (P x)).re + energy P d := by
  have hh : (inner ℂ x (P d)).re = (inner ℂ d (P x)).re := by
    rw [← hs]
    exact inner_re_symm (𝕜 := ℂ) (P x) d
  simp only [energy,map_add,inner_add_left,inner_add_right,Complex.add_re]
  linarith

theorem quadratic_remainder_bound (P : E →L[ℂ] E) (d : E) (h C : ℝ)
    (hC : 0 ≤ C) (hd : ‖d‖ ≤ C*|h|) :
    ‖h⁻¹*energy P d‖ ≤ (‖P‖*C^2)*|h| := by
  have he : |energy P d| ≤ ‖P‖*‖d‖^2 := by
    apply (Complex.abs_re_le_norm _).trans
    apply (norm_inner_le_norm d (P d)).trans
    have hn := mul_le_mul_of_nonneg_left (P.le_opNorm d) (norm_nonneg d)
    nlinarith
  have hs : ‖d‖^2 ≤ (C*|h|)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
  rw [norm_mul,Real.norm_eq_abs,abs_inv,Real.norm_eq_abs]
  calc
    _ ≤ |h|⁻¹*(‖P‖*‖d‖^2) := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ |h|⁻¹*(‖P‖*(C*|h|)^2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) (by positivity)
    _ = (‖P‖*C^2)*|h| := by
      by_cases hh : h = 0
      · simp [hh]
      · have ha : |h| ≠ 0 := abs_ne_zero.mpr hh
        field_simp

theorem energy_derivative_of_weak (P : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (u : ℝ → E) (d : E) (x C : ℝ) (hC : 0 ≤ C)
    (hl : ∀ᶠ h in 𝓝[≠] (0:ℝ), ‖u (x+h)-u x‖ ≤ C*|h|)
    (hd : ∀ y, HasDerivAt (fun z => inner ℂ (u z) y) (inner ℂ d y) x) :
    HasDerivAt (fun z => energy P (u z)) (2*(inner ℂ d (P (u x))).re) x := by
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd (P (u x)))
  have hlin : Tendsto (fun h : ℝ => h⁻¹*(inner ℂ (u (x+h)-u x) (P (u x))).re)
      (𝓝[≠] 0) (𝓝 (inner ℂ d (P (u x))).re) := by
    simpa only [Function.comp_def,Complex.reCLM_apply,inner_sub_left,Complex.sub_re,
      smul_eq_mul] using hreal.tendsto_slope_zero
  have hrem : Tendsto (fun h : ℝ => h⁻¹*energy P (u (x+h)-u x)) (𝓝[≠] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (hl.mono (fun h hh => quadratic_remainder_bound P _ h C hC hh))
    have hh : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 |(0:ℝ)|) :=
      (continuous_abs.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [abs_zero,mul_zero] using hh.const_mul (‖P‖*C^2)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have he (h : ℝ) : energy P (u (x+h))-energy P (u x) =
      2*(inner ℂ (u (x+h)-u x) (P (u x))).re+energy P (u (x+h)-u x) := by
    have hsum : u x+(u (x+h)-u x) = u (x+h) := by abel
    simpa only [hsum] using energy_increment P hs (u x) (u (x+h)-u x)
  have hh := (hlin.const_mul 2).add hrem
  simp only [add_zero] at hh
  convert hh using 1
  funext h
  rw [he,smul_eq_mul]
  ring

#print axioms energy_increment
#print axioms quadratic_remainder_bound
#print axioms energy_derivative_of_weak

end
end UnifiedTheory.Audit.KFCausalWeakQuadraticDerivative
