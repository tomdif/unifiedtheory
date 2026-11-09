/- A form-space chain rule. The state is only continuous in the form
norm. Its mass-dual curve is locally Lipschitz with weak derivatives.
This suffices for a bounded physical observable preserving the form space. -/
import UnifiedTheory.Audit.KFCausalWeakQuadraticDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFormObservableDerivative
noncomputable section
open Filter
open scoped Topology

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def expectation (J : V →L[ℂ] H) (D : H →L[ℂ] H) (x : V) : ℝ :=
  (inner ℂ (J x) (D (J x))).re

theorem mixed_increment (J : V →L[ℂ] H) (D : H →L[ℂ] H)
    (G A : V →L[ℂ] V)
    (hG : ∀ x y, inner ℂ (G x) y = inner ℂ (J x) (J y))
    (hA : ∀ x, J (A x) = D (J x))
    (hD : ∀ x y, inner ℂ (D x) y = inner ℂ x (D y)) (x d : V) :
    expectation J D (x+d)-expectation J D x =
      2*(inner ℂ (G d) (A x)).re + (inner ℂ (G d) (A d)).re := by
  simp only [hG,hA]
  simpa only [expectation,map_add,KFCausalWeakQuadraticDerivative.energy] using
    KFCausalWeakQuadraticDerivative.energy_increment D hD (J x) (J d)

theorem mixed_remainder_bound (G A : V →L[ℂ] V) (d : V) (h C : ℝ) (hC : 0 ≤ C)
    (hd : ‖G d‖ ≤ C*|h|) :
    ‖h⁻¹*(inner ℂ (G d) (A d)).re‖ ≤ (C*‖A‖)*‖d‖ := by
  by_cases hz : h = 0
  · simp only [hz,inv_zero,zero_mul,norm_zero]
    positivity
  ·
    have hp := (Complex.abs_re_le_norm (inner ℂ (G d) (A d))).trans (norm_inner_le_norm _ _)
    have hn := mul_le_mul hd (A.le_opNorm d) (norm_nonneg _) (by positivity : 0 ≤ C*|h|)
    rw [norm_mul,Real.norm_eq_abs,abs_inv,Real.norm_eq_abs]
    calc
      _ ≤ |h|⁻¹*((C*|h|)*(‖A‖*‖d‖)) :=
        mul_le_mul_of_nonneg_left (hp.trans hn) (by positivity)
      _ = (C*‖A‖)*‖d‖ := by field_simp

theorem expectation_derivative (J : V →L[ℂ] H) (D : H →L[ℂ] H)
    (G A : V →L[ℂ] V)
    (hG : ∀ x y, inner ℂ (G x) y = inner ℂ (J x) (J y))
    (hA : ∀ x, J (A x) = D (J x))
    (hD : ∀ x y, inner ℂ (D x) y = inner ℂ x (D y))
    (u : ℝ → V) (v : V) (x C : ℝ) (hC : 0 ≤ C)
    (hu : ContinuousAt u x)
    (hl : ∀ᶠ h in 𝓝[≠] (0:ℝ), ‖G (u (x+h))-G (u x)‖ ≤ C*|h|)
    (hd : ∀ y, HasDerivAt (fun z => inner ℂ (G (u z)) y) (inner ℂ v y) x) :
    HasDerivAt (fun z => expectation J D (u z))
      (2*(inner ℂ v (A (u x))).re) x := by
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd (A (u x)))
  have hlin : Tendsto (fun h : ℝ => h⁻¹*(inner ℂ (G (u (x+h)-u x)) (A (u x))).re)
      (𝓝[≠] 0) (𝓝 (inner ℂ v (A (u x))).re) := by
    simpa only [Function.comp_def,Complex.reCLM_apply,map_sub,inner_sub_left,Complex.sub_re,
      smul_eq_mul] using hreal.tendsto_slope_zero
  have hzero : Tendsto (fun h : ℝ => ‖u (x+h)-u x‖) (𝓝[≠] 0) (𝓝 0) := by
    have ht : Tendsto (fun h : ℝ => x+h) (𝓝[≠] 0) (𝓝 x) := by
      have hi : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa only [add_zero] using hi.const_add x
    simpa only [sub_self,norm_zero] using ((hu.tendsto.comp ht).sub_const (u x)).norm
  have hrem : Tendsto (fun h : ℝ => h⁻¹*(inner ℂ (G (u (x+h)-u x)) (A (u (x+h)-u x))).re)
      (𝓝[≠] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (hl.mono (fun h hh => mixed_remainder_bound G A _ h C hC (by simpa only [map_sub] using hh)))
    simpa only [mul_zero] using hzero.const_mul (C*‖A‖)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have he (h : ℝ) : expectation J D (u (x+h))-expectation J D (u x) =
      2*(inner ℂ (G (u (x+h)-u x)) (A (u x))).re+
        (inner ℂ (G (u (x+h)-u x)) (A (u (x+h)-u x))).re := by
    have hsum : u x+(u (x+h)-u x) = u (x+h) := by abel
    simpa only [hsum] using mixed_increment J D G A hG hA hD (u x) (u (x+h)-u x)
  have ht := (hlin.const_mul 2).add hrem
  simp only [add_zero] at ht
  convert ht using 1
  funext h
  rw [he,smul_eq_mul]
  ring

#print axioms mixed_increment
#print axioms mixed_remainder_bound
#print axioms expectation_derivative

end
end UnifiedTheory.Audit.KFCausalFormObservableDerivative
