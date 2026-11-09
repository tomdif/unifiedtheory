/- A uniform L2 majorant and almost-everywhere parameter continuity give
continuity of the actual L2 vectors. This provides an orbit-lift criterion
without choosing pointwise representatives of arbitrary L2 limits. -/
import UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDominatedL2Continuity
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)

variable {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [MeasurableSpace X] {μ : Measure X}

omit [TopologicalSpace P] [FirstCountableTopology P] in
theorem difference_square_integral (F : P → X → ℂ) (hF : ∀ p, MemLp (F p) 2 μ) (p q : P) :
    ‖(hF p).toLp (F p)-(hF q).toLp (F q)‖^2 = ∫ x, ‖F p x-F q x‖^2 ∂μ := by
  rw [← MemLp.toLp_sub,toLp_square_integral]
  rfl

theorem continuous_toLp (F : P → X → ℂ) (hF : ∀ p, MemLp (F p) 2 μ)
    (g : X → ℂ) (hg : MemLp g 2 μ)
    (hb : ∀ p, ∀ᵐ x ∂μ, ‖F p x‖ ≤ ‖g x‖)
    (hc : ∀ᵐ x ∂μ, Continuous (fun p => F p x)) :
    Continuous (fun p => (hF p).toLp (F p)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hi : Continuous (fun p => ∫ x, ‖F p x-F q x‖^2 ∂μ) := by
    apply continuous_of_dominated
      (bound := fun x => 4*‖g x‖^2)
      (fun p => ((hF p).aestronglyMeasurable.sub (hF q).aestronglyMeasurable).norm.pow 2)
    · intro p
      filter_upwards [hb p,hb q] with x hp hq
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hd : ‖F p x-F q x‖ ≤ 2*‖g x‖ := (norm_sub_le _ _).trans (by linarith)
      have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
      dsimp only [Pi.pow_apply,Pi.sub_apply]
      nlinarith
    · exact hg2.const_mul 4
    · filter_upwards [hc] with x hx
      exact (hx.sub continuous_const).norm.pow 2
  have hs := (Real.continuous_sqrt.comp hi).continuousAt (x := q)
  have he : (fun p => Real.sqrt (∫ x, ‖F p x-F q x‖^2 ∂μ)) =
      fun p => ‖(hF p).toLp (F p)-(hF q).toLp (F q)‖ := by
    funext p
    rw [← difference_square_integral F hF,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  change ContinuousAt (fun p => Real.sqrt (∫ x, ‖F p x-F q x‖^2 ∂μ)) q at hs
  rw [he] at hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [ContinuousAt,sub_self,norm_zero] using hs

#print axioms difference_square_integral
#print axioms continuous_toLp

end
end UnifiedTheory.Audit.KFCausalDominatedL2Continuity
