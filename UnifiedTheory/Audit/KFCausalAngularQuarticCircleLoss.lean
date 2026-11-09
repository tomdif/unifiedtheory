/- Reflection extends the actual quartic circle estimate to every signed
tilt. The one finite constant controls the original linked field derivative
for all real field coefficients, with no normalization premise. -/
import UnifiedTheory.Audit.KFCausalAngularQuarticCircleEndpoint

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularQuarticCircleLoss
noncomputable section
open MeasureTheory Set
open KFCausalAngularQuarticCircle

private theorem cosine_reflection (f : ℝ→ℝ) (hf : Continuous f) :
    (∫ theta in 0..(2*Real.pi), f (-Real.cos theta)) =
      ∫ theta in 0..(2*Real.pi), f (Real.cos theta) := by
  rw [KFCausalAngularCosineEndpoint.cosine_integral (fun x => f (-x)) (hf.comp continuous_neg),
    KFCausalAngularCosineEndpoint.cosine_integral f hf]
  have he := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := (1:ℝ))
    (fun x : ℝ => f x*(Real.sqrt (1-x^2))⁻¹)
  simp only [neg_neg,neg_sq] at he
  exact congrArg (fun x : ℝ => 2*x) he

theorem energy_reflection (z mu l : ℝ) : energy (-z) mu l=energy z mu (-l) := by
  let f : ℝ→ℝ := fun x => Real.exp (-z*x)*(mu-l*x)^4
  have he := cosine_reflection f (by dsimp [f]; fun_prop)
  convert he using 1 <;> apply intervalIntegral.integral_congr <;> intro theta _ <;>
    dsimp [energy,integrand,f] <;> congr 1 <;> ring

theorem defect_reflection (z mu l : ℝ) : defect (-z) mu l=defect z mu (-l) := by
  let f : ℝ→ℝ := fun x => (-2*z*x)*Real.exp (-z*x)*(mu-l*x)^4+
    l*Real.exp (-z*x)*(4*x*(mu-l*x)^3)
  have he := cosine_reflection f (by dsimp [f]; fun_prop)
  convert he using 1 <;> apply intervalIntegral.integral_congr <;> intro theta _ <;>
    dsimp [defect,defectIntegrand,integrand,fieldIntegrand,f] <;>
    simp only [neg_mul,mul_neg,neg_neg] <;> ring

theorem global_loss :
    ∃ C : ℝ, 0≤C ∧ ∀ z mu l : ℝ,
      0≤defect z mu l+C*energy z mu l := by
  obtain ⟨C,hC,hbound⟩ := KFCausalAngularQuarticCircleEndpoint.nonnegative_tilt_loss
  refine ⟨C,hC,?_⟩
  intro z mu l
  by_cases hz : 0≤z
  · exact hbound z mu l hz
  · have hb := hbound (-z) mu (-l) (by linarith)
    simpa only [energy_reflection,defect_reflection,neg_neg] using hb

theorem global_linked_loss :
    ∃ C : ℝ, 0≤C ∧ ∀ z mu l : ℝ,
      0≤2*tilt z mu l-l*deriv (fun x => energy z mu x) l+C*energy z mu l := by
  obtain ⟨C,hC,hbound⟩ := global_loss
  refine ⟨C,hC,?_⟩
  intro z mu l
  rw [(field_derivative z mu l).deriv,← defect_eq]
  exact hbound z mu l

#print axioms energy_reflection
#print axioms defect_reflection
#print axioms global_loss
#print axioms global_linked_loss
end
end UnifiedTheory.Audit.KFCausalAngularQuarticCircleLoss
