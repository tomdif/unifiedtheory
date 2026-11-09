/- Jacobian-weighted transverse pullback. The actual dilation/shear flow
preserves the L2 norm after multiplication by exp(-t); both integrability
directions are proved by change of variables. -/
import UnifiedTheory.Audit.KFCausalTransverseDilationFlow
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseDilationPullback
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow

def flowCLM (t : ℝ) : Transverse →L[ℝ] Transverse :=
  (flowEquiv t).toContinuousLinearEquiv.toContinuousLinearMap

theorem flowCLM_det (t : ℝ) : (flowCLM t).det = Real.exp (2*t) := by
  have he : (flowCLM t).toLinearMap = Matrix.toLin' (flowMatrix t) := by
    apply LinearMap.ext
    intro x
    exact (flowMatrix_apply t x).symm
  change LinearMap.det (flowCLM t).toLinearMap = _
  rw [he,LinearMap.det_toLin',flowMatrix_det]

def pullback (t : ℝ) (ψ : Transverse → ℂ) (x : Transverse) : ℂ :=
  (Real.exp (-t):ℂ)*ψ (flow (-t) x)

theorem pullback_density (t : ℝ) (ψ : Transverse → ℂ) (x : Transverse) :
    ‖pullback t ψ x‖^2 = Real.exp (2*(-t))*‖ψ (flow (-t) x)‖^2 := by
  simp only [pullback,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_pow,← Real.exp_nat_mul]
  norm_num

theorem pullback_square_integral (t : ℝ) (ψ : Transverse → ℂ) :
    (∫ x, ‖pullback t ψ x‖^2) = ∫ x, ‖ψ x‖^2 := by
  have hh := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    (f := flow (-t)) (f' := fun _ => flowCLM (-t)) MeasurableSet.univ
    (fun x _ => (flowCLM (-t)).hasFDerivAt.hasFDerivWithinAt)
    (flow_bijective (-t)).1.injOn (fun x => ‖ψ x‖^2)
  simpa only [image_univ,(flow_bijective (-t)).2.range_eq,setIntegral_univ,
    flowCLM_det,abs_of_pos (Real.exp_pos _),smul_eq_mul,pullback_density] using hh.symm

theorem pullback_square_integrable_iff (t : ℝ) (ψ : Transverse → ℂ) :
    Integrable (fun x => ‖pullback t ψ x‖^2) ↔ Integrable (fun x => ‖ψ x‖^2) := by
  have hh := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
    (f := flow (-t)) (f' := fun _ => flowCLM (-t)) MeasurableSet.univ
    (fun x _ => (flowCLM (-t)).hasFDerivAt.hasFDerivWithinAt)
    (flow_bijective (-t)).1.injOn (fun x => ‖ψ x‖^2)
  simpa only [image_univ,(flow_bijective (-t)).2.range_eq,integrableOn_univ,
    flowCLM_det,abs_of_pos (Real.exp_pos _),smul_eq_mul,pullback_density] using hh.symm

theorem pullback_initial (ψ : Transverse → ℂ) : pullback 0 ψ = ψ := by
  funext x
  simp [pullback,flow_initial]

theorem pullback_compose (t u : ℝ) (ψ : Transverse → ℂ) :
    pullback t (pullback u ψ) = pullback (t+u) ψ := by
  funext x
  simp only [pullback,flow_compose,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,← neg_add]

#print axioms flowCLM_det
#print axioms pullback_density
#print axioms pullback_square_integral
#print axioms pullback_square_integrable_iff
#print axioms pullback_compose

end
end UnifiedTheory.Audit.KFCausalTransverseDilationPullback
