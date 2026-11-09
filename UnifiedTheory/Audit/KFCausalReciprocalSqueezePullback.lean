/- The reciprocal squeeze has Jacobian exp(a); its inverse pullback therefore
has half-density exp(-a/2). The exact L2 change of variables is proved. -/
import UnifiedTheory.Audit.KFCausalReciprocalSqueezeFlow
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalReciprocalSqueezePullback
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalReciprocalSqueezeFlow

def squeezeCLM (a : ℝ) : Transverse →L[ℝ] Transverse :=
  (squeezeEquiv a).toContinuousLinearEquiv.toContinuousLinearMap

theorem squeezeCLM_det (a : ℝ) : (squeezeCLM a).det = Real.exp a := by
  have he : (squeezeCLM a).toLinearMap = Matrix.toLin' (squeezeMatrix a) := by
    apply LinearMap.ext
    intro x
    exact (squeezeMatrix_apply a x).symm
  change LinearMap.det (squeezeCLM a).toLinearMap = _
  rw [he,LinearMap.det_toLin',squeezeMatrix_det]

def pullback (a : ℝ) (ψ : Transverse → ℂ) (x : Transverse) : ℂ :=
  (Real.exp (-a/2):ℂ)*ψ (squeeze (-a) x)

theorem pullback_density (a : ℝ) (ψ : Transverse → ℂ) (x : Transverse) :
    ‖pullback a ψ x‖^2 = Real.exp (-a)*‖ψ (squeeze (-a) x)‖^2 := by
  simp only [pullback,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_pow,← Real.exp_nat_mul]
  congr 2
  norm_num
  ring

theorem pullback_square_integral (a : ℝ) (ψ : Transverse → ℂ) :
    (∫ x, ‖pullback a ψ x‖^2) = ∫ x, ‖ψ x‖^2 := by
  have hh := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    (f := squeeze (-a)) (f' := fun _ => squeezeCLM (-a)) MeasurableSet.univ
    (fun x _ => (squeezeCLM (-a)).hasFDerivAt.hasFDerivWithinAt)
    (squeeze_bijective (-a)).1.injOn (fun x => ‖ψ x‖^2)
  simpa only [image_univ,(squeeze_bijective (-a)).2.range_eq,setIntegral_univ,
    squeezeCLM_det,abs_of_pos (Real.exp_pos _),smul_eq_mul,pullback_density] using hh.symm

theorem pullback_square_integrable_iff (a : ℝ) (ψ : Transverse → ℂ) :
    Integrable (fun x => ‖pullback a ψ x‖^2) ↔ Integrable (fun x => ‖ψ x‖^2) := by
  have hh := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
    (f := squeeze (-a)) (f' := fun _ => squeezeCLM (-a)) MeasurableSet.univ
    (fun x _ => (squeezeCLM (-a)).hasFDerivAt.hasFDerivWithinAt)
    (squeeze_bijective (-a)).1.injOn (fun x => ‖ψ x‖^2)
  simpa only [image_univ,(squeeze_bijective (-a)).2.range_eq,integrableOn_univ,
    squeezeCLM_det,abs_of_pos (Real.exp_pos _),smul_eq_mul,pullback_density] using hh.symm

#print axioms squeezeCLM_det
#print axioms pullback_density
#print axioms pullback_square_integral
#print axioms pullback_square_integrable_iff

end
end UnifiedTheory.Audit.KFCausalReciprocalSqueezePullback
