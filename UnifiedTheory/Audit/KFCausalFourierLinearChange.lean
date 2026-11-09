/- Fourier change of variables for a genuine invertible linear map,
including its determinant. No isometry of that map is assumed. -/
import UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFourierLinearChange
noncomputable section
open MeasureTheory Set
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem inverse_adjoint_left (A : E ≃L[ℝ] E) (x : E) :
    (A : E →L[ℝ] E).adjoint ((A.symm : E →L[ℝ] E).adjoint x) = x := by
  have he : (A.symm : E →L[ℝ] E).comp (A : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    ext y
    exact A.symm_apply_apply y
  have hh := congrArg (ContinuousLinearMap.adjoint : (E →L[ℝ] E) → (E →L[ℝ] E)) he
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at hh
  exact congrArg (fun Q : E →L[ℝ] E => Q x) hh

def dualEquiv (A : E ≃L[ℝ] E) : E ≃L[ℝ] E where
  toFun := (A.symm : E →L[ℝ] E).adjoint
  invFun := (A : E →L[ℝ] E).adjoint
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv := inverse_adjoint_left A
  right_inv := inverse_adjoint_left A.symm
  continuous_toFun := (A.symm : E →L[ℝ] E).adjoint.continuous
  continuous_invFun := (A : E →L[ℝ] E).adjoint.continuous

theorem dual_inner (A : E ≃L[ℝ] E) (x k : E) :
    inner ℝ x (dualEquiv A k) = inner ℝ (A.symm x) k :=
  ContinuousLinearMap.adjoint_inner_right (A.symm : E →L[ℝ] E) x k

variable [MeasurableSpace E] [BorelSpace E]

theorem dual_quasiMeasurePreserving (A : E ≃L[ℝ] E) :
    Measure.QuasiMeasurePreserving (dualEquiv A) volume volume :=
  KFCausalCoupledCoordinateNullSets.homeomorph_quasiMeasurePreserving volume
    (dualEquiv A).toHomeomorph (dualEquiv A).symm.differentiable

theorem linear_quasiMeasurePreserving (A : E ≃L[ℝ] E) :
    Measure.QuasiMeasurePreserving A volume volume :=
  KFCausalCoupledCoordinateNullSets.homeomorph_quasiMeasurePreserving volume
    A.toHomeomorph A.symm.differentiable

def jacobian (A : E ≃L[ℝ] E) : ℝ := |(A.symm : E →L[ℝ] E).det|

theorem integral_change (A : E ≃L[ℝ] E) (f : E → ℂ) :
    (∫ x, f x) = jacobian A • ∫ y, f (A.symm y) := by
  have hh := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    (f := A.symm) (f' := fun _ => (A.symm : E →L[ℝ] E)) MeasurableSet.univ
    (fun x _ => A.symm.hasFDerivAt.hasFDerivWithinAt) A.symm.injective.injOn f
  simpa only [image_univ,A.symm.surjective.range_eq,setIntegral_univ,integral_smul,jacobian] using hh

theorem fourier_comp (A : E ≃L[ℝ] E) (f : E → ℂ) (k : E) :
    (𝓕 (fun x => f (A x))) k = (jacobian A:ℂ)*(𝓕 f) (dualEquiv A k) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  rw [integral_change A]
  simp only [A.apply_symm_apply,← dual_inner,Circle.smul_def,smul_eq_mul,Complex.real_smul]

theorem fourier_weighted_comp (A : E ≃L[ℝ] E) (w : ℂ) (f : E → ℂ) (k : E) :
    (𝓕 (fun x => w*f (A x))) k = (w*(jacobian A:ℂ))*(𝓕 f) (dualEquiv A k) := by
  have he : (𝓕 (fun x => w*f (A x))) k = w*(𝓕 (fun x => f (A x))) k := by
    simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [he,fourier_comp,mul_assoc]

#print axioms dual_inner
#print axioms dual_quasiMeasurePreserving
#print axioms linear_quasiMeasurePreserving
#print axioms integral_change
#print axioms fourier_comp
#print axioms fourier_weighted_comp
end
end UnifiedTheory.Audit.KFCausalFourierLinearChange
