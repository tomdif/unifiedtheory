/- The actual symmetric charged-coordinate insertion after undoing the
relative complex shear. Its expression in the target Gaussian variables
keeps the charge angle and shear order explicit. -/
import UnifiedTheory.Audit.KFCausalWidthGaussianHolomorphicContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalSymmetricInsertionCoordinate
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalWidthGaussianHolomorphicQuotient (targetVector baselineVector)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalComplexShearPerturbation (flow rotatedFlow)
open KFCausalPhysicalReciprocalNormalization (coupling)

def coordinateIndex (i : Fin 2) : Fin 5 := ![2,3] i

def coordinateScale (α w : ℝ) (i : Fin 2) : ℝ :=
  ![Real.sqrt (α/w),Real.sqrt (α*w)] i

def increment (ε h : ℝ) (q : ℂ) : ℂ :=
  complexInverse ε (shift h q)-complexInverse ε q

def coefficient (ε h α w c θ : ℝ) (i : Fin 2) (q : ℂ) (x : Joint 2 4) : ℂ :=
  Complex.exp (-increment ε h q/2)*
    (rotationIsometry θ (targetVector ε h α w c θ q x)) (coordinateIndex i)/
      (coordinateScale α w i : ℂ)

theorem coordinateScale_positive (α w : ℝ) (hα : 0 < α) (hw : 0 < w) (i : Fin 2) :
    0 < coordinateScale α w i := by
  fin_cases i <;> dsimp [coordinateScale] <;> positivity

theorem rotation_target (ε h α w c θ : ℝ) (q : ℂ) (x : Joint 2 4) :
    rotationIsometry θ (targetVector ε h α w c θ q x) =
      flow (coupling α w) (increment ε h q)
        (rotationIsometry θ (baselineVector ε α w c q x)) := by
  exact (rotationIsometry θ).apply_symm_apply _

private theorem flow_coordinate (σ : ℝ) (z : ℂ)
    (x : KFCausalComplexShearPerturbation.Space) (i : Fin 2) :
    flow σ z x (coordinateIndex i) = Complex.exp (z/2)*x (coordinateIndex i) := by
  fin_cases i <;> rfl

theorem coefficient_eq_baseline (ε h α w c θ : ℝ) (i : Fin 2) (q : ℂ) (x : Joint 2 4) :
    coefficient ε h α w c θ i q x =
      (rotationIsometry θ (baselineVector ε α w c q x)) (coordinateIndex i)/
        (coordinateScale α w i : ℂ) := by
  rw [coefficient,rotation_target,flow_coordinate,← mul_assoc,← Complex.exp_add]
  rw [show -increment ε h q/2+increment ε h q/2=0 by ring,Complex.exp_zero,one_mul]

#print axioms coordinateScale_positive
#print axioms rotation_target
#print axioms coefficient_eq_baseline
end
end UnifiedTheory.Audit.KFCausalSymmetricInsertionCoordinate
