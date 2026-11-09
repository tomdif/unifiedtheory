/- Undoing the relative neutral shear gives the physical neutral and
full point-field insertion as explicit linear expressions in the target
Gaussian coordinates. This is a coordinate identity only. -/
import UnifiedTheory.Audit.KFCausalSymmetricInsertionCoordinate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPointFieldInsertionCoordinate
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalWidthGaussianHolomorphicQuotient (targetVector baselineVector)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalComplexShearPerturbation (flow)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalSymmetricInsertionCoordinate (increment rotation_target)

def neutralScale (α : ℝ) : ℝ := Real.sqrt (α/32)

def neutralCoefficient (ε h α w c θ : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  (targetVector ε h α w c θ q x 4-
    2*(coupling α w:ℂ)*(1-Complex.exp (-increment ε h q/2))*
      (rotationIsometry θ (targetVector ε h α w c θ q x)) 3)/(neutralScale α:ℂ)

def coefficient (ε h α w c θ : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  2*(KFCausalPairedModeCoordinates.scale:ℂ)*
    KFCausalSymmetricInsertionCoordinate.coefficient ε h α w c θ 1 q x+
      neutralCoefficient ε h α w c θ q x

theorem neutralScale_positive (α : ℝ) (hα : 0 < α) : 0 < neutralScale α := by
  unfold neutralScale
  positivity

theorem neutralCoefficient_eq_baseline (ε h α w c θ : ℝ) (q : ℂ) (x : Joint 2 4) :
    neutralCoefficient ε h α w c θ q x = baselineVector ε α w c q x 4/(neutralScale α:ℂ) := by
  let Z := targetVector ε h α w c θ q x
  let Y := baselineVector ε α w c q x
  let δ := increment ε h q
  have h3 : (rotationIsometry θ Z) 3 = Complex.exp (δ/2)*(rotationIsometry θ Y) 3 := by
    have hh := congrArg (fun y : KFCausalComplexShearPerturbation.Space => y 3)
      (rotation_target ε h α w c θ q x)
    exact hh
  have h4 : Z 4 = Y 4+2*(coupling α w:ℂ)*(Complex.exp (δ/2)-1)*(rotationIsometry θ Y) 3 := by
    have hh := congrArg (fun y : KFCausalComplexShearPerturbation.Space => y 4)
      (rotation_target ε h α w c θ q x)
    exact hh
  have he : Complex.exp (-δ/2)*Complex.exp (δ/2)=1 := by
    rw [← Complex.exp_add,show -δ/2+δ/2=0 by ring,Complex.exp_zero]
  change (Z 4-2*(coupling α w:ℂ)*(1-Complex.exp (-δ/2))*(rotationIsometry θ Z) 3)/
    (neutralScale α:ℂ)=Y 4/(neutralScale α:ℂ)
  rw [h3,h4]
  congr 1
  calc
    _ = Y 4+2*(coupling α w:ℂ)*(Complex.exp (-δ/2)*Complex.exp (δ/2)-1)*
      (rotationIsometry θ Y) 3 := by ring
    _ = Y 4 := by rw [he]; ring

theorem coefficient_eq_baseline (ε h α w c θ : ℝ) (q : ℂ) (x : Joint 2 4) :
    coefficient ε h α w c θ q x =
      2*(KFCausalPairedModeCoordinates.scale:ℂ)*
        ((rotationIsometry θ (baselineVector ε α w c q x)) 3/(Real.sqrt (α*w):ℂ))+
      baselineVector ε α w c q x 4/(neutralScale α:ℂ) := by
  rw [coefficient,KFCausalSymmetricInsertionCoordinate.coefficient_eq_baseline,
    neutralCoefficient_eq_baseline]
  rfl

#print axioms neutralScale_positive
#print axioms neutralCoefficient_eq_baseline
#print axioms coefficient_eq_baseline
end
end UnifiedTheory.Audit.KFCausalPointFieldInsertionCoordinate
