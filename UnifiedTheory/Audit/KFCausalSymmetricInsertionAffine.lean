/- Exact affine neutral and half-shifted matter coordinates along the
actual symmetric momentum directions. -/
import UnifiedTheory.Audit.KFCausalSymmetricNormalizedDirection
import UnifiedTheory.Audit.KFCausalMatterInsertionCoordinate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricInsertionAffine
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalSymmetricMixedTranslation (velocity)
open KFCausalSymmetricNormalizedDirection (direction targetDirection baselineVector_affine targetVector_affine)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector targetVector)
open KFCausalWidthGaussianNeutralMultiplier (neutral)
open KFCausalMatterInsertionCoordinate (coefficient halfScale)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalPairedModeCoordinates (scale)

def neutralSlope (ε h α w θ : ℝ) (i : Fin 2) (q : ℂ) : ℂ :=
  targetDirection ε h α w θ i q 4/(Real.sqrt (α/32):ℂ)

def matterSlope (ε h α w θ : ℝ) (i : Fin 2) (q : ℂ) : ℂ :=
  direction α w i 4/(Real.sqrt (α/32):ℂ)+
    2*(scale:ℂ)*(3*halfScale ε h q-2)*
      ((rotationIsometry θ (direction α w i)) 3/(Real.sqrt (α*w):ℂ))

theorem matter_eq_baseline (ε h α w c θ : ℝ) (q : ℂ) (x : Joint 2 4) :
    coefficient ε h α w c θ q x=
      baselineVector ε α w c q x 4/(Real.sqrt (α/32):ℂ)+
        2*(scale:ℂ)*(3*halfScale ε h q-2)*
          ((rotationIsometry θ (baselineVector ε α w c q x)) 3/(Real.sqrt (α*w):ℂ)) := by
  rw [coefficient,KFCausalPointFieldInsertionCoordinate.neutralCoefficient_eq_baseline,
    KFCausalSymmetricInsertionCoordinate.coefficient_eq_baseline]
  rfl

theorem neutral_affine (ε : ℝ) (hε : 0 < ε) (h α w c θ : ℝ) (i : Fin 2)
    (q t : ℝ) (x : Joint 2 4) (hα : 0 < α) (hw : 0 < w) :
    neutral ε h α w c θ (q:ℂ) (x+t • velocity ε hε i q)=
      neutral ε h α w c θ (q:ℂ) x+(t:ℂ)*neutralSlope ε h α w θ i (q:ℂ) := by
  unfold neutral
  rw [targetVector_affine ε hε h α w c θ i q t x hα hw]
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,neutralSlope]
  ring

theorem matter_affine (ε : ℝ) (hε : 0 < ε) (h α w c θ : ℝ) (i : Fin 2)
    (q t : ℝ) (x : Joint 2 4) (hα : 0 < α) (hw : 0 < w) :
    coefficient ε h α w c θ (q:ℂ) (x+t • velocity ε hε i q)=
      coefficient ε h α w c θ (q:ℂ) x+(t:ℂ)*matterSlope ε h α w θ i (q:ℂ) := by
  rw [matter_eq_baseline,matter_eq_baseline,baselineVector_affine ε hε α w c i q t x hα hw]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,matterSlope]
  ring

#print axioms matter_eq_baseline
#print axioms neutral_affine
#print axioms matter_affine
end
end UnifiedTheory.Audit.KFCausalSymmetricInsertionAffine
