/- Actual first and second symmetric derivatives of the full shifted
vacuum/matter numerator, with the physical source and both clock shifts. -/
import UnifiedTheory.Audit.KFCausalSymmetricInsertionAffine
import UnifiedTheory.Audit.KFCausalSymmetricJetBounds
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSymmetricPhysicalJets
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockFloorComplexDefect (complexClock)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalWidthGaussianHolomorphicQuotient (targetVector baselineVector)
open KFCausalWidthGaussianNeutralMultiplier (neutral)
open KFCausalMatterInsertionCoordinate (coefficient)
open KFCausalSymmetricNormalizedDirection (targetDirection)
open KFCausalSymmetricInsertionAffine (neutralSlope matterSlope)
open KFCausalSymmetricNumeratorJets (slope curvature)
open KFCausalSymmetricJetBounds (firstCore secondCore)
open KFCausalComplexQuadraticPerturbation (quadratic)
open KFCausalSymmetricMixedTranslation (velocity)

def core (Q P : Polynomial ℂ) (A z a d g c : ℂ) (order : Fin 3) : ℂ :=
  ![Q.eval A*P.eval z,firstCore Q P A z a d g,secondCore Q P A z a d g c] order

def prefactor (ε h a α : ℝ) (C : ℂ) (p : ℝ) (q : ℂ) : ℂ :=
  (C*clockPhase p (complexInverse ε (shift h q)))*
    ((Real.pi/α:ℝ):ℂ)*(complexClock ε q)⁻¹*
      Complex.exp (-complexInverse ε (shift h q))*Complex.exp (-(a:ℂ)*(shift h q)^2)

def actualCore (ε h α w c θ : ℝ) (b : ℂ) (Q P : Polynomial ℂ)
    (i : Fin 2) (order : Fin 3) (q : ℂ) (x : Joint 2 4) : ℂ :=
  core Q P (coefficient ε h α w c θ q x) (neutral ε h α w c θ q x)
    (matterSlope ε h α w θ i q) (neutralSlope ε h α w θ i q)
    (slope b (neutralSlope ε h α w θ i q)
      (fun j => targetVector ε h α w c θ q x j) (fun j => targetDirection ε h α w θ i q j))
    (curvature (fun j => targetDirection ε h α w θ i q j)) order

def numerator (ε h a α w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) (q : ℂ) (x : Joint 2 4) : ℂ :=
  prefactor ε h a α C p q*
    Complex.exp (b*neutral ε h α w c θ q x-quadratic (fun j => targetVector ε h α w c θ q x j))*
      actualCore ε h α w c θ b Q P i order q x

def multiplier (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) (q : ℂ) (x : Joint 2 4) : ℂ :=
  (C*clockPhase p (complexInverse ε (shift h q)))*
    (actualCore ε h α w c θ b Q P i order q x*Complex.exp (b*neutral ε h α w c θ q x))*
      KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c θ q x

theorem multiplier_mul_baseline (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) (q : ℂ) (x : Joint 2 4)
    (hW : W ≠ 0) :
    multiplier ε h a α W w c θ C p b Q P i order q x*
      KFCausalWidthGaussianHolomorphicQuotient.baseline ε a α W w c q x=
        numerator ε h a α w c θ C p b Q P i order q x := by
  rw [multiplier,mul_assoc,KFCausalWidthGaussianHolomorphicQuotient.multiplier_mul_baseline
    ε h a α W w c θ hW q x]
  simp only [numerator,prefactor,KFCausalWidthGaussianHolomorphicQuotient.numerator,
    sub_eq_add_neg,Complex.exp_add]
  ring

theorem multiplier_zero_order (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k : ℕ) (i : Fin 2) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W w c θ C p b (Polynomial.X^k) P i 0 q x=
      KFCausalSourcedWidthMatterMultiplier.multiplier ε h a α W w c θ C p b P k q x := by
  simp only [multiplier,actualCore,core,Matrix.cons_val_zero,Polynomial.eval_pow,Polynomial.eval_X,
    KFCausalSourcedWidthMatterMultiplier.multiplier,KFCausalWidthGaussianNeutralMultiplier.multiplier]
  ring

theorem numerator_zero_derivative (ε : ℝ) (hε : 0 < ε) (h a α w c θ : ℝ)
    (C : ℂ) (p : ℝ) (b : ℂ) (Q P : Polynomial ℂ) (i : Fin 2)
    (q : ℝ) (x : Joint 2 4) (hα : 0 < α) (hw : 0 < w) :
    HasDerivAt (fun t : ℝ => numerator ε h a α w c θ C p b Q P i 0 (q:ℂ)
      (x+t • velocity ε hε i q)) (numerator ε h a α w c θ C p b Q P i 1 (q:ℂ) x) 0 := by
  have he := KFCausalSymmetricNumeratorJets.value_real_derivative
    (prefactor ε h a α C p (q:ℂ)) b Q P
    (coefficient ε h α w c θ (q:ℂ) x) (neutral ε h α w c θ (q:ℂ) x)
    (matterSlope ε h α w θ i (q:ℂ)) (neutralSlope ε h α w θ i (q:ℂ))
    (fun j => targetVector ε h α w c θ (q:ℂ) x j)
    (fun j => targetDirection ε h α w θ i (q:ℂ) j) 0
  convert he using 1
  · funext t
    simp only [numerator,actualCore,core,Matrix.cons_val_zero,
      KFCausalSymmetricNumeratorJets.value,
      KFCausalSymmetricInsertionAffine.matter_affine ε hε h α w c θ i q t x hα hw,
      KFCausalSymmetricInsertionAffine.neutral_affine ε hε h α w c θ i q t x hα hw,
      KFCausalSymmetricNormalizedDirection.targetVector_affine ε hε h α w c θ i q t x hα hw,
      PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  · simp only [numerator,actualCore,core,Matrix.cons_val_one,Matrix.cons_val_zero,
      KFCausalSymmetricNumeratorJets.first,firstCore,Complex.ofReal_zero,zero_mul,add_zero]

theorem numerator_first_derivative (ε : ℝ) (hε : 0 < ε) (h a α w c θ : ℝ)
    (C : ℂ) (p : ℝ) (b : ℂ) (Q P : Polynomial ℂ) (i : Fin 2)
    (q : ℝ) (x : Joint 2 4) (hα : 0 < α) (hw : 0 < w) :
    HasDerivAt (fun t : ℝ => numerator ε h a α w c θ C p b Q P i 1 (q:ℂ)
      (x+t • velocity ε hε i q)) (numerator ε h a α w c θ C p b Q P i 2 (q:ℂ) x) 0 := by
  have he := KFCausalSymmetricNumeratorJets.first_real_derivative
    (prefactor ε h a α C p (q:ℂ)) b Q P
    (coefficient ε h α w c θ (q:ℂ) x) (neutral ε h α w c θ (q:ℂ) x)
    (matterSlope ε h α w θ i (q:ℂ)) (neutralSlope ε h α w θ i (q:ℂ))
    (fun j => targetVector ε h α w c θ (q:ℂ) x j)
    (fun j => targetDirection ε h α w θ i (q:ℂ) j) 0
  convert he using 1
  · funext t
    simp only [numerator,actualCore,core,Matrix.cons_val_one,Matrix.cons_val_zero,
      KFCausalSymmetricNumeratorJets.first,firstCore,
      KFCausalSymmetricInsertionAffine.matter_affine ε hε h α w c θ i q t x hα hw,
      KFCausalSymmetricInsertionAffine.neutral_affine ε hε h α w c θ i q t x hα hw,
      KFCausalSymmetricNormalizedDirection.targetVector_affine ε hε h α w c θ i q t x hα hw,
      PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  · simp only [numerator,actualCore,core,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      KFCausalSymmetricNumeratorJets.second,secondCore,Complex.ofReal_zero,zero_mul,add_zero]

#print axioms multiplier_mul_baseline
#print axioms multiplier_zero_order
#print axioms numerator_zero_derivative
#print axioms numerator_first_derivative
end
end UnifiedTheory.Audit.KFCausalSymmetricPhysicalJets
