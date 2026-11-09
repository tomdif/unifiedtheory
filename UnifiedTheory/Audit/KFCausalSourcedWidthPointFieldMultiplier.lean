/- The corrected neutral coordinate and symmetric charged coordinate give
a bounded holomorphic point-field insertion multiplier with full sources. -/
import UnifiedTheory.Audit.KFCausalPointFieldInsertionCoordinate
import UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSourcedWidthPointFieldMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPointFieldInsertionCoordinate (coefficient neutralCoefficient neutralScale)
open KFCausalSymmetricInsertionCoordinate (increment coordinateScale)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector targetVector)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalSourcedWidthSymmetricMultiplier (polynomialCap radius_source_polynomial_bound)

def neutralCap (ε h α w : ℝ) : ℝ :=
  (20/17:ℝ)*(1+2*|coupling α w| *(1+Real.exp (|h|/(2*ε))))/neutralScale α

def coefficientCap (ε h α w : ℝ) : ℝ :=
  2*|KFCausalPairedModeCoordinates.scale| *
    (Real.exp (|h|/(2*ε))*(20/17)/coordinateScale α w 1)+neutralCap ε h α w

def multiplier (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  coefficient ε h α w c θ q x*
    KFCausalWidthGaussianNeutralMultiplier.multiplier ε h a α W w c θ C p b P q x

def bound (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) : ℝ :=
  coefficientCap ε h α w*‖C‖*Real.exp (|p| *Real.pi/3)*
    (4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2))*polynomialCap α b P

private theorem exponential_increment_bound (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖Complex.exp (-increment ε h q/2)‖ ≤ Real.exp (|h|/(2*ε)) := by
  have hd : ‖increment ε h q‖ ≤ |h|/ε := by
    simpa only [increment,norm_sub_rev] using
      KFCausalTwoShearClockQuotient.inverse_increment ε h hε hh q hq
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hn := Complex.re_le_norm (-increment ε h q/2)
  have hn' : ‖-increment ε h q/2‖ = ‖increment ε h q‖/2 := by norm_num
  rw [hn'] at hn
  calc
    _ ≤ ‖increment ε h q‖/2 := hn
    _ ≤ (|h|/ε)/2 := div_le_div_of_nonneg_right hd (by norm_num)
    _ = _ := by ring

theorem neutral_coefficient_bound (ε h α w c θ : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖neutralCoefficient ε h α w c θ q x‖ ≤
      neutralCap ε h α w*‖baselineVector ε α w c (q.re:ℂ) x‖ := by
  let R := ‖baselineVector ε α w c (q.re:ℂ) x‖
  have hs := KFCausalPointFieldInsertionCoordinate.neutralScale_positive α hα
  have hZ := KFCausalWidthGaussianNeutralMultiplier.target_norm_bound
    ε h α w c θ hε hh hα hw q hq x
  have h0 := (PiLp.norm_apply_le (targetVector ε h α w c θ q x) 4).trans hZ
  have h3 := PiLp.norm_apply_le (rotationIsometry θ (targetVector ε h α w c θ q x)) 3
  rw [(rotationIsometry θ).norm_map] at h3
  have h3' := h3.trans hZ
  have he : ‖1-Complex.exp (-increment ε h q/2)‖ ≤ 1+Real.exp (|h|/(2*ε)) := by
    exact (norm_sub_le _ _).trans (by
      simpa only [norm_one] using add_le_add_right
        (exponential_increment_bound ε h hε hh q hq) 1)
  have hc : ‖2*(coupling α w:ℂ)*(1-Complex.exp (-increment ε h q/2))‖ ≤
      2*|coupling α w| *(1+Real.exp (|h|/(2*ε))) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    norm_num only [Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  have ht : ‖targetVector ε h α w c θ q x 4-
      2*(coupling α w:ℂ)*(1-Complex.exp (-increment ε h q/2))*
        (rotationIsometry θ (targetVector ε h α w c θ q x)) 3‖ ≤
      (20/17:ℝ)*R+(2*|coupling α w| *(1+Real.exp (|h|/(2*ε))))*((20/17:ℝ)*R) := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    exact add_le_add h0 (mul_le_mul hc h3' (norm_nonneg _) (by positivity))
  rw [neutralCoefficient,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  calc
    _ ≤ ((20/17:ℝ)*R+(2*|coupling α w| *(1+Real.exp (|h|/(2*ε))))*((20/17:ℝ)*R))/
      neutralScale α := div_le_div_of_nonneg_right ht hs.le
    _ = _ := by unfold neutralCap; dsimp [R]; ring

theorem coefficient_bound (ε h α w c θ : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖coefficient ε h α w c θ q x‖ ≤
      coefficientCap ε h α w*‖baselineVector ε α w c (q.re:ℂ) x‖ := by
  have hi := KFCausalSourcedWidthSymmetricMultiplier.coefficient_bound
    ε h α w c θ 1 hε hh hα hw q hq x
  have hn := neutral_coefficient_bound ε h α w c θ hε hh hα hw q hq x
  unfold coefficient
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (2*|KFCausalPairedModeCoordinates.scale|)*
        ((Real.exp (|h|/(2*ε))*(20/17)/coordinateScale α w 1)*
          ‖baselineVector ε α w c (q.re:ℂ) x‖)+
        neutralCap ε h α w*‖baselineVector ε α w c (q.re:ℂ) x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hi (by positivity)) hn
    _ = _ := by unfold coefficientCap; ring

theorem bound_nonnegative (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (hε : 0 < ε) (hα : 0 < α) (hw : 1 ≤ w)
    (hW : w ≤ W) : 0 ≤ bound ε h a α W w C p b P := by
  have hs := KFCausalSymmetricInsertionCoordinate.coordinateScale_positive α w hα
    (zero_lt_one.trans_le hw) 1
  have hn := KFCausalPointFieldInsertionCoordinate.neutralScale_positive α hα
  have hcap := KFCausalTransversePolynomialEnvelope.evalCap_nonnegative P
    (KFCausalWidthGaussianNeutralMultiplier.neutralScale α)
    (by unfold KFCausalWidthGaussianNeutralMultiplier.neutralScale; positivity)
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  unfold bound coefficientCap neutralCap polynomialCap
  positivity

theorem multiplier_mul_baseline (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (hW : W ≠ 0) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W w c θ C p b P q x*
      KFCausalWidthGaussianHolomorphicQuotient.baseline ε a α W w c q x =
      coefficient ε h α w c θ q x*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a α w c θ C p b P q x := by
  rw [multiplier,mul_assoc,KFCausalWidthGaussianNeutralMultiplier.multiplier_mul_baseline
    ε h a α W w c θ hW C p b P q x]

theorem multiplier_bound (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W w c θ C p b P q x‖ ≤ bound ε h a α W w C p b P := by
  let R := ‖baselineVector ε α w c (q.re:ℂ) x‖
  let A := coefficientCap ε h α w
  let H := ‖C‖*Real.exp (|p| *Real.pi/3)
  let M := 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2)
  have hs := KFCausalSymmetricInsertionCoordinate.coordinateScale_positive α w hα
    (zero_lt_one.trans_le hw) 1
  have hn := KFCausalPointFieldInsertionCoordinate.neutralScale_positive α hα
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  have hA : 0 ≤ A := by dsimp [A,coefficientCap,neutralCap]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 ≤ R := norm_nonneg _
  have hp := radius_source_polynomial_bound P b
    (KFCausalWidthGaussianNeutralMultiplier.neutral ε h α w c θ q x)
    (KFCausalWidthGaussianNeutralMultiplier.neutralScale α) R (78/289)
    (by unfold KFCausalWidthGaussianNeutralMultiplier.neutralScale; positivity) hR (by norm_num)
    (KFCausalWidthGaussianNeutralMultiplier.neutral_norm_bound ε h α w c θ hε hh hα hw q hq x)
  change _ ≤ polynomialCap α b P at hp
  have hg := KFCausalWidthGaussianHolomorphicQuotient.multiplier_gaussian_bound
    ε h a α W w c θ hε hh ha hα hw hW q hq x
  have he : Real.exp (-(a/2)*q.re^2+4*a*h^2) ≤ Real.exp (4*a*h^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha (sq_nonneg q.re)]
  have hg' : ‖KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c θ q x‖ ≤
      M*Real.exp (-(78/289:ℝ)*R^2) := by
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ (4*W)*(ε⁻¹*Real.exp (|h|/ε)*Real.exp (4*a*h^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
      _ = _ := by dsimp [M]; rw [Real.exp_add]; ring
  have hc : ‖C*clockPhase p (complexInverse ε (shift h q))‖ ≤ H := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (KFCausalWidthGaussianNeutralMultiplier.phase_bound ε h p hε hh q hq) (norm_nonneg _)
  have hi := coefficient_bound ε h α w c θ hε hh hα hw q hq x
  rw [norm_mul] at hc
  unfold multiplier KFCausalWidthGaussianNeutralMultiplier.multiplier
  simp only [norm_mul]
  calc
    _ ≤ (A*R)*(H*(‖P.eval (KFCausalWidthGaussianNeutralMultiplier.neutral ε h α w c θ q x)‖*
        ‖Complex.exp (b*KFCausalWidthGaussianNeutralMultiplier.neutral ε h α w c θ q x)‖)*
          (M*Real.exp (-(78/289:ℝ)*R^2))) := by
      exact mul_le_mul hi (mul_le_mul
        (mul_le_mul_of_nonneg_right hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hg'
        (norm_nonneg _) (mul_nonneg hH (mul_nonneg (norm_nonneg _) (norm_nonneg _))))
        (by positivity) (mul_nonneg hA hR)
    _ = (A*H*M)*(R*‖P.eval (KFCausalWidthGaussianNeutralMultiplier.neutral ε h α w c θ q x)*
        Complex.exp (b*KFCausalWidthGaussianNeutralMultiplier.neutral ε h α w c θ q x)‖*
          Real.exp (-(78/289:ℝ)*R^2)) := by
      rw [norm_mul]
      ring
    _ ≤ (A*H*M)*polynomialCap α b P := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by dsimp [A,H,M,bound]; ring

#print axioms neutral_coefficient_bound
#print axioms coefficient_bound
#print axioms bound_nonnegative
#print axioms multiplier_mul_baseline
#print axioms multiplier_bound
end
end UnifiedTheory.Audit.KFCausalSourcedWidthPointFieldMultiplier
