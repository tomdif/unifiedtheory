/- Powers of the actual half-shifted matter insertion share the Gaussian
margin with every neutral source and polynomial. No unshifted field is substituted. -/
import UnifiedTheory.Audit.KFCausalMatterInsertionCoordinate
import UnifiedTheory.Audit.KFCausalSourcedWidthPointFieldMultiplier
import UnifiedTheory.Audit.KFCausalScalarPowerSourceAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSourcedWidthMatterMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalMatterInsertionCoordinate (coefficient halfScale)
open KFCausalSymmetricInsertionCoordinate (coordinateScale)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector)
open KFCausalWidthGaussianNeutralMultiplier (neutral neutralScale)
open KFCausalSourcedWidthPointFieldMultiplier (neutralCap)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)

def coefficientCap (ε h α w : ℝ) : ℝ :=
  neutralCap ε h α w+2*|KFCausalPairedModeCoordinates.scale| *
    (3*Real.exp (|h|/(4*ε))+2)*
      (Real.exp (|h|/(2*ε))*(20/17)/coordinateScale α w 1)

def polynomialCap (α : ℝ) (b : ℂ) (P : Polynomial ℂ) (k : ℕ) : ℝ :=
  KFCausalTransversePolynomialEnvelope.evalCap P (neutralScale α)*
    Real.exp (((P.natDegree:ℝ)+(k:ℝ)+‖b‖*neutralScale α)^2/(4*(78/289:ℝ)))

def multiplier (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k : ℕ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  (coefficient ε h α w c θ q x)^k*
    KFCausalWidthGaussianNeutralMultiplier.multiplier ε h a α W w c θ C p b P q x

def bound (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (k : ℕ) : ℝ :=
  ‖C‖*Real.exp (|p| *Real.pi/3)*(4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2))*
    (coefficientCap ε h α w)^k*polynomialCap α b P k

theorem half_shift_membership (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) :
    shift (h/2) q ∈ KFCausalComplexClockChart.targetStrip ε := by
  change |(shift (h/2) q).im| ≤ Real.pi*ε/2
  rw [KFCausalTwoShearClockQuotient.shift_im]
  have hi := abs_sub q.im (h/2)
  rw [abs_div,show |(2:ℝ)|=2 by norm_num] at hi
  have hp := mul_lt_mul_of_pos_right Real.pi_gt_three hε
  linarith

theorem halfScale_bound (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖halfScale ε h q‖ ≤ Real.exp (|h|/(4*ε)) := by
  have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq
  have hd := KFCausalComplexClockInverse.complexInverse_norm_bound ε hε q
    (shift (h/2) q) hm.1 (half_shift_membership ε h hε hh q hq)
  rw [KFCausalTwoShearClockQuotient.shift_distance,abs_div,
    show |(2:ℝ)|=2 by norm_num,norm_sub_rev] at hd
  rw [halfScale,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hn := Complex.re_le_norm ((complexInverse ε (shift (h/2) q)-complexInverse ε q)/2)
  have hn' : ‖(complexInverse ε (shift (h/2) q)-complexInverse ε q)/2‖ =
      ‖complexInverse ε (shift (h/2) q)-complexInverse ε q‖/2 := by norm_num
  rw [hn'] at hn
  calc
    _ ≤ ‖complexInverse ε (shift (h/2) q)-complexInverse ε q‖/2 := hn
    _ ≤ ((|h|/2)/ε)/2 := div_le_div_of_nonneg_right hd (by norm_num)
    _ = _ := by ring

theorem coefficient_bound (ε h α w c θ : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖coefficient ε h α w c θ q x‖ ≤
      coefficientCap ε h α w*‖baselineVector ε α w c (q.re:ℂ) x‖ := by
  have hn := KFCausalSourcedWidthPointFieldMultiplier.neutral_coefficient_bound
    ε h α w c θ hε hh hα hw q hq x
  have hi := KFCausalSourcedWidthSymmetricMultiplier.coefficient_bound
    ε h α w c θ 1 hε hh hα hw q hq x
  have he : ‖3*halfScale ε h q-2‖ ≤ 3*Real.exp (|h|/(4*ε))+2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    norm_num only [Complex.norm_ofNat]
    exact add_le_add_left (mul_le_mul_of_nonneg_left
      (halfScale_bound ε h hε hh q hq) (by norm_num : (0:ℝ) ≤ 3)) 2
  have hc : ‖2*(KFCausalPairedModeCoordinates.scale:ℂ)*(3*halfScale ε h q-2)‖ ≤
      2*|KFCausalPairedModeCoordinates.scale| *(3*Real.exp (|h|/(4*ε))+2) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    norm_num only [Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  unfold coefficient
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  calc
    _ ≤ neutralCap ε h α w*‖baselineVector ε α w c (q.re:ℂ) x‖+
      (2*|KFCausalPairedModeCoordinates.scale| *(3*Real.exp (|h|/(4*ε))+2))*
        ((Real.exp (|h|/(2*ε))*(20/17)/coordinateScale α w 1)*
          ‖baselineVector ε α w c (q.re:ℂ) x‖) :=
      add_le_add hn (mul_le_mul hc hi (norm_nonneg _) (by positivity))
    _ = _ := by unfold coefficientCap; ring

theorem bound_nonnegative (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k : ℕ) (hε : 0 < ε) (hα : 0 < α) (hw : 1 ≤ w)
    (hW : w ≤ W) : 0 ≤ bound ε h a α W w C p b P k := by
  have hs := KFCausalSymmetricInsertionCoordinate.coordinateScale_positive α w hα
    (zero_lt_one.trans_le hw) 1
  have hn := KFCausalPointFieldInsertionCoordinate.neutralScale_positive α hα
  have hcap := KFCausalTransversePolynomialEnvelope.evalCap_nonnegative P (neutralScale α)
    (by unfold neutralScale; positivity)
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  unfold bound coefficientCap neutralCap polynomialCap
  positivity

theorem multiplier_mul_baseline (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k : ℕ) (hW : W ≠ 0) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W w c θ C p b P k q x*
      KFCausalWidthGaussianHolomorphicQuotient.baseline ε a α W w c q x =
      (coefficient ε h α w c θ q x)^k*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a α w c θ C p b P q x := by
  rw [multiplier,mul_assoc,KFCausalWidthGaussianNeutralMultiplier.multiplier_mul_baseline
    ε h a α W w c θ hW C p b P q x]

theorem multiplier_bound (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k : ℕ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W w c θ C p b P k q x‖ ≤ bound ε h a α W w C p b P k := by
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
  have hp := KFCausalScalarPowerSourceAbsorption.linear_power_source_bound k P b
    (neutral ε h α w c θ q x) (coefficient ε h α w c θ q x) A (neutralScale α) R (78/289)
    hA (by unfold neutralScale; positivity) (norm_nonneg _) (by norm_num)
    (coefficient_bound ε h α w c θ hε hh hα hw q hq x)
    (KFCausalWidthGaussianNeutralMultiplier.neutral_norm_bound ε h α w c θ hε hh hα hw q hq x)
  change _ ≤ A^k*polynomialCap α b P k at hp
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
  have heq : multiplier ε h a α W w c θ C p b P k q x =
      (C*clockPhase p (complexInverse ε (shift h q)))*
        ((coefficient ε h α w c θ q x)^k*
          (P.eval (neutral ε h α w c θ q x)*Complex.exp (b*neutral ε h α w c θ q x)))*
        KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c θ q x := by
    unfold multiplier KFCausalWidthGaussianNeutralMultiplier.multiplier
    ring
  rw [heq,norm_mul,norm_mul]
  calc
    _ ≤ H*‖(coefficient ε h α w c θ q x)^k*
          (P.eval (neutral ε h α w c θ q x)*Complex.exp (b*neutral ε h α w c θ q x))‖*
        (M*Real.exp (-(78/289:ℝ)*R^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hg'
        (norm_nonneg _) (mul_nonneg hH (norm_nonneg _))
    _ = (H*M)*(‖(coefficient ε h α w c θ q x)^k*
          (P.eval (neutral ε h α w c θ q x)*Complex.exp (b*neutral ε h α w c θ q x))‖*
        Real.exp (-(78/289:ℝ)*R^2)) := by ring
    _ ≤ (H*M)*(A^k*polynomialCap α b P k) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hH hM)
    _ = _ := by dsimp [A,H,M,bound]; ring

#print axioms half_shift_membership
#print axioms halfScale_bound
#print axioms coefficient_bound
#print axioms bound_nonnegative
#print axioms multiplier_mul_baseline
#print axioms multiplier_bound
end
end UnifiedTheory.Audit.KFCausalSourcedWidthMatterMultiplier
