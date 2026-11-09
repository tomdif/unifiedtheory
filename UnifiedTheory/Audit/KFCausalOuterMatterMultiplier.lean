/- The outer physical point field is evaluated at the opposite half
clock shift. Both insertion powers share the original Gaussian margin. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterRegularity
import UnifiedTheory.Audit.KFCausalSourcedWidthPointFieldRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalOuterMatterMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector)
open KFCausalPhysicalReciprocalNormalization (normalize coupling)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalWidthGaussianNeutralMultiplier (neutral neutralScale)
open KFCausalClockFloorCoherentStrip (clockPhase)

def outerCoefficient (ε h α w c : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  KFCausalPointFieldInsertionCoordinate.coefficient ε h α w c 0 (shift (-h/2) q) x

def outerCap (α w : ℝ) : ℝ :=
  (20/17:ℝ)*(2*|KFCausalPairedModeCoordinates.scale| /Real.sqrt (α*w)+1/Real.sqrt (α/32))

def multiplier (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  (outerCoefficient ε h α w c q x)^m*
    KFCausalSourcedWidthMatterMultiplier.multiplier ε h a α W w c θ C p b P k q x

def bound (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) : ℝ :=
  ‖C‖*Real.exp (|p| *Real.pi/3)*(4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2))*
    (outerCap α w)^m*(KFCausalSourcedWidthMatterMultiplier.coefficientCap ε h α w)^k*
      KFCausalSourcedWidthMatterMultiplier.polynomialCap α b P (k+m)

theorem outer_shift_membership (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) :
    shift (-h/2) q ∈ KFCausalComplexClockChart.targetStrip ε := by
  change |(shift (-h/2) q).im| ≤ Real.pi*ε/2
  rw [KFCausalTwoShearClockQuotient.shift_im]
  have hi := abs_sub q.im (-h/2)
  rw [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num] at hi
  have hp := mul_lt_mul_of_pos_right Real.pi_gt_three hε
  linarith

theorem shifted_baseline_norm_bound (ε h α w c : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖baselineVector ε α w c (shift (-h/2) q) x‖ ≤
      (20/17:ℝ)*‖baselineVector ε α w c (q.re:ℂ) x‖ := by
  have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq
  have hd := KFCausalComplexClockInverse.complexInverse_norm_bound ε hε
    (shift (-h/2) q) (q.re:ℂ) (outer_shift_membership ε h hε hh q hq) hm.2.2
  have he : shift (-h/2) q-(q.re:ℂ)=((q.im+h/2:ℝ):ℂ)*Complex.I := by
    apply Complex.ext <;> simp [shift]
    all_goals ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hd
  have hi : |q.im+h/2| ≤ 3*|h|/2 := by
    have hb := abs_add_le q.im (h/2)
    rw [abs_div,show |(2:ℝ)|=2 by norm_num] at hb
    linarith
  have hz : ‖complexInverse ε (shift (-h/2) q)-complexInverse ε (q.re:ℂ)‖ ≤ 1/5 := by
    apply hd.trans
    apply (div_le_iff₀ hε).mpr
    linarith
  let U : Space ≃ₗᵢ[ℂ] Space := LinearIsometryEquiv.refl ℂ Space
  have hb := KFCausalComplexShearPerturbation.baseline_norm U (coupling α w)
    (KFCausalPhysicalReciprocalNormalization.coupling_bound α w hα hw)
    (complexInverse ε (shift (-h/2) q)-complexInverse ε (q.re:ℂ)) hz
    (baselineVector ε α w c (q.re:ℂ) x)
  change ‖flow (coupling α w) (complexInverse ε (shift (-h/2) q)-complexInverse ε (q.re:ℂ))
    (flow (coupling α w) (complexInverse ε (q.re:ℂ)) (normalize α w c x))‖ ≤ _ at hb
  rw [KFCausalComplexShearGroup.flow_compose,sub_add_cancel] at hb
  exact hb

theorem outer_coefficient_bound (ε h α w c : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖outerCoefficient ε h α w c q x‖ ≤ outerCap α w*‖baselineVector ε α w c (q.re:ℂ) x‖ := by
  have hw0 := zero_lt_one.trans_le hw
  have h3 := (PiLp.norm_apply_le (baselineVector ε α w c (shift (-h/2) q) x) 3).trans
    (shifted_baseline_norm_bound ε h α w c hε hh hα hw q hq x)
  have h4 := (PiLp.norm_apply_le (baselineVector ε α w c (shift (-h/2) q) x) 4).trans
    (shifted_baseline_norm_bound ε h α w c hε hh hα hw q hq x)
  have hs : 0 < Real.sqrt (α*w) := Real.sqrt_pos.2 (mul_pos hα hw0)
  have hn : 0 < Real.sqrt (α/32) := Real.sqrt_pos.2 (by positivity)
  rw [outerCoefficient,KFCausalPointFieldInsertionCoordinate.coefficient_eq_baseline,
    KFCausalNormalizedComplexRotation.rotationIsometry_apply,KFCausalNormalizedComplexRotation.rotate_zero]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    KFCausalPointFieldInsertionCoordinate.neutralScale,abs_of_pos hs,abs_of_pos hn]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (2*|KFCausalPairedModeCoordinates.scale|)*
        (((20/17:ℝ)*‖baselineVector ε α w c (q.re:ℂ) x‖)/Real.sqrt (α*w))+
        ((20/17:ℝ)*‖baselineVector ε α w c (q.re:ℂ) x‖)/Real.sqrt (α/32) :=
      add_le_add (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h3 hs.le) (by positivity))
        (div_le_div_of_nonneg_right h4 hn.le)
    _ = _ := by unfold outerCap; ring

private theorem caps_nonnegative (ε h α w : ℝ) (hα : 0 < α) (hw : 1 ≤ w) :
    0 ≤ outerCap α w ∧ 0 ≤ KFCausalSourcedWidthMatterMultiplier.coefficientCap ε h α w := by
  have hs := KFCausalSymmetricInsertionCoordinate.coordinateScale_positive α w hα
    (zero_lt_one.trans_le hw) 1
  have hn := KFCausalPointFieldInsertionCoordinate.neutralScale_positive α hα
  constructor
  · unfold outerCap
    positivity
  · unfold KFCausalSourcedWidthMatterMultiplier.coefficientCap
      KFCausalSourcedWidthPointFieldMultiplier.neutralCap
    positivity

theorem bound_nonnegative (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) (hε : 0 < ε) (hα : 0 < α) (hw : 1 ≤ w)
    (hW : w ≤ W) : 0 ≤ bound ε h a α W w C p b P k m := by
  obtain ⟨hAo,hAi⟩ := caps_nonnegative ε h α w hα hw
  have hcap := KFCausalTransversePolynomialEnvelope.evalCap_nonnegative P (neutralScale α)
    (by unfold neutralScale; positivity)
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  unfold bound KFCausalSourcedWidthMatterMultiplier.polynomialCap
  positivity

theorem multiplier_mul_baseline (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) (hW : W ≠ 0) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W w c θ C p b P k m q x*
      KFCausalWidthGaussianHolomorphicQuotient.baseline ε a α W w c q x =
      (outerCoefficient ε h α w c q x)^m*
        ((KFCausalMatterInsertionCoordinate.coefficient ε h α w c θ q x)^k*
          KFCausalWidthGaussianNeutralMultiplier.numerator ε h a α w c θ C p b P q x) := by
  rw [multiplier,mul_assoc,KFCausalSourcedWidthMatterMultiplier.multiplier_mul_baseline
    ε h a α W w c θ C p b P k hW q x]

theorem multiplier_bound (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W w c θ C p b P k m q x‖ ≤ bound ε h a α W w C p b P k m := by
  let R := ‖baselineVector ε α w c (q.re:ℂ) x‖
  let Ao := outerCap α w
  let Ai := KFCausalSourcedWidthMatterMultiplier.coefficientCap ε h α w
  let H := ‖C‖*Real.exp (|p| *Real.pi/3)
  let M := 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2)
  let O := outerCoefficient ε h α w c q x
  let I := KFCausalMatterInsertionCoordinate.coefficient ε h α w c θ q x
  let N := P.eval (neutral ε h α w c θ q x)*Complex.exp (b*neutral ε h α w c θ q x)
  obtain ⟨hAo,hAi⟩ := caps_nonnegative ε h α w hα hw
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ho := pow_le_pow_left₀ (norm_nonneg O)
    (outer_coefficient_bound ε h α w c hε hh hα hw q hq x) m
  have hi := pow_le_pow_left₀ (norm_nonneg I)
    (KFCausalSourcedWidthMatterMultiplier.coefficient_bound ε h α w c θ hε hh hα hw q hq x) k
  rw [mul_pow] at ho hi
  have hr := KFCausalScalarPowerSourceAbsorption.radius_power_source_bound (k+m) P b
    (neutral ε h α w c θ q x) (neutralScale α) R (78/289)
    (by unfold neutralScale; positivity) (norm_nonneg _) (by norm_num)
    (KFCausalWidthGaussianNeutralMultiplier.neutral_norm_bound ε h α w c θ hε hh hα hw q hq x)
  change R^(k+m)*‖N‖*Real.exp (-(78/289:ℝ)*R^2) ≤
    KFCausalSourcedWidthMatterMultiplier.polynomialCap α b P (k+m) at hr
  have hp : ‖O^m*(I^k*N)‖*Real.exp (-(78/289:ℝ)*R^2) ≤
      (Ao^m*Ai^k)*KFCausalSourcedWidthMatterMultiplier.polynomialCap α b P (k+m) := by
    simp only [norm_mul,norm_pow]
    calc
      _ ≤ (Ao^m*R^m)*((Ai^k*R^k)*‖N‖)*Real.exp (-(78/289:ℝ)*R^2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul ho (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
          (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) (by positivity)
      _ = (Ao^m*Ai^k)*(R^(k+m)*‖N‖*Real.exp (-(78/289:ℝ)*R^2)) := by
        rw [pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
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
  have heq : multiplier ε h a α W w c θ C p b P k m q x =
      (C*clockPhase p (complexInverse ε (shift h q)))*(O^m*(I^k*N))*
        KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c θ q x := by
    unfold multiplier KFCausalSourcedWidthMatterMultiplier.multiplier
      KFCausalWidthGaussianNeutralMultiplier.multiplier
    dsimp [O,I,N]
    ring
  rw [heq,norm_mul,norm_mul]
  calc
    _ ≤ H*‖O^m*(I^k*N)‖*(M*Real.exp (-(78/289:ℝ)*R^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hg'
        (norm_nonneg _) (mul_nonneg hH (norm_nonneg _))
    _ = (H*M)*(‖O^m*(I^k*N)‖*Real.exp (-(78/289:ℝ)*R^2)) := by ring
    _ ≤ (H*M)*((Ao^m*Ai^k)*KFCausalSourcedWidthMatterMultiplier.polynomialCap α b P (k+m)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hH hM)
    _ = _ := by dsimp [Ao,Ai,H,M,bound]; ring

#print axioms outer_shift_membership
#print axioms shifted_baseline_norm_bound
#print axioms outer_coefficient_bound
#print axioms bound_nonnegative
#print axioms multiplier_mul_baseline
#print axioms multiplier_bound
end
end UnifiedTheory.Audit.KFCausalOuterMatterMultiplier
