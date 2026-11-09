/- Actual antisymmetric momentum powers share the Gaussian margin with
the half-shifted matter factor and all neutral sources and polynomials.
The inserted momentum is evaluated on the real clock line. -/
import UnifiedTheory.Audit.KFCausalAntisymmetricInsertionCoordinate
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalAntisymmetricInsertionMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalSymmetricInsertionCoordinate (coordinateScale coordinateScale_positive)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector)
open KFCausalWidthGaussianNeutralMultiplier (neutral neutralScale)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalAntisymmetricInsertionCoordinate (coefficient lowerIndex)

def coefficientCap (α w : ℝ) (i : Fin 2) : ℝ :=
  2*|KFCausalPairedModeCoordinates.scale|/coordinateScale α w i

def multiplier (ε h a α W w θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k n : ℕ) (i : Fin 2) (q : ℂ) (x : Joint 2 4) : ℂ :=
  (coefficient ε h i (q.re:ℂ) x)^n*
    KFCausalSourcedWidthMatterMultiplier.multiplier ε h a α W w (momentumScale h) θ C p b P k q x

def bound (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k n : ℕ) (i : Fin 2) : ℝ :=
  ‖C‖*Real.exp (|p| *Real.pi/3)*(4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2))*
    (coefficientCap α w i)^n*(KFCausalSourcedWidthMatterMultiplier.coefficientCap ε h α w)^k*
      KFCausalSourcedWidthMatterMultiplier.polynomialCap α b P (k+n)

theorem coefficient_bound (ε h α w : ℝ) (hα : 0 < α)
    (hw : 0 < w) (i : Fin 2) (r : ℝ) (x : Joint 2 4) :
    ‖coefficient ε h i (r:ℂ) x‖ ≤
      coefficientCap α w i*‖baselineVector ε α w (momentumScale h) (r:ℂ) x‖ := by
  rw [KFCausalAntisymmetricInsertionCoordinate.coefficient_eq_baseline ε h α w i (r:ℂ) x hα hw]
  simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (coordinateScale_positive α w hα hw i)]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (2*|KFCausalPairedModeCoordinates.scale| *
        ‖baselineVector ε α w (momentumScale h) (r:ℂ) x‖)/coordinateScale α w i :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ (lowerIndex i)) (by positivity))
        (coordinateScale_positive α w hα hw i).le
    _ = _ := by unfold coefficientCap; ring

private theorem caps_nonnegative (ε h α w : ℝ) (hα : 0 < α) (hw : 1 ≤ w)
    (i : Fin 2) :
    0 ≤ coefficientCap α w i ∧ 0 ≤ KFCausalSourcedWidthMatterMultiplier.coefficientCap ε h α w := by
  have hs := coordinateScale_positive α w hα (zero_lt_one.trans_le hw) 1
  have hi := coordinateScale_positive α w hα (zero_lt_one.trans_le hw) i
  have hn := KFCausalPointFieldInsertionCoordinate.neutralScale_positive α hα
  constructor
  · unfold coefficientCap
    positivity
  · unfold KFCausalSourcedWidthMatterMultiplier.coefficientCap
      KFCausalSourcedWidthPointFieldMultiplier.neutralCap
    positivity

theorem bound_nonnegative (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k n : ℕ) (i : Fin 2) (hε : 0 < ε) (hα : 0 < α)
    (hw : 1 ≤ w) (hW : w ≤ W) : 0 ≤ bound ε h a α W w C p b P k n i := by
  obtain ⟨hAo,hAi⟩ := caps_nonnegative ε h α w hα hw i
  have hcap := KFCausalTransversePolynomialEnvelope.evalCap_nonnegative P (neutralScale α)
    (by unfold neutralScale; positivity)
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  unfold bound KFCausalSourcedWidthMatterMultiplier.polynomialCap
  positivity

theorem multiplier_bound (ε h a α W w θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k n : ℕ) (i : Fin 2) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W w θ C p b P k n i q x‖ ≤ bound ε h a α W w C p b P k n i := by
  let c := momentumScale h
  let R := ‖baselineVector ε α w c (q.re:ℂ) x‖
  let Ao := coefficientCap α w i
  let Ai := KFCausalSourcedWidthMatterMultiplier.coefficientCap ε h α w
  let H := ‖C‖*Real.exp (|p| *Real.pi/3)
  let M := 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2)
  let O := coefficient ε h i (q.re:ℂ) x
  let I := KFCausalMatterInsertionCoordinate.coefficient ε h α w c θ q x
  let N := P.eval (neutral ε h α w c θ q x)*Complex.exp (b*neutral ε h α w c θ q x)
  obtain ⟨hAo,hAi⟩ := caps_nonnegative ε h α w hα hw i
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ho := pow_le_pow_left₀ (norm_nonneg O)
    (coefficient_bound ε h α w hα (zero_lt_one.trans_le hw) i q.re x) n
  have hi := pow_le_pow_left₀ (norm_nonneg I)
    (KFCausalSourcedWidthMatterMultiplier.coefficient_bound ε h α w c θ hε hh hα hw q hq x) k
  rw [mul_pow] at ho hi
  have hr := KFCausalScalarPowerSourceAbsorption.radius_power_source_bound (k+n) P b
    (neutral ε h α w c θ q x) (neutralScale α) R (78/289)
    (by unfold neutralScale; positivity) (norm_nonneg _) (by norm_num)
    (KFCausalWidthGaussianNeutralMultiplier.neutral_norm_bound ε h α w c θ hε hh hα hw q hq x)
  change R^(k+n)*‖N‖*Real.exp (-(78/289:ℝ)*R^2) ≤
    KFCausalSourcedWidthMatterMultiplier.polynomialCap α b P (k+n) at hr
  have hp : ‖O^n*(I^k*N)‖*Real.exp (-(78/289:ℝ)*R^2) ≤
      (Ao^n*Ai^k)*KFCausalSourcedWidthMatterMultiplier.polynomialCap α b P (k+n) := by
    simp only [norm_mul,norm_pow]
    calc
      _ ≤ (Ao^n*R^n)*((Ai^k*R^k)*‖N‖)*Real.exp (-(78/289:ℝ)*R^2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul ho (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
          (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) (by positivity)
      _ = (Ao^n*Ai^k)*(R^(k+n)*‖N‖*Real.exp (-(78/289:ℝ)*R^2)) := by rw [pow_add]; ring
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
  have heq : multiplier ε h a α W w θ C p b P k n i q x =
      (C*clockPhase p (complexInverse ε (shift h q)))*(O^n*(I^k*N))*
        KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c θ q x := by
    unfold multiplier KFCausalSourcedWidthMatterMultiplier.multiplier
      KFCausalWidthGaussianNeutralMultiplier.multiplier
    dsimp [O,I,N,c]
    ring
  rw [heq,norm_mul,norm_mul]
  calc
    _ ≤ H*‖O^n*(I^k*N)‖*(M*Real.exp (-(78/289:ℝ)*R^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hg'
        (norm_nonneg _) (mul_nonneg hH (norm_nonneg _))
    _ = (H*M)*(‖O^n*(I^k*N)‖*Real.exp (-(78/289:ℝ)*R^2)) := by ring
    _ ≤ (H*M)*((Ao^n*Ai^k)*KFCausalSourcedWidthMatterMultiplier.polynomialCap α b P (k+n)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hH hM)
    _ = _ := by dsimp [Ao,Ai,H,M,bound]; ring

theorem multiplier_angle_continuous (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k n : ℕ) (i : Fin 2) (q : ℂ) (x : Joint 2 4) :
    Continuous (fun θ => multiplier ε h a α W w θ C p b P k n i q x) :=
  continuous_const.mul (KFCausalSourcedWidthMatterMultiplier.multiplier_angle_continuous
    ε h a α W w (momentumScale h) C p b P k q x)

theorem multiplier_horizontal_continuous (ε h a α W w θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k n : ℕ) (i : Fin 2) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun v : ℝ × Joint 2 4 =>
      multiplier ε h a α W w θ C p b P k n i ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2) := by
  have ho : Continuous (fun v : ℝ × Joint 2 4 => coefficient ε h i (v.1:ℂ) v.2) := by
    exact KFCausalAntisymmetricInsertionCoordinate.coefficient_real_continuous ε hε h i
  simpa only [multiplier,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
    Complex.ofReal_im,neg_zero,add_zero] using
      (ho.pow n).mul (KFCausalSourcedWidthMatterMultiplier.multiplier_horizontal_continuous
        ε h a α W w (momentumScale h) θ C p b P k hε hh y hy)

#print axioms coefficient_bound
#print axioms bound_nonnegative
#print axioms multiplier_bound
#print axioms multiplier_angle_continuous
#print axioms multiplier_horizontal_continuous
end
end UnifiedTheory.Audit.KFCausalAntisymmetricInsertionMultiplier
