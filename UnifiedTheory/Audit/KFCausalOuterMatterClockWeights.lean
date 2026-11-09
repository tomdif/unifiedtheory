/- Arbitrary natural half-clock moments of the actual sourced outer
matter multipliers are bounded by the retained clock Gaussian. -/
import UnifiedTheory.Audit.KFCausalOuterMatterClockDecay
import UnifiedTheory.Audit.KFCausalClockTrialWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalOuterMatterClockWeights
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalOuterMatterClockDecay (decayBound)

def realClock (ε : ℝ) (hε : 0 < ε) (r : ℝ) : ℝ :=
  KFCausalClockTrialWeights.clock ε hε r+ε

def clockWeight (ε : ℝ) (hε : 0 < ε) (n : ℕ) (r : ℝ) : ℝ :=
  (Real.sqrt (realClock ε hε r))^n

def scalarCap (ε a : ℝ) (n : ℕ) : ℝ :=
  (ε+2)^n*Real.exp ((n:ℝ)^2/a)

def bound (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m n : ℕ) : ℝ :=
  scalarCap ε a n*decayBound ε h a α W w C p b P k m

theorem realClock_positive (ε : ℝ) (hε : 0 < ε) (r : ℝ) :
    0 < realClock ε hε r := by
  unfold realClock KFCausalClockTrialWeights.clock
  positivity

theorem clockWeight_nonnegative (ε : ℝ) (hε : 0 < ε) (n : ℕ) (r : ℝ) :
    0 ≤ clockWeight ε hε n r := pow_nonneg (Real.sqrt_nonneg _) _

theorem clockWeight_continuous (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    Continuous (clockWeight ε hε n) := by
  unfold clockWeight realClock KFCausalClockTrialWeights.clock
  exact (((Real.continuous_exp.comp
    (KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm.toHomeomorph.continuous).add
      continuous_const).sqrt).pow n

theorem clockWeight_zero (ε : ℝ) (hε : 0 < ε) (r : ℝ) : clockWeight ε hε 0 r = 1 :=
  pow_zero _

theorem scalarCap_nonnegative (ε a : ℝ) (n : ℕ) (hε : 0 < ε) :
    0 ≤ scalarCap ε a n := by unfold scalarCap; positivity

theorem clockWeight_gaussian_bound (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (n : ℕ) (r : ℝ) :
    clockWeight ε hε n r*Real.exp (-(a/4)*r^2) ≤ scalarCap ε a n := by
  have hc := KFCausalClockTrialWeights.clock_bound ε hε r
  have hc0 := (realClock_positive ε hε r).le
  have hs : Real.sqrt (realClock ε hε r) ≤ realClock ε hε r+1 := by
    nlinarith [Real.sq_sqrt hc0,sq_nonneg (Real.sqrt (realClock ε hε r)-1/2)]
  have hr : Real.sqrt (realClock ε hε r) ≤ (ε+2)*(1+|r|) := by
    unfold realClock at hs ⊢
    nlinarith [mul_nonneg hε.le (abs_nonneg r),abs_nonneg r]
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg (realClock ε hε r)) hr n
  rw [mul_pow] at hp
  have he := KFCausalComplexPolynomialGaussianAbsorption.power_radius_bound n |r| (abs_nonneg r)
  have hcomp := KFCausalComplexPolynomialGaussianAbsorption.complete_square_bound
    (a/4) (n:ℝ) |r| (by positivity)
  rw [sq_abs,show 4*(a/4)=a by ring] at hcomp
  calc
    _ ≤ ((ε+2)^n*Real.exp ((n:ℝ)*|r|))*Real.exp (-(a/4)*r^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact hp.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ = (ε+2)^n*Real.exp ((n:ℝ)*|r|-(a/4)*r^2) := by
      rw [sub_eq_add_neg,Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcomp) (by positivity)

theorem bound_nonnegative (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m n : ℕ) (hε : 0 < ε) (hα : 0 < α)
    (hw : 1 ≤ w) (hW : w ≤ W) : 0 ≤ bound ε h a α W w C p b P k m n :=
  mul_nonneg (scalarCap_nonnegative ε a n hε)
    (KFCausalOuterMatterClockDecay.decayBound_nonnegative ε h a α W w C p b P k m hε hα hw hW)

theorem weighted_splitFactor_bound (ε h a : ℝ) (n : ℕ) (hε : 0 < ε)
    (ha : 0 < a) (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖(clockWeight ε hε n q.re:ℂ)*KFCausalOuterMatterClockDecay.splitFactor a h q‖ ≤
      scalarCap ε a n*Real.exp (7*a*h^2/4) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (clockWeight_nonnegative ε hε n q.re)]
  calc
    _ ≤ clockWeight ε hε n q.re*Real.exp (-(a/4)*q.re^2+7*a*h^2/4) :=
      mul_le_mul_of_nonneg_left
        (KFCausalOuterMatterClockDecay.splitFactor_norm_bound a h ha.le q hq)
        (clockWeight_nonnegative ε hε n q.re)
    _ = (clockWeight ε hε n q.re*Real.exp (-(a/4)*q.re^2))*Real.exp (7*a*h^2/4) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (clockWeight_gaussian_bound ε a hε ha n q.re)
      (Real.exp_pos _).le

theorem multiplier_bound (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m n : ℕ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (ha : 0 < a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    clockWeight ε hε n q.re *
      ‖KFCausalOuterMatterMultiplier.multiplier ε h a α W w c θ C p b P k m q x‖ ≤
      bound ε h a α W w C p b P k m n := by
  have hg := KFCausalOuterMatterClockDecay.multiplier_gaussian_bound
    ε h a α W w c θ C p b P k m hε hh ha.le hα hw hW q hq x
  calc
    _ ≤ clockWeight ε hε n q.re *
        (decayBound ε h a α W w C p b P k m *Real.exp (-(a/4)*q.re^2)) :=
      mul_le_mul_of_nonneg_left hg (clockWeight_nonnegative ε hε n q.re)
    _ = (clockWeight ε hε n q.re*Real.exp (-(a/4)*q.re^2))*
        decayBound ε h a α W w C p b P k m := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (clockWeight_gaussian_bound ε a hε ha n q.re)
      (KFCausalOuterMatterClockDecay.decayBound_nonnegative ε h a α W w C p b P k m hε hα hw hW)

theorem weighted_multiplier_bound (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m n : ℕ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (ha : 0 < a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖(clockWeight ε hε n q.re:ℂ)*
      KFCausalOuterMatterMultiplier.multiplier ε h a α W w c θ C p b P k m q x‖ ≤
      bound ε h a α W w C p b P k m n := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (clockWeight_nonnegative ε hε n q.re)]
  exact multiplier_bound ε h a α W w c θ C p b P k m n hε hh ha hα hw hW q hq x

#print axioms realClock_positive
#print axioms clockWeight_nonnegative
#print axioms clockWeight_continuous
#print axioms clockWeight_zero
#print axioms scalarCap_nonnegative
#print axioms clockWeight_gaussian_bound
#print axioms bound_nonnegative
#print axioms weighted_splitFactor_bound
#print axioms multiplier_bound
#print axioms weighted_multiplier_bound
end
end UnifiedTheory.Audit.KFCausalOuterMatterClockWeights
