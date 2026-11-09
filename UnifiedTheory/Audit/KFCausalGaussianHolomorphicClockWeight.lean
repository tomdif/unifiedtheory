/- The actual clock and its reciprocal, multiplied by a spare clock
Gaussian, are bounded holomorphic functions on the required strip.
These are complex-clock functions, not functions of the real part. -/
import UnifiedTheory.Audit.KFCausalTwoShearClockQuotient
import UnifiedTheory.Audit.KFCausalComplexClockWeights
import UnifiedTheory.Audit.KFCausalComplexPolynomialGaussianAbsorption
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGaussianHolomorphicClockWeight
noncomputable section
open KFCausalClockFloorComplexDefect (complexClock complexClock_ne_zero complexClock_real)
open KFCausalComplexClockInverse (complexInverse complexInverse_analytic)
open KFCausalRegularizedLongitudinalChart (chart chartIso)

def clockPower (ε : ℝ) (inverse : Bool) (q : ℂ) : ℂ :=
  if inverse then (complexClock ε q)⁻¹ else complexClock ε q

def physicalPower (ε : ℝ) (inverse : Bool) (s : ℝ) : ℂ :=
  if inverse then ((Real.exp s+ε:ℝ):ℂ)⁻¹ else ((Real.exp s+ε:ℝ):ℂ)

def multiplier (ε a : ℝ) (inverse : Bool) (q : ℂ) : ℂ :=
  clockPower ε inverse q*Complex.exp (-((a/2:ℝ):ℂ)*q^2)

def bound (ε h a : ℝ) (inverse : Bool) : ℝ :=
  if inverse then ε⁻¹*Real.exp (a*h^2/2)
  else (1+ε)*Real.exp ((1/ε)^2/(2*a)+a*h^2/2)

theorem bound_nonnegative (ε h a : ℝ) (inverse : Bool) (hε : 0 < ε) :
    0 ≤ bound ε h a inverse := by
  cases inverse <;> simp only [bound,Bool.false_eq_true,ite_false,ite_true] <;> positivity

theorem multiplier_analytic (ε h a : ℝ) (inverse : Bool) (hε : 0 < ε)
    (hb : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) :
    AnalyticAt ℂ (multiplier ε a inverse) q := by
  have ht := (KFCausalTwoShearClockQuotient.strip_membership ε h hε hb q hq).1
  have hc : AnalyticAt ℂ (complexClock ε) q :=
    (complexInverse_analytic ε hε q ht).cexp.add analyticAt_const
  have hg : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-((a/2:ℝ):ℂ)*z^2)) q := by fun_prop
  cases inverse
  · exact hc.mul hg
  · exact (hc.inv (complexClock_ne_zero ε hε q ht)).mul hg

private theorem gaussian_bound (a h : ℝ) (ha : 0 ≤ a) (q : ℂ)
    (hq : |q.im| ≤ |h|) :
    ‖Complex.exp (-((a/2:ℝ):ℂ)*q^2)‖ ≤
      Real.exp (-(a/2)*q.re^2+a*h^2/2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hs : q.im^2 ≤ h^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q.im) hq 2
  have hm := mul_le_mul_of_nonneg_left hs ha
  simp [pow_two,Complex.mul_re,Complex.mul_im]
  nlinarith

theorem multiplier_bound (ε h a : ℝ) (inverse : Bool) (hε : 0 < ε)
    (hb : |h| ≤ ε/10) (ha : 0 < a) (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖multiplier ε a inverse q‖ ≤ bound ε h a inverse := by
  have ht := (KFCausalTwoShearClockQuotient.strip_membership ε h hε hb q hq).1
  have hg := gaussian_bound a h ha.le q hq
  cases inverse
  · have hc : ‖complexClock ε q‖ ≤ (1+ε)*Real.exp (|q.re|/ε) := by
      have hu := KFCausalComplexClockWeights.complexInverse_re_upper ε hε q ht
      have hl := div_le_div_of_nonneg_right (le_abs_self q.re) hε.le
      have he := Real.exp_le_exp.mpr (hu.trans hl)
      have h1 : 1 ≤ Real.exp (|q.re|/ε) := Real.one_le_exp (by positivity)
      have hn := norm_add_le (Complex.exp (complexInverse ε q)) (ε:ℂ)
      rw [Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] at hn
      change ‖Complex.exp (complexInverse ε q)+(ε:ℂ)‖ ≤ _
      nlinarith [mul_le_mul_of_nonneg_left h1 hε.le]
    have hs := KFCausalComplexPolynomialGaussianAbsorption.complete_square_bound
      (a/2) (1/ε) |q.re| (by positivity)
    rw [sq_abs,show 4*(a/2)=2*a by ring] at hs
    change ‖complexClock ε q*Complex.exp (-((a/2:ℝ):ℂ)*q^2)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ((1+ε)*Real.exp (|q.re|/ε))*Real.exp (-(a/2)*q.re^2+a*h^2/2) :=
        mul_le_mul hc hg (norm_nonneg _) (by positivity)
      _ = (1+ε)*Real.exp (|q.re|/ε-(a/2)*q.re^2+a*h^2/2) := by
        rw [mul_assoc,← Real.exp_add]
        congr 2
        ring
      _ ≤ (1+ε)*Real.exp ((1/ε)^2/(2*a)+a*h^2/2) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        simp only [div_eq_mul_inv] at hs ⊢
        nlinarith only [hs]
  · have hc := KFCausalTwoShearClockQuotient.inverse_clock_bound ε hε q ht
    change ‖(complexClock ε q)⁻¹*Complex.exp (-((a/2:ℝ):ℂ)*q^2)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ε⁻¹*Real.exp (-(a/2)*q.re^2+a*h^2/2) :=
        mul_le_mul hc hg (norm_nonneg _) (by positivity)
      _ ≤ ε⁻¹*Real.exp (a*h^2/2) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith [mul_nonneg ha.le (sq_nonneg q.re)]

theorem clockPower_real (ε : ℝ) (inverse : Bool) (hε : 0 < ε) (s : ℝ) :
    clockPower ε inverse (chart ε s:ℂ)=physicalPower ε inverse s := by
  have hc : complexClock ε (chart ε s:ℂ)=((Real.exp s+ε:ℝ):ℂ) := by
    rw [complexClock_real ε hε]
    simp only [KFCausalClockFloorComplexDefect.realClock,
      KFCausalClockFloorFlow.clock,show (chartIso ε hε).symm (chart ε s)=s from
        (chartIso ε hε).symm_apply_apply s]
  cases inverse <;> simp only [clockPower,physicalPower,Bool.false_eq_true,ite_false,ite_true,hc]

theorem profile_split (ε a h w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (inverse : Bool) (hε : 0 < ε) (x : KFCausalCoupledLongitudinalFlow.Configuration) :
    multiplier ε a inverse (chart ε x.1:ℂ)*
      KFCausalReciprocalNeutralPackets.profile ε (a/2) h w C p b P x =
      physicalPower ε inverse x.1*KFCausalReciprocalNeutralPackets.profile ε a h w C p b P x := by
  have hc : Complex.exp (-((a/2:ℝ):ℂ)*(chart ε x.1:ℂ)^2)*
      KFCausalClockFloorInvariantTrial.clockFunction ε (a/2) x.1 =
      KFCausalClockFloorInvariantTrial.clockFunction ε a x.1 := by
    unfold KFCausalClockFloorInvariantTrial.clockFunction
      KFCausalClockFloorInvariantTrial.realClock
    push_cast
    rw [mul_left_comm,← Complex.exp_add]
    congr 2
    ring
  rw [multiplier,clockPower_real ε inverse hε]
  unfold KFCausalReciprocalNeutralPackets.profile
    KFCausalReciprocalGaussianStates.configurationDensity
  calc
    _ = physicalPower ε inverse x.1*
      ((C*KFCausalClockFloorCoherentStrip.clockPhase p (x.1:ℂ)*Complex.exp (b*(x.2 4:ℂ))*P.eval (x.2 4:ℂ))*
        ((Complex.exp (-((a/2:ℝ):ℂ)*(chart ε x.1:ℂ)^2)*
          KFCausalClockFloorInvariantTrial.clockFunction ε (a/2) x.1)*
          Complex.exp (-((KFCausalChargeGaussianGeometry.groundWidth h*
            KFCausalReciprocalGaussianStates.quadratic w x.2+
            KFCausalClockFloorInvariantTrial.neutralWidth h*(x.2 4)^2:ℝ):ℂ)))) := by ring
    _ = _ := by rw [hc]

#print axioms bound_nonnegative
#print axioms multiplier_analytic
#print axioms multiplier_bound
#print axioms clockPower_real
#print axioms profile_split
end
end UnifiedTheory.Audit.KFCausalGaussianHolomorphicClockWeight
