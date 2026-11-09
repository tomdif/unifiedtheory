/- Splitting the clock Gaussian parameter preserves a Gaussian margin
after all transverse source and polynomial insertions have been bounded. -/
import UnifiedTheory.Audit.KFCausalOuterMatterMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalOuterMatterClockDecay
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalOuterMatterMultiplier (multiplier)

def splitFactor (a h : ℝ) (q : ℂ) : ℂ :=
  Complex.exp (-((a/2:ℝ):ℂ)*(shift h q)^2+((a/4:ℝ):ℂ)*q^2)

def decayBound (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) : ℝ :=
  KFCausalOuterMatterMultiplier.bound ε h (a/2) α W w C p b P k m *
    Real.exp (7*a*h^2/4)

theorem multiplier_split (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W w c θ C p b P k m q x =
      splitFactor a h q * multiplier ε h (a/2) α W w c θ C p b P k m q x := by
  unfold multiplier KFCausalSourcedWidthMatterMultiplier.multiplier
    KFCausalWidthGaussianNeutralMultiplier.multiplier
    KFCausalWidthGaussianHolomorphicQuotient.multiplier
    KFCausalTwoShearClockQuotient.quotient splitFactor
  push_cast
  have he : -(a:ℂ)*(shift h q)^2+((a:ℂ)/2)*q^2 =
      (-((a:ℂ)/2)*(shift h q)^2+((a:ℂ)/4)*q^2)+
        (-((a:ℂ)/2)*(shift h q)^2+((a:ℂ)/2/2)*q^2) := by ring
  rw [he,Complex.exp_add]
  simp only [Complex.exp_add]
  ring

theorem splitFactor_continuous (a h : ℝ) : Continuous (splitFactor a h) := by
  unfold splitFactor shift
  fun_prop

theorem splitFactor_norm_bound (a h : ℝ) (ha : 0 ≤ a) (q : ℂ)
    (hq : |q.im| ≤ |h|) :
    ‖splitFactor a h q‖ ≤ Real.exp (-(a/4)*q.re^2+7*a*h^2/4) := by
  rw [splitFactor,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hy : q.im^2 ≤ h^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q.im) hq 2
  have hm : -(q.im*h) ≤ h^2 := by
    have ht := mul_le_mul_of_nonneg_right hq (abs_nonneg h)
    rw [← abs_mul,← pow_two,sq_abs] at ht
    exact (neg_le_abs (q.im*h)).trans ht
  have h₁ := mul_le_mul_of_nonneg_left hy ha
  have h₂ := mul_le_mul_of_nonneg_left hm ha
  simp [shift,pow_two,Complex.mul_re,Complex.mul_im]
  nlinarith

theorem decayBound_nonnegative (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) (hε : 0 < ε) (hα : 0 < α)
    (hw : 1 ≤ w) (hW : w ≤ W) : 0 ≤ decayBound ε h a α W w C p b P k m :=
  mul_nonneg (KFCausalOuterMatterMultiplier.bound_nonnegative
    ε h (a/2) α W w C p b P k m hε hα hw hW) (Real.exp_pos _).le

theorem multiplier_gaussian_bound (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k m : ℕ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W w c θ C p b P k m q x‖ ≤
      decayBound ε h a α W w C p b P k m * Real.exp (-(a/4)*q.re^2) := by
  rw [multiplier_split,norm_mul]
  calc
    _ ≤ Real.exp (-(a/4)*q.re^2+7*a*h^2/4) *
        KFCausalOuterMatterMultiplier.bound ε h (a/2) α W w C p b P k m :=
      mul_le_mul (splitFactor_norm_bound a h ha q hq)
        (KFCausalOuterMatterMultiplier.multiplier_bound ε h (a/2) α W w c θ C p b P k m
          hε hh (by positivity) hα hw hW q hq x) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; unfold decayBound; ring

#print axioms multiplier_split
#print axioms splitFactor_continuous
#print axioms splitFactor_norm_bound
#print axioms decayBound_nonnegative
#print axioms multiplier_gaussian_bound
end
end UnifiedTheory.Audit.KFCausalOuterMatterClockDecay
