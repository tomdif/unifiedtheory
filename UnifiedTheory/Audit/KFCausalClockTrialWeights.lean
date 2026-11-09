/- The proposed positive clock dressing has actual L2 control. The
inverse chart bounds the clock by a linear function of |q|; Gaussian
moments control both the half-clock dressed state and its clock energy. -/
import UnifiedTheory.Audit.KFCausalDampedProductDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockTrialWeights
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalDampedGaussianStrip
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality

def clock (ε : ℝ) (hε : 0 < ε) (q : ℝ) : ℝ := Real.exp ((chartIso ε hε).symm q)

theorem clock_bound (ε : ℝ) (hε : 0 < ε) (q : ℝ) : clock ε hε q ≤ 1+|q| := by
  let s := (chartIso ε hε).symm q
  have hq : chart ε s = q := (chartIso ε hε).apply_symm_apply q
  change Real.exp s ≤ 1+|q|
  by_cases hs : s ≤ 0
  · have he : Real.exp s ≤ 1 := by simpa using Real.exp_le_exp.mpr hs
    linarith [abs_nonneg q]
  · have hp : 0 ≤ ε*s := mul_nonneg hε.le (le_of_not_ge hs)
    have hqa := le_abs_self q
    dsimp [chart] at hq
    linarith

theorem clock_square_bound (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    (clock ε hε q)^2 ≤ 2*(1+q^2) := by
  have hs := pow_le_pow_left₀ (Real.exp_pos ((chartIso ε hε).symm q)).le (clock_bound ε hε q) 2
  change (clock ε hε q)^2 ≤ (1+|q|)^2 at hs
  have ha := sq_nonneg (|q|-1)
  nlinarith [sq_abs q]

theorem realTrial_square_bound (ε a q : ℝ) (hε : 0 ≤ ε) :
    ‖realTrial ε a q‖^2 ≤ Real.exp (-a*q^2) := by
  have hb : ‖realTrial ε a q‖ ≤ Real.exp (-(a/2)*q^2) := by
    simpa only [line_zero,mul_zero,zero_pow (by decide : 2 ≠ 0),Real.exp_zero,one_mul] using
      line_gaussian_bound ε a 0 q hε (by simp)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have he : (Real.exp (-(a/2)*q^2))^2 = Real.exp (-a*q^2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  exact hs.trans_eq he

theorem clock_square_energy (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun q => (clock ε hε q)^2*‖realTrial ε a q‖^2) := by
  have h₀ : Integrable (fun q : ℝ => Real.exp (-a*q^2)) := integrable_exp_neg_mul_sq ha
  have h₂ : Integrable (fun q : ℝ => q^2*Real.exp (-a*q^2)) := by
    simpa only [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq ha (s := (2:ℕ)) (by norm_num)
  have hi : Integrable (fun q : ℝ => 2*(1+q^2)*Real.exp (-a*q^2)) := by
    convert (h₀.add h₂).const_mul 2 using 1
    funext q
    dsimp only [Pi.add_apply]
    ring
  have hc : Continuous (fun q => (clock ε hε q)^2*‖realTrial ε a q‖^2) :=
    ((Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous).pow 2).mul ((realTrial_continuous ε a).norm.pow 2)
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_mul (clock_square_bound ε hε q) (realTrial_square_bound ε a q hε.le)
    (sq_nonneg _) (by positivity)

theorem clock_energy (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun q => clock ε hε q*‖realTrial ε a q‖^2) := by
  have hi := (realTrial_square_integrable ε a hε.le ha).add (clock_square_energy ε a hε ha)
  have hc : Continuous (fun q => clock ε hε q*‖realTrial ε a q‖^2) :=
    (Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous).mul ((realTrial_continuous ε a).norm.pow 2)
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ clock ε hε q*‖realTrial ε a q‖^2 from
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  dsimp only [Pi.add_apply]
  have hb : clock ε hε q ≤ 1+(clock ε hε q)^2 := by nlinarith [sq_nonneg (clock ε hε q-1/2)]
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg ‖realTrial ε a q‖)]

def clockTrial (ε a : ℝ) (hε : 0 < ε) (p b q : ℝ) : ℂ :=
  (Real.exp (b*(chartIso ε hε).symm q):ℂ)*modulate p (realTrial ε a) q

theorem clockTrial_continuous (ε a : ℝ) (hε : 0 < ε) (p b : ℝ) :
    Continuous (clockTrial ε a hε p b) :=
  (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul (chartIso ε hε).symm.toHomeomorph.continuous))).mul
    (modulate_continuous p _ (realTrial_continuous ε a))

theorem clockTrial_square (ε a : ℝ) (hε : 0 < ε) (p b q : ℝ) :
    ‖clockTrial ε a hε p b q‖^2 = Real.exp (2*b*(chartIso ε hε).symm q)*‖realTrial ε a q‖^2 := by
  rw [clockTrial,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),modulate_norm,
    ← Real.exp_nat_mul]
  congr 2
  norm_num
  ring

theorem clockTrial_one_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : ℝ) :
    MemLp (clockTrial ε a hε p 1) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (clockTrial_continuous ε a hε p 1).aestronglyMeasurable).mpr
  have he (q : ℝ) : ‖clockTrial ε a hε p 1 q‖^2 = (clock ε hε q)^2*‖realTrial ε a q‖^2 := by
    rw [clockTrial_square,clock,← Real.exp_nat_mul]
    norm_num
  simpa only [he] using clock_square_energy ε a hε ha

theorem clockTrial_half_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : ℝ) :
    MemLp (clockTrial ε a hε p (1/2)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (clockTrial_continuous ε a hε p (1/2)).aestronglyMeasurable).mpr
  have he (q : ℝ) : ‖clockTrial ε a hε p (1/2) q‖^2 = clock ε hε q*‖realTrial ε a q‖^2 := by
    rw [clockTrial_square]
    norm_num [clock]
  simpa only [he] using clock_energy ε a hε ha

theorem clockTrial_ne_zero (ε a : ℝ) (hε : 0 < ε) (p b q : ℝ) : clockTrial ε a hε p b q ≠ 0 := by
  unfold clockTrial modulate
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    (mul_ne_zero (Circle.coe_ne_zero _) (realTrial_ne_zero ε a q))

#print axioms clock_bound
#print axioms clock_square_bound
#print axioms realTrial_square_bound
#print axioms clock_square_energy
#print axioms clock_energy
#print axioms clockTrial_continuous
#print axioms clockTrial_square
#print axioms clockTrial_one_memLp
#print axioms clockTrial_half_memLp
#print axioms clockTrial_ne_zero

end
end UnifiedTheory.Audit.KFCausalClockTrialWeights
