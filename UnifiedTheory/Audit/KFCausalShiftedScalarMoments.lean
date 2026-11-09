/- Gaussian moment control for the actual complex-shifted scalar output.
These estimates include the strip boundary and the clock-square weight
needed for quadratic transverse position factors after the exponential. -/
import UnifiedTheory.Audit.KFCausalShiftedDampedScalar
import UnifiedTheory.Audit.KFCausalClockTrialWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedScalarMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalDampedGaussianStrip
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalClockTrialWeights
open UnifiedTheory.Audit.KFCausalShiftedDampedScalar

theorem line_square_bound (ε a y q : ℝ) (hε : 0 ≤ ε) (hy : 0 ≤ Real.cos (y/ε)) :
    ‖line ε a y q‖^2 ≤ Real.exp (a*y^2)*Real.exp (-a*q^2) := by
  have hs := pow_le_pow_left₀ (norm_nonneg _) (line_gaussian_bound ε a y q hε hy) 2
  convert hs using 1
  rw [mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  congr 1 <;> congr 1 <;> ring

theorem shiftedScalar_square_bound (ε a p y q : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/2) :
    ‖shiftedScalar ε a p y q‖^2 ≤
      Real.exp (-4*Real.pi*p*y+a*y^2)*Real.exp (-a*q^2) := by
  rw [shiftedScalar_square,Real.exp_add]
  calc
    _ ≤ Real.exp (-4*Real.pi*p*y)*(Real.exp (a*y^2)*Real.exp (-a*q^2)) :=
      mul_le_mul_of_nonneg_left
        (line_square_bound ε a y q hε.le (cosine_nonnegative ε (Real.pi*ε/2) y hε le_rfl hy))
        (Real.exp_pos _).le
    _ = _ := by ring

theorem shiftedScalar_moment (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (n : ℕ) :
    Integrable (fun q : ℝ => q^(2*n)*‖shiftedScalar ε a p y q‖^2) := by
  have hi : Integrable (fun q : ℝ => q^(2*n)*Real.exp (-a*q^2)) := by
    simpa only [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq ha
      (s := (2*n:ℕ)) (by have hn : 0 ≤ ((2*n:ℕ):ℝ) := Nat.cast_nonneg _; linarith)
  have hp (q : ℝ) : 0 ≤ q^(2*n) := by rw [pow_mul]; positivity
  apply (hi.const_mul (Real.exp (-4*Real.pi*p*y+a*y^2))).mono'
    (show Continuous (fun q : ℝ => q^(2*n)*‖shiftedScalar ε a p y q‖^2) from
      (continuous_id.pow _).mul ((shiftedScalar_continuous ε a p y).norm.pow 2)).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hp q) (sq_nonneg _))]
  calc
    _ ≤ q^(2*n)*(Real.exp (-4*Real.pi*p*y+a*y^2)*Real.exp (-a*q^2)) :=
      mul_le_mul_of_nonneg_left (shiftedScalar_square_bound ε a p y q hε hy) (hp q)
    _ = _ := by ring

theorem shiftedScalar_clock_square_energy (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) :
    Integrable (fun q => (clock ε hε q)^2*‖shiftedScalar ε a p y q‖^2) := by
  have h₀ := (memLp_two_iff_integrable_sq_norm (shiftedScalar_memLp ε a p y hε ha hy).aestronglyMeasurable).mp
    (shiftedScalar_memLp ε a p y hε ha hy)
  have h₂ : Integrable (fun q : ℝ => q^2*‖shiftedScalar ε a p y q‖^2) := by
    simpa using shiftedScalar_moment ε a p y hε ha hy 1
  have hc : Continuous (fun q => (clock ε hε q)^2*‖shiftedScalar ε a p y q‖^2) :=
    ((Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous).pow 2).mul
      ((shiftedScalar_continuous ε a p y).norm.pow 2)
  apply ((h₀.add h₂).const_mul 2).mono' hc.aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  dsimp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right (clock_square_bound ε hε q) (sq_nonneg ‖shiftedScalar ε a p y q‖)]

theorem shiftedScalar_one_add_clock_square_energy (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) :
    Integrable (fun q => (1+(clock ε hε q)^2)*‖shiftedScalar ε a p y q‖^2) := by
  have h₀ := (memLp_two_iff_integrable_sq_norm (shiftedScalar_memLp ε a p y hε ha hy).aestronglyMeasurable).mp
    (shiftedScalar_memLp ε a p y hε ha hy)
  convert h₀.add (shiftedScalar_clock_square_energy ε a p y hε ha hy) using 1
  funext q
  dsimp only [Pi.add_apply]
  ring

#print axioms line_square_bound
#print axioms shiftedScalar_square_bound
#print axioms shiftedScalar_moment
#print axioms shiftedScalar_clock_square_energy
#print axioms shiftedScalar_one_add_clock_square_energy

end
end UnifiedTheory.Audit.KFCausalShiftedScalarMoments
