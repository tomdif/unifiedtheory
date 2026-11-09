/- The complex-shifted repaired scalar also has finite inverse-clock
energy. This supplies the reversed-order adjoint tests for E C^(-1/2). -/
import UnifiedTheory.Audit.KFCausalShiftedScalarMoments
import UnifiedTheory.Audit.KFCausalRegularizedAdjointTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedInverseClock
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
open UnifiedTheory.Audit.KFCausalShiftedDampedScalar
open UnifiedTheory.Audit.KFCausalShiftedScalarMoments

theorem shifted_inverse_clock_energy (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) :
    Integrable (fun q => Real.exp (-((chartIso ε hε).symm q))*‖shiftedScalar ε a p y q‖^2) := by
  have h₀ : Integrable (fun q : ℝ => Real.exp (-a*q^2)) := integrable_exp_neg_mul_sq ha
  have h₁ : Integrable (fun q : ℝ => Real.exp ((1-q)/ε)*Real.exp (-a*q^2)) := by
    convert quadratic_exp_integrable a (-1/ε) (1/ε) ha using 1
    funext q
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : Continuous (fun q => Real.exp (-((chartIso ε hε).symm q))*‖shiftedScalar ε a p y q‖^2) :=
    (Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous.neg).mul
      ((shiftedScalar_continuous ε a p y).norm.pow 2)
  apply ((h₀.add h₁).const_mul (Real.exp (-4*Real.pi*p*y+a*y^2))).mono' hc.aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hb : Real.exp (-((chartIso ε hε).symm q)) ≤ 1+Real.exp ((1-q)/ε) := by
    simpa only [clockQ,Real.exp_neg] using inverse_clock_bound ε hε q
  have hm := mul_le_mul hb (shiftedScalar_square_bound ε a p y q hε hy)
    (sq_nonneg ‖shiftedScalar ε a p y q‖) (by positivity : 0 ≤ 1+Real.exp ((1-q)/ε))
  dsimp only [Pi.add_apply]
  convert hm using 1
  ring

def inverseHalfShift (ε a p y : ℝ) (hε : 0 < ε) (q : ℝ) : ℂ :=
  (Real.exp (-(1/2)*((chartIso ε hε).symm q)):ℂ)*shiftedScalar ε a p y q

theorem inverseHalfShift_continuous (ε a p y : ℝ) (hε : 0 < ε) :
    Continuous (inverseHalfShift ε a p y hε) :=
  (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (chartIso ε hε).symm.toHomeomorph.continuous))).mul
      (shiftedScalar_continuous ε a p y)

theorem inverseHalfShift_square (ε a p y q : ℝ) (hε : 0 < ε) :
    ‖inverseHalfShift ε a p y hε q‖^2 =
      Real.exp (-((chartIso ε hε).symm q))*‖shiftedScalar ε a p y q‖^2 := by
  rw [inverseHalfShift,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*(-(1/2)*((chartIso ε hε).symm q)) = -((chartIso ε hε).symm q) by ring]

theorem inverseHalfShift_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) : MemLp (inverseHalfShift ε a p y hε) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (inverseHalfShift_continuous ε a p y hε).aestronglyMeasurable).mpr
  simpa only [inverseHalfShift_square] using shifted_inverse_clock_energy ε a p y hε ha hy

#print axioms shifted_inverse_clock_energy
#print axioms inverseHalfShift_continuous
#print axioms inverseHalfShift_square
#print axioms inverseHalfShift_memLp

end
end UnifiedTheory.Audit.KFCausalShiftedInverseClock
