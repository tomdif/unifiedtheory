/- Modulated revised field-coefficient trials have exact shifted Fourier
images with proved L1 and L2 bounds. These are scalar inputs for the
reversed matter domains, not an assumed operator core. -/
import UnifiedTheory.Audit.KFCausalClockFloorFieldCoefficient
import UnifiedTheory.Audit.KFCausalShiftedInverseClock
import UnifiedTheory.Audit.KFCausalRegularizedClockFactor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorShiftedCoefficient
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
open UnifiedTheory.Audit.KFCausalClockFloorFieldCoefficient

def shiftedWeighted (ε a j p y : ℝ) (q : ℝ) : ℂ :=
  (Real.exp (-2*Real.pi*p*y):ℂ)*modulate p (weightedLine ε a j y) q

theorem shiftedWeighted_continuous (ε a j p y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/2) : Continuous (shiftedWeighted ε a j p y) :=
  continuous_const.mul (modulate_continuous p _ (weightedLine_continuous ε a j y hε hy))

theorem shiftedWeighted_integrable (ε a j p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hj : 0 ≤ j) (hy : |y| ≤ Real.pi*ε/2) : Integrable (shiftedWeighted ε a j p y) :=
  (modulate_integrable p _ (weightedLine_integrable ε a j y hε ha hj hy)).const_mul _

theorem shiftedWeighted_memLp (ε a j p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hj : 0 ≤ j) (hy : |y| ≤ Real.pi*ε/2) : MemLp (shiftedWeighted ε a j p y) 2 :=
  (KFCausalRegularizedClockFactor.modulate_memLp p _
    (weightedLine_memLp ε a j y hε ha hj hy)).const_mul _

theorem shiftedWeighted_square_bound (ε a j p y q : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hj : 0 ≤ j) (hy : |y| ≤ Real.pi*ε/2) :
    ‖shiftedWeighted ε a j p y q‖^2 ≤
      (Real.exp (-4*Real.pi*p*y)*(stripConstant ε a j (Real.pi*ε/2))^2)*
        Real.exp (-(a/2)*q^2) := by
  rw [shiftedWeighted,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),modulate_norm,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have hb := weightedLine_gaussian_bound ε a j _ hε ha hj le_rfl y q hy
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-4*Real.pi*p*y)).le
  convert hm using 1
  · congr 2
    ring
  · rw [mul_pow,← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-(a/4)*q^2)= -(a/2)*q^2 by ring]
    ring

theorem shiftedWeighted_fourier (ε a j p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hj : 0 ≤ j) (hy : |y| ≤ Real.pi*ε/2) (k : ℝ) :
    (𝓕 (shiftedWeighted ε a j p y)) k =
      (Real.exp (-2*Real.pi*k*y):ℂ)*(𝓕 (modulate p (weightedLine ε a j 0))) k := by
  have hc (c : ℂ) (f : ℝ → ℂ) : (𝓕 (fun q => c*f q)) k = c*(𝓕 f) k := by
    simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext q
    ring
  change (𝓕 (fun q => (Real.exp (-2*Real.pi*p*y):ℂ)*modulate p (weightedLine ε a j y) q)) k = _
  rw [hc,fourier_modulate,fourier_modulate,weightedLine_fourier ε a j y hε ha hj hy,
    ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show -2*Real.pi*p*y+-2*Real.pi*(k-p)*y = -2*Real.pi*k*y by ring]

theorem shiftedWeighted_zero (ε a j p : ℝ) :
    shiftedWeighted ε a j p 0=modulate p (weightedLine ε a j 0) := by
  funext q
  simp [shiftedWeighted]

#print axioms shiftedWeighted_continuous
#print axioms shiftedWeighted_integrable
#print axioms shiftedWeighted_memLp
#print axioms shiftedWeighted_square_bound
#print axioms shiftedWeighted_fourier
#print axioms shiftedWeighted_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorShiftedCoefficient
