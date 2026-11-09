/- Gaussian physical-clock functions have finite energy under every real
clock power. These bounds will supply dense reversed-order momentum tests. -/
import UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
import UnifiedTheory.Audit.KFCausalWeightedProductTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalGaussianClockWeights
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests

def weightedGaussian (b s : ℝ) : ℂ := (Real.exp (b*s):ℂ)*gaussian s

theorem weightedGaussian_continuous (b : ℝ) : Continuous (weightedGaussian b) :=
  (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
    gaussian_continuous

theorem weightedGaussian_square (b s : ℝ) :
    ‖weightedGaussian b s‖^2=Real.exp (-2*Real.pi*s^2+2*b*s) := by
  rw [weightedGaussian,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),gaussian_norm_square,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem weightedGaussian_memLp (b : ℝ) : MemLp (weightedGaussian b) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (weightedGaussian_continuous b).aestronglyMeasurable).mpr
  simpa only [weightedGaussian_square,add_zero,neg_mul] using
    quadratic_exp_integrable (2*Real.pi) (2*b) 0 (by positivity)

theorem gaussian_memLp : MemLp gaussian 2 := by
  have he : weightedGaussian 0=gaussian := by
    funext s
    simp [weightedGaussian]
  rw [← he]
  exact weightedGaussian_memLp 0

theorem gaussian_ne_zero (s : ℝ) : gaussian s ≠ 0 := Complex.exp_ne_zero _

theorem modulatedGaussian_memLp (p : ℝ) : MemLp (modulate p gaussian) 2 :=
  KFCausalWeightedProductTotality.modulate_memLp gaussian gaussian_memLp p

theorem modulatedWeightedGaussian_memLp (b p : ℝ) : MemLp (modulate p (weightedGaussian b)) 2 :=
  KFCausalWeightedProductTotality.modulate_memLp (weightedGaussian b) (weightedGaussian_memLp b) p

#print axioms weightedGaussian_continuous
#print axioms weightedGaussian_square
#print axioms weightedGaussian_memLp
#print axioms gaussian_memLp
#print axioms gaussian_ne_zero
#print axioms modulatedGaussian_memLp
#print axioms modulatedWeightedGaussian_memLp

end
end UnifiedTheory.Audit.KFCausalGaussianClockWeights
