/- Self-Fourier Euclidean Gaussians and their exponential momentum weights.
These supply explicit graph-admissible weights for the modulated graph core. -/
import UnifiedTheory.Audit.KFCausalModulatedGraphCore
import UnifiedTheory.Audit.KFCausalEuclideanConfiguration
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalEuclideanGaussianCore
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussian (x : E) : ℂ := Complex.exp (-Real.pi*(‖x‖:ℂ)^2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_continuous : Continuous (gaussian : E → ℂ) := by unfold gaussian; fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_ne_zero (x : E) : gaussian x ≠ 0 := Complex.exp_ne_zero _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_norm_square (x : E) : ‖gaussian x‖^2 = Real.exp (-2*Real.pi*‖x‖^2) := by
  simp only [gaussian,← Complex.ofReal_pow,← Complex.ofReal_neg,← Complex.ofReal_mul,
    Complex.norm_exp,Complex.ofReal_re,← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem gaussian_integrable : Integrable (gaussian : E → ℂ) := by
  simpa only [mul_zero,zero_mul,add_zero] using
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (Real.pi:ℂ))
      (by simpa using Real.pi_pos) 0 (0:E)

theorem quadratic_exp_integrable (a c : ℝ) (ha : 0 < a) (v : E) :
    Integrable (fun x : E => Real.exp (-a*‖x‖^2+c*inner ℝ v x)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (a:ℂ))
    (by simpa using ha) (c:ℂ) v).norm
  simpa only [← Complex.ofReal_pow,← Complex.ofReal_neg,← Complex.ofReal_mul,
    ← Complex.ofReal_add,Complex.norm_exp,Complex.ofReal_re] using h

theorem gaussian_memLp : MemLp (gaussian : E → ℂ) 2 := by
  apply (memLp_two_iff_integrable_sq_norm gaussian_continuous.aestronglyMeasurable).mpr
  simp only [gaussian_norm_square]
  simpa only [zero_mul,add_zero,neg_mul] using quadratic_exp_integrable (2*Real.pi) 0 (by positivity) (0:E)

theorem gaussian_fourier : 𝓕 (gaussian : E → ℂ) = gaussian := by
  funext k
  have h := fourier_gaussian_innerProductSpace (b := (Real.pi:ℂ))
    (by simpa using Real.pi_pos) k
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_self hp,Complex.one_cpow,one_mul] at h
  change (𝓕 (gaussian : E → ℂ)) k = _ at h
  rw [h]
  unfold gaussian
  congr 1
  field_simp

def exponentialWeight (hbar : ℝ) (k : Space) : ℝ := Real.exp (Real.pi*hbar*k 0)

theorem exponentialWeight_measurable (hbar : ℝ) : Measurable (exponentialWeight hbar) := by
  unfold exponentialWeight
  fun_prop

theorem weighted_gaussian_memLp (hbar : ℝ) :
    MemLp (fun k : Space => (exponentialWeight hbar k:ℂ)*gaussian k) 2 := by
  have hc : Continuous (fun k : Space => (exponentialWeight hbar k:ℂ)*gaussian k) := by
    unfold exponentialWeight gaussian
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have h := quadratic_exp_integrable (2*Real.pi) (2*Real.pi*hbar) (by positivity) clockVector
  convert h using 1
  funext k
  unfold exponentialWeight
  rw [norm_mul,mul_pow,gaussian_norm_square,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul,← Real.exp_add,clockVector_inner]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem gaussian_spectral_graph_core (hbar : ℝ) :
    (Submodule.span ℂ (Set.range (KFCausalModulatedGraphCore.packet (exponentialWeight hbar)
      gaussian gaussian_memLp (weighted_gaussian_memLp hbar)))).topologicalClosure =
      KFCausalMultiplierGraphCoordinates.graph (exponentialWeight hbar) (exponentialWeight_measurable hbar) :=
  KFCausalModulatedGraphCore.graph_core (exponentialWeight hbar) (exponentialWeight_measurable hbar)
    gaussian gaussian_memLp (weighted_gaussian_memLp hbar) gaussian_ne_zero

#print axioms gaussian_continuous
#print axioms gaussian_ne_zero
#print axioms gaussian_norm_square
#print axioms gaussian_integrable
#print axioms quadratic_exp_integrable
#print axioms gaussian_memLp
#print axioms gaussian_fourier
#print axioms exponentialWeight_measurable
#print axioms weighted_gaussian_memLp
#print axioms gaussian_spectral_graph_core

end
end UnifiedTheory.Audit.KFCausalEuclideanGaussianCore
