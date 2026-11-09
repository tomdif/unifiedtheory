/- Powers of arbitrary real linear forms times the physical Gaussian
are actual L2 states. Integrability follows from the proved multivariate
polynomial Gaussian theorem, without an extra domain hypothesis. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianIntegrals
import UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalDirectionalGaussianStates
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalPhysicalGaussianMoments
open KFCausalClockFloorCoherentDerivative (physicalProfile clockMultiplier clockMultiplier_memLp)
open KFCausalPhysicalGaussianDerivative (configuration_product_memLp)

def linearForm (d q : Transverse) : ℝ := ∑ i, d i*q i

def linearPolynomial (d : Transverse) : MvPolynomial (Fin 5) ℝ :=
  ∑ i, MvPolynomial.C (d i)*MvPolynomial.X i

theorem linearPolynomial_eval (d q : Transverse) :
    MvPolynomial.eval q (linearPolynomial d) = linearForm d q := by
  simp [linearPolynomial,linearForm]

theorem gaussian_norm_weight (α β : ℝ) (q : Transverse) :
    ‖physicalGaussian α β q‖^2 =
      KFCausalPolynomialGaussianIntegrals.weight (fun i => 2*widths α β i) q := by
  rw [physicalGaussian_product,norm_prod,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Complex.ofReal_re] using KFCausalGaussianSliceDomain.gaussian_norm_square
    (widths α β i:ℂ) (q i)

theorem realPolynomial_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (P : MvPolynomial (Fin 5) ℝ) :
    MemLp (fun q : Transverse => (MvPolynomial.eval q P:ℂ)*physicalGaussian α β q) 2 volume := by
  have hc := (Complex.continuous_ofReal.comp P.continuous_eval).mul
    (physicalGaussian_continuous α β)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := KFCausalPolynomialGaussianIntegrals.polynomial_integrable 5
    (fun i => 2*widths α β i)
    (fun i => mul_pos (by norm_num) (widths_positive α β hα hβ i)) (P^2)
  simpa only [Pi.mul_apply,Function.comp_def,map_pow,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    gaussian_norm_weight] using hi

theorem linearForm_continuous (d : Transverse) : Continuous (linearForm d) := by
  unfold linearForm
  fun_prop

theorem direction_power_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (d : Transverse) (n : ℕ) :
    MemLp (fun q => (linearForm d q:ℂ)^n*physicalGaussian α β q) 2 volume := by
  simpa only [map_pow,linearPolynomial_eval,Complex.ofReal_pow] using
    realPolynomial_memLp α β hα hβ ((linearPolynomial d)^n)

def profile (C : ℂ) (p α β : ℝ) (g : ℝ → ℂ) (d : Transverse)
    (n : ℕ) (x : Configuration) : ℂ :=
  (linearForm d x.2:ℂ)^n*physicalProfile C p α β 0 g x

theorem profile_memLp (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (d : Transverse) (n : ℕ) :
    MemLp (profile C p α β g d n) 2 volume := by
  convert configuration_product_memLp _ _ (clockMultiplier_memLp C p g hg)
    (direction_power_memLp α β hα hβ d n) using 1
  funext x
  simp only [profile,physicalProfile,KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,Complex.exp_zero,one_mul]
  ring

#print axioms linearPolynomial_eval
#print axioms gaussian_norm_weight
#print axioms realPolynomial_memLp
#print axioms linearForm_continuous
#print axioms direction_power_memLp
#print axioms profile_memLp
end
end UnifiedTheory.Audit.KFCausalDirectionalGaussianStates
