/- Exact positive kernel for arbitrary complex superpositions of the
centered state and its paired quadratic excitation. Positivity is proved
from two explicit transverse evaluations, including destructive interference. -/
import UnifiedTheory.Audit.KFCausalPairedSpanMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalPairedSpanKernel
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalChargedPairCoordinates
open KFCausalPairedSpanMoments
open KFCausalQuarticPlaneDomination (potential)
open KFCausalRelativeGaussianDifferential (exponent)
open KFCausalMatterOrderedDomain (pointField)

def physicalDensity (α β : ℝ) (r : ℂ) (c : Coefficients) (q : Transverse) : ℝ :=
  potential (pointField q) *
    ‖(c.1+c.2*r^2*(pairPolynomial q:ℂ))*Complex.exp (exponent α β 0 r q)‖^2

def kernel (α β : ℝ) (r : ℂ) (c : Coefficients) : ℝ :=
  ∫ q, physicalDensity α β r c q

theorem density_reconstruct (α β : ℝ) (r : ℂ) (c : Coefficients) (u : Transverse) :
    physicalDensity α β r c (reconstruct r u) = density α β c r u := by
  simp only [physicalDensity, field_reconstruct, norm_mul, mul_pow, pair_reconstruct,
    gaussian_norm_reconstruct, KFCausalChargedPairTransverseCoupling.gaussian_weight]
  unfold density pairedCoordinate KFCausalChargedPairPotentialKernel.widths
  ring

theorem kernel_formula (α β : ℝ) (r : ℂ) (c : Coefficients)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    kernel α β r c = value α β r c := by
  rw [kernel, integral_coordinates r]
  simp_rw [density_reconstruct]
  rw [value_integral α β c r hA hB hβ]
  ring

theorem exists_nonzero_profile (r : ℂ) (c : Coefficients) (hr : r ≠ 0) (hc : c ≠ 0) :
    ∃ u : Transverse, c.1+c.2*r^2*(pairedCoordinate u:ℂ) ≠ 0 := by
  by_cases h0 : c.1=0
  · have h1 : c.2 ≠ 0 := by
      intro hz
      exact hc (Prod.ext h0 hz)
    refine ⟨![1,1,0,0,0], ?_⟩
    have hp : pairedCoordinate ![1,1,0,0,0] = 1 := by
      norm_num [pairedCoordinate, Matrix.cons_val_two, Matrix.cons_val_three]
    rw [h0, hp, Complex.ofReal_one, mul_one, zero_add]
    exact mul_ne_zero h1 (pow_ne_zero 2 hr)
  · refine ⟨0, ?_⟩
    simpa only [pairedCoordinate, Pi.zero_apply, mul_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero, zero_div, Complex.ofReal_zero, add_zero] using h0

theorem density_continuous (α β : ℝ) (r : ℂ) (c : Coefficients) :
    Continuous (density α β c r) := by
  have hp : Continuous (fun u : Transverse =>
      ‖c.1+c.2*r^2*(pairedCoordinate u:ℂ)‖^2*potential (u 4+fieldSlope r*u 2)) := by
    unfold pairedCoordinate potential
    fun_prop
  exact hp.mul (KFCausalPolynomialGaussianIntegrals.weight_continuous 5 _)

theorem density_nonnegative (α β : ℝ) (r : ℂ) (c : Coefficients) (u : Transverse) :
    0 ≤ density α β c r u := by
  unfold density potential
  exact mul_nonneg (by positivity)
    (KFCausalPolynomialGaussianIntegrals.weight_positive 5 _ u).le

theorem value_positive (α β : ℝ) (r : ℂ) (c : Coefficients)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β)
    (hr : r ≠ 0) (hc : c ≠ 0) : 0 < value α β r c := by
  obtain ⟨u,hu⟩ := exists_nonzero_profile r c hr hc
  have hp : 0 < density α β c r u := by
    unfold density
    have hn : 0 < ‖c.1+c.2*r^2*(pairedCoordinate u:ℂ)‖ := norm_pos_iff.mpr hu
    have hv : 0 < potential (u 4+fieldSlope r*u 2) := by unfold potential; positivity
    exact mul_pos (mul_pos (sq_pos_of_pos hn) hv)
      (KFCausalPolynomialGaussianIntegrals.weight_positive 5 _ u)
  have hi : 0 < ∫ v, density α β c r v := integral_pos_of_integrable_nonneg_nonzero
    (f := density α β c r) (x := u)
    (density_continuous α β r c) (density_integrable α β c r hA hB hβ)
    (density_nonnegative α β r c) hp.ne'
  rw [value_integral α β c r hA hB hβ]
  exact div_pos hi (by norm_num)

theorem physicalDensity_smul (α β : ℝ) (r : ℂ) (c : Coefficients) (z : ℂ) (q : Transverse) :
    physicalDensity α β r (z • c) q = ‖z‖^2*physicalDensity α β r c q := by
  have he : ((z*c.1)+(z*c.2)*r^2*(pairPolynomial q:ℂ))*
      Complex.exp (exponent α β 0 r q) =
        z*((c.1+c.2*r^2*(pairPolynomial q:ℂ))*Complex.exp (exponent α β 0 r q)) := by ring
  change potential (pointField q) *
    ‖((z*c.1)+(z*c.2)*r^2*(pairPolynomial q:ℂ))*Complex.exp (exponent α β 0 r q)‖^2 = _
  rw [he, norm_mul, mul_pow]
  unfold physicalDensity
  ring

theorem kernel_smul (α β : ℝ) (r : ℂ) (c : Coefficients) (z : ℂ) :
    kernel α β r (z • c) = ‖z‖^2*kernel α β r c := by
  simp_rw [kernel, physicalDensity_smul, integral_const_mul]

theorem kernel_zero (α β : ℝ) (r : ℂ) : kernel α β r 0 = 0 := by
  simp [kernel, physicalDensity]

theorem kernel_nonnegative (α β : ℝ) (r : ℂ) (c : Coefficients) :
    0 ≤ kernel α β r c := by
  apply integral_nonneg
  intro q
  unfold physicalDensity potential
  positivity

#print axioms density_reconstruct
#print axioms kernel_formula
#print axioms exists_nonzero_profile
#print axioms density_continuous
#print axioms density_nonnegative
#print axioms value_positive
#print axioms physicalDensity_smul
#print axioms kernel_smul
#print axioms kernel_zero
#print axioms kernel_nonnegative
end
end UnifiedTheory.Audit.KFCausalPairedSpanKernel
