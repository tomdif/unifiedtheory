/- The normalized fundamental SU(2) Wilson crossing kernel has an exact
constant Haar mode. Subtracting this mode preserves positive definiteness.
Its inverse is bounded by the already proved polynomial Gaussian-mass cap.
This is an integral-form floor, not a pointwise lower bound on the kernel. -/
import UnifiedTheory.Clay.YangMills.CompactKernelMeanFloor
import UnifiedTheory.Clay.YangMills.SU2GaussianMass
import UnifiedTheory.Clay.YangMills.WilsonEnergyDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2CrossingHaarFloor
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonCrossingKernel
open PositiveKernelForm SU2HaarTilt

local instance haar_left : haar.IsMulLeftInvariant := by
  unfold haar RegulatedGauge.compactHaar
  infer_instance

def kernel (β : ℝ) (x y : Q) : ℝ := SU2GaussianMass.weight β (x⁻¹ * y)

theorem kernel_eq_crossing (β : ℝ) (x y : Q) :
    kernel β x y = Real.exp (-2 * β) *
      crossingKernel WilsonEnergyDensity.representation β x y := by
  unfold kernel SU2GaussianMass.weight crossingKernel
  rw [WilsonEnergyDensity.representation_character, WilsonSingleLinkStaples.character_re,
    SU2GaussianMass.chord_square, ← Real.exp_add]
  congr 1
  ring

theorem kernel_continuous (β : ℝ) :
    Continuous (fun xy : Q × Q => kernel β xy.1 xy.2) :=
  (SU2GaussianMass.weight_continuous β).comp (continuous_fst.inv.mul continuous_snd)

def positiveKernel (β : ℝ) (hβ : 0 ≤ β) : PositiveKernel Q where
  value xy := (kernel β xy.1 xy.2 : ℂ)
  positive N x z := by
    have hp := crossingKernel_positive WilsonEnergyDensity.representation β hβ x z
    have he : complexQuadratic (fun i j => kernel β (x i) (x j)) z =
        (Real.exp (-2 * β) : ℂ) * complexQuadratic
          (fun i j => crossingKernel WilsonEnergyDensity.representation β (x i) (x j)) z := by
      simp only [kernel_eq_crossing, WilsonSlabPositivity.complexQuadratic_scale]
    have him : (complexQuadratic (fun i j => kernel β (x i) (x j)) z).im = 0 := by
      rw [he, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hp.2]
      ring
    have hre : 0 ≤ (complexQuadratic (fun i j => kernel β (x i) (x j)) z).re := by
      rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (Real.exp_pos _).le hp.1
    simpa only [CountableCorrelationCompactness.gramValue, complexQuadratic, mul_right_comm]
      using And.intro him hre

theorem positiveKernel_continuous (β : ℝ) (hβ : 0 ≤ β) :
    Continuous (positiveKernel β hβ).value :=
  Complex.continuous_ofReal.comp (kernel_continuous β)

theorem row_mass (β : ℝ) (x : Q) :
    (∫ y, kernel β x y ∂haar) = SU2GaussianMass.mass β :=
  integral_mul_left_eq_self (SU2GaussianMass.weight β) x⁻¹

theorem positiveKernel_row (β : ℝ) (hβ : 0 ≤ β) (x : Q) :
    (∫ y, (positiveKernel β hβ).value (x, y) ∂haar) =
      (SU2GaussianMass.mass β : ℂ) := by
  change (∫ y, (kernel β x y : ℂ) ∂haar) = _
  rw [integral_complex_ofReal, row_mass]

def remainder (β : ℝ) (hβ : 0 ≤ β) : PositiveKernel Q :=
  CompactKernelMeanFloor.centeredKernel haar (positiveKernel β hβ)

theorem remainder_value (β : ℝ) (hβ : 0 ≤ β) (x y : Q) :
    (remainder β hβ).value (x, y) =
      ((kernel β x y - SU2GaussianMass.mass β : ℝ) : ℂ) := by
  exact (CompactKernelMeanFloor.centeredKernel_value haar (positiveKernel β hβ)
    (positiveKernel_continuous β hβ) _ (positiveKernel_row β hβ) x y).trans
      (Complex.ofReal_sub _ _).symm

theorem remainder_continuous (β : ℝ) (hβ : 0 ≤ β) :
    Continuous (remainder β hβ).value :=
  CompactKernelMeanFloor.centeredKernel_continuous haar (positiveKernel β hβ)
    (positiveKernel_continuous β hβ)

theorem inverse_mass_le (β : ℝ) (hβ : 3 / 4 ≤ β) :
    (SU2GaussianMass.mass β)⁻¹ ≤ SU2GaussianMass.cap β := by
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (SU2GaussianMass.mass_pos β)).mpr
  simpa only [mul_comm] using SU2GaussianMass.mass_cap_lower β hβ

end
end UnifiedTheory.Clay.YangMills.SU2CrossingHaarFloor
