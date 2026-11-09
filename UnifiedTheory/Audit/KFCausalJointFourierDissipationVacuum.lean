/- The field-free neutral Fourier sector contracts when the squared
imaginary translation contracts, after pairing opposite charged angles.
This retains all neutral sources and degrees. It does not include the
quadratic or quartic physical field weights. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierEnergy
import UnifiedTheory.Audit.KFCausalJointNeutralClockTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointFourierDissipationVacuum
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralFourierShift (line)
open KFCausalNeutralFourierField (spectrum fieldPolynomial fieldLine)
open KFCausalNeutralFourierEnergy (frequencyMoment)
open KFCausalJointNeutralClockTransport (imaginaryArea)
open KFCausalReciprocalWedgeGeometry (first)

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def pairedDensity (y k : ℝ) : ℝ :=
  frequencyMoment n β b c P 0 0 y k+frequencyMoment n β b c P 0 0 (-y) k

theorem zero_spectrum (q : ℂ) :
    spectrum n β b c P 0 q = 𝓕 (line n β b c P 0) := by
  simp only [KFCausalNeutralFourierField.spectrum,fieldPolynomial,pow_zero,one_mul]

theorem pairedDensity_cosh (y k : ℝ) :
    pairedDensity n β b c P y k =
      2*Real.cosh (4*Real.pi*k*y)*‖(𝓕 (line n β b c P 0)) k‖^2 := by
  unfold pairedDensity frequencyMoment
  simp only [zero_spectrum]
  rw [Real.cosh_eq]
  ring_nf

theorem pairedDensity_mono (y₁ y₂ k : ℝ) (hy : y₁^2 ≤ y₂^2) :
    pairedDensity n β b c P y₁ k ≤ pairedDensity n β b c P y₂ k := by
  rw [pairedDensity_cosh,pairedDensity_cosh]
  have ha : |y₁| ≤ |y₂| := by nlinarith [sq_abs y₁,sq_abs y₂,abs_nonneg y₁,abs_nonneg y₂]
  have hm : |4*Real.pi*k*y₁| ≤ |4*Real.pi*k*y₂| := by
    simpa only [abs_mul] using mul_le_mul_of_nonneg_left ha (abs_nonneg (4*Real.pi*k))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.cosh_le_cosh.mpr hm) (by norm_num)) (sq_nonneg _)

theorem pairedDensity_integrable (hβ : 0 < β) (y : ℝ) :
    Integrable (pairedDensity n β b c P y) :=
  (KFCausalNeutralFourierEnergy.frequencyMoment_integrable n β b c P hβ 0 0 y).add
    (KFCausalNeutralFourierEnergy.frequencyMoment_integrable n β b c P hβ 0 0 (-y))

theorem paired_integral_mono (hβ : 0 < β) (y₁ y₂ : ℝ) (hy : y₁^2 ≤ y₂^2) :
    (∫ k, pairedDensity n β b c P y₁ k) ≤ ∫ k, pairedDensity n β b c P y₂ k :=
  integral_mono (pairedDensity_integrable n β b c P hβ y₁)
    (pairedDensity_integrable n β b c P hβ y₂)
    (pairedDensity_mono n β b c P y₁ y₂ · hy)

theorem paired_physical_integral (hβ : 0 < β) (y : ℝ) :
    (∫ x, ‖line n β b c P y x‖^2)+(∫ x, ‖line n β b c P (-y) x‖^2) =
      ∫ k, pairedDensity n β b c P y k := by
  have hp := KFCausalNeutralFourierEnergy.field_plancherel n β b c P hβ 0 0 y
  have hm := KFCausalNeutralFourierEnergy.field_plancherel n β b c P hβ 0 0 (-y)
  simp only [fieldLine,pow_zero,one_mul] at hp hm
  unfold pairedDensity
  rw [hp,hm,integral_add
    (KFCausalNeutralFourierEnergy.frequencyMoment_integrable n β b c P hβ 0 0 y)
    (KFCausalNeutralFourierEnergy.frequencyMoment_integrable n β b c P hβ 0 0 (-y))]

theorem paired_physical_contraction (hβ : 0 < β) (y₁ y₂ : ℝ) (hy : y₁^2 ≤ y₂^2) :
    (∫ x, ‖line n β b c P y₁ x‖^2)+(∫ x, ‖line n β b c P (-y₁) x‖^2) ≤
      (∫ x, ‖line n β b c P y₂ x‖^2)+(∫ x, ‖line n β b c P (-y₂) x‖^2) := by
  rw [paired_physical_integral n β b c P hβ y₁,paired_physical_integral n β b c P hβ y₂]
  exact paired_integral_mono n β b c P hβ y₁ y₂ hy

omit n β b c P in
theorem imaginary_radius_square (α : ℝ) (r z : ℂ) (θ : ℝ)
    (hX : 0 ≤ first α r z) :
    (2*r.im*Real.sqrt (first α r z)*Real.cos θ)^2 =
      imaginaryArea α r z*(Real.cos θ)^2 := by
  rw [mul_pow,mul_pow,Real.sq_sqrt hX]
  unfold imaginaryArea
  ring

theorem fixed_charged_paired_contraction (hβ : 0 < β) (α : ℝ) (r₁ r₂ z : ℂ) (θ : ℝ)
    (hX₁ : 0 ≤ first α r₁ z) (hX₂ : 0 ≤ first α r₂ z)
    (hI : imaginaryArea α r₁ z ≤ imaginaryArea α r₂ z) :
    (∫ k, pairedDensity n β b c P (2*r₁.im*Real.sqrt (first α r₁ z)*Real.cos θ) k) ≤
      ∫ k, pairedDensity n β b c P (2*r₂.im*Real.sqrt (first α r₂ z)*Real.cos θ) k := by
  apply paired_integral_mono n β b c P hβ
  rw [imaginary_radius_square α r₁ z θ hX₁,imaginary_radius_square α r₂ z θ hX₂]
  exact mul_le_mul_of_nonneg_right hI (sq_nonneg _)

#print axioms zero_spectrum
#print axioms pairedDensity_cosh
#print axioms pairedDensity_mono
#print axioms pairedDensity_integrable
#print axioms paired_integral_mono
#print axioms paired_physical_integral
#print axioms paired_physical_contraction
#print axioms imaginary_radius_square
#print axioms fixed_charged_paired_contraction
end
end UnifiedTheory.Audit.KFCausalJointFourierDissipationVacuum
