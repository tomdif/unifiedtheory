/- The complete original quartic energy has a full integrable charged
dilation response. Its integral is exactly minus four times the rate
and the original positive energy, with arbitrary finite interference. -/
import UnifiedTheory.Audit.KFCausalJointFourierDilationResponse
import UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalJointFourierDilationQuartic
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalJointFourierDilationRepresentation (fieldDensity)
open KFCausalJointFourierDilationResponse (response)
open KFCausalReciprocalGaussianCoordinates (area)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r : ℂ) (ell : ℝ)

def quartic (p : Joint) : ℝ :=
  response n α β w b c P r ell 0 p+response n α β w b c P r ell 1 p/2+
    response n α β w b c P r ell 2 p/4

theorem density_identity (p : Joint) :
    positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 (P i)) p =
      fieldDensity n α β w b c P r ell 0 0 p+
        fieldDensity n α β w b c P r ell 0 1 p/2+
        fieldDensity n α β w b c P r ell 0 2 p/4 := by
  have hp : ((p.1.1,![p.1.2 0,p.1.2 1]),p.2) = p := by
    congr 2
    ext i
    fin_cases i <;> rfl
  have h := KFCausalJointNeutralFourierOuterDensity.density_quartic n α β w b c P r
    p.1.1 (p.1.2 0) (p.1.2 1) p.2
  rw [hp] at h
  simpa only [KFCausalJointFourierDilationRepresentation.density_zero,KFCausalClusteredClockFactors.Z] using h

variable (hβ : 0 < β) (hA : ∀ i, 0 < (w i*α)*area r)
  (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2)
include hβ hA hC

theorem integrable : Integrable (quartic n α β w b c P r ell) jointMeasure := by
  have h := KFCausalJointFourierDilationResponse.response_integrable n α β w b c P r ell hβ hA hC
  exact ((h 0).add ((h 1).div_const 2)).add ((h 2).div_const 4)

theorem density_integrable :
    Integrable (positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 (P i))) jointMeasure := by
  have h := KFCausalJointFourierDilationResponse.density_integrable n α β w b c P r 0 hβ hA hC
  change Integrable (fun p => positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 (P i)) p) jointMeasure
  simp_rw [density_identity n α β w b c P r 0]
  exact ((h 0).add ((h 1).div_const 2)).add ((h 2).div_const 4)

theorem integral_identity :
    (∫ p, quartic n α β w b c P r ell p ∂jointMeasure) =
      -4*ell*(∫ p, positiveDensity n α β w r c
        (fun i => exponentialProfile (b i) 1 (P i)) p ∂jointMeasure) := by
  have hr := KFCausalJointFourierDilationResponse.response_integrable n α β w b c P r ell hβ hA hC
  have hd := KFCausalJointFourierDilationResponse.density_integrable n α β w b c P r ell hβ hA hC
  have hrs := integral_add ((hr 0).add ((hr 1).div_const 2)) ((hr 2).div_const 4)
  have hds := integral_add ((hd 0).add ((hd 1).div_const 2)) ((hd 2).div_const 4)
  simp only [Pi.add_apply] at hrs hds
  unfold quartic
  rw [hrs,
    integral_add (hr 0) ((hr 1).div_const 2),integral_div,integral_div]
  simp_rw [KFCausalJointFourierDilationResponse.response_integral n α β w b c P r ell hβ hA hC,
    density_identity n α β w b c P r ell]
  rw [hds,
    integral_add (hd 0) ((hd 1).div_const 2),integral_div,integral_div]
  ring

omit n β w b c P ell hβ hA hC in
theorem width_floors (w β : ℝ) (hw : 1 ≤ w)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    0 < (w*α)*area r ∧ 0 < (w*α)*area r-8*β*r.im^2 := by
  have hm := mul_le_mul_of_nonneg_right hw hA.le
  simp only [one_mul] at hm
  constructor
  · simpa only [mul_assoc] using hA.trans_le hm
  · have he : α*area r-8*β*r.im^2 ≤ w*(α*area r)-8*β*r.im^2 := sub_le_sub_right hm _
    simpa only [mul_assoc] using hC.trans_le he

#print axioms density_identity
#print axioms integrable
#print axioms density_integrable
#print axioms integral_identity
#print axioms width_floors
end
end UnifiedTheory.Audit.KFCausalJointFourierDilationQuartic
