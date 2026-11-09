/- The pure exponential-tilt response is absolutely integrable in all
charged and Fourier variables, and its complete integral obeys the
uniform energy bound. This is one component of the full response. -/
import UnifiedTheory.Audit.KFCausalJointFourierFrequencyDomain
import UnifiedTheory.Audit.KFCausalJointFourierChargedTiltBound
import UnifiedTheory.Audit.KFCausalJointFourierDilationQuartic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000

namespace UnifiedTheory.Audit.KFCausalJointFourierFullTiltBound
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalJointFourierFrequencyDomain (amplitude)
open KFCausalJointFourierMatrixIntegral (density)
open KFCausalJointFourierChargedTiltBound (chargedTilt)
open KFCausalJointFourierMomentMatrix (matrixEnergy)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalClockFloorRelativeShift (scale)

local instance : SFinite chargedMeasure := by unfold chargedMeasure; infer_instance

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r : ℂ)

theorem density_amplitude (hβ : 0 < β) (q : Charged × ℝ) :
    density n β w b c P α r q = ‖amplitude n α β w b c P r 0 q‖^2+
      ‖amplitude n α β w b c P r 1 q‖^2/2+‖amplitude n α β w b c P r 2 q‖^2/4 := by
  unfold density
  rw [← KFCausalJointFourierQuadraticJet.frequencySlice_jet n β w b c P hβ]
  simp only [KFCausalJointNeutralFourierIntegral.frequencySlice,
    KFCausalNeutralFourierEnergy.frequencyDensity,KFCausalNeutralFourierEnergy.frequencyMoment,
    amplitude,KFCausalJointFourierFrequencyDomain.spatial,
    KFCausalNeutralFourierField.fieldLine_fourier_square n β hβ]

theorem field_tilt_integrable (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) (j : ℕ) :
    Integrable (fun q : Charged × ℝ => q.1.1.2*q.2*‖amplitude n α β w b c P r j q‖^2)
      (chargedMeasure.prod volume) := by
  have hv := KFCausalJointFourierFrequencyDomain.amplitude_weighted_memLp
    n α β w b c P r hβ hA hC 1 j
  have hk := KFCausalJointFourierFrequencyDomain.amplitude_frequency_memLp
    n α β w b c P r hβ hA hC j
  simp only [pow_one] at hv
  apply (hv.star.integrable_mul hk).re.congr
  filter_upwards [] with q
  change (star ((q.1.1.2:ℂ)*amplitude n α β w b c P r j q)*
    ((q.2:ℂ)*amplitude n α β w b c P r j q)).re = _
  simp only [Complex.star_def,map_mul,Complex.conj_ofReal]
  rw [show (q.1.1.2:ℂ)*conj (amplitude n α β w b c P r j q)*
      ((q.2:ℂ)*amplitude n α β w b c P r j q) =
      ((q.1.1.2*q.2:ℝ):ℂ)*(conj (amplitude n α β w b c P r j q)*
        amplitude n α β w b c P r j q) by push_cast; ring]
  rw [Complex.conj_mul',← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]

theorem tilt_density_integrable (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) :
    Integrable (fun q : Charged × ℝ => (-8*Real.pi*q.2*r.im*q.1.1.2)*
      density n β w b c P α r q) (chargedMeasure.prod volume) := by
  have hi := field_tilt_integrable n α β w b c P r hβ hA hC
  have hs := (((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)).const_mul (-8*Real.pi*r.im)
  apply hs.congr
  filter_upwards [] with q
  rw [density_amplitude n α β w b c P r hβ]
  simp only [Pi.add_apply]
  ring

theorem chargedTilt_integrable (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) :
    Integrable (chargedTilt n β w b c P α r) :=
  (tilt_density_integrable n α β w b c P r hβ hA hC).integral_prod_right

omit n w b c P r in
theorem actual_widths (ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (w : ℝ) (hw : 1 ≤ w) :
    0 < (w*α)*area (scale ε y s) ∧
      0 < (w*α)*area (scale ε y s)-8*β*(scale ε y s).im^2 := by
  have hp := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _
    (KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy)
  exact KFCausalJointFourierDilationQuartic.width_floors α (scale ε y s) w β hw hp.2 hp.1

theorem actual_tilt_integrable (ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) :
    Integrable (chargedTilt n β w b c P α (scale ε y s)) := by
  have hi (i : Fin n) := actual_widths α β ε y s hα hβ hwidth hε hy (w i) (hw i)
  exact chargedTilt_integrable n α β w b c P _ hβ (fun i => (hi i).1) (fun i => (hi i).2)

theorem full_tilt_lower (ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) :
    -2400*KFCausalJointFourierQuadraticJet.energy n β w b c P α (scale ε y s) ≤
      Real.pi/4*(∫ k : ℝ, chargedTilt n β w b c P α (scale ε y s) k) := by
  have hm := KFCausalJointFourierMatrixIntegral.matrix_integrable n β w b c P
    α ε y s hα hβ hwidth hε hy hw
  have ht := actual_tilt_integrable n α β w b c P ε y s hα hβ hwidth hε hy hw
  have he := integral_mono (hm.const_mul (-2400)) ht (fun k =>
    KFCausalJointFourierChargedTiltBound.actual_clock_charged_tilt_lower
      n β w b c P α ε y s hα hβ hε hy hw k)
  rw [integral_const_mul] at he
  rw [KFCausalJointFourierMatrixIntegral.energy_matrix_integral n β w b c P
    α ε y s hα hβ hwidth hε hy hw]
  nlinarith [Real.pi_pos]

#print axioms density_amplitude
#print axioms field_tilt_integrable
#print axioms tilt_density_integrable
#print axioms chargedTilt_integrable
#print axioms actual_widths
#print axioms actual_tilt_integrable
#print axioms full_tilt_lower
end
end UnifiedTheory.Audit.KFCausalJointFourierFullTiltBound
