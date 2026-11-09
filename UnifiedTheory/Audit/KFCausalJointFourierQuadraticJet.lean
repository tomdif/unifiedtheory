/- The three neutral Fourier moments represent the complete original
positive energy, including both field weights and all interference.
No estimate on the resulting charged moment matrix is assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierQuadraticJet
import UnifiedTheory.Audit.KFCausalJointNeutralFourierResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalJointFourierQuadraticJet
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralFourierQuadraticJet (packetMoment jetEnergy)
open KFCausalNeutralFourierField (spectrum)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalJointNeutralFourierIntegral (frequencySlice)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalClockFloorRelativeShift (scale)

def complexShear (r : ℂ) : ℂ := (fieldSlope r:ℂ)-(2*r.im:ℝ)*Complex.I

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ)

def chargedJet (j : ℕ) (z : ℂ) (k : ℝ) : ℂ :=
  ∑ i, coefficients n w c z i*(𝓕 (packetMoment β (b i) (P i) j)) k

def jetSlice (r z : ℂ) (v k : ℝ) : ℝ :=
  Real.exp (-8*Real.pi*k*r.im*v)*jetEnergy (complexShear r*(v:ℂ))
    (chargedJet n β w b c P 0 z k) (chargedJet n β w b c P 1 z k)
    (chargedJet n β w b c P 2 z k)

theorem chargedJet_spectrum (hβ : 0 < β) (j : ℕ) (z : ℂ) (k : ℝ) :
    chargedJet n β w b c P j z k = spectrum n β b (coefficients n w c z) P j 0 k := by
  exact (KFCausalNeutralFourierQuadraticJet.spectrum_sum n β b (coefficients n w c z) P hβ j k).symm

theorem frequencySlice_jet (hβ : 0 < β) (r z : ℂ) (v k : ℝ) :
    frequencySlice n β w b c P r z v k = jetSlice n β w b c P r z v k := by
  unfold frequencySlice jetSlice
  rw [KFCausalNeutralFourierQuadraticJet.frequencyDensity_jet n β b (coefficients n w c z) P hβ]
  simp_rw [chargedJet_spectrum n β w b c P hβ]
  congr 2
  · ring
  · unfold complexShear
    push_cast
    ring

theorem jetSlice_nonnegative (r z : ℂ) (v k : ℝ) :
    0 ≤ jetSlice n β w b c P r z v k := by
  unfold jetSlice jetEnergy
  positivity

theorem jetSlice_integrable (hβ : 0 < β) (r z : ℂ) (v : ℝ) :
    Integrable (jetSlice n β w b c P r z v) := by
  have he : jetSlice n β w b c P r z v = frequencySlice n β w b c P r z v :=
    funext (fun k => (frequencySlice_jet n β w b c P hβ r z v k).symm)
  rw [he]
  exact KFCausalJointNeutralFourierIntegral.frequencySlice_integrable n β w b c P hβ r z v

def energy (α : ℝ) (r : ℂ) : ℝ :=
  Real.pi/4*(∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
    jetSlice n β w b c P r (chart α r (u^2+v^2) Y) v k)

theorem energy_eq_fourier (hβ : 0 < β) (α : ℝ) (r : ℂ) :
    energy n β w b c P α r = KFCausalJointNeutralFourierResponse.energy n α β w b c P r := by
  unfold energy KFCausalJointNeutralFourierResponse.energy
  simp_rw [frequencySlice_jet n β w b c P hβ]

theorem energy_eq_total (ε y α : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α) (hw : ∀ i, 1 ≤ w i) (s : ℝ) :
    energy n β w b c P α (scale ε y s) =
      KFCausalReciprocalNeutralClockDerivative.totalEnergy n ε y α β w b P (fun _ => c) s := by
  rw [energy_eq_fourier n β w b c P hβ]
  exact KFCausalJointNeutralFourierResponse.energy_eq_total n ε y α β w b P
    (fun _ => c) hε hy hα hβ hwidth hw s

theorem energy_derivative (ε y α : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α) (hw : ∀ i, 1 ≤ w i) (s : ℝ) :
    HasDerivAt (fun t => energy n β w b c P α (scale ε y t))
      (KFCausalReciprocalNeutralClockDerivative.totalResponse n ε y α β w b P (fun _ => c) s) s := by
  have he : (fun t => energy n β w b c P α (scale ε y t)) =
      fun t => KFCausalJointNeutralFourierResponse.energy n α β w b c P (scale ε y t) :=
    funext (fun t => energy_eq_fourier n β w b c P hβ α (scale ε y t))
  rw [he]
  exact KFCausalJointNeutralFourierResponse.energy_derivative n ε y α β w b P
    (fun _ => c) hε hy hα hβ hwidth hw (fun _ => contDiff_const) s

#print axioms chargedJet_spectrum
#print axioms frequencySlice_jet
#print axioms jetSlice_nonnegative
#print axioms jetSlice_integrable
#print axioms energy_eq_fourier
#print axioms energy_eq_total
#print axioms energy_derivative
end
end UnifiedTheory.Audit.KFCausalJointFourierQuadraticJet
