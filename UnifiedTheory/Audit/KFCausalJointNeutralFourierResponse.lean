/- The complete physical frozen-coefficient transport response is the
clock derivative of the newly proved positive Fourier energy integral.
No derivative is exchanged with that integral without justification, and
no dissipative or uniform bound is inferred from this identity. -/
import UnifiedTheory.Audit.KFCausalJointNeutralFourierIntegral
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPotentialTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointNeutralFourierResponse
noncomputable section
open MeasureTheory
open KFCausalJointNeutralFourierIntegral (frequencySlice)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalNeutralClockDerivative (totalEnergy totalResponse)
open KFCausalReciprocalNeutralPositiveEnergy (coefficients)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

def energy (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) : ℝ :=
  Real.pi/4*(∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
    frequencySlice n β w b c P r (chart α r (u^2+v^2) Y) v k)

theorem energy_nonnegative (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) : 0 ≤ energy n α β w b c P r := by
  unfold energy
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro Y
  apply integral_nonneg
  intro u
  apply integral_nonneg
  intro v
  exact integral_nonneg (fun k => KFCausalJointNeutralFourierIntegral.frequencySlice_nonnegative n β w b c P r _ v k)

variable (n : ℕ) (ε y α β : ℝ) (w : Fin n → ℝ) (b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (c : ℝ → Fin n → ℂ)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
  (hwidth : 32*β ≤ α) (hw : ∀ i, 1 ≤ w i)
include hε hy hα hβ hwidth hw

theorem energy_eq_total (s : ℝ) :
    energy n α β w b (c s) P (scale ε y s) = totalEnergy n ε y α β w b P c s := by
  have he := KFCausalJointNeutralFourierIntegral.actual_pairing_integral n β w b (c s) P
    α ε y s hα hβ hwidth hε hy hw
  rw [KFCausalReciprocalNeutralKernelDerivative.pairing_totalEnergy n ε y α β w b P c hε hy hα hβ hwidth hw] at he
  exact (Complex.ofReal_injective he).symm

theorem energy_derivative (hc : ∀ i, ContDiff ℝ 1 (fun s => c s i)) (s : ℝ) :
    HasDerivAt (fun t => energy n α β w b (c t) P (scale ε y t))
      (totalResponse n ε y α β w b P c s) s := by
  have he : (fun t => energy n α β w b (c t) P (scale ε y t)) = totalEnergy n ε y α β w b P c :=
    funext (energy_eq_total n ε y α β w b P c hε hy hα hβ hwidth hw)
  rw [he]
  exact KFCausalReciprocalNeutralClockDerivative.total_derivative n ε y α β w b P c hε hy hα hβ hwidth hw hc s

omit n ε y α β w b P c hε hy hα hβ hwidth hw in
theorem actual_transport_fourier (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ)
    (C b : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    KFCausalReciprocalNeutralWholeClock.transportResponse n ε h a w p C b P s =
      deriv (fun t => energy n (groundWidth h) (neutralWidth h) w b
        (coefficients n ε h a p C s) P (scale ε (-h/2) t)) s := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  rw [KFCausalReciprocalNeutralWholeClock.transport_frozen_derivative n ε h a w p C b P hε hh hw hb]
  exact (energy_derivative n ε (-h/2) (groundWidth h) (neutralWidth h) w b P
    (fun _ => coefficients n ε h a p C s) hε hy (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hw (fun _ => contDiff_const) s).deriv.symm

omit n ε y α β w b P c hε hy hα hβ hwidth hw in
theorem actual_slice_fourier (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ)
    (C b : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    KFCausalReciprocalNeutralPositiveEnergy.positiveSlice n ε h a w p C b P s =
      energy n (groundWidth h) (neutralWidth h) w b
        (coefficients n ε h a p C s) P (scale ε (-h/2) s) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  exact congrArg (fun x : ℝ => Real.pi/4*x)
    (KFCausalJointNeutralFourierIntegral.actual_positive_integral n (neutralWidth h) w b
      (coefficients n ε h a p C s) P (groundWidth h) ε (-h/2) s
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hw)

omit n ε y α β w b P c hε hy hα hβ hwidth hw in
theorem actual_reduced_fourier (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ)
    (C b : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    KFCausalReciprocalNeutralWholeClock.reducedResponse n ε h a w p C b P s =
      KFCausalClockResponseTransport.coefficient ε (-h/2) s*
        energy n (groundWidth h) (neutralWidth h) w b (coefficients n ε h a p C s) P (scale ε (-h/2) s)-
      deriv (fun t => energy n (groundWidth h) (neutralWidth h) w b
        (coefficients n ε h a p C s) P (scale ε (-h/2) t)) s/KFCausalClockResponseTransport.clock ε s := by
  rw [KFCausalReciprocalNeutralWholeClock.reducedResponse,
    actual_slice_fourier n ε h a w p C b P hε hh hw hb,
    actual_transport_fourier n ε h a w p C b P hε hh hw hb]

omit n ε y α β w b P c hε hy hα hβ hwidth hw in
theorem actual_potential_fourier (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ)
    (C b : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) :
    KFCausalReciprocalNeutralPotentialTransport.potentialResponse n ε h a w p C b P hε ha hh hw hb =
      ∫ s, KFCausalClockResponseTransport.coefficient ε (-h/2) s*
        energy n (groundWidth h) (neutralWidth h) w b (coefficients n ε h a p C s) P (scale ε (-h/2) s)-
      deriv (fun t => energy n (groundWidth h) (neutralWidth h) w b
        (coefficients n ε h a p C s) P (scale ε (-h/2) t)) s/KFCausalClockResponseTransport.clock ε s := by
  rw [KFCausalReciprocalNeutralPotentialTransport.potentialResponse_reduced_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (actual_reduced_fourier n ε h a w p C b P hε hh hw hb)

#print axioms energy_nonnegative
#print axioms energy_eq_total
#print axioms energy_derivative
#print axioms actual_transport_fourier
#print axioms actual_slice_fourier
#print axioms actual_reduced_fourier
#print axioms actual_potential_fourier
end
end UnifiedTheory.Audit.KFCausalJointNeutralFourierResponse
