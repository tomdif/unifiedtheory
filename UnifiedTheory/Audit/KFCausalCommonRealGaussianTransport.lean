/- The common-real-source, constant-neutral-polynomial response bound on the
original transported-state slice. Coefficients are frozen at the evaluation
clock. This is the geometric transport component, not their clock derivative. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianResponse
import UnifiedTheory.Audit.KFCausalJointNeutralFourierResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianTransport
noncomputable section
open KFCausalReciprocalNeutralPositiveEnergy (coefficients positiveSlice)
open KFCausalReciprocalNeutralClockDerivative (totalEnergy)
open KFCausalReciprocalNeutralWholeClock (transportResponse)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)

theorem frozen_energy_eq (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ)
    (C b : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    totalEnergy n ε (-h/2) (groundWidth h) (neutralWidth h) w b P
      (fun _ => coefficients n ε h a p C s) s = positiveSlice n ε h a w p C b P s := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  rw [KFCausalJointNeutralFourierResponse.actual_slice_fourier n ε h a w p C b P hε hh hw hb s]
  exact (KFCausalJointNeutralFourierResponse.energy_eq_total n ε (-h/2)
    (groundWidth h) (neutralWidth h) w b P (fun _ => coefficients n ε h a p C s)
    hε hy (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) hw s).symm

theorem transport_bound (n : ℕ) (ε h B : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
    (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    transportResponse n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s ≤
      536*fraction ε s*positiveSlice n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) s := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  rw [KFCausalReciprocalNeutralWholeClock.transport_frozen_derivative n ε h a w p C
    (fun _ => (B:ℂ)) (fun _ => 1) hε hh hw hb s]
  have he := KFCausalCommonRealGaussianResponse.total_response_bound n (groundWidth h)
    (neutralWidth h) ε (-h/2) s B w (coefficients n ε h a p C s)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hw
  rw [frozen_energy_eq n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) hε hh hw hb s] at he
  exact he

#print axioms frozen_energy_eq
#print axioms transport_bound
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianTransport
