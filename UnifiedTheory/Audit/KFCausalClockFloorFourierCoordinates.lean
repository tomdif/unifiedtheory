/- The revised clock-floor transport is diagonal in an actual full
six-dimensional Fourier unitary, with the physical 2*pi normalization. -/
import UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
import UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization (fourier_clock_translation clock_phase)

def coupledFourier (ε : ℝ) (hε : 0 < ε) : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert :=
  (coordinates ε hε).symm.trans fourierCoordinates

theorem coupledFourier_apply (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    coupledFourier ε hε f = fourierCoordinates ((coordinates ε hε).symm f) := rfl

theorem coordinates_symm_transport (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    (coordinates ε hε).symm (transport ε hε t f) = translation t ((coordinates ε hε).symm f) := by
  rw [transport_apply,LinearIsometryEquiv.symm_apply_apply]

theorem coupledFourier_transport (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    coupledFourier ε hε (transport ε hε t f) =
      KFCausalFourierTranslation.phaseAction (t • clockVector) (coupledFourier ε hε f) := by
  rw [coupledFourier_apply,coordinates_symm_transport,fourier_clock_translation]
  rfl

theorem coupledFourier_transport_coe (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    coupledFourier ε hε (transport ε hε t f) =ᵐ[volume]
      fun k => Complex.exp ((2*Real.pi*t*k 0:ℝ)*Complex.I)*(coupledFourier ε hε f) k := by
  rw [coupledFourier_transport]
  filter_upwards [KFCausalFourierTranslation.phaseAction_coe (t • clockVector) (coupledFourier ε hε f)] with k hk
  rw [hk,clock_phase]

#print axioms coupledFourier
#print axioms coupledFourier_apply
#print axioms coordinates_symm_transport
#print axioms coupledFourier_transport
#print axioms coupledFourier_transport_coe

end
end UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
