/- Actual all-L2 Fourier representatives of transverse shear, in both
canonical and coupled clock coordinates. Clock frequency stays fixed. -/
import UnifiedTheory.Audit.KFCausalL2FourierLinearChange
import UnifiedTheory.Audit.KFCausalTransverseShearEuclidean
import UnifiedTheory.Audit.KFCausalTransverseShearClockCommutation
import UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 30000

namespace UnifiedTheory.Audit.KFCausalTransverseShearFourier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalTransverseShearTransport (transport)
open UnifiedTheory.Audit.KFCausalTransverseShearEuclidean
open UnifiedTheory.Audit.KFCausalFourierLinearChange
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)

def coefficient (t : ℝ) : ℂ := (Real.exp t:ℂ)*(jacobian (linearFlow t):ℂ)

private theorem coordinates_result (F : FrequencyHilbert ≃ₗᵢ[ℂ] FrequencyHilbert)
    (t : ℝ) (f : Hilbert)
    (hr : F (euclideanTransport t (euclideanPullback f)) =ᵐ[volume]
      fun k => coefficient t*(F (euclideanPullback f)) (dualEquiv (linearFlow t) k)) :
    (euclideanPullback.trans F) (transport t f) =ᵐ[volume]
      fun k => coefficient t*((euclideanPullback.trans F) f) (dualEquiv (linearFlow t) k) := by
  change F (euclideanPullback (transport t f)) =ᵐ[volume] _
  have he := congrArg (fun v : FrequencyHilbert => (F v : Space → ℂ))
    (euclideanTransport_coordinates t f).symm
  exact (Filter.EventuallyEq.of_eq he).trans hr

theorem fourier_coe (t : ℝ) (f : Hilbert) :
    fourierCoordinates (transport t f) =ᵐ[volume]
      fun k => coefficient t*(fourierCoordinates f) (dualEquiv (linearFlow t) k) := by
  apply coordinates_result (Lp.fourierTransformₗᵢ Space ℂ) t f
  exact KFCausalL2FourierLinearChange.fourier_unitary_coe (linearFlow t) (Real.exp t:ℂ)
    (euclideanTransport t) (euclideanTransport_coe t) (euclideanPullback f)

private theorem commuted_coordinates (P : Hilbert ≃ₗᵢ[ℂ] Hilbert)
    (F : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert) (S : Hilbert ≃ₗᵢ[ℂ] Hilbert)
    (w : ℂ) (e : Space → Space)
    (hc : ∀ f, P (S f) = S (P f))
    (hr : ∀ f, F (S f) =ᵐ[volume] fun k => w*(F f) (e k)) (f : Hilbert) :
    (P.trans F) (S f) =ᵐ[volume] fun k => w*((P.trans F) f) (e k) := by
  change F (P (S f)) =ᵐ[volume] _
  rw [hc f]
  exact hr (P f)

theorem coupled_fourier_coe (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    coupledFourier ε hε (transport t f) =ᵐ[volume]
      fun k => coefficient t*(coupledFourier ε hε f) (dualEquiv (linearFlow t) k) := by
  exact commuted_coordinates (KFCausalClockFloorUnitaryCoordinates.coordinates ε hε).symm
    fourierCoordinates (transport t) (coefficient t) (dualEquiv (linearFlow t))
    (fun f => (KFCausalTransverseShearClockCommutation.coupled_inverse_coordinates ε hε t f).symm)
    (fourier_coe t) f

#print axioms fourier_coe
#print axioms coupled_fourier_coe
end
end UnifiedTheory.Audit.KFCausalTransverseShearFourier
