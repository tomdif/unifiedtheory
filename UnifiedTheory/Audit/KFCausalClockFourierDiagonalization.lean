/- The actual coupled longitudinal transport is diagonal in constructed
six-dimensional Fourier coordinates. This identifies the full L2 group,
without asserting an unbounded Fourier multiplier domain yet. -/
import UnifiedTheory.Audit.KFCausalEuclideanConfiguration
import UnifiedTheory.Audit.KFCausalFourierTranslation
import UnifiedTheory.Audit.KFCausalLongitudinalMomentumConjugacy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalCoupledUnitaryTransport

theorem clock_translation_coe (t : ℝ) (f : Hilbert) :
    translation t f =ᵐ[volume] fun x => f (clockShift t x) := by
  rw [translation_eq_compMeasurePreserving]
  exact Lp.coeFn_compMeasurePreserving f (clockShift_measurePreserving t)

theorem euclidean_clock_translation (t : ℝ) (f : Hilbert) :
    euclideanPullback (translation t f) =
      KFCausalFourierTranslation.translation (t • clockVector) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (translation t f),
    split_preserves_volume.quasiMeasurePreserving.ae (clock_translation_coe t f),
    KFCausalFourierTranslation.translation_coe (t • clockVector) (euclideanPullback f),
    (KFCausalFourierTranslation.shift_preserves_volume (t • clockVector)).quasiMeasurePreserving.ae
      (euclideanPullback_coe f)] with x hR hc hT hf
  simp only [Function.comp_apply] at hR hc hf
  change (euclideanPullback f) (x+t • clockVector) = f (split (x+t • clockVector)) at hf
  rw [hR,hc,hT,hf,split_clock_add]

theorem fourier_clock_translation (t : ℝ) (f : Hilbert) :
    fourierCoordinates (translation t f) =
      KFCausalFourierTranslation.phaseAction (t • clockVector) (fourierCoordinates f) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (euclideanPullback (translation t f)) = _
  rw [euclidean_clock_translation,KFCausalFourierTranslation.fourier_translation
    (t • clockVector) (euclideanPullback f)]
  rfl

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
  calc
    _ = fourierCoordinates ((coordinates ε hε).symm (transport ε hε t f)) :=
      coupledFourier_apply ε hε (transport ε hε t f)
    _ = fourierCoordinates (translation t ((coordinates ε hε).symm f)) :=
      congrArg fourierCoordinates (coordinates_symm_transport ε hε t f)
    _ = KFCausalFourierTranslation.phaseAction (t • clockVector)
        (fourierCoordinates ((coordinates ε hε).symm f)) :=
      fourier_clock_translation t ((coordinates ε hε).symm f)
    _ = _ := congrArg (KFCausalFourierTranslation.phaseAction (t • clockVector))
      (coupledFourier_apply ε hε f).symm

theorem clock_phase (t : ℝ) (k : Space) :
    KFCausalFourierTranslation.phase (t • clockVector) k =
      Complex.exp ((2*Real.pi*t*k 0:ℝ)*Complex.I) := by
  simp only [KFCausalFourierTranslation.phase,real_inner_smul_left,clockVector_inner,
    Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem coupledFourier_transport_coe (ε : ℝ) (hε : 0 < ε) (t : ℝ) (f : Hilbert) :
    coupledFourier ε hε (transport ε hε t f) =ᵐ[volume]
      fun k => Complex.exp ((2*Real.pi*t*k 0:ℝ)*Complex.I)*(coupledFourier ε hε f) k := by
  rw [coupledFourier_transport]
  filter_upwards [KFCausalFourierTranslation.phaseAction_coe (t • clockVector) (coupledFourier ε hε f)] with k hk
  rw [hk,clock_phase]

#print axioms clock_translation_coe
#print axioms euclidean_clock_translation
#print axioms fourier_clock_translation
#print axioms coupledFourier
#print axioms coupledFourier_transport
#print axioms clock_phase
#print axioms coupledFourier_transport_coe

end
end UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
