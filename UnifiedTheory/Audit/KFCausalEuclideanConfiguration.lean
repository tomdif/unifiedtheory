/- Measure-preserving flattening of clock plus five transverse coordinates.
This gives a unitary map to the Euclidean L2 space used by Fourier theory. -/
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
import UnifiedTheory.Audit.KFCausalConfigurationTranslation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Fourier.LpSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalEuclideanConfiguration
noncomputable section
open MeasureTheory WithLp
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

abbrev Space := EuclideanSpace ℝ (Fin 6)
abbrev FrequencyHilbert := Lp ℂ 2 (volume : Measure Space)

def split : Space ≃ᵐ Configuration :=
  (MeasurableEquiv.toLp 2 (Fin 6 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 6 => ℝ) 0)

theorem split_preserves_volume : MeasurePreserving split :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 6 => ℝ) 0).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 6))

theorem split_apply (x : Space) : split x = (x 0,fun i : Fin 5 => x i.succ) := by
  rfl

def euclideanPullback : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert := unitaryPullback split split_preserves_volume

theorem euclideanPullback_coe (f : Hilbert) : euclideanPullback f =ᵐ[volume] f ∘ split :=
  unitaryPullback_coe split split_preserves_volume f

def clockVector : Space := toLp 2 (Pi.single 0 1)

theorem split_clock_add (t : ℝ) (x : Space) :
    split (x+t • clockVector) = clockShift t (split x) := by
  rw [split_apply,clockShift_apply,split_apply]
  ext i
  · simp [clockVector]
  · simp [clockVector,Fin.succ_ne_zero]

theorem clockVector_inner (k : Space) : inner ℝ clockVector k = k 0 := by
  simp [clockVector,PiLp.inner_apply]

def fourierCoordinates : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert :=
  euclideanPullback.trans (Lp.fourierTransformₗᵢ Space ℂ)

theorem fourierCoordinates_norm (f : Hilbert) : ‖fourierCoordinates f‖ = ‖f‖ :=
  fourierCoordinates.norm_map f

#print axioms split_preserves_volume
#print axioms split_apply
#print axioms euclideanPullback
#print axioms euclideanPullback_coe
#print axioms split_clock_add
#print axioms clockVector_inner
#print axioms fourierCoordinates_norm

end
end UnifiedTheory.Audit.KFCausalEuclideanConfiguration
