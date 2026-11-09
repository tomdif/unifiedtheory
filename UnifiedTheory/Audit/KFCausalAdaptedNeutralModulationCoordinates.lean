/- The adapted coordinate x4 - 2*(x2+x3) is invariant under longitudinal
straightening. Its phase test shifts only transverse Fourier coordinates,
leaving the exponential symbol fixed. This is not the bare neutral position
and no commutation with charge averaging is asserted. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
import UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
import UnifiedTheory.Audit.KFCausalL2FourierModulation
import UnifiedTheory.Audit.KFCausalClockFloorExponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (flow)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback (weight)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)

def coordinate : Configuration →L[ℝ] ℝ where
  toFun x := x.2 4-2*(x.2 2+x.2 3)
  map_add' x y := by dsimp; ring
  map_smul' c x := by dsimp; ring
  cont := by fun_prop

theorem coordinate_apply (x : Configuration) : coordinate x = x.2 4-2*(x.2 2+x.2 3) := rfl

def frequency (v : ℝ) : Configuration →L[ℝ] ℝ := v • coordinate

theorem frequency_apply (v : ℝ) (x : Configuration) : frequency v x = v*coordinate x := rfl

def action (v : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := modulation (frequency v)

theorem action_coe (v : ℝ) (f : Hilbert) :
    action v f =ᵐ[volume] fun x => scalar (v*coordinate x)*f x := modulation_coe _ _

theorem action_inverse (v : ℝ) (f : Hilbert) : action (-v) (action v f) = f := by
  have hn : frequency (-v) = -frequency v := by
    apply ContinuousLinearMap.ext
    intro x
    simp [frequency_apply]
  simpa only [action,hn] using modulation_inverse (frequency v) f

theorem coordinate_neutral (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    coordinate (coordinateHomeomorph ε hε x) = coordinate x := by
  change flow (-x.1) x.2 4-2*(flow (-x.1) x.2 2+flow (-x.1) x.2 3) = x.2 4-2*(x.2 2+x.2 3)
  simp [flow]
  ring

theorem coordinates_commutes (ε : ℝ) (hε : 0 < ε) (v : ℝ) (f : Hilbert) :
    coordinates ε hε (action v f) = action v (coordinates ε hε f) := by
  apply Lp.ext
  filter_upwards [coordinates_coe ε hε (action v f),
    (coordinate_quasiMeasurePreserving ε hε).ae (action_coe v f),
    action_coe v (coordinates ε hε f),coordinates_coe ε hε f] with x hc ha hm hf
  change action v f (coordinateHomeomorph ε hε x) = _ at ha
  rw [hc,hm,hf]
  change weight ε x*action v f (coordinateHomeomorph ε hε x) = _
  rw [ha,coordinate_neutral]
  change weight ε x*(scalar (v*coordinate x)*f (coordinateHomeomorph ε hε x)) =
    scalar (v*coordinate x)*(weight ε x*f (coordinateHomeomorph ε hε x))
  ring

theorem coordinates_inverse_commutes (ε : ℝ) (hε : 0 < ε) (v : ℝ) (f : Hilbert) :
    (coordinates ε hε).symm (action v f) = action v ((coordinates ε hε).symm f) := by
  apply (coordinates ε hε).injective
  rw [LinearIsometryEquiv.apply_symm_apply,coordinates_commutes,LinearIsometryEquiv.apply_symm_apply]

def spectralVector (v : ℝ) : Space := WithLp.toLp 2 ![0,0,0,-2*v/(2*Real.pi),-2*v/(2*Real.pi),v/(2*Real.pi)]

theorem spectralVector_inner (v : ℝ) (x : Space) :
    inner ℝ (spectralVector v) x = v/(2*Real.pi)*(x 5-2*(x 3+x 4)) := by
  simp [spectralVector,PiLp.inner_apply,Fin.sum_univ_succ]
  ring

theorem phase_identity (v : ℝ) (x : Space) :
    KFCausalFourierTranslation.phase (spectralVector v) x = scalar (v*coordinate (split x)) := by
  rw [KFCausalFourierTranslation.phase,spectralVector_inner]
  simp only [Real.fourierChar_apply,scalar,coordinate_apply,split_apply]
  congr 1
  push_cast
  field_simp

theorem euclidean_action (v : ℝ) (f : Hilbert) :
    euclideanPullback (action v f) =
      KFCausalFourierTranslation.phaseAction (spectralVector v) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (action v f),
    split_preserves_volume.quasiMeasurePreserving.ae (action_coe v f),
    KFCausalFourierTranslation.phaseAction_coe (spectralVector v) (euclideanPullback f),
    euclideanPullback_coe f] with x he ha hp hf
  change action v f (split x) = _ at ha
  rw [he,hp,hf]
  simp only [Function.comp_apply]
  rw [ha,phase_identity]

theorem coupledFourier_action (ε : ℝ) (hε : 0 < ε) (v : ℝ) (f : Hilbert) :
    coupledFourier ε hε (action v f) =
      KFCausalFourierTranslation.translation (-spectralVector v) (coupledFourier ε hε f) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (euclideanPullback ((coordinates ε hε).symm (action v f))) = _
  rw [coordinates_inverse_commutes,euclidean_action,KFCausalL2FourierModulation.fourier_phaseAction]
  rfl

theorem coupledFourier_action_coe (ε : ℝ) (hε : 0 < ε) (v : ℝ) (f : Hilbert) :
    coupledFourier ε hε (action v f) =ᵐ[volume]
      fun k => coupledFourier ε hε f (k + -spectralVector v) := by
  rw [coupledFourier_action]
  exact KFCausalFourierTranslation.translation_coe _ _

theorem symbol_shift (h v : ℝ) (x : Space) :
    symbol h (x + -spectralVector v) = symbol h x := by
  simp [symbol,spectralVector]

#print axioms coordinate_apply
#print axioms frequency_apply
#print axioms action_coe
#print axioms action_inverse
#print axioms coordinate_neutral
#print axioms coordinates_commutes
#print axioms coordinates_inverse_commutes
#print axioms spectralVector_inner
#print axioms phase_identity
#print axioms euclidean_action
#print axioms coupledFourier_action
#print axioms coupledFourier_action_coe
#print axioms symbol_shift

end
end UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationCoordinates
