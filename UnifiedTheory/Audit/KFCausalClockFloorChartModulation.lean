/- Actual unitary phases of the straightened clock coordinate. Their
Fourier action is an exact frequency shift on every physical L2 state. -/
import UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
import UnifiedTheory.Audit.KFCausalL2FourierModulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorChartModulation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso)
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)

def phase (ε r : ℝ) (x : Configuration) : ℂ := Real.fourierChar (r*chart ε x.1)

theorem phase_measurable (ε r : ℝ) : Measurable (phase ε r) := by
  unfold phase chart
  fun_prop

theorem phase_norm (ε r : ℝ) (x : Configuration) : ‖phase ε r x‖ = 1 := Circle.norm_coe _

def modulation (ε r : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  KFCausalUnitModulusMultiplier.unitary (phase ε r) (phase_measurable ε r) (phase_norm ε r)

theorem modulation_coe (ε r : ℝ) (f : Hilbert) :
    modulation ε r f =ᵐ[volume] fun x => phase ε r x*f x :=
  KFCausalUnitModulusMultiplier.unitary_coe _ _ _ f

theorem modulation_inverse (ε r : ℝ) (f : Hilbert) : modulation ε (-r) (modulation ε r f) = f := by
  apply Lp.ext
  filter_upwards [modulation_coe ε (-r) (modulation ε r f),modulation_coe ε r f] with x hx hy
  rw [hx,hy,← mul_assoc]
  have he : phase ε (-r) x*phase ε r x = 1 := by
    simp only [phase,Real.fourierChar_apply,neg_mul,← Complex.exp_add]
    conv_rhs => rw [← Complex.exp_zero]
    congr 1
    push_cast
    ring
  rw [he,one_mul]

theorem modulation_density (ε r : ℝ) (f : Hilbert) :
    (fun x => ‖modulation ε r f x‖) =ᵐ[volume] fun x => ‖f x‖ := by
  filter_upwards [modulation_coe ε r f] with x hx
  rw [hx,norm_mul,phase_norm,one_mul]

def flat (ε : ℝ) (hε : 0 < ε) : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert :=
  (coordinates ε hε).symm.trans euclideanPullback

theorem flat_modulation (ε : ℝ) (hε : 0 < ε) (r : ℝ) (f : Hilbert) :
    flat ε hε (modulation ε r f) =
      KFCausalFourierTranslation.phaseAction (r • clockVector) (flat ε hε f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe ((coordinates ε hε).symm (modulation ε r f)),
    euclideanPullback_coe ((coordinates ε hε).symm f),
    split_preserves_volume.quasiMeasurePreserving.ae (coordinates_inverse_coe ε hε (modulation ε r f)),
    split_preserves_volume.quasiMeasurePreserving.ae (coordinates_inverse_coe ε hε f),
    ((coordinate_inverse_quasiMeasurePreserving ε hε).comp
      split_preserves_volume.quasiMeasurePreserving).ae (modulation_coe ε r f),
    KFCausalFourierTranslation.phaseAction_coe (r • clockVector) (flat ε hε f)]
    with x h1 h2 h3 h4 h5 h6
  simp only [Function.comp_def] at h1 h2 h5
  change euclideanPullback ((coordinates ε hε).symm (modulation ε r f)) x = _
  rw [h1,h3,h6]
  change _ = KFCausalFourierTranslation.phase (r • clockVector) x*
    euclideanPullback ((coordinates ε hε).symm f) x
  rw [h2,h4]
  change _ = _ at h5
  simp only [inverseFunction,h5]
  have he : phase ε r ((coordinateHomeomorph ε hε).symm (split x)) =
      KFCausalFourierTranslation.phase (r • clockVector) x := by
    have hc : chart ε ((coordinateHomeomorph ε hε).symm (split x)).1 = x 0 :=
      (chartIso ε hε).apply_symm_apply (x 0)
    rw [phase,hc,KFCausalFourierTranslation.phase,real_inner_smul_left,clockVector_inner]
  rw [he]
  ring

theorem fourier_modulation (ε : ℝ) (hε : 0 < ε) (r : ℝ) (f : Hilbert) :
    coupledFourier ε hε (modulation ε r f) =
      KFCausalFourierTranslation.translation (-(r • clockVector)) (coupledFourier ε hε f) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (flat ε hε (modulation ε r f)) =
    KFCausalFourierTranslation.translation (-(r • clockVector))
      ((Lp.fourierTransformₗᵢ Space ℂ) (flat ε hε f))
  rw [flat_modulation,KFCausalL2FourierModulation.fourier_phaseAction]

#print axioms phase_measurable
#print axioms phase_norm
#print axioms modulation_coe
#print axioms modulation_inverse
#print axioms modulation_density
#print axioms flat_modulation
#print axioms fourier_modulation
end
end UnifiedTheory.Audit.KFCausalClockFloorChartModulation
