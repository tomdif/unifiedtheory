/- Faithful vacuum detection on the full angle-L2 output. The comparison
with total clock dissipation is valid without a charge-sector restriction. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumDetection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph (OrbitSpace coordinate coordinateLp)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator (driftOperator)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput (classicalOutput)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

variable (ε : ℝ) (hε : 0 < ε)
def detector : OrbitSpace →L[ℂ] OrbitSpace := (driftOperator ε hε).compLpL 2 angleMeasure
def detection (q : OrbitSpace) : ℝ := -(inner ℂ q (detector ε hε q)).re

theorem detector_injective : Function.Injective (detector ε hε) :=
  KFCausalLpClosedOperator.compLp_injective angleMeasure (driftOperator ε hε)
    (KFCausalClockFloorDriftDetection.drift_injective ε hε)

theorem detection_integrable (q : OrbitSpace) :
    Integrable (fun θ => KFCausalClockFloorDriftDetection.detection ε hε (q θ)) angleMeasure := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) q (detector ε hε q)).re.neg
  apply hi.congr
  filter_upwards [(driftOperator ε hε).coeFn_compLp q] with θ hθ
  change -(inner ℂ (q θ) ((driftOperator ε hε).compLp q θ)).re = _
  rw [hθ]
  rfl

theorem detection_integral (q : OrbitSpace) :
    detection ε hε q = ∫ θ, KFCausalClockFloorDriftDetection.detection ε hε (q θ) ∂angleMeasure := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) q (detector ε hε q))
  change (∫ θ, (inner ℂ (q θ) (detector ε hε q θ)).re ∂angleMeasure) =
    (∫ θ, inner ℂ (q θ) (detector ε hε q θ) ∂angleMeasure).re at he
  rw [detection,L2.inner_def,← he,← integral_neg]
  apply integral_congr_ae
  filter_upwards [(driftOperator ε hε).coeFn_compLp q] with θ hθ
  change -(inner ℂ (q θ) ((driftOperator ε hε).compLp q θ)).re = _
  rw [hθ]
  rfl

theorem detection_nonnegative (q : OrbitSpace) : 0 ≤ detection ε hε q := by
  rw [detection_integral]
  exact integral_nonneg (fun θ => KFCausalClockFloorDriftDetection.detection_nonnegative ε hε (q θ))

theorem detection_smul (c : ℂ) (q : OrbitSpace) :
    detection ε hε (c • q) = ‖c‖^2*detection ε hε q := by
  unfold detection
  rw [map_smul,inner_smul_left,inner_smul_right,← mul_assoc,Complex.conj_mul',← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem detector_norm_sq_bound (q : OrbitSpace) :
    ‖detector ε hε q‖^2 ≤ (1/ε)*detection ε hε q := by
  rw [l2_norm_square,detection_integral,← integral_const_mul]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (detector ε hε q))).mp (Lp.memLp _))
    ((detection_integrable ε hε q).const_mul (1/ε))
  filter_upwards [(driftOperator ε hε).coeFn_compLp q] with θ hθ
  change ‖(driftOperator ε hε).compLp q θ‖^2 ≤ _
  rw [hθ]
  exact KFCausalClockFloorDriftDetection.drift_norm_sq_bound ε hε (q θ)

theorem output_detection_bound (q : EnergyOutputSpace) :
    detection ε hε (coordinateLp q) ≤ -(inner ℂ q ((classicalOutput ε hε).compLp q)).re := by
  have hi := L2.integrable_inner (𝕜 := ℂ) q ((classicalOutput ε hε).compLp q)
  have he := integral_re hi
  change (∫ θ, (inner ℂ (q θ) ((classicalOutput ε hε).compLp q θ)).re ∂angleMeasure) =
    (∫ θ, inner ℂ (q θ) ((classicalOutput ε hε).compLp q θ) ∂angleMeasure).re at he
  rw [detection_integral,L2.inner_def,← he,← integral_neg]
  apply integral_mono_ae (detection_integrable ε hε (coordinateLp q)) hi.re.neg
  filter_upwards [coordinate.coeFn_compLp q,(classicalOutput ε hε).coeFn_compLp q] with θ h1 h2
  change KFCausalClockFloorDriftDetection.detection ε hε (coordinate.compLp q θ) ≤
    -(inner ℂ (q θ) ((classicalOutput ε hε).compLp q θ)).re
  rw [h1,h2]
  exact KFCausalClockFloorVacuumObservation.coordinate_detection_bound ε hε (q θ)

#print axioms detector_injective
#print axioms detection_integrable
#print axioms detection_integral
#print axioms detection_nonnegative
#print axioms detection_smul
#print axioms detector_norm_sq_bound
#print axioms output_detection_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumDetection
