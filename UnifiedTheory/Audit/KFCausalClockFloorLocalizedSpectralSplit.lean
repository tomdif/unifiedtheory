/- Exact upper/lower spectral mass splitting of the localized physical
charge orbit. Only the clock weight, not the momentum, commutes with charge. -/
import UnifiedTheory.Audit.KFCausalClockFloorWeightedClockControl
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectrum
import UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf
import UnifiedTheory.Audit.KFCausalClockFloorChargeDefect

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectralSplit
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (FrequencyHilbert)
open KFCausalClockFloorWeightedClockControl (weighted)
open KFCausalClockFloorLocalizedSpectrum (observation orbitObservation)
open KFCausalClockFloorFourierCoordinates (coupledFourier)
open KFCausalClockFloorFourierMultiplier (symbol)
open KFCausalClockFloorExponential (symbol_measurable)
open KFCausalClockFloorOrbitVacuumGraph (physicalOrbit physicalOrbit_coe)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalPhysicalCircleAction (action)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)

def lowerObservation (R : ℝ) : Hilbert →L[ℂ] FrequencyHilbert :=
  (KFCausalBornLocalization.mask volume {p | R ≤ symbol h p}ᶜ
    (measurableSet_le measurable_const (symbol_measurable h)).compl).comp
      ((coupledFourier ε hε).toLinearIsometry.toContinuousLinearMap.comp (weighted ε hε))

def lowerOrbit (hne : h ≠ 0) (R : ℝ) : Hilbert →L[ℂ] Lp FrequencyHilbert 2 angleMeasure :=
  ((lowerObservation ε hε h R).compLpL 2 angleMeasure).comp
    (physicalOrbit h hne).toContinuousLinearMap

theorem weighted_action (hne : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    weighted ε hε (action h hne θ f)=action h hne θ (weighted ε hε f) := by
  change KFCausalClockFloorBoundedInverse.inverseL ε hε
    (KFCausalClockFloorDefectOperator.defectOperator ε hε (action h hne θ f)-
      KFCausalClockFloorDefectOperator.defectOperator ε hε
        (KFCausalClockFloorDefectOperator.defectOperator ε hε (action h hne θ f))) = _
  rw [KFCausalClockFloorChargeDefect.defect_action,
    KFCausalClockFloorChargeDefect.defect_action,← map_sub,
    KFCausalClockFloorChargeClockHalf.inverseL_action]
  rfl

theorem lower_norm_square (R : ℝ) (f : Hilbert) :
    ‖lowerObservation ε hε h R f‖^2 =
      ∫ p in {p | symbol h p < R}, ‖(coupledFourier ε hε (weighted ε hε f)) p‖^2 := by
  change ‖KFCausalBornLocalization.mask volume _
    (measurableSet_le measurable_const (symbol_measurable h)).compl
      (coupledFourier ε hε (weighted ε hε f))‖^2 = _
  rw [KFCausalBornLocalization.mask_norm_square]
  rw [show {p | R ≤ symbol h p}ᶜ={p | symbol h p < R} from by
    ext p
    simp only [Set.mem_compl_iff,Set.mem_setOf_eq,not_le]]

theorem observation_split (R : ℝ) (f : Hilbert) :
    ‖observation ε hε h R f‖^2+‖lowerObservation ε hε h R f‖^2=‖weighted ε hε f‖^2 := by
  let q := coupledFourier ε hε (weighted ε hε f)
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable q)).mp (Lp.memLp q)
  change ‖KFCausalBornLocalization.mask volume _
    (measurableSet_le measurable_const (symbol_measurable h)) q‖^2+
    ‖KFCausalBornLocalization.mask volume _
      (measurableSet_le measurable_const (symbol_measurable h)).compl q‖^2=‖weighted ε hε f‖^2
  rw [KFCausalBornLocalization.mask_norm_square,KFCausalBornLocalization.mask_norm_square,
    integral_add_compl (measurableSet_le measurable_const (symbol_measurable h)) hi,
    ← KFCausalAveragedEnergyGraph.l2_norm_square]
  exact congrArg (fun r : ℝ => r^2) ((coupledFourier ε hε).norm_map (weighted ε hε f))

theorem lower_orbit_integral (hne : h ≠ 0) (R : ℝ) (f : Hilbert) :
    ‖lowerOrbit ε hε h hne R f‖^2 = ∫ θ,
      (∫ p in {p | symbol h p < R},
        ‖(coupledFourier ε hε (weighted ε hε (action h hne (2*Real.pi*θ) f))) p‖^2) ∂angleMeasure := by
  rw [KFCausalAveragedEnergyGraph.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [(lowerObservation ε hε h R).coeFn_compLp (physicalOrbit h hne f),
    physicalOrbit_coe h hne f] with θ h1 h2
  change ‖(lowerObservation ε hε h R).compLp (physicalOrbit h hne f) θ‖^2 = _
  rw [h1,lower_norm_square,h2]

theorem orbit_split (hne : h ≠ 0) (R : ℝ) (f : Hilbert) :
    ‖orbitObservation ε hε h hne R f‖^2+‖lowerOrbit ε hε h hne R f‖^2=‖weighted ε hε f‖^2 := by
  have hiu := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (orbitObservation ε hε h hne R f))).mp (Lp.memLp _)
  have hil := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (lowerOrbit ε hε h hne R f))).mp (Lp.memLp _)
  rw [KFCausalAveragedEnergyGraph.l2_norm_square,KFCausalAveragedEnergyGraph.l2_norm_square,
    ← integral_add hiu hil]
  calc
    _ = ∫ _θ : ℝ, ‖weighted ε hε f‖^2 ∂angleMeasure := by
      apply integral_congr_ae
      filter_upwards [(observation ε hε h R).coeFn_compLp (physicalOrbit h hne f),
        (lowerObservation ε hε h R).coeFn_compLp (physicalOrbit h hne f),
        physicalOrbit_coe h hne f] with θ hu hl hθ
      change ‖(observation ε hε h R).compLp (physicalOrbit h hne f) θ‖^2+
        ‖(lowerObservation ε hε h R).compLp (physicalOrbit h hne f) θ‖^2 = _
      rw [hu,hl,observation_split,hθ,weighted_action,LinearIsometryEquiv.norm_map]
    _ = _ := by simp

theorem curve_mass (hne : h ≠ 0) (L R η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η)
    (f : ℝ → Hilbert) (hf : Continuous f)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) L, η ≤ ‖weighted ε hε (f t)‖) :
    η^2*L ≤ (∫ t in 0..L, ‖orbitObservation ε hε h hne R (f t)‖^2)+
      (∫ t in 0..L, ‖lowerOrbit ε hε h hne R (f t)‖^2) := by
  have hu := (((orbitObservation ε hε h hne R).continuous.comp hf).norm.pow 2).intervalIntegrable (μ := volume) 0 L
  have hl := (((lowerOrbit ε hε h hne R).continuous.comp hf).norm.pow 2).intervalIntegrable (μ := volume) 0 L
  have hi := intervalIntegral.integral_mono_on (μ := volume) hL
    (intervalIntegrable_const (c := η^2)) (hu.add hl) (fun t ht =>
      (pow_le_pow_left₀ hη (hbound t ht) 2).trans_eq (orbit_split ε hε h hne R _).symm)
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add hu hl] at hi
  simpa only [sub_zero,smul_eq_mul,mul_comm] using hi

#print axioms weighted_action
#print axioms lower_norm_square
#print axioms observation_split
#print axioms lower_orbit_integral
#print axioms orbit_split
#print axioms curve_mass
end
end UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectralSplit
