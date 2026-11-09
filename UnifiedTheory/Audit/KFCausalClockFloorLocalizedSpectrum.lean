/- A bounded observation of every fixed upper half-space of the actual
coupled longitudinal spectrum, after analytic clock localization.
The charge-angle L2 observation retains the complete physical orbit. -/
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedVacuum
import UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumDetection
import UnifiedTheory.Audit.KFCausalClockFloorMovingDissipation
import UnifiedTheory.Audit.KFCausalBornLocalization

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectrum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (FrequencyHilbert)
open KFCausalClockFloorFourierCoordinates (coupledFourier)
open KFCausalClockFloorFourierMultiplier (symbol)
open KFCausalClockFloorExponential (symbol_measurable)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorLocalizedVacuum (clockWeight)
open KFCausalClockFloorOrbitVacuumGraph
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)

def observation (R : ℝ) : Hilbert →L[ℂ] FrequencyHilbert :=
  (KFCausalBornLocalization.mask volume {p | R ≤ symbol h p}
    (measurableSet_le measurable_const (symbol_measurable h))).comp
      ((coupledFourier ε hε).toLinearIsometry.toContinuousLinearMap.comp
        ((inverseL ε hε).comp (clockWeight ε hε)))

theorem observation_norm_square (R : ℝ) (f : Hilbert) :
    ‖observation ε hε h R f‖^2 = KFCausalClockFloorLongitudinalTails.positiveTail ε hε h R
      (inverseL ε hε (clockWeight ε hε f)) :=
  KFCausalBornLocalization.mask_norm_square volume _
    (measurableSet_le measurable_const (symbol_measurable h)) _

def orbitLift (R : ℝ) : OrbitSpace →L[ℂ] Lp FrequencyHilbert 2 angleMeasure :=
  (observation ε hε h R).compLpL 2 angleMeasure

def orbitObservation (hne : h ≠ 0) (R : ℝ) : Hilbert →L[ℂ] Lp FrequencyHilbert 2 angleMeasure :=
  (orbitLift ε hε h R).comp (physicalOrbit h hne).toContinuousLinearMap

theorem orbit_integral (hne : h ≠ 0) (R : ℝ) (f : Hilbert) :
    ‖orbitObservation ε hε h hne R f‖^2 =
      ∫ θ, KFCausalClockFloorLongitudinalTails.positiveTail ε hε h R
        (inverseL ε hε (clockWeight ε hε
          (KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ) f))) ∂angleMeasure := by
  rw [KFCausalAveragedEnergyGraph.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [(observation ε hε h R).coeFn_compLp (physicalOrbit h hne f),
    physicalOrbit_coe h hne f] with θ h1 h2
  change ‖(observation ε hε h R).compLp (physicalOrbit h hne f) θ‖^2 = _
  rw [h1,observation_norm_square,h2]

theorem orbit_graph_bound (hb : |h| ≤ 2*Real.pi*ε/3) (R : ℝ) (f g : OrbitSpace)
    (hfg : (f,g) ∈ (vacuumOperator ε hε h).graph) :
    ‖orbitLift ε hε h R f‖^2 ≤
      64*ε*Real.exp (-R)*KFCausalClockFloorOrbitVacuumDetection.detection ε hε g := by
  rw [KFCausalAveragedEnergyGraph.l2_norm_square,
    KFCausalClockFloorOrbitVacuumDetection.detection_integral,← integral_const_mul]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (orbitLift ε hε h R f))).mp
      (Lp.memLp _))
    ((KFCausalClockFloorOrbitVacuumDetection.detection_integrable ε hε g).const_mul _)
  rw [vacuumOperator,KFCausalLpClosedOperator.operator_graph] at hfg
  filter_upwards [(observation ε hε h R).coeFn_compLp f,hfg] with θ hθ hgraph
  change ‖(observation ε hε h R).compLp f θ‖^2 ≤ _
  rw [hθ,observation_norm_square]
  exact KFCausalClockFloorLocalizedVacuum.localized_tail_bound ε hε h hb R _ _ hgraph

theorem form_bound (hne : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (m g k R : ℝ)
    (hk : 0 < k) (v : FormSpace ε hε h hne hb m g k 0) :
    ‖orbitObservation ε hε h hne R (embedding ε hε h hne hb m g k 0 v)‖^2 ≤
      (128*ε*Real.exp (-R)/k)*KFCausalClockFloorMovingDissipation.detector ε hε h hne hb m g k v := by
  let c := KFCausalPhysicalEnergyFactors.energyWeight m g k 0 7
  have hc : ‖c‖^2=k := by
    change ‖((Real.exp 0*Real.sqrt k:ℝ):ℂ)‖^2=k
    simp only [Real.exp_zero,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hk.le]
  have hbnd := orbit_graph_bound ε hε h hb R _ _ (vacuum_graph ε hε h hne hb m g k 0 v)
  have he : orbitLift ε hε h R
      (physicalOrbit h hne (c • embedding ε hε h hne hb m g k 0 v)) =
      c • orbitObservation ε hε h hne R (embedding ε hε h hne hb m g k 0 v) := by
    change orbitObservation ε hε h hne R (c • embedding ε hε h hne hb m g k 0 v)=_
    exact (orbitObservation ε hε h hne R).map_smul c _
  change ‖orbitLift ε hε h R
    (physicalOrbit h hne (c • embedding ε hε h hne hb m g k 0 v))‖^2 ≤ _ at hbnd
  rw [he,norm_smul,mul_pow,hc] at hbnd
  have hd := KFCausalClockFloorOrbitVacuumDetection.output_detection_bound ε hε
    (energyOutput ε hε h hne hb m g k 0 v)
  have ht := hbnd.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hk).mpr
  change _ ≤ (128*ε*Real.exp (-R))*
    (-(inner ℂ (energyOutput ε hε h hne hb m g k 0 v)
      ((KFCausalClockFloorQuantumVelocityOutput.classicalOutput ε hε).compLp
        (energyOutput ε hε h hne hb m g k 0 v))).re/2)
  nlinarith only [ht]

#print axioms observation_norm_square
#print axioms orbit_integral
#print axioms orbit_graph_bound
#print axioms form_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectrum
