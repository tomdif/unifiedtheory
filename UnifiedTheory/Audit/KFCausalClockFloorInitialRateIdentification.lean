/- Initial dynamical correspondence: the derivative of the actual quantum
clock-defect expectation tends to the classical Hamiltonian bracket averaged
against the proved initial law. No positive-time transport limit is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialQuantumRate
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialRateIdentification
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction (hamiltonian potential)
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction (canonicalHamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical (classical_defect_velocity)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification (dampedClock_square)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed
open UnifiedTheory.Audit.KFCausalClockFloorInitialQuantumRate
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)

def vacuumDefectVelocity (ε vacuum t : ℝ) (z : PhaseSpace) : ℝ :=
  bracket (fun s _ => defect ε s) (canonicalHamiltonian ε vacuum t) z.1.1 z.2.1

theorem vacuumDefectVelocity_eq (ε vacuum t : ℝ) (hε : 0 < ε) (z : PhaseSpace) :
    vacuumDefectVelocity ε vacuum t z =
      drift ε (defect ε z.1.1)*(potential ε (vacuum*Real.exp (2*t)) z.1.1 z.2.1/clock ε z.1.1) :=
  classical_defect_velocity ε 0 (vacuum*Real.exp (2*t)) z.1.1 z.2.1 hε

theorem vacuumDefectVelocity_continuous (ε vacuum t : ℝ) (hε : 0 < ε) :
    Continuous (vacuumDefectVelocity ε vacuum t) := by
  have hc : Continuous (fun z : PhaseSpace => clock ε z.1.1) := by unfold clock; fun_prop
  have hn (z : PhaseSpace) : clock ε z.1.1 ≠ 0 := (clock_positive ε z.1.1 hε.le).ne'
  have hl := continuous_snd.fst.div hc hn
  have hp : Continuous (fun z : PhaseSpace => potential ε (vacuum*Real.exp (2*t)) z.1.1 z.2.1) :=
    continuous_const.mul (Real.continuous_exp.comp hl)
  have hd := ((drift_clock_continuous ε hε).comp continuous_fst.fst).mul (hp.div hc hn)
  exact hd.congr (fun z => (vacuumDefectVelocity_eq ε vacuum t hε z).symm)

theorem drift_density_identity (ε a vacuum t s : ℝ) (hε : 0 < ε) :
    vacuumDefectVelocity ε vacuum t (clockAxis s)*clockDensity ε a s =
      (Real.exp (2*t)*vacuum)*(drift ε (defect ε s)*‖dampedClockFunction ε a s‖^2)/clockMass ε a := by
  rw [vacuumDefectVelocity_eq ε vacuum t hε,dampedClock_square ε a s hε]
  simp only [clockAxis,potential,longitudinal,zero_div,Real.exp_zero,mul_one,clockDensity]
  ring

theorem initial_drift_clockLaw (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ s : ℝ, vacuumDefectVelocity ε vacuum t (clockAxis s) ∂clockLaw ε a) =
      initialClassicalDrift ε a vacuum t := by
  rw [clockLaw,integral_withDensity_eq_integral_toReal_smul
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ s : ℝ, (Real.exp (2*t)*vacuum)*(drift ε (defect ε s)*‖dampedClockFunction ε a s‖^2)/clockMass ε a := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul]
      exact (mul_comm _ _).trans (drift_density_identity ε a vacuum t s hε)
    _ = _ := by
      rw [integral_div,integral_const_mul]
      unfold initialClassicalDrift driftMass
      ring

theorem initial_drift_clockLaw_integrable (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun s : ℝ => vacuumDefectVelocity ε vacuum t (clockAxis s)) (clockLaw ε a) := by
  rw [clockLaw,integrable_withDensity_iff_integrable_smul'
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply (((driftMass_integrable ε a hε ha).const_mul (Real.exp (2*t)*vacuum)).div_const (clockMass ε a)).congr
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul]
  exact (drift_density_identity ε a vacuum t s hε).symm.trans (mul_comm _ _)

theorem initial_drift_classicalLaw (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ z, vacuumDefectVelocity ε vacuum t z ∂classicalLaw ε a) = initialClassicalDrift ε a vacuum t := by
  rw [classicalLaw,integral_map clockAxis_continuous.measurable.aemeasurable
    (vacuumDefectVelocity_continuous ε vacuum t hε).aestronglyMeasurable]
  exact initial_drift_clockLaw ε a vacuum t hε ha

theorem initial_drift_classicalLaw_integrable (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (vacuumDefectVelocity ε vacuum t) (classicalLaw ε a) :=
  (integrable_map_measure (vacuumDefectVelocity_continuous ε vacuum t hε).aestronglyMeasurable
    clockAxis_continuous.measurable.aemeasurable).mpr (initial_drift_clockLaw_integrable ε a vacuum t hε ha)

def quantumExpectation (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (hbar : ℝ) (hh : hbar ≠ 0)
    (hb : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) : ℝ :=
  (inner ℂ (evolution ε hε hbar hh hb mass2 quartic vacuum s t (unitTrial ε a hbar hε ha hh))
    (defectOperator ε hε (evolution ε hε hbar hh hb mass2 quartic vacuum s t
      (unitTrial ε a hbar hε ha hh)))).re

theorem quantumExpectation_derivative (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) (h1 : |hbar| ≤ 1)
    (mass2 quartic vacuum s t : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    HasDerivAt (quantumExpectation ε a hε ha hbar hh hb mass2 quartic vacuum s)
      (exactRate ε hε hbar hh hb mass2 quartic vacuum s t
        (state ε a hε ha hbar hh hb h1 mass2 quartic vacuum s hm hq hv)) t := by
  have hd := expectation_derivative ε hε hbar hh hb mass2 quartic vacuum s t
    (state ε a hε ha hbar hh hb h1 mass2 quartic vacuum s hm hq hv)
  rw [state_embedding] at hd
  exact hd

theorem initial_quantum_derivative_classical_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (h : ℕ → ℝ) (hn : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => deriv (quantumExpectation ε a hε ha (h n) (hn n) (hb n) mass2 quartic vacuum s) s)
      atTop (𝓝 (∫ z, vacuumDefectVelocity ε vacuum s z ∂classicalLaw ε a)) := by
  have he (n : ℕ) := (quantumExpectation_derivative ε a hε ha (h n) (hn n) (hb n) (h1 n)
    mass2 quartic vacuum s s hm hq hv).deriv
  simp_rw [he]
  rw [initial_drift_classicalLaw ε a vacuum s hε ha]
  exact exact_initial_rate_tendsto ε a hε ha mass2 quartic vacuum s hm hq hv h hn hb h1 hz

#print axioms vacuumDefectVelocity_eq
#print axioms vacuumDefectVelocity_continuous
#print axioms drift_density_identity
#print axioms initial_drift_clockLaw
#print axioms initial_drift_clockLaw_integrable
#print axioms initial_drift_classicalLaw
#print axioms initial_drift_classicalLaw_integrable
#print axioms quantumExpectation_derivative
#print axioms initial_quantum_derivative_classical_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialRateIdentification
