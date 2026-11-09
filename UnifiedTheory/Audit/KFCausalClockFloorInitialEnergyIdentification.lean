/- Identification of the proved initial quantum-energy limit with the
reduced vacuum Hamiltonian integrated against the already constructed
classical initial law. This does not identify a full classical symbol or
prove propagation of that law. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialAveragedEnergy
import UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
import UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive longitudinal)
open UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction (hamiltonian potential)
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction (canonicalHamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit
open UnifiedTheory.Audit.KFCausalClockFloorInitialAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)

theorem halfClock_square (ε a s : ℝ) (hε : 0 < ε) :
    ‖halfClockFunction ε a s‖^2 = clock ε s*‖clockFunction ε a s‖^2 := by
  simp only [halfClockFunction,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [Real.sq_sqrt (by positivity)]
  rfl

theorem dampedClock_square (ε a s : ℝ) (hε : 0 < ε) :
    ‖dampedClockFunction ε a s‖^2 = ‖clockFunction ε a s‖^2/clock ε s := by
  simp only [dampedClockFunction,norm_mul,norm_inv,mul_pow,Complex.norm_real,
    Real.norm_eq_abs,inv_pow,sq_abs]
  rw [Real.sq_sqrt (by positivity)]
  exact (div_eq_inv_mul _ _).symm

theorem vacuum_density_identity (ε a vacuum t s : ℝ) (hε : 0 < ε) :
    canonicalHamiltonian ε vacuum t s 0*clockDensity ε a s =
      (‖halfClockFunction ε a s‖^2/2+Real.exp (2*t)*vacuum*‖dampedClockFunction ε a s‖^2)/clockMass ε a := by
  rw [halfClock_square ε a s hε,dampedClock_square ε a s hε]
  simp only [canonicalHamiltonian,hamiltonian,potential,longitudinal,zero_div,Real.exp_zero,
    mul_one,zero_add,clockDensity]
  ring

theorem initial_energy_density_integral (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ s : ℝ, canonicalHamiltonian ε vacuum t s 0*clockDensity ε a s) =
      initialClassicalEnergy ε a vacuum t := by
  have hh := halfClockFunction_memLp ε a hε ha
  have hd := dampedClockFunction_memLp ε a hε ha
  have hi := (memLp_two_iff_integrable_sq_norm hh.1).mp hh
  have hj := (memLp_two_iff_integrable_sq_norm hd.1).mp hd
  simp_rw [vacuum_density_identity ε a vacuum t _ hε]
  rw [integral_div,integral_add (hi.div_const 2) (hj.const_mul (Real.exp (2*t)*vacuum)),
    integral_div,integral_const_mul]
  rfl

theorem initial_energy_clockLaw (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ s : ℝ, canonicalHamiltonian ε vacuum t s 0 ∂clockLaw ε a) =
      initialClassicalEnergy ε a vacuum t := by
  rw [clockLaw,integral_withDensity_eq_integral_toReal_smul
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [← initial_energy_density_integral ε a vacuum t hε ha]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul]
  exact mul_comm _ _

theorem vacuum_clockLaw_integrable (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun s : ℝ => canonicalHamiltonian ε vacuum t s 0) (clockLaw ε a) := by
  rw [clockLaw,integrable_withDensity_iff_integrable_smul'
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hh := halfClockFunction_memLp ε a hε ha
  have hd := dampedClockFunction_memLp ε a hε ha
  have hi := (memLp_two_iff_integrable_sq_norm hh.1).mp hh
  have hj := (memLp_two_iff_integrable_sq_norm hd.1).mp hd
  apply (((hi.div_const 2).add (hj.const_mul (Real.exp (2*t)*vacuum))).div_const (clockMass ε a)).congr
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul]
  exact (vacuum_density_identity ε a vacuum t s hε).symm.trans (mul_comm _ _)

/-- Only the reduced vacuum Hamiltonian, evaluated on the clock variables.
No assertion that this is the full Hamiltonian's symbol away from the axis. -/
def vacuumHamiltonianOnPhaseSpace (ε vacuum t : ℝ) (z : PhaseSpace) : ℝ :=
  canonicalHamiltonian ε vacuum t z.1.1 z.2.1

theorem vacuumHamiltonian_continuous (ε vacuum t : ℝ) (hε : 0 < ε) :
    Continuous (vacuumHamiltonianOnPhaseSpace ε vacuum t) := by
  have hc : Continuous (fun z : PhaseSpace => clock ε z.1.1) := by unfold clock; fun_prop
  have hn (z : PhaseSpace) : clock ε z.1.1 ≠ 0 := (clock_positive ε z.1.1 hε.le).ne'
  have hl := continuous_snd.fst.div hc hn
  exact (hc.div_const 2).add ((continuous_const.add
    (continuous_const.mul (Real.continuous_exp.comp hl))).div hc hn)

theorem initial_energy_classicalLaw (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ z, vacuumHamiltonianOnPhaseSpace ε vacuum t z ∂classicalLaw ε a) =
      initialClassicalEnergy ε a vacuum t := by
  rw [classicalLaw,integral_map clockAxis_continuous.measurable.aemeasurable
    (vacuumHamiltonian_continuous ε vacuum t hε).aestronglyMeasurable]
  exact initial_energy_clockLaw ε a vacuum t hε ha

theorem vacuum_classicalLaw_integrable (ε a vacuum t : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (vacuumHamiltonianOnPhaseSpace ε vacuum t) (classicalLaw ε a) :=
  (integrable_map_measure (vacuumHamiltonian_continuous ε vacuum t hε).aestronglyMeasurable
    clockAxis_continuous.measurable.aemeasurable).mpr (vacuum_clockLaw_integrable ε a vacuum t hε ha)

theorem physical_initial_energy_classical_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (mass2 quartic vacuum t : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (h : ℕ → ℝ) (hn : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => timeEnergy ε hε (h n) (hn n) (hb n) mass2 quartic vacuum t
      (state ε a hε ha (h n) (hn n) (hb n) (h1 n) mass2 quartic vacuum t hm hq hv))
      atTop (𝓝 (∫ z, vacuumHamiltonianOnPhaseSpace ε vacuum t z ∂classicalLaw ε a)) := by
  rw [initial_energy_classicalLaw ε a vacuum t hε ha]
  exact physical_initial_energy_tendsto ε a hε ha mass2 quartic vacuum t hm hq hv h hn hb h1 hz

#print axioms halfClock_square
#print axioms dampedClock_square
#print axioms vacuum_density_identity
#print axioms initial_energy_density_integral
#print axioms initial_energy_clockLaw
#print axioms vacuum_clockLaw_integrable
#print axioms vacuumHamiltonian_continuous
#print axioms initial_energy_classicalLaw
#print axioms vacuum_classicalLaw_integrable
#print axioms physical_initial_energy_classical_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification
