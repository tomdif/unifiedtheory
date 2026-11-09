/- Initial dynamical correspondence for arbitrary canonical momentum
boosts and the full matter Hamiltonian, including mass and quartic fields.
This is an initial derivative limit, not a positive-time transport theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialRate
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftSymbols
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedRateIdentification
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols (weightedMean weightedMean_vacuum)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect bracket clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical (defect_clock_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFactorLimits (symbolMean)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyAssembly (hamiltonian_symbolMean)
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy (energyPolynomial)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftSymbols
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialRate
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates (clockExpectation)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw)

def boostedDefectVelocity (ε m g κ t : ℝ) (p : Configuration) (s : ℝ) : ℝ :=
  bracket (fun s _ => defect ε s) (hamiltonian ε m g κ t (0,toPaired p)) s p.1

theorem matter_defect_velocity (ε m g κ t : ℝ) (hε : 0 < ε) (z : Phase) (s r : ℝ) :
    bracket (fun s _ => defect ε s) (hamiltonian ε m g κ t z) s r =
      drift ε (defect ε s)*(amplitude ε t s r*weightedMean m g κ (clock ε s) z/clock ε s) := by
  rw [bracket,(defect_clock_derivative ε s hε).deriv,deriv_const,zero_mul,sub_zero,
    (hamiltonian_momentum_derivative ε m g κ t z s r).deriv]
  have hc := (clock_positive ε s hε.le).ne'
  unfold clockRate drift defect
  field_simp
  unfold clock
  ring

theorem potential_symbolMean (ε m g κ t : ℝ) (p : Configuration) (s : ℝ) :
    amplitude ε t s p.1*weightedMean m g κ (clock ε s) (0,toPaired p)/clock ε s =
      Real.exp (2*t)*(m/2*symbolMean ε p s 5+g/4*symbolMean ε p s 6+κ*symbolMean ε p s 7) := by
  calc
    _ = hamiltonian ε m g κ t (0,toPaired p) s p.1-hamiltonian ε 0 0 0 t (0,toPaired p) s p.1 := by
      simp only [hamiltonian,weightedMean_vacuum,zero_mul,mul_zero,add_zero]
      ring
    _ = _ := by
      rw [hamiltonian_symbolMean,hamiltonian_symbolMean]
      unfold energyPolynomial
      ring

theorem boostedDefectVelocity_symbolMean (ε m g κ t : ℝ) (hε : 0 < ε) (p : Configuration) (s : ℝ) :
    boostedDefectVelocity ε m g κ t p s = Real.exp (2*t)*
      (m/2*(drift ε (defect ε s)*symbolMean ε p s 5)+
        g/4*(drift ε (defect ε s)*symbolMean ε p s 6)+κ*(drift ε (defect ε s)*symbolMean ε p s 7)) := by
  rw [boostedDefectVelocity,matter_defect_velocity ε m g κ t hε,potential_symbolMean]
  ring

theorem boostedDefectVelocity_integrable (ε a m g κ t : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    Integrable (boostedDefectVelocity ε m g κ t p) (clockLaw ε a) := by
  have h5 := (drift_symbolMean_integrable ε a hε ha p 5).const_mul (m/2)
  have h6 := (drift_symbolMean_integrable ε a hε ha p 6).const_mul (g/4)
  have h7 := (drift_symbolMean_integrable ε a hε ha p 7).const_mul κ
  exact (((h5.add h6).add h7).const_mul (Real.exp (2*t))).congr
    (Eventually.of_forall (fun s => (boostedDefectVelocity_symbolMean ε m g κ t hε p s).symm))

theorem initialRateLimit_classical (ε a m g κ t : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    initialRateLimit ε a m g κ t p = ∫ s, boostedDefectVelocity ε m g κ t p s ∂clockLaw ε a := by
  unfold initialRateLimit
  rw [averagedFieldDriftLimit_symbolMean ε a hε ha p 0,
    averagedFieldDriftLimit_symbolMean ε a hε ha p 1,averagedDriftLimit_symbolMean ε a hε ha p]
  simp_rw [boostedDefectVelocity_symbolMean ε m g κ t hε p]
  have h5 := (drift_symbolMean_integrable ε a hε ha p 5).const_mul (m/2)
  have h6 := (drift_symbolMean_integrable ε a hε ha p 6).const_mul (g/4)
  have h7 := (drift_symbolMean_integrable ε a hε ha p 7).const_mul κ
  have hadd := integral_add (h5.add h6) h7
  simp only [Pi.add_apply] at hadd
  rw [integral_const_mul,hadd,integral_add h5 h6]
  simp only [integral_const_mul]
  rfl

theorem initial_quantum_derivative_classical_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ t : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => deriv (clockExpectation ε a (h n) hε ha (hh n) (hb n) m g κ t p) t) atTop
      (𝓝 (∫ s, boostedDefectVelocity ε m g κ t p s ∂clockLaw ε a)) := by
  rw [← initialRateLimit_classical ε a m g κ t hε ha p]
  exact initial_derivative_tendsto ε a hε ha m g κ t p hm hg hκ h hh hb hz

#print axioms matter_defect_velocity
#print axioms potential_symbolMean
#print axioms boostedDefectVelocity_symbolMean
#print axioms boostedDefectVelocity_integrable
#print axioms initialRateLimit_classical
#print axioms initial_quantum_derivative_classical_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedRateIdentification
