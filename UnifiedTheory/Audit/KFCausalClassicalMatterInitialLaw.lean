/- The already proved quantum initial law embedded into the actual full
classical matter flow coordinates. Initial energy identification is on this
law's clock-axis support, not a full symbol theorem away from that support. -/
import UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase
import UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumSector
import UnifiedTheory.Audit.KFCausalClassicalMatterLaw
import UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification
import UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClassicalMatterInitialLaw
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase rotate rotate_smul shear)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean (mean_const)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterClock (fullHamiltonian_clockShift)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents (clockShift)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit (initialClassicalEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorInitialAveragedEnergy (physical_initial_energy_tendsto)
open UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)

def initialLaw (ε a τ : ℝ) : Measure TimePhase := (classicalLaw ε a).map (initialEmbedding τ)

theorem initialLaw_probability (ε a τ : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    IsProbabilityMeasure (initialLaw ε a τ) := by
  letI := classicalLaw_probability ε a hε ha
  exact Measure.isProbabilityMeasure_map (initialEmbedding_continuous τ).measurable.aemeasurable

theorem initialLaw_axis (ε a τ : ℝ) :
    initialLaw ε a τ = (clockLaw ε a).map (fun s => (τ,clockShift s 0 (0:Phase))) := by
  unfold initialLaw classicalLaw
  rw [Measure.map_map (initialEmbedding_continuous τ).measurable clockAxis_continuous.measurable]
  congr 1
  funext s
  exact initialEmbedding_axis τ s

def phaseTest (r u : ℝ) (ξ η : KFCausalTransverseDilationFlow.Transverse) (x : TimePhase) : ℂ :=
  classicalPhase r u ξ η (phaseEquiv.symm x.2)

theorem phaseTest_continuous (r u : ℝ) (ξ η : KFCausalTransverseDilationFlow.Transverse) :
    Continuous (phaseTest r u ξ η) :=
  (classicalPhase_continuous r u ξ η).comp (phaseEquiv.symm.continuous.comp continuous_snd)

theorem initialLaw_test (ε a τ r u : ℝ) (ξ η : KFCausalTransverseDilationFlow.Transverse) :
    (∫ x, phaseTest r u ξ η x ∂initialLaw ε a τ) =
      ∫ z, classicalPhase r u ξ η z ∂classicalLaw ε a := by
  rw [initialLaw,integral_map (initialEmbedding_continuous τ).measurable.aemeasurable
    (phaseTest_continuous r u ξ η).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [phaseTest,initialEmbedding,Homeomorph.symm_apply_apply]

theorem weightedMean_zero (m g κ C : ℝ) : weightedMean m g κ C (0:Phase) = κ := by
  have hr (θ : ℝ) : rotate θ (0:Phase) = 0 := by
    simpa only [zero_smul] using rotate_smul θ 0 (0:Phase)
  simp [weightedMean,hr,potential,fieldValue_eq,KFCausalClassicalChargePhase.shear_eq,
    KFCausalClassicalChargePhase.diagonalPairing,mean_const]

theorem hamiltonian_axis (ε m g κ τ s r : ℝ) :
    fullHamiltonian ε m g κ (τ,clockShift s r (0:Phase)) =
      KFCausalClockFloorVacuumReduction.canonicalHamiltonian ε κ τ s r := by
  rw [fullHamiltonian_clockShift]
  simp only [map_zero,zero_add]
  have he : hamiltonian ε m g κ τ (0:Phase) s r = hamiltonian ε 0 0 κ τ (0:Phase) s r := by
    simp only [hamiltonian,weightedMean_zero]
  rw [he,hamiltonian_vacuum]
  exact KFCausalClassicalAveragedVacuumSector.hamiltonian_zero ε κ τ s r

theorem initialLaw_energy (ε a m g κ τ : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ x, fullHamiltonian ε m g κ x ∂initialLaw ε a τ) = initialClassicalEnergy ε a κ τ := by
  have hc : Continuous (fun s => (τ,clockShift s 0 (0:Phase))) := by
    have he := funext (initialEmbedding_axis τ)
    exact he ▸ ((initialEmbedding_continuous τ).comp clockAxis_continuous)
  rw [initialLaw_axis,integral_map hc.measurable.aemeasurable
    (fullHamiltonian_contDiff ε m g κ hε.le 1).continuous.aestronglyMeasurable]
  simp_rw [hamiltonian_axis]
  exact initial_energy_clockLaw ε a κ τ hε ha

theorem physical_initial_energy_full_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ τ : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hn : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => timeEnergy ε hε (h n) (hn n) (hb n) m g κ τ
      (state ε a hε ha (h n) (hn n) (hb n) (h1 n) m g κ τ hm hg hκ))
      atTop (𝓝 (∫ x, fullHamiltonian ε m g κ x ∂initialLaw ε a τ)) := by
  rw [initialLaw_energy ε a m g κ τ hε ha]
  exact physical_initial_energy_tendsto ε a hε ha m g κ τ hm hg hκ h hn hb h1 hz

theorem physical_initial_characteristic_full_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0))
    (m g κ τ : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (r u : ℝ) (ξ η : KFCausalTransverseDilationFlow.Transverse) :
    Tendsto (fun n =>
      let f := KFCausalClockFloorAveragedFormTransport.embedding ε hε (h n) (hh n) (hb n) m g κ 0
        (state ε a hε ha (h n) (hh n) (hb n) (h1 n) m g κ τ hm hg hκ)
      inner ℂ f (observable (h n) r u ξ η f)) atTop
      (𝓝 (∫ x, phaseTest r u ξ η x ∂initialLaw ε a τ)) := by
  rw [initialLaw_test]
  exact physical_state_characteristic_tendsto ε a hε ha h hh hb h1 hz m g κ τ hm hg hκ r u ξ η

#print axioms initialLaw_probability
#print axioms initialLaw_axis
#print axioms phaseTest_continuous
#print axioms initialLaw_test
#print axioms weightedMean_zero
#print axioms hamiltonian_axis
#print axioms initialLaw_energy
#print axioms physical_initial_energy_full_limit
#print axioms physical_initial_characteristic_full_limit

end
end UnifiedTheory.Audit.KFCausalClassicalMatterInitialLaw

