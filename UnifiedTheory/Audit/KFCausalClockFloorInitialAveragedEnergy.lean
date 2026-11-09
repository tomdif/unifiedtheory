/- Exact initial energy in the actual completed charge-averaged form.
The invariant trial's averaging and completion preserve its seed energy;
its previously constructed normalized form state therefore has the same
semiclassical energy limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit
import UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialAveragedEnergy
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory (timeEnergy_smul)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector)
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (seedEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (hbar : ℝ) (hh : hbar ≠ 0)
  (hb : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
  (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
local notation "V₀" => FormSpace ε hε hbar hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hb mass2 quartic vacuum 0
local notation "E" => timeEnergy ε hε hbar hh hb mass2 quartic vacuum
local notation "f" => trialState ε a hbar hε ha hh
local notation "B" => energyBudget ε a modelDirections pointField mass2 quartic vacuum s
local notation "M" => gaussianMass (groundWidth hbar) (neutralWidth hbar)

include hm hq hv in
theorem exists_trial_exact_energy : ∃ w : V₀, J w = f ∧
    E s w = seedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum s
      (trialCommon ε a hbar hε ha hh hb modelDirections pointField) := by
  let baseData := KFCausalClockFloorFormHamiltonian.formData ε hε hbar
    (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s
  let v := KFCausalClockFloorFormHamiltonian.commonFormVector ε hε hbar
    (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s
    (trialCommon ε a hbar hε ha hh hb modelDirections pointField)
  have hjv : KFCausalClosedGraphForm.embedding baseData v = f :=
    KFCausalClockFloorFormHamiltonian.commonFormVector_embedding ε hε hbar
      (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s _
  have hzv : KFCausalClosedGraphForm.embedding baseData v ∈ zeroSector hbar hh :=
    Eq.mpr (congrArg (fun z : Hilbert => z ∈ zeroSector hbar hh) hjv)
      (trialState_mem_zeroSector ε a hbar hε ha hh)
  have lift := KFCausalAveragedFixedEnergy.exists_fixed_lift
    (H := Hilbert) («E» := KFCausalClosedGraphForm.FormSpace baseData)
    (K := KFCausalFiniteJointGraph.Output (Fin 8) Hilbert)
    (KFCausalPhysicalCircleAction.group hbar hh) (2*Real.pi)
    (KFCausalClosedGraphForm.embedding baseData) (KFCausalClosedGraphForm.energyOutput baseData)
    (KFCausalClosedGraphForm.embedding_injective baseData) (by positivity)
  have hl := lift v hzv
  let u := Classical.choose hl
  have hu := Classical.choose_spec hl
  let g := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε hbar hh hb mass2 quartic vacuum s u
  let w : V₀ := formTransfer ε hε hbar hh hb mass2 quartic vacuum s 0 g
  have hj : J w = f :=
    (transfer_embedding ε hε hbar hh hb mass2 quartic vacuum s 0 g).trans (hu.1.trans hjv)
  have he : E s w = KFCausalClockFloorJointEnergy.seedEnergy ε hε hbar modelDirections pointField
      mass2 quartic vacuum s (trialCommon ε a hbar hε ha hh hb modelDirections pointField) := by
    calc
      _ = ‖energyOutput ε hε hbar hh hb mass2 quartic vacuum s g‖^2 :=
        (timeEnergy_actual ε hε hbar hh hb mass2 quartic vacuum s w).symm.trans
          (congrArg (fun z => ‖energyOutput ε hε hbar hh hb mass2 quartic vacuum s z‖^2)
            (transfer_inverse ε hε hbar hh hb mass2 quartic vacuum s 0 g))
      _ = ‖KFCausalClosedGraphForm.energyOutput baseData v‖^2 := hu.2
      _ = _ := KFCausalClockFloorFormHamiltonian.commonFormVector_energy ε hε hbar
        (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s hm hq hv _
  exact ⟨w,hj,he⟩

theorem state_exact_energy :
    E s (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv) =
      seedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum s
        (trialCommon ε a hbar hε ha hh hb modelDirections pointField)/‖f‖^2 := by
  obtain ⟨w,hw,he⟩ := exists_trial_exact_energy ε a hε ha hbar hh hb mass2 quartic vacuum s hm hq hv
  let r : ℝ := ‖f‖⁻¹
  have hj : J (r • w) = unitTrial ε a hbar hε ha hh :=
    ((J).map_smul_of_tower r w).trans (congrArg (fun x : Hilbert => r • x) hw)
  have hs : state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv = r • w :=
    embedding_injective ε hε hbar hh hb mass2 quartic vacuum 0
      ((state_embedding ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv).trans hj.symm)
  rw [hs,timeEnergy_smul,he]
  dsimp only [r]
  rw [inv_pow]
  ring

omit hbar hh hb hh1 in
theorem physical_initial_energy_tendsto
    (h : ℕ → ℝ) (hn : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => timeEnergy ε hε (h n) (hn n) (hb n) mass2 quartic vacuum s
      (state ε a hε ha (h n) (hn n) (hb n) (h1 n) mass2 quartic vacuum s hm hq hv))
      atTop (𝓝 (initialClassicalEnergy ε a vacuum s)) := by
  simp_rw [state_exact_energy]
  exact seed_energy_tendsto ε a hε ha h hn hb hz modelDirections pointField mass2 quartic vacuum s

#print axioms exists_trial_exact_energy
#print axioms state_exact_energy
#print axioms physical_initial_energy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialAveragedEnergy
