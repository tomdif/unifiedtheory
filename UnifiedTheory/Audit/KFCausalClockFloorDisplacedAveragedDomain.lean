/- Constructed averaged energy-form vectors for the enlarged family.
Every canonical momentum boost is admissible because its whole charge
orbit has an actual integrable graph-form lift. No uniform small-hbar
averaged energy bound or propagation theorem is asserted here. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (state state_norm action_state)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit (parameter_clock state_boost)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure orbit orbitState_coe)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (m g κ t : ℝ) (q k : Joint 2 4) (hq : q (.inr 0) = 0)
local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε h (hamiltonian_bound ε h hb) m g κ t
local notation "BaseSpace" => KFCausalClosedGraphForm.FormSpace 𝒟
local notation "J" => KFCausalClosedGraphForm.embedding 𝒟
local notation "S" => state ε a h hε ha hh q k

def orbitLift : Lp BaseSpace 2 angleMeasure :=
  (formVector_orbit_memLp ε a h hε ha hh hb q k hq m g κ t).toLp
    (fun θ => formVector ε a h hε ha hh hb (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)
      ((parameter_clock (2*Real.pi*θ) q).trans hq) m g κ t)

theorem orbitLift_compatibility :
    (J).compLp (orbitLift ε a h hε ha hh hb m g κ t q k hq) = orbit (group h hh) (2*Real.pi) S := by
  apply Lp.ext
  filter_upwards [(J).coeFn_compLp (orbitLift ε a h hε ha hh hb m g κ t q k hq),
    (formVector_orbit_memLp ε a h hε ha hh hb q k hq m g κ t).coeFn_toLp,
    orbitState_coe (group h hh) (2*Real.pi) S] with θ hJ hv ho
  refine hJ.trans ?_
  change orbitLift ε a h hε ha hh hb m g κ t q k hq θ = _ at hv
  rw [hv,formVector_embedding,← action_state]
  exact ho.symm

def averagedVector : AveragedSpace ε hε h (hamiltonian_bound ε h hb) hh m g κ t :=
  ⟨WithLp.toLp 2 (S,orbitLift ε a h hε ha hh hb m g κ t q k hq),by
    change (J).compLp (orbitLift ε a h hε ha hh hb m g κ t q k hq) - orbit (group h hh) (2*Real.pi) S = 0
    exact sub_eq_zero.mpr (orbitLift_compatibility ε a h hε ha hh hb m g κ t q k hq)⟩

theorem averagedVector_embedding :
    embedding ε hε h (hamiltonian_bound ε h hb) hh m g κ t
      (averagedVector ε a h hε ha hh hb m g κ t q k hq) = S := rfl

theorem averagedVector_norm :
    ‖embedding ε hε h (hamiltonian_bound ε h hb) hh m g κ t
      (averagedVector ε a h hε ha hh hb m g κ t q k hq)‖ = 1 := state_norm ε a h hε ha hh q k

theorem averagedVector_energy (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    ‖energyOutput ε hε h (hamiltonian_bound ε h hb) hh m g κ t
      (averagedVector ε a h hε ha hh hb m g κ t q k hq)‖^2 =
      ∫ θ, KFCausalClockFloorJointEnergy.seedEnergy ε hε h modelDirections pointField m g κ t
        ⟨state ε a h hε ha hh (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k),
          state_commonEnergyDomain ε a h hε ha hh hb (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)
            ((parameter_clock (2*Real.pi*θ) q).trans hq) modelDirections pointField⟩ ∂angleMeasure := by
  rw [energy_integral]
  apply integral_congr_ae
  filter_upwards [(formVector_orbit_memLp ε a h hε ha hh hb q k hq m g κ t).coeFn_toLp] with θ hθ
  change ‖KFCausalClosedGraphForm.energyOutput 𝒟 (orbitLift ε a h hε ha hh hb m g κ t q k hq θ)‖^2 = _
  change orbitLift ε a h hε ha hh hb m g κ t q k hq θ = _ at hθ
  rw [hθ]
  exact formVector_energy ε a h hε ha hh hb _ _ _ m g κ t hm hg hκ

include hq in
theorem state_mem_energy_domain :
    S ∈ (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain :=
  (energy_domain ε hε h (hamiltonian_bound ε h hb) hh m g κ t S).mpr
    ⟨averagedVector ε a h hε ha hh hb m g κ t q k hq,rfl⟩

omit q k hq in
theorem boostedState_mem_energy_domain (p : Configuration) :
    boostedState ε a h hε ha hh (positionFrequency p.1 p.2) ∈
      (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain := by
  rw [← state_boost ε a h hε ha hh p]
  exact state_mem_energy_domain ε a h hε ha hh hb m g κ t (boostQ h (h⁻¹ • p)) (boostK (h⁻¹ • p)) rfl

#print axioms orbitLift_compatibility
#print axioms averagedVector_embedding
#print axioms averagedVector_norm
#print axioms averagedVector_energy
#print axioms state_mem_energy_domain
#print axioms boostedState_mem_energy_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedDomain
