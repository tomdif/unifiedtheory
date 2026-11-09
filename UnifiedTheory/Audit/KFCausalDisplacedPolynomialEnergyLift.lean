/- Neutral polynomial packets and their actual pure-clock momenta lift
into the full charge-averaged eight-factor energy form. The lifts and
projected form domains are constructed from continuous actual orbits. -/
import UnifiedTheory.Audit.KFCausalDisplacedPolynomialFormOrbit
import UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalDisplacedPolynomialEnergyLift
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialOrbit
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialFormOrbit
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift (lift)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (P : Polynomial ℂ)

def inputOrbit (j : Fin 8) (θ : ℝ) : Hilbert :=
  packetFactor ε a h hε ha hh (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)
    P hb modelDirections pointField j

def momentumOrbit (j : Fin 8) (θ : ℝ) : Hilbert :=
  momentumFactor ε a h hε ha hh (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)
    P hb modelDirections pointField j

theorem inputOrbit_continuous (j : Fin 8) :
    Continuous (inputOrbit ε a h hε ha hh hb q k P j) :=
  (packetFactor_continuous ε a h hε ha hh hb q k P modelDirections pointField j).comp
    (continuous_const.mul continuous_id)

theorem momentumOrbit_continuous (j : Fin 8) :
    Continuous (momentumOrbit ε a h hε ha hh hb q k P j) :=
  (momentumFactor_continuous ε a h hε ha hh hb q k P modelDirections pointField j).comp
    (continuous_const.mul continuous_id)

theorem orbit_memLp (j : Fin 8) :
    MemLp (inputOrbit ε a h hε ha hh hb q k P j) 2 angleMeasure ∧
      MemLp (momentumOrbit ε a h hε ha hh hb q k P j) 2 angleMeasure :=
  ⟨continuous_angle_memLp _ (inputOrbit_continuous ε a h hε ha hh hb q k P j),
    continuous_angle_memLp _ (momentumOrbit_continuous ε a h hε ha hh hb q k P j)⟩

variable (hq : q (.inr 0) = 0)

include hq in
theorem inputOrbit_graph (θ : ℝ) (j : Fin 8) :
    (action h hh (2*Real.pi*θ) (packet ε a h hε ha hh q k P),
      inputOrbit ε a h hε ha hh hb q k P j θ) ∈
        (energyFactor ε hε h modelDirections pointField j).graph :=
  packetFactor_action_graph ε a h hε ha hh q k P hq hb (2*Real.pi*θ) modelDirections pointField j

include hq in
theorem momentumOrbit_graph (θ : ℝ) (j : Fin 8) :
    (action h hh (2*Real.pi*θ) (momentum ε a h hε ha hh q k P),
      momentumOrbit ε a h hε ha hh hb q k P j θ) ∈
        (energyFactor ε hε h modelDirections pointField j).graph :=
  momentumFactor_action_graph ε a h hε ha hh q k P hq hb (2*Real.pi*θ) modelDirections pointField j

variable (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "E" => energyOperator ε hε h hp hh mass2 quartic vacuum t
local notation "f" => packet ε a h hε ha hh q k P
local notation "b" => momentum ε a h hε ha hh q k P
local notation "g" => inputOrbit ε a h hε ha hh hb q k P
local notation "v" => momentumOrbit ε a h hε ha hh hb q k P

def inputLift : Full :=
  lift ε h hε hh hb mass2 quartic vacuum t f g
    (inputOrbit_continuous ε a h hε ha hh hb q k P)
    (inputOrbit_graph ε a h hε ha hh hb q k P hq)

def momentumLift : Full :=
  lift ε h hε hh hb mass2 quartic vacuum t b v
    (momentumOrbit_continuous ε a h hε ha hh hb q k P)
    (momentumOrbit_graph ε a h hε ha hh hb q k P hq)

theorem lifts_embedding :
    embed (inputLift ε a h hε ha hh hb q k P hq mass2 quartic vacuum t) = f ∧
      embed (momentumLift ε a h hε ha hh hb q k P hq mass2 quartic vacuum t) = b := ⟨rfl,rfl⟩

include hq in
theorem both_energy_domains : f ∈ (E).domain ∧ b ∈ (E).domain :=
  ⟨(energy_domain ε hε h hp hh mass2 quartic vacuum t f).mpr
      ⟨inputLift ε a h hε ha hh hb q k P hq mass2 quartic vacuum t,rfl⟩,
    (energy_domain ε hε h hp hh mass2 quartic vacuum t b).mpr
      ⟨momentumLift ε a h hε ha hh hb q k P hq mass2 quartic vacuum t,rfl⟩⟩

include hq in
theorem actual_momentum_energy_domain (z : Hilbert) (hz : (f,z) ∈ (pureMomentum ε hε h).graph) :
    z ∈ (E).domain := by
  have he := (pureMomentum ε hε h).mem_graph_snd_inj' hz
    (momentum_graph ε a h hε ha hh q k P) rfl
  dsimp only at he
  rw [he]
  exact (both_energy_domains ε a h hε ha hh hb q k P hq mass2 quartic vacuum t).2

include hq in
theorem projected_energy_domains :
    zeroProjection h hh f ∈ (E).domain ∧ zeroProjection h hh b ∈ (E).domain := by
  have he := both_energy_domains ε a h hε ha hh hb q k P hq mass2 quartic vacuum t
  exact ⟨zeroProjection_mem_energy_domain ε hε h hp hh mass2 quartic vacuum t f he.1,
    zeroProjection_mem_energy_domain ε hε h hp hh mass2 quartic vacuum t b he.2⟩

#print axioms inputOrbit_continuous
#print axioms momentumOrbit_continuous
#print axioms orbit_memLp
#print axioms inputOrbit_graph
#print axioms momentumOrbit_graph
#print axioms lifts_embedding
#print axioms both_energy_domains
#print axioms actual_momentum_energy_domain
#print axioms projected_energy_domains
end
end UnifiedTheory.Audit.KFCausalDisplacedPolynomialEnergyLift
