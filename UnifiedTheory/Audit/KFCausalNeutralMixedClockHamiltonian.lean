/- Mixed-clock neutral states and their actual clock momenta lift into
the completed form of the model's charge-averaged Hamiltonian. The
energy and signed form response include all eight physical factors.
This is a fixed-time form identity, not a trajectory derivative. -/
import UnifiedTheory.Audit.KFCausalFixedCommonEnergyPairing
import UnifiedTheory.Audit.KFCausalNeutralMixedClockFactorResponse
import UnifiedTheory.Audit.KFCausalNeutralMixedClockCharge
import UnifiedTheory.Audit.KFCausalNeutralMixedClockBound
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralMixedClockHamiltonian
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight energyWeight_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open UnifiedTheory.Audit.KFCausalFixedCommonEnergyPairing
open UnifiedTheory.Audit.KFCausalNeutralMixedClockState
open UnifiedTheory.Audit.KFCausalNeutralMixedClockCharge (state_mem_zeroSector momentum_mem_zeroSector)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockFactorResponse (factorRate factorEnergy)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockPotential (potentialEnergy potentialResponse)
open UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse (physicalWeights)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)

private theorem physical_sum (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (r : Fin 8 → ℝ) :
    (∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*r i) =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+mass2/2*r 5+quartic/4*r 6+vacuum*r 7) := by
  simp_rw [energyWeight_norm_square mass2 quartic vacuum t hm hq hv]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
  (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ)
local notation "f" => state ε h hε hh N a p ha b C P
local notation "Bf" => momentum ε h hε hh N a p ha b C P
local notation "u" => output ε h hε hh N a p ha b C P hb
local notation "v" => momentumOutput ε h hε hh N a p ha b C P hb
local notation "E" => factorEnergy ε h hε hh hb N a p ha b C P
local notation "R" => factorRate ε h hε hh hb N a p ha b C P

variable (mass2 quartic vacuum t : ℝ)
local notation "V" => FormSpace ε hε h hh hb mass2 quartic vacuum t
local notation "J" => embedding ε hε h hh hb mass2 quartic vacuum t
local notation "A" => energyOutput ε hε h hh hb mass2 quartic vacuum t

def inputLift : V :=
  graphFormVector ε hε h hh hb mass2 quartic vacuum t
    (fixedLift ε h hε hh hb mass2 quartic vacuum t f
      (state_mem_zeroSector ε h hε hh N a p ha b C P) u
      (output_graph ε h hε hh N a p ha b C P hb))

def momentumLift : V :=
  graphFormVector ε hε h hh hb mass2 quartic vacuum t
    (fixedLift ε h hε hh hb mass2 quartic vacuum t Bf
      (momentum_mem_zeroSector ε h hε hh N a p ha b C P) v
      (momentumOutput_graph ε h hε hh N a p ha b C P hb))

local notation "L" => inputLift ε h hε hh hb N a p ha b C P mass2 quartic vacuum t
local notation "BL" => momentumLift ε h hε hh hb N a p ha b C P mass2 quartic vacuum t

theorem inputLift_embedding : J L = f := rfl
theorem momentumLift_embedding : J BL = Bf := rfl

theorem lifted_momentum_graph : (J L,J BL) ∈ (pureMomentum ε hε h).graph :=
  momentum_graph ε h hε hh N a p ha b C P

def fullEnergy : ℝ := ‖A L‖^2
def fullResponse : ℝ := (-2/h)*(inner ℂ (A L) (A BL)).im

theorem energy_decomposition :
    fullEnergy ε h hε hh hb N a p ha b C P mass2 quartic vacuum t =
      ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*E i :=
  fixedLift_energy ε h hε hh hb mass2 quartic vacuum t f
    (state_mem_zeroSector ε h hε hh N a p ha b C P) u
    (output_graph ε h hε hh N a p ha b C P hb)

theorem response_decomposition :
    fullResponse ε h hε hh hb N a p ha b C P mass2 quartic vacuum t =
      ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*R i :=
  fixedLift_response ε h hε hh hb mass2 quartic vacuum t f
    (state_mem_zeroSector ε h hε hh N a p ha b C P) u
    (output_graph ε h hε hh N a p ha b C P hb) Bf
    (momentum_mem_zeroSector ε h hε hh N a p ha b C P) v
    (momentumOutput_graph ε h hε hh N a p ha b C P hb)

theorem physical_energy (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    fullEnergy ε h hε hh hb N a p ha b C P mass2 quartic vacuum t =
      (E 0+E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2+mass2/2*E 5+quartic/4*E 6+vacuum*E 7) := by
  rw [energy_decomposition]
  exact physical_sum mass2 quartic vacuum t hm hq hv E

theorem physical_response (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    fullResponse ε h hε hh hb N a p ha b C P mass2 quartic vacuum t =
      (R 0+R 1+R 2)/2+Real.exp (2*t)*((R 3+R 4)/2+mass2/2*R 5+quartic/4*R 6+vacuum*R 7) := by
  rw [response_decomposition]
  exact physical_sum mass2 quartic vacuum t hm hq hv R

omit mass2 quartic vacuum t in
theorem unit_potential_energy :
    potentialEnergy ε h N a p b C P hε hh ha hb = E 7+E 5/2+E 6/4 := by
  simp [potentialEnergy,physicalWeights,index,factorEnergy,Fin.sum_univ_succ]
  ring

omit mass2 quartic vacuum t in
theorem unit_potential_response :
    potentialResponse ε h N a p b C P hε hh ha hb = R 7+R 5/2+R 6/4 := by
  simp [potentialResponse,physicalWeights,index,factorRate,Fin.sum_univ_succ]
  ring

omit mass2 quartic vacuum in
theorem unit_full_energy :
    fullEnergy ε h hε hh hb N a p ha b C P 1 1 1 t =
      E 0/2+(E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2+
        potentialEnergy ε h N a p b C P hε hh ha hb) := by
  rw [physical_energy ε h hε hh hb N a p ha b C P 1 1 1 t
    (by norm_num) (by norm_num) (by norm_num),unit_potential_energy]
  ring

omit mass2 quartic vacuum in
theorem unit_full_response :
    fullResponse ε h hε hh hb N a p ha b C P 1 1 1 t =
      R 0/2+(R 1+R 2)/2+Real.exp (2*t)*((R 3+R 4)/2+
        potentialResponse ε h N a p b C P hε hh ha hb) := by
  rw [physical_response ε h hε hh hb N a p ha b C P 1 1 1 t
    (by norm_num) (by norm_num) (by norm_num),unit_potential_response]
  ring

#print axioms inputLift_embedding
#print axioms momentumLift_embedding
#print axioms lifted_momentum_graph
#print axioms energy_decomposition
#print axioms response_decomposition
#print axioms physical_energy
#print axioms physical_response
#print axioms unit_potential_energy
#print axioms unit_potential_response
#print axioms unit_full_energy
#print axioms unit_full_response
end
end UnifiedTheory.Audit.KFCausalNeutralMixedClockHamiltonian
