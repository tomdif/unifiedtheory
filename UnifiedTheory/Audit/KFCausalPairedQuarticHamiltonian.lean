/- The corrected quartic and its actual clock momentum belong to the
completed charge-averaged Hamiltonian form. Exact energy and response
decompositions are supplied; no lower response estimate is asserted. -/
import UnifiedTheory.Audit.KFCausalPairedQuarticDomain
import UnifiedTheory.Audit.KFCausalFixedCommonEnergyPairing
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPairedQuarticHamiltonian
noncomputable section
open KFCausalPairedQuarticCharge (correctedState corrected_zeroSector corrected_ne_zero)
open KFCausalPairedQuarticDomain
  (momentum momentum_zeroSector momentum_graph output output_graph momentumOutput momentumOutput_graph)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open KFCausalFixedCommonEnergyPairing (fixedLift fixedLift_energy fixedLift_response)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "ψ" => correctedState ε a h hε ha hh
local notation "Bψ" => momentum ε a h hε ha hh
local notation "u" => output ε a h hε ha hh hb modelDirections pointField
local notation "v" => momentumOutput ε a h hε ha hh hb modelDirections pointField

def stateLift (mass2 quartic vacuum t : ℝ) : FormSpace ε hε h hh hb mass2 quartic vacuum t :=
  graphFormVector ε hε h hh hb mass2 quartic vacuum t
    (fixedLift ε h hε hh hb mass2 quartic vacuum t ψ
      (corrected_zeroSector ε a h hε ha hh) u
      (output_graph ε a h hε ha hh hb modelDirections pointField))
def momentumLift (mass2 quartic vacuum t : ℝ) : FormSpace ε hε h hh hb mass2 quartic vacuum t :=
  graphFormVector ε hε h hh hb mass2 quartic vacuum t
    (fixedLift ε h hε hh hb mass2 quartic vacuum t Bψ
      (momentum_zeroSector ε a h hε ha hh) v
      (momentumOutput_graph ε a h hε ha hh hb modelDirections pointField))

theorem stateLift_embedding (mass2 quartic vacuum t : ℝ) :
    embedding ε hε h hh hb mass2 quartic vacuum t
      (stateLift ε a h hε ha hh hb mass2 quartic vacuum t) = ψ := rfl

theorem momentumLift_embedding (mass2 quartic vacuum t : ℝ) :
    embedding ε hε h hh hb mass2 quartic vacuum t
      (momentumLift ε a h hε ha hh hb mass2 quartic vacuum t) = Bψ := rfl

theorem lifted_momentum_graph (mass2 quartic vacuum t : ℝ) :
    (embedding ε hε h hh hb mass2 quartic vacuum t
        (stateLift ε a h hε ha hh hb mass2 quartic vacuum t),
      embedding ε hε h hh hb mass2 quartic vacuum t
        (momentumLift ε a h hε ha hh hb mass2 quartic vacuum t)) ∈ (pureMomentum ε hε h).graph :=
  momentum_graph ε a h hε ha hh

theorem stateLift_ne_zero (mass2 quartic vacuum t : ℝ) :
    stateLift ε a h hε ha hh hb mass2 quartic vacuum t ≠ 0 := by
  intro hz
  have he := congrArg (embedding ε hε h hh hb mass2 quartic vacuum t) hz
  rw [stateLift_embedding,map_zero] at he
  exact corrected_ne_zero ε a h hε ha hh he

def fullEnergy (mass2 quartic vacuum t : ℝ) : ℝ :=
  ‖energyOutput ε hε h hh hb mass2 quartic vacuum t
    (stateLift ε a h hε ha hh hb mass2 quartic vacuum t)‖^2
def fullResponse (mass2 quartic vacuum t : ℝ) : ℝ :=
  (-2/h)*(inner ℂ
    (energyOutput ε hε h hh hb mass2 quartic vacuum t
      (stateLift ε a h hε ha hh hb mass2 quartic vacuum t))
    (energyOutput ε hε h hh hb mass2 quartic vacuum t
      (momentumLift ε a h hε ha hh hb mass2 quartic vacuum t))).im

theorem energy_decomposition (mass2 quartic vacuum t : ℝ) :
    fullEnergy ε a h hε ha hh hb mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*‖u j‖^2 :=
  fixedLift_energy ε h hε hh hb mass2 quartic vacuum t ψ
    (corrected_zeroSector ε a h hε ha hh) u
    (output_graph ε a h hε ha hh hb modelDirections pointField)

theorem response_decomposition (mass2 quartic vacuum t : ℝ) :
    fullResponse ε a h hε ha hh hb mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*((-2/h)*(inner ℂ (u j) (v j)).im) :=
  fixedLift_response ε h hε hh hb mass2 quartic vacuum t ψ
    (corrected_zeroSector ε a h hε ha hh) u
    (output_graph ε a h hε ha hh hb modelDirections pointField) Bψ
    (momentum_zeroSector ε a h hε ha hh) v
    (momentumOutput_graph ε a h hε ha hh hb modelDirections pointField)

#print axioms stateLift_embedding
#print axioms momentumLift_embedding
#print axioms lifted_momentum_graph
#print axioms stateLift_ne_zero
#print axioms energy_decomposition
#print axioms response_decomposition
end
end UnifiedTheory.Audit.KFCausalPairedQuarticHamiltonian
