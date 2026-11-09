/- The paired excitation has exact clock and kinetic responses on its
actual pure-clock composition graphs. The clock contribution is bounded
below by its energy and all four kinetic responses are nonnegative. -/
import UnifiedTheory.Audit.KFCausalChargedPairClockMomentum
import UnifiedTheory.Audit.KFCausalDirectionalClockComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalChargedPairFactorResponse
noncomputable section
open KFCausalChargedPairDomain (state output output_graph directions combine)
open KFCausalChargedPairClockMomentum (momentum factor momentum_graph factor_graph)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalCoherentFactorResponseBounds (kineticIndex)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "f" => state ε a h hε ha hh
local notation "Bf" => momentum ε a h hε ha hh
local notation "u" => output ε a h hε ha hh hb modelDirections pointField
local notation "v" => factor ε a h hε ha hh hb modelDirections pointField

def factorRate (j : Fin 8) : ℝ := (-2/h)*(inner ℂ (u j) (v j)).im
def factorEnergy (j : Fin 8) : ℝ := ‖u j‖^2

theorem clock_composition_graph :
    (u 0,v 0-correction ε hε h (u 0)) ∈ (pureMomentum ε hε h).graph := by
  have hg (i : Fin 4) := KFCausalDirectionalClockComposition.composition_graph
    ε a h hε ha hh hb 1 0 (directions i) 2
  have hs := (pureMomentum ε hε h).graph.smul_mem (1/4:ℂ)
    ((pureMomentum ε hε h).graph.add_mem
      ((pureMomentum ε hε h).graph.sub_mem
        ((pureMomentum ε hε h).graph.sub_mem (hg 0) (hg 1)) (hg 2)) (hg 3))
  convert hs using 1
  congr 1
  simp only [output,factor,combine,Prod.add_def,Prod.sub_def,
    map_smul,map_add,map_sub,smul_add,smul_sub]
  abel

theorem clock_response :
    factorRate ε a h hε ha hh hb 0 =
      -KFCausalClockFloorPureClockKineticResponse.response ε hε (u 0) :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh f (u 0) Bf (v 0) _
    (output_graph ε a h hε ha hh hb modelDirections pointField 0)
    (momentum_graph ε a h hε ha hh)
    (factor_graph ε a h hε ha hh hb modelDirections pointField 0)
    (clock_composition_graph ε a h hε ha hh hb)

theorem clock_bounds :
    -‖f‖^2 ≤ factorRate ε a h hε ha hh hb 0 ∧ factorRate ε a h hε ha hh hb 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_norm_bound ε hε f (u 0)
    (output_graph ε a h hε ha hh hb modelDirections pointField 0)

theorem clock_energy_bounds :
    -(1/(4*ε))*factorEnergy ε a h hε ha hh hb 0 ≤ factorRate ε a h hε ha hh hb 0 ∧
      factorRate ε a h hε ha hh hb 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε f (u 0)

theorem kinetic_response (i : Fin 4) :
    factorRate ε a h hε ha hh hb (kineticIndex i) =
      KFCausalClockFloorPureClockKineticResponse.response ε hε (u (kineticIndex i)) := by
  apply KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i)
    f _ Bf _
  · have hg := output_graph ε a h hε ha hh hb modelDirections pointField (kineticIndex i)
    fin_cases i <;> exact hg
  · exact momentum_graph ε a h hε ha hh
  · have hg := factor_graph ε a h hε ha hh hb modelDirections pointField (kineticIndex i)
    fin_cases i <;> exact hg

theorem kinetic_bounds (i : Fin 4) :
    0 ≤ factorRate ε a h hε ha hh hb (kineticIndex i) ∧
      factorRate ε a h hε ha hh hb (kineticIndex i) ≤
        (1/(4*ε))*factorEnergy ε a h hε ha hh hb (kineticIndex i) := by
  rw [kinetic_response]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε (u (kineticIndex i))

#print axioms clock_composition_graph
#print axioms clock_response
#print axioms clock_bounds
#print axioms clock_energy_bounds
#print axioms kinetic_response
#print axioms kinetic_bounds
end
end UnifiedTheory.Audit.KFCausalChargedPairFactorResponse
