/- The actual clock and four kinetic responses on mixed-clock neutral
polynomial states. The clock composition is proved, and every response
identity uses the existing natural operator graphs. -/
import UnifiedTheory.Audit.KFCausalPolynomialClockComposition
import UnifiedTheory.Audit.KFCausalNeutralMixedClockState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralMixedClockFactorResponse
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic (correction)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalCoherentFactorResponseBounds (kineticIndex)
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles (neutralSource)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockState

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
  (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ)
local notation "f" => state ε h hε hh N a p ha b C P
local notation "Bf" => momentum ε h hε hh N a p ha b C P
local notation "u" => output ε h hε hh N a p ha b C P hb
local notation "v" => momentumOutput ε h hε hh N a p ha b C P hb

def factorRate (j : Fin 8) : ℝ := (-2/h)*(inner ℂ (u j) (v j)).im
def factorEnergy (j : Fin 8) : ℝ := ‖u j‖^2

theorem clock_composition_graph :
    (u 0,v 0-correction ε hε h (u 0)) ∈ (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      KFCausalPolynomialClockComposition.polynomial_composition_graph
        ε (a i) h hε (ha i) hh hb (C i) (p i) (neutralSource (b i)) 4 (P i))
  simpa only [output,momentumOutput,← prod_mk_sum,Finset.sum_sub_distrib,map_sum] using hs

theorem clock_response :
    factorRate ε h hε hh hb N a p ha b C P 0 =
      -KFCausalClockFloorPureClockKineticResponse.response ε hε (u 0) :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh f (u 0) Bf (v 0) _
    (output_graph ε h hε hh N a p ha b C P hb 0)
    (momentum_graph ε h hε hh N a p ha b C P)
    (momentumOutput_graph ε h hε hh N a p ha b C P hb 0)
    (clock_composition_graph ε h hε hh hb N a p ha b C P)

theorem clock_bounds :
    -‖f‖^2 ≤ factorRate ε h hε hh hb N a p ha b C P 0 ∧
      factorRate ε h hε hh hb N a p ha b C P 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_norm_bound ε hε f (u 0)
    (output_graph ε h hε hh N a p ha b C P hb 0)

theorem clock_energy_bounds :
    -(1/(4*ε))*factorEnergy ε h hε hh hb N a p ha b C P 0 ≤
      factorRate ε h hε hh hb N a p ha b C P 0 ∧
      factorRate ε h hε hh hb N a p ha b C P 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε f (u 0)

theorem kinetic_response (i : Fin 4) :
    factorRate ε h hε hh hb N a p ha b C P (kineticIndex i) =
      KFCausalClockFloorPureClockKineticResponse.response ε hε (u (kineticIndex i)) := by
  apply KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i)
    f _ Bf _
  · have hg := output_graph ε h hε hh N a p ha b C P hb (kineticIndex i)
    fin_cases i <;> exact hg
  · exact momentum_graph ε h hε hh N a p ha b C P
  · have hg := momentumOutput_graph ε h hε hh N a p ha b C P hb (kineticIndex i)
    fin_cases i <;> exact hg

theorem kinetic_bounds (i : Fin 4) :
    0 ≤ factorRate ε h hε hh hb N a p ha b C P (kineticIndex i) ∧
      factorRate ε h hε hh hb N a p ha b C P (kineticIndex i) ≤
        (1/(4*ε))*factorEnergy ε h hε hh hb N a p ha b C P (kineticIndex i) := by
  rw [kinetic_response]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε (u (kineticIndex i))

#print axioms clock_composition_graph
#print axioms clock_response
#print axioms clock_bounds
#print axioms clock_energy_bounds
#print axioms kinetic_response
#print axioms kinetic_bounds
end
end UnifiedTheory.Audit.KFCausalNeutralMixedClockFactorResponse
