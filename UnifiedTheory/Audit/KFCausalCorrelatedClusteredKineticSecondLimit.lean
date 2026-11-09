/- The natural second kinetic action D P_j P_j D on general clustered
limits. Both unbounded momentum steps are actual graphs; the final inverse
half-clock is an everywhere-defined bounded operator. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredSecondTransverseGraphs
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticGraphs
import UnifiedTheory.Audit.KFCausalClockFloorKineticSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticSecondLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredClockVectors (vector limitingVector)
open KFCausalCorrelatedClusteredInverseHalfLimit (damped damped_continuous damped_memLp)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalClockFloorKineticSquare (reverse square)

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε h : ℝ)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

local notation "dc" => damped_continuous ε c hε hc
local notation "dc2" => damped_memLp ε c hε hc hc2
local notation "K" => KFCausalCorrelatedClusteredKineticGraphs.finiteOutput f c α β ε h hα hβ hε hc hc2
local notation "k" => KFCausalCorrelatedClusteredKineticGraphs.limitingOutput f c α β ε h hα hβ hε hc hc2

def finiteOutput (δ : ℝ) (j : Fin 4) : Hilbert := inverseL ε hε
  (KFCausalCorrelatedClusteredSecondTransverseGraphs.finiteOutput f (damped ε c) α β h hα hβ dc dc2 δ j)

def limitingOutput (j : Fin 4) : Hilbert := inverseL ε hε
  (KFCausalCorrelatedClusteredSecondTransverseGraphs.limitingOutput f (damped ε c) α β h hα hβ dc dc2 j)

theorem finite_reverse_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    (K δ j,finiteOutput f c α β ε h hα hβ hε hc hc2 δ j) ∈ (reverse ε h (modelDirections j)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalCorrelatedClusteredSecondTransverseGraphs.finite_graph f (damped ε c) α β h hα hβ dc dc2 δ hδ j,
    (inverseL_graph ε hε _ _).mpr rfl⟩

theorem finite_square_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    (vector f c α β hα hβ hw hc2 δ,finiteOutput f c α β ε h hα hβ hε hc hc2 δ j) ∈
      (square ε h (modelDirections j)).graph :=
  (composition_graph _ _ _ _).mpr ⟨K δ j,
    KFCausalCorrelatedClusteredKineticGraphs.finite_graph f c α β ε h hα hβ hw hε hc hc2 δ hδ j,
    finite_reverse_graph f c α β ε h hα hβ hε hc hc2 δ hδ j⟩

theorem output_tendsto (j : Fin 4) :
    Tendsto (fun δ => finiteOutput f c α β ε h hα hβ hε hc hc2 δ j) (𝓝[>] 0)
      (𝓝 (limitingOutput f c α β ε h hα hβ hε hc hc2 j)) :=
  ((inverseL ε hε).continuous.tendsto _).comp
    (KFCausalCorrelatedClusteredSecondTransverseGraphs.output_tendsto f (damped ε c) α β h hα hβ dc dc2 j)

theorem limiting_reverse_graph (j : Fin 4) :
    (k j,limitingOutput f c α β ε h hα hβ hε hc hc2 j) ∈ (reverse ε h (modelDirections j)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalCorrelatedClusteredSecondTransverseGraphs.limiting_graph f (damped ε c) α β h hα hβ dc dc2 j,
    (inverseL_graph ε hε _ _).mpr rfl⟩

theorem limiting_square_graph (j : Fin 4) :
    (limitingVector f c α β hα hβ hw hc2 hc,limitingOutput f c α β ε h hα hβ hε hc hc2 j) ∈
      (square ε h (modelDirections j)).graph :=
  (composition_graph _ _ _ _).mpr ⟨k j,
    KFCausalCorrelatedClusteredKineticGraphs.limiting_graph f c α β ε h hα hβ hw hε hc hc2 j,
    limiting_reverse_graph f c α β ε h hα hβ hε hc hc2 j⟩

include hε in
theorem limiting_square_domain (j : Fin 4) : limitingVector f c α β hα hβ hw hc2 hc ∈
    (square ε h (modelDirections j)).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_square_graph f c α β ε h hα hβ hw hε hc hc2 j)

theorem reverse_graph_tendsto (j : Fin 4) :
    Tendsto (fun δ => (K δ j,finiteOutput f c α β ε h hα hβ hε hc hc2 δ j)) (𝓝[>] 0)
      (𝓝 (k j,limitingOutput f c α β ε h hα hβ hε hc hc2 j)) :=
  (KFCausalCorrelatedClusteredKineticGraphs.output_tendsto f c α β ε h hα hβ hε hc hc2 j).prodMk_nhds
    (output_tendsto f c α β ε h hα hβ hε hc hc2 j)

#print axioms finite_reverse_graph
#print axioms finite_square_graph
#print axioms output_tendsto
#print axioms limiting_reverse_graph
#print axioms limiting_square_graph
#print axioms limiting_square_domain
#print axioms reverse_graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticSecondLimit
