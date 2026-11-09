/- All four natural clock-dressed kinetic graphs on the clustered
limits. The two closed factors are treated separately, retaining the
intermediate vector rather than presuming the composition is closed. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredTransverseGraphs
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInverseHalfLimit
import UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticGraphs
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredClockVectors (vector limitingVector vector_tendsto)
open KFCausalCorrelatedClusteredInverseHalfLimit (damped damped_continuous damped_memLp)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalPhysicalEnergyFactors (modelDirections)

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε h : ℝ)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

local notation "dc" => damped_continuous ε c hε hc
local notation "dc2" => damped_memLp ε c hε hc hc2

def finiteOutput (δ : ℝ) (j : Fin 4) : Hilbert :=
  KFCausalCorrelatedClusteredTransverseGraphs.finiteOutput f (damped ε c) α β h hα hβ dc dc2 δ j

def limitingOutput (j : Fin 4) : Hilbert :=
  KFCausalCorrelatedClusteredTransverseGraphs.limitingOutput f (damped ε c) α β h hα hβ dc dc2 j

theorem finite_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    (vector f c α β hα hβ hw hc2 δ,finiteOutput f c α β ε h hα hβ hε hc hc2 δ j) ∈
      (clockMomentum ε h (modelDirections j)).graph :=
  (composition_graph _ _ _ _).mpr ⟨vector f (damped ε c) α β hα hβ hw dc2 δ,
    KFCausalCorrelatedClusteredInverseHalfLimit.finite_graph ε c f α β hε hα hβ hw hc hc2 δ hδ,
    KFCausalCorrelatedClusteredTransverseGraphs.finite_graph f (damped ε c) α β h hα hβ hw dc dc2 δ hδ j⟩

theorem output_tendsto (j : Fin 4) :
    Tendsto (fun δ => finiteOutput f c α β ε h hα hβ hε hc hc2 δ j) (𝓝[>] 0)
      (𝓝 (limitingOutput f c α β ε h hα hβ hε hc hc2 j)) :=
  KFCausalCorrelatedClusteredTransverseGraphs.output_tendsto f (damped ε c) α β h hα hβ dc dc2 j

theorem limiting_graph (j : Fin 4) :
    (limitingVector f c α β hα hβ hw hc2 hc,limitingOutput f c α β ε h hα hβ hε hc hc2 j) ∈
      (clockMomentum ε h (modelDirections j)).graph :=
  (composition_graph _ _ _ _).mpr ⟨limitingVector f (damped ε c) α β hα hβ hw dc2 dc,
    KFCausalCorrelatedClusteredInverseHalfLimit.limiting_graph ε c f α β hε hα hβ hw hc hc2,
    KFCausalCorrelatedClusteredTransverseGraphs.limiting_graph f (damped ε c) α β h hα hβ hw dc dc2 j⟩

include hε in
theorem limiting_domain (j : Fin 4) : limitingVector f c α β hα hβ hw hc2 hc ∈
    (clockMomentum ε h (modelDirections j)).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_graph f c α β ε h hα hβ hw hε hc hc2 j)

theorem graph_tendsto (j : Fin 4) :
    Tendsto (fun δ => (vector f c α β hα hβ hw hc2 δ,finiteOutput f c α β ε h hα hβ hε hc hc2 δ j))
      (𝓝[>] 0) (𝓝 (limitingVector f c α β hα hβ hw hc2 hc,limitingOutput f c α β ε h hα hβ hε hc hc2 j)) :=
  (vector_tendsto f c α β hα hβ hw hc2 hc).prodMk_nhds (output_tendsto f c α β ε h hα hβ hε hc hc2 j)

#print axioms finite_graph
#print axioms output_tendsto
#print axioms limiting_graph
#print axioms limiting_domain
#print axioms graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticGraphs
