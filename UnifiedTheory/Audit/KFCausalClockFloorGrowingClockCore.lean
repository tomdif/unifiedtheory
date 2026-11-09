/- The intersection of the actual growing-operator and half-clock domains
is a core for each of these two operators. The reverse graph density uses
strong convergence in the half-clock graph, not Hilbert-space density alone.
The static kinetic terms of the full Hamiltonian are not covered here. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingClockApproximation
import UnifiedTheory.Audit.KFCausalHamiltonianCoreFromSources

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingClockCore
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorGrowingClockApproximation
open KFCausalHamiltonianCoreFromSources (graphMap sectorGraph source_graph_closure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb m g k
local notation "R" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hb m g k

def commonDomain : Submodule ℂ Hilbert := (G).domain ⊓ (clockHalf ε).domain
def growingGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (G).graph ⊓ (clockHalf ε).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)
def halfGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (clockHalf ε).graph ⊓ (G).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)

theorem growing_graph_core :
    (growingGraph ε hε h hh hb m g k).topologicalClosure = (G).graph := by
  have hd : (clockHalf ε).domain.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (clockHalf_selfAdjoint ε).dense_domain
  have he := source_graph_closure G (R 1) 1
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hb m g k 1 zero_lt_one)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hb m g k 1 zero_lt_one)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_closed ε hε h hh hb m g k)
    ⊤ (clockHalf ε).domain isClosed_univ hd (fun _ _ => trivial) (fun _ _ => trivial)
  have hm : (clockHalf ε).domain.map (graphMap (R 1) 1).toLinearMap ≤
      growingGraph ε hε h hh hb m g k := by
    rintro p ⟨f,hf,rfl⟩
    obtain ⟨hx,hv⟩ := KFCausalClockFloorGrowingYosida.resolves ε hε h hh hb m g k 1 zero_lt_one f
    exact ⟨(G).mem_graph_iff.mpr ⟨⟨R 1 f,hx⟩,rfl,hv⟩,
      KFCausalClockFloorGrowingClockResolvent.resolvent_half_domain
        ε hε h hh hb m g k 1 zero_lt_one f hf⟩
  have hc := Submodule.topologicalClosure_mono hm
  rw [he] at hc
  have hs : sectorGraph G ⊤ = (G).graph := by simp [sectorGraph]
  rw [hs] at hc
  exact le_antisymm (Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_closed ε hε h hh hb m g k)) hc

theorem half_graph_core :
    (halfGraph ε hε h hh hb m g k).topologicalClosure = (clockHalf ε).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
      (clockHalf_selfAdjoint ε).isClosed
  · rintro ⟨f,z⟩ hf
    exact mem_closure_of_tendsto (half_graph_convergence ε hε h hh hb m g k f z)
      (Eventually.of_forall fun n =>
        ⟨approximation_half_graph ε hε h hh hb m g k n f z hf,
          approximation_growing_domain ε hε h hh hb m g k n f⟩)

theorem common_dense : Dense (commonDomain ε hε h hh hb m g k : Set Hilbert) := by
  have hs : ((clockHalf ε).domain : Set Hilbert) ⊆
      closure (commonDomain ε hε h hh hb m g k : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (approximation_strong ε hε h hh hb m g k f)
      (Eventually.of_forall fun n =>
        ⟨approximation_growing_domain ε hε h hh hb m g k n f,
          LinearPMap.mem_domain_of_mem_graph
            (approximation_half_graph ε hε h hh hb m g k n f
              (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩))⟩)
  intro f
  exact closure_minimal hs isClosed_closure ((clockHalf_selfAdjoint ε).dense_domain f)

#print axioms growing_graph_core
#print axioms half_graph_core
#print axioms common_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingClockCore
