/- The intersection of the actual ordered-potential Hamiltonian domain and the
unbounded half-clock domain is a graph core for each of these two operators.
The reverse graph density uses strong convergence in the half-clock graph norm.
Static kinetic terms and the full residual Hamiltonian are not covered here. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockApproximation
import UnifiedTheory.Audit.KFCausalHamiltonianCoreFromSources

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialClockCore
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorPotentialClockResolvent (resolvent resolves resolvent_half_domain)
open KFCausalClockFloorPotentialClockApproximation
open KFCausalHamiltonianCoreFromSources (graphMap sectorGraph source_graph_closure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "F" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb m g k
local notation "R" => resolvent ε hε h hh hb m g k

def commonDomain : Submodule ℂ Hilbert := (P).domain ⊓ (clockHalf ε).domain
def potentialGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (P).graph ⊓ (clockHalf ε).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)
def halfGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (clockHalf ε).graph ⊓ (P).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)

theorem potential_graph_core :
    (potentialGraph ε hε h hh hb m g k).topologicalClosure = (P).graph := by
  have hd : (clockHalf ε).domain.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (clockHalf_selfAdjoint ε).dense_domain
  have he := source_graph_closure P (R 1) 1
    (resolves ε hε h hh hb m g k 1 zero_lt_one)
    (left_inverse ε hε h hh hb m g k 1 zero_lt_one)
    (KFCausalClosedGraphForm.hamiltonian_closed F)
    ⊤ (clockHalf ε).domain isClosed_univ hd (fun _ _ => trivial) (fun _ _ => trivial)
  have hm : (clockHalf ε).domain.map (graphMap (R 1) 1).toLinearMap ≤
      potentialGraph ε hε h hh hb m g k := by
    rintro p ⟨f,hf,rfl⟩
    obtain ⟨hx,hv⟩ := resolves ε hε h hh hb m g k 1 zero_lt_one f
    exact ⟨(P).mem_graph_iff.mpr ⟨⟨R 1 f,hx⟩,rfl,hv⟩,
      resolvent_half_domain ε hε h hh hb m g k 1 zero_lt_one f hf⟩
  have hc := Submodule.topologicalClosure_mono hm
  rw [he] at hc
  have hs : sectorGraph P ⊤ = (P).graph := by simp [sectorGraph]
  rw [hs] at hc
  exact le_antisymm (Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
    (KFCausalClosedGraphForm.hamiltonian_closed F)) hc

theorem half_graph_core :
    (halfGraph ε hε h hh hb m g k).topologicalClosure = (clockHalf ε).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
      (clockHalf_selfAdjoint ε).isClosed
  · rintro ⟨f,z⟩ hf
    exact mem_closure_of_tendsto (half_graph_convergence ε hε h hh hb m g k f z)
      (Eventually.of_forall fun n =>
        ⟨approximation_half_graph ε hε h hh hb m g k n f z hf,
          approximation_potential_domain ε hε h hh hb m g k n f⟩)

theorem common_dense : Dense (commonDomain ε hε h hh hb m g k : Set Hilbert) := by
  have hs : ((clockHalf ε).domain : Set Hilbert) ⊆
      closure (commonDomain ε hε h hh hb m g k : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (approximation_strong ε hε h hh hb m g k f)
      (Eventually.of_forall fun n =>
        ⟨approximation_potential_domain ε hε h hh hb m g k n f,
          LinearPMap.mem_domain_of_mem_graph
            (approximation_half_graph ε hε h hh hb m g k n f
              (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩))⟩)
  intro f
  exact closure_minimal hs isClosed_closure ((clockHalf_selfAdjoint ε).dense_domain f)

#print axioms potential_graph_core
#print axioms half_graph_core
#print axioms common_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialClockCore
