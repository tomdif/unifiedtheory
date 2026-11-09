/- An actual graph core for the growing Hamiltonian in the zero-charge
sector: its unit-shift resolvent applied to the dense projected coherent
source span. No common full/growing graph core or evolution invariance is
asserted, and these resolvent images are not identified with the original
finite sourced packet family. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingProjection
import UnifiedTheory.Audit.KFCausalHamiltonianCoreFromSources
import UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalGrowingCoreProjectedCoherent
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalStandingChargeOperator
open KFCausalClockFloorCoherentProjection
open KFCausalClockFloorFastResolvent (limitResolvent)
open KFCausalClockFloorFastResolventIdentification
open KFCausalClockFloorGrowingProjection
open KFCausalHamiltonianCoreFromSources

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2 * Real.pi * ε / 3) (m g k : ℝ)
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb m g k
local notation "R" => limitResolvent ε hε h hh hb m g k
local notation "Z" => zeroSector h hh
local notation "D" => Submodule.span ℂ (Set.range (projectedState ε 1 h hε zero_lt_one hh))

private theorem growing_resolves : KFCausalPositiveResolventBounds.Resolves G R 1 := by
  intro f
  refine ⟨(limitPoint ε hε h hh hb m g k f).property, ?_⟩
  simpa only [one_smul] using
    (eq_sub_iff_add_eq.mpr (limit_right_inverse ε hε h hh hb m g k f))

def core : Submodule ℂ (Hilbert × Hilbert) := (D).map (graphMap R 1).toLinearMap

theorem core_graph_closure :
    (core ε hε h hh hb m g k).topologicalClosure = sectorGraph G Z :=
  source_graph_closure G R 1 (growing_resolves ε hε h hh hb m g k)
    (fun x => by simpa only [one_smul] using limit_left_inverse ε hε h hh hb m g k x)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_closed ε hε h hh hb m g k)
    Z D (zeroSector_closed h hh) (dense_projected_span ε 1 h hε zero_lt_one hh)
    (limit_resolvent_zero_sector ε hε h hh hb m g k)
    (growing_zero_sector ε hε h hh hb m g k)

theorem coherent_resolvent_mem_core (ξ : Joint 2 4) :
    (R (projectedState ε 1 h hε zero_lt_one hh ξ),
      projectedState ε 1 h hε zero_lt_one hh ξ - R (projectedState ε 1 h hε zero_lt_one hh ξ)) ∈
        core ε hε h hh hb m g k := by
  have hm : graphMap R 1 (projectedState ε 1 h hε zero_lt_one hh ξ) ∈
      core ε hε h hh hb m g k := ⟨_, Submodule.subset_span ⟨ξ, rfl⟩, rfl⟩
  simpa only [graphMap_apply, one_smul] using hm

theorem core_mem_graph (v : Hilbert × Hilbert)
    (hv : v ∈ core ε hε h hh hb m g k) : v ∈ (G).graph ∧ v.1 ∈ Z := by
  have hc := (core ε hε h hh hb m g k).le_topologicalClosure hv
  rw [core_graph_closure ε hε h hh hb m g k] at hc
  exact hc

theorem every_zero_graph_approximable (x : (G).domain) (hx : (x : Hilbert) ∈ Z) :
    ((x : Hilbert), G x) ∈ (core ε hε h hh hb m g k).topologicalClosure := by
  rw [core_graph_closure ε hε h hh hb m g k]
  exact ⟨(G).mem_graph x, hx⟩

#print axioms core_graph_closure
#print axioms coherent_resolvent_mem_core
#print axioms core_mem_graph
#print axioms every_zero_graph_approximable
end
end UnifiedTheory.Audit.KFCausalGrowingCoreProjectedCoherent
