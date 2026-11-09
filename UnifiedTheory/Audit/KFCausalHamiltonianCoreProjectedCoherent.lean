/- An explicit zero-charge Hamiltonian graph core: apply one actual shifted
resolvent to the finite span of projected coherent sources. The source span's
Hilbert density is proved independently; the resolvent upgrades it to graph
density. These smoothed vectors are not asserted to belong to the clock
composition domains or to the correlated response family. -/
import UnifiedTheory.Audit.KFCausalHamiltonianCoreFromSources
import UnifiedTheory.Audit.KFCausalClockFloorAveragedDynamicsProjection
import UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalHamiltonianCoreProjectedCoherent
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalClockFloorCoherentProjection
open KFCausalStandingChargeOperator
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalClockFloorAveragedShiftedResolvent
open KFCausalClockFloorAveragedYosida (averaged_resolves)
open KFCausalHamiltonianCoreFromSources

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ)
local notation "H" => hamiltonian ε hε h hh hb mass2 quartic vacuum t
local notation "R" => shiftedResolvent ε hε h hh hb mass2 quartic vacuum a t
local notation "Z" => zeroSector h hh
local notation "P" => zeroProjection h hh
local notation "D" => Submodule.span ℂ (Set.range (projectedState ε 1 h hε zero_lt_one hh))

def core : Submodule ℂ (Hilbert × Hilbert) := (D).map (graphMap R a).toLinearMap

theorem resolvent_zero_sector (ha : 0 < a) (f : Hilbert) (hf : f ∈ Z) : R f ∈ Z := by
  have he : R f = P (R f) := by
    calc
      R f = R (P f) := congrArg R (zeroProjection_fixes h hh f hf).symm
      _ = P (R f) :=
        KFCausalClockFloorAveragedDynamicsProjection.shiftedResolvent_zeroProjection
          ε hε h hh hb mass2 quartic vacuum a ha t f
  exact he ▸ zeroProjection_mem h hh (R f)

theorem core_graph_closure (ha : 0 < a) :
    (core ε hε h hh hb mass2 quartic vacuum a t).topologicalClosure = sectorGraph H Z :=
  source_graph_closure H R a (averaged_resolves ε hε h hh hb mass2 quartic vacuum a t ha)
    (shiftedResolvent_left ε hε h hh hb mass2 quartic vacuum a t ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_closed ε hε h hh hb mass2 quartic vacuum t)
    Z D (zeroSector_closed h hh) (dense_projected_span ε 1 h hε zero_lt_one hh)
    (resolvent_zero_sector ε hε h hh hb mass2 quartic vacuum a t ha)
    (KFCausalClockFloorHamiltonianProjection.hamiltonian_zero_sector ε hε h hh hb mass2 quartic vacuum t)

theorem coherent_resolvent_mem_core (k : Joint 2 4) :
    (R (projectedState ε 1 h hε zero_lt_one hh k),
      projectedState ε 1 h hε zero_lt_one hh k-a • R (projectedState ε 1 h hε zero_lt_one hh k)) ∈
        core ε hε h hh hb mass2 quartic vacuum a t :=
  ⟨_,Submodule.subset_span ⟨k,rfl⟩,rfl⟩

theorem core_mem_graph (ha : 0 < a) (v : Hilbert × Hilbert)
    (hv : v ∈ core ε hε h hh hb mass2 quartic vacuum a t) : v ∈ (H).graph ∧ v.1 ∈ Z := by
  have hc := (core ε hε h hh hb mass2 quartic vacuum a t).le_topologicalClosure hv
  rw [core_graph_closure ε hε h hh hb mass2 quartic vacuum a t ha] at hc
  exact hc

theorem every_zero_graph_approximable (ha : 0 < a) (x : (H).domain) (hx : (x:Hilbert) ∈ Z) :
    ((x:Hilbert),H x) ∈
      (core ε hε h hh hb mass2 quartic vacuum a t).topologicalClosure := by
  rw [core_graph_closure ε hε h hh hb mass2 quartic vacuum a t ha]
  exact ⟨(H).mem_graph x,hx⟩

#print axioms resolvent_zero_sector
#print axioms core_graph_closure
#print axioms coherent_resolvent_mem_core
#print axioms core_mem_graph
#print axioms every_zero_graph_approximable
end
end UnifiedTheory.Audit.KFCausalHamiltonianCoreProjectedCoherent
