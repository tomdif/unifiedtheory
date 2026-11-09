/- A dense graph core for the ordered vacuum factor with both actual
 longitudinal and shear momenta on input and output. This does not yet
 identify the pure-clock momentum on this core. -/
import UnifiedTheory.Audit.KFCausalClockFloorShearVacuumGraph
import UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCore
import UnifiedTheory.Audit.KFCausalTransverseShearGraphCommutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearGroup shearMomentum)
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (average average_tendsto)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum longitudinal_closed)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (orderedExponential_closed)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalTransverseShearGraphCommutation (coupled_graph_shear)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
local notation "J" => shearMomentum h
local notation "L" => longitudinalMomentum ε hε h
local notation "T" => orderedExponential ε hε h
local notation "G" => KFCausalClockFloorOrderedMomentumCore.regularGraph ε hε h

def regularGraph : Submodule ℂ (Hilbert × Hilbert) := G ⊓ (J).domain.prod (J).domain

theorem average_longitudinal_graph (hh : h ≠ 0) (f lf : Hilbert)
    (hf : (f,lf) ∈ (L).graph) (a : ℝ) :
    (average shearGroup f a,average shearGroup lf a) ∈ (L).graph :=
  KFCausalClosedOperatorUnitaryCommutation.average_graph shearGroup _
    (longitudinal_closed ε hε h hh) (coupled_graph_shear ε hε h hh) f lf hf a

theorem average_regular_graph (hh : h ≠ 0) (f g : Hilbert) (hfg : (f,g) ∈ G) (a : ℝ) :
    (average shearGroup f a,average shearGroup g a) ∈ regularGraph ε hε h := by
  have ht := KFCausalClockFloorShearVacuumGraph.average_regular_graph ε hε h f g hfg.1 a
  obtain ⟨lf,hlf⟩ := LinearPMap.mem_domain_iff.mp hfg.2.1
  obtain ⟨lg,hlg⟩ := LinearPMap.mem_domain_iff.mp hfg.2.2
  exact ⟨⟨ht.1,LinearPMap.mem_domain_of_mem_graph (average_longitudinal_graph ε hε h hh f lf hlf a),
    LinearPMap.mem_domain_of_mem_graph (average_longitudinal_graph ε hε h hh g lg hlg a)⟩,ht.2⟩

theorem regular_graph_core (hh : h ≠ 0) (hbound : |h| ≤ 2*Real.pi*ε/3) :
    (regularGraph ε hε h).topologicalClosure = (T).graph := by
  have hg : G ≤ (regularGraph ε hε h).topologicalClosure := by
    rintro ⟨f,g⟩ hfg
    exact mem_closure_of_tendsto ((average_tendsto shearGroup f).prodMk_nhds (average_tendsto shearGroup g))
      (Eventually.of_forall fun a => average_regular_graph ε hε h hh f g hfg a)
  have hc := Submodule.topologicalClosure_minimal _ hg (regularGraph ε hε h).isClosed_topologicalClosure
  rw [KFCausalClockFloorOrderedMomentumCore.regular_graph_core ε hε h hh hbound] at hc
  exact le_antisymm (Submodule.topologicalClosure_minimal _ (fun _ hz => hz.1.1)
    (orderedExponential_closed ε hε h)) hc

theorem common_compositions (hh : h ≠ 0) (hbound : |h| ≤ 2*Real.pi*ε/3)
    (f g : Hilbert) (hfg : (f,g) ∈ regularGraph ε hε h) :
    ∃ lf tlf ltf jf jtf : Hilbert,
      (f,lf) ∈ (L).graph ∧ (lf,tlf) ∈ (T).graph ∧ (g,ltf) ∈ (L).graph ∧
      ltf-tlf = correction ε hε h hbound g ∧
      (f,jf) ∈ (J).graph ∧ (jf,jtf) ∈ (T).graph ∧ (g,jtf) ∈ (J).graph := by
  obtain ⟨lf,tlf,ltf,hl,htl,hlt,he⟩ :=
    KFCausalClockFloorOrderedMomentumCore.common_compositions ε hε h hh hbound f g hfg.1
  obtain ⟨jf,jtf,hj,hjt,htj⟩ := KFCausalClockFloorShearVacuumGraph.common_compositions ε hε h hh f g
    ⟨hfg.1.1,hfg.2⟩
  exact ⟨lf,tlf,ltf,jf,jtf,hl,htl,hlt,he,hj,htj,hjt⟩

theorem graph_approximation (hh : h ≠ 0) (hbound : |h| ≤ 2*Real.pi*ε/3)
    (f g : Hilbert) (hfg : (f,g) ∈ (T).graph) :
    ∃ z : ℕ → Hilbert × Hilbert, (∀ n, z n ∈ regularGraph ε hε h) ∧ Tendsto z atTop (𝓝 (f,g)) := by
  apply mem_closure_iff_seq_limit.mp
  change (f,g) ∈ (regularGraph ε hε h).topologicalClosure
  rw [regular_graph_core ε hε h hh hbound]
  exact hfg

#print axioms average_longitudinal_graph
#print axioms average_regular_graph
#print axioms regular_graph_core
#print axioms common_compositions
#print axioms graph_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore
