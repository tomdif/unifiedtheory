/- The actual transverse momentum commutes with the vacuum exponential
 and ordered factor on their proved composition domains. Orbit averages
 construct graph cores; no Hamiltonian momentum bound is assumed. -/
import UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation
import UnifiedTheory.Audit.KFCausalClockFloorShearExponential
import UnifiedTheory.Audit.KFCausalTransverseShearMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorShearVacuumGraph
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearGroup shearMomentum)
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (average)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (orderedExponential_closed)
open UnifiedTheory.Audit.KFCausalClockFloorShearExponential

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
local notation "J" => shearMomentum h
local notation "T" => orderedExponential ε hε h

theorem exponential_graph_interchange (hh : h ≠ 0) (a : ℝ) (f g j k : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h a).graph) (hj : (f,j) ∈ (J).graph) :
    (j,k) ∈ (longitudinalExponential ε hε h a).graph ↔ (g,k) ∈ (J).graph :=
  KFCausalClosedOperatorUnitaryCommutation.graph_interchange shearGroup _
    (longitudinal_exponential_closed ε hε h a) (exponential_graph_shear ε hε h a) h hh f g j k hfg hj

theorem ordered_graph_interchange (hh : h ≠ 0) (f g j k : Hilbert)
    (hfg : (f,g) ∈ (T).graph) (hj : (f,j) ∈ (J).graph) :
    (j,k) ∈ (T).graph ↔ (g,k) ∈ (J).graph :=
  KFCausalClosedOperatorUnitaryCommutation.graph_interchange shearGroup _
    (orderedExponential_closed ε hε h) (ordered_graph_shear ε hε h) h hh f g j k hfg hj

theorem ordered_composition_domain_iff (hh : h ≠ 0) (f g j : Hilbert)
    (hfg : (f,g) ∈ (T).graph) (hj : (f,j) ∈ (J).graph) :
    j ∈ (T).domain ↔ g ∈ (J).domain :=
  KFCausalClosedOperatorUnitaryCommutation.composition_domain_iff shearGroup _
    (orderedExponential_closed ε hε h) (ordered_graph_shear ε hε h) h hh f g j hfg hj

def regularGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓ (J).domain.prod (J).domain

theorem average_regular_graph (f g : Hilbert) (hfg : (f,g) ∈ (T).graph) (a : ℝ) :
    (average shearGroup f a,average shearGroup g a) ∈ regularGraph ε hε h :=
  KFCausalClosedOperatorUnitaryCommutation.average_regular_graph shearGroup _
    (orderedExponential_closed ε hε h) (ordered_graph_shear ε hε h) h f g hfg a

theorem regular_graph_core : (regularGraph ε hε h).topologicalClosure = (T).graph :=
  KFCausalClosedOperatorUnitaryCommutation.regular_graph_core shearGroup _
    (orderedExponential_closed ε hε h) (ordered_graph_shear ε hε h) h

theorem common_compositions (hh : h ≠ 0) (f g : Hilbert) (hfg : (f,g) ∈ regularGraph ε hε h) :
    ∃ j k : Hilbert, (f,j) ∈ (J).graph ∧ (g,k) ∈ (J).graph ∧ (j,k) ∈ (T).graph :=
  KFCausalClosedOperatorUnitaryCommutation.common_compositions shearGroup _
    (orderedExponential_closed ε hε h) (ordered_graph_shear ε hε h) h hh f g hfg

theorem compositions_equal (hh : h ≠ 0) (f g j tj jg : Hilbert)
    (hfg : (f,g) ∈ (T).graph) (hj : (f,j) ∈ (J).graph)
    (htj : (j,tj) ∈ (T).graph) (hjg : (g,jg) ∈ (J).graph) : jg = tj :=
  (J).mem_graph_snd_inj' hjg ((ordered_graph_interchange ε hε h hh f g j tj hfg hj).mp htj) rfl

theorem graph_approximation (f g : Hilbert) (hfg : (f,g) ∈ (T).graph) :
    ∃ z : ℕ → Hilbert × Hilbert, (∀ n, z n ∈ regularGraph ε hε h) ∧ Tendsto z atTop (𝓝 (f,g)) := by
  apply mem_closure_iff_seq_limit.mp
  change (f,g) ∈ (regularGraph ε hε h).topologicalClosure
  rw [regular_graph_core ε hε h]
  exact hfg

#print axioms exponential_graph_interchange
#print axioms ordered_graph_interchange
#print axioms ordered_composition_domain_iff
#print axioms average_regular_graph
#print axioms regular_graph_core
#print axioms common_compositions
#print axioms compositions_equal
#print axioms graph_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorShearVacuumGraph
