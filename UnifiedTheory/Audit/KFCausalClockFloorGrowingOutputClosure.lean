/- Close the actual growing-output restriction on the full reference
form domain. Closed factor graphs exclude vertical limits, so this is
an actual densely defined operator on physical L2. Its domain is not
identified with a larger maximal growing-factor domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrbitFactorGraphs

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingOutputClosure
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph (physicalOrbit)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (coordinateLp)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (growingMap)
open UnifiedTheory.Audit.KFCausalClockFloorOrbitFactorGraphs
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "B" => growingMap ε hε h hne hb m g k
local notation "R" => physicalOrbit h hne

def initialGraph : Submodule ℂ (Hilbert × EnergyOutputSpace) :=
  ((J).prod B).toLinearMap.range

theorem initialGraph_mem (u : V) : (J u,B u) ∈ initialGraph ε hε h hne hb m g k :=
  ⟨u,rfl⟩

theorem closure_component (z : Hilbert × EnergyOutputSpace)
    (hz : z ∈ (initialGraph ε hε h hne hb m g k).topologicalClosure) (i : Fin 8) :
    (R (growingWeight m g k i • z.1),coordinateLp i z.2) ∈ (factorOperator ε hε h i).graph := by
  have hc : IsClosed {z : Hilbert × EnergyOutputSpace |
      (R (growingWeight m g k i • z.1),coordinateLp i z.2) ∈ (factorOperator ε hε h i).graph} :=
    (factorOperator_closed ε hε h (hamiltonian_bound ε h hb) i).preimage
      (((R).continuous.comp (continuous_const.smul continuous_fst)).prodMk
        ((coordinateLp i).continuous.comp continuous_snd))
  apply closure_minimal (t := {z : Hilbert × EnergyOutputSpace |
      (R (growingWeight m g k i • z.1),coordinateLp i z.2) ∈ (factorOperator ε hε h i).graph}) ?_ hc
    (by simpa only [Submodule.topologicalClosure_coe] using hz)
  rintro z ⟨u,rfl⟩
  exact growing_factor_graph ε hε h hne hb m g k u i

theorem closure_vertical_zero (z : Hilbert × EnergyOutputSpace)
    (hz : z ∈ (initialGraph ε hε h hne hb m g k).topologicalClosure) (hzero : z.1 = 0) : z.2 = 0 := by
  apply coordinates_detect_zero
  intro i
  have hi := closure_component ε hε h hne hb m g k z hz i
  exact (factorOperator ε hε h i).graph_fst_eq_zero_snd hi (by simp only [hzero,smul_zero,map_zero])

def operator : Hilbert →ₗ.[ℂ] EnergyOutputSpace :=
  (initialGraph ε hε h hne hb m g k).topologicalClosure.toLinearPMap

theorem operator_graph : (operator ε hε h hne hb m g k).graph =
    (initialGraph ε hε h hne hb m g k).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (closure_vertical_zero ε hε h hne hb m g k)

theorem operator_closed : (operator ε hε h hne hb m g k).IsClosed := by
  rw [LinearPMap.IsClosed,operator_graph]
  exact (initialGraph ε hε h hne hb m g k).isClosed_topologicalClosure

theorem reference_graph (u : V) : (J u,B u) ∈ (operator ε hε h hne hb m g k).graph := by
  rw [operator_graph]
  exact (initialGraph ε hε h hne hb m g k).le_topologicalClosure
    (initialGraph_mem ε hε h hne hb m g k u)

theorem operator_dense : Dense ((operator ε hε h hne hb m g k).domain : Set Hilbert) := by
  have hd := KFCausalClosedGraphForm.embedding_dense
    (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hne hb m g k 0)
  apply hd.mono
  rintro f ⟨u,rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (reference_graph ε hε h hne hb m g k u)

theorem operator_minimal (T : Hilbert →ₗ.[ℂ] EnergyOutputSpace) (hT : T.IsClosed)
    (hTB : ∀ u : V, (J u,B u) ∈ T.graph) : operator ε hε h hne hb m g k ≤ T := by
  rw [← LinearPMap.le_graph_iff,operator_graph]
  apply Submodule.topologicalClosure_minimal _ ?_ hT
  rintro z ⟨u,rfl⟩
  exact hTB u

#print axioms initialGraph_mem
#print axioms closure_component
#print axioms closure_vertical_zero
#print axioms operator_graph
#print axioms operator_closed
#print axioms reference_graph
#print axioms operator_dense
#print axioms operator_minimal
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingOutputClosure
