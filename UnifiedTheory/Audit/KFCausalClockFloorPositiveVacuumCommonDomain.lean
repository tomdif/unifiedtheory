/- For strictly positive vacuum coupling, the actual static/growing
operator intersection lies in the original interacting form. This removes
the reference-range restriction from the previously proved common-domain
identity. It does not assert that every H-domain vector belongs to G. -/
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumFormReconstruction
import UnifiedTheory.Audit.KFCausalClockFloorStaticGrowingDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumCommonDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedFormTransport

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ : ℝ)
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb m g κ
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb m g κ
local notation "V" => FormSpace ε hε h hh hb m g κ 0
local notation "J" => embedding ε hε h hh hb m g κ 0

theorem common_reference_range (hκ : 0 < κ) (f : Hilbert)
    (ht : f ∈ (T).domain) (hg : f ∈ (G).domain) :
    f ∈ (J).toLinearMap.range := by
  have hr := KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨f,ht⟩
  let D := KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hb m g κ
  let u := KFCausalClosedGraphForm.formLift D ⟨f,hg⟩
  have hu : KFCausalClosedGraphForm.embedding D u = f :=
    KFCausalClosedGraphForm.embedding_formLift D ⟨f,hg⟩
  have hb' : f ∈ (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hb m g κ).domain := by
    rw [← hu]
    exact LinearPMap.mem_domain_of_mem_graph u.property
  have he := (KFCausalClockFloorPositiveVacuumFormReconstruction.root_growing_domain_iff
    ε hε h hh hb m g κ hκ f).mpr ⟨hr,hb'⟩
  exact ⟨KFCausalClosedGraphForm.graphVector
    (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g κ 0) ⟨f,he⟩,rfl⟩

theorem sum_graph (hκ : 0 < κ) (t : ℝ) (x y z : Hilbert)
    (ht : (x,y) ∈ (T).graph) (hg : (x,z) ∈ (G).graph) :
    (x,y+Real.exp (2*t) • z) ∈ (H t).graph := by
  obtain ⟨u,hu⟩ := common_reference_range ε hε h hh hb m g κ hκ x
    (LinearPMap.mem_domain_of_mem_graph ht) (LinearPMap.mem_domain_of_mem_graph hg)
  change J u = x at hu
  have ht' : (J u,y) ∈ (T).graph := by simpa only [hu] using ht
  have hg' : (J u,z) ∈ (G).graph := by simpa only [hu] using hg
  simpa only [hu] using KFCausalClockFloorStaticGrowingDecomposition.sum_graph
    ε hε h hh hb m g κ t u y z ht' hg'

theorem common_domain_eq (hκ : 0 < κ) (t : ℝ) :
    (H t).domain ⊓ (G).domain = (T).domain ⊓ (G).domain := by
  rw [KFCausalClockFloorStaticGrowingDecomposition.original_common_domain_eq]
  apply le_antisymm inf_le_left
  intro f hf
  exact ⟨hf,common_reference_range ε hε h hh hb m g κ hκ f hf.1 hf.2⟩

theorem common_static_domain_eq (hκ : 0 < κ) (t : ℝ) :
    (H t).domain ⊓ (T).domain = (T).domain ⊓ (G).domain := by
  rw [← KFCausalClockFloorStaticGrowingDecomposition.common_domain_eq]
  exact common_domain_eq ε hε h hh hb m g κ hκ t

#print axioms common_reference_range
#print axioms sum_graph
#print axioms common_domain_eq
#print axioms common_static_domain_eq
end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumCommonDomain
