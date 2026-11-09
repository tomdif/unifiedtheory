/- Closed, densely defined mode fields on the occupation Hilbert space.
The graph closure is single-valued by the proved core adjoint relation.
This proves closability, not essential self-adjointness. -/
import UnifiedTheory.Audit.KFCausalBosonicCCR
import UnifiedTheory.Audit.KFCausalSeparatedGraphClosure

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalBosonicFieldClosure
noncomputable section
open KFCausalBosonicOccupationSpace KFCausalBosonicCCR KFCausalSeparatedGraphClosure
variable {ι : Type*}

theorem core_separates (y : Fock ι)
    (hy : ∀ u : Core ι, inner ℂ (embed u) y = 0) : y = 0 := by
  classical
  apply lp.ext
  funext n
  have he := hy (Finsupp.single n 1)
  simpa [lp.inner_single_left, RCLike.inner_apply] using he

def coreField (i : ι) : Fock ι →ₗ.[ℂ] Fock ι :=
  initialOperator embed (embed.comp (field i))

def closedField (i : ι) : Fock ι →ₗ.[ℂ] Fock ι :=
  closedOperator embed (embed.comp (field i))

theorem closedField_graph (i : ι) :
    (closedField i).graph = (graphRange embed (embed.comp (field i))).topologicalClosure := by
  apply closedOperator_graph _ _ (fun u : Core ι => embed (field i u)) embed
    core_separates
  intro v u
  exact (field_symmetric i u v).symm

theorem coreField_closable (i : ι) : (coreField i).IsClosable := by
  apply operator_closable _ _ (fun u : Core ι => embed (field i u)) embed core_separates
  intro v u
  exact (field_symmetric i u v).symm

theorem closedField_closed (i : ι) : (closedField i).IsClosed := by
  apply operator_closed _ _ (fun u : Core ι => embed (field i u)) embed core_separates
  intro v u
  exact (field_symmetric i u v).symm

theorem closedField_extends_core (i : ι) (u : Core ι) :
    (embed u, embed (field i u)) ∈ (closedField i).graph := by
  rw [closedField_graph]
  apply (graphRange embed (embed.comp (field i))).le_topologicalClosure
  exact ⟨u, rfl⟩

theorem closedField_domain_dense (i : ι) : Dense ((closedField i).domain : Set (Fock ι)) := by
  apply core_dense.mono
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv, _⟩ := (closedField i).mem_graph_iff.mp (closedField_extends_core i u)
  change (v : Fock ι) = embed u at hv
  simpa only [← hv] using v.property

end
end UnifiedTheory.Audit.KFCausalBosonicFieldClosure
