/- The Hamiltonian represented by the full direct-sum energy form
is exactly the maximal direct sum of its sector Hamiltonians. -/
import UnifiedTheory.Audit.KFCausalDirectSumEnergyForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDirectSumFormHamiltonian
noncomputable section
open KFCausalClosedGraphForm KFCausalDirectSumEnergyForm

variable {ι : Type*} {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [∀ i, CompleteSpace (F i)]
variable (D : ∀ i, Data (E i) (F i))
local instance : DecidableEq ι := Classical.decEq _

theorem coordinate_graph (x : (hamiltonian (formData D)).domain) (i : ι) :
    ((x : lp E 2) i, hamiltonian (formData D) x i) ∈ (hamiltonian (D i)).graph := by
  let u := coordinate D (formLift (formData D) x) i
  have hp (v : FormSpace (D i)) :
      inner ℂ (energyOutput (D i) u) (energyOutput (D i) v) =
        inner ℂ (hamiltonian (formData D) x i) (embedding (D i) v) := by
    have he := hamiltonian_represents_form (formData D) x (singleForm D i v)
    rw [singleForm_output, singleForm_embedding, lp.inner_single_right,
      lp.inner_single_right] at he
    exact he
  obtain ⟨hx, hy⟩ := (hamiltonian_domain_characterization (D i) u _).mpr hp
  rw [LinearPMap.mem_graph_iff]
  refine ⟨⟨embedding (D i) u, hx⟩, ?_, hy⟩
  change embedding (formData D) (formLift (formData D) x) i = (x : lp E 2) i
  rw [embedding_formLift]

theorem inclusion (x : (hamiltonian (formData D)).domain) :
    ((x : lp E 2), hamiltonian (formData D) x) ∈
      (KFCausalHilbertDirectSumHamiltonian.operator (fun i => hamiltonian (D i))).graph :=
  (KFCausalHilbertDirectSumHamiltonian.graph_iff _ _ _).mpr (coordinate_graph D x)

theorem graph_identification (x y : lp E 2) :
    (x, y) ∈ (hamiltonian (formData D)).graph ↔
      (x, y) ∈ (KFCausalHilbertDirectSumHamiltonian.operator
        (fun i => hamiltonian (D i))).graph := by
  constructor
  · intro hg
    obtain ⟨u, hu, hv⟩ := (hamiltonian (formData D)).mem_graph_iff.mp hg
    simpa only [hu, hv] using inclusion D u
  · intro hg
    let A := KFCausalHilbertDirectSumHamiltonian.operator (fun i => hamiltonian (D i))
    have hA : IsSelfAdjoint A :=
      KFCausalHilbertDirectSumHamiltonian.selfAdjoint _ (fun i => hamiltonian_selfAdjoint (D i))
    have hf : A.IsFormalAdjoint A := by
      have hh := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
      rwa [LinearPMap.isSelfAdjoint_def.mp hA] at hh
    have hp (v : (hamiltonian (formData D)).domain) :
        inner ℂ y (v : lp E 2) = inner ℂ x (hamiltonian (formData D) v) := by
      obtain ⟨a, ha, hay⟩ := A.mem_graph_iff.mp hg
      obtain ⟨b, hb, hby⟩ := A.mem_graph_iff.mp (inclusion D v)
      have hh := hf a b
      dsimp only at ha hay hb hby
      rw [ha, hay, hb, hby] at hh
      exact hh
    have hx : x ∈ (hamiltonian (formData D)).adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨y, hp⟩
    have hy := LinearPMap.adjoint_apply_eq (hamiltonian_selfAdjoint (formData D)).dense_domain
      ⟨x, hx⟩ hp
    have he : (x, y) ∈ (hamiltonian (formData D)).adjoint.graph := by
      rw [LinearPMap.mem_graph_iff]
      exact ⟨⟨x, hx⟩, rfl, hy⟩
    rwa [LinearPMap.isSelfAdjoint_def.mp (hamiltonian_selfAdjoint (formData D))] at he

theorem hamiltonian_eq : hamiltonian (formData D) =
    KFCausalHilbertDirectSumHamiltonian.operator (fun i => hamiltonian (D i)) := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  exact graph_identification D p.1 p.2

theorem operator_form_dense : DenseRange (formLift (formData D)) :=
  KFCausalFormHamiltonian.operator_domain_form_dense _ _ _

end
end UnifiedTheory.Audit.KFCausalDirectSumFormHamiltonian
