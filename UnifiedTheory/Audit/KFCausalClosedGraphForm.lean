/- A densely defined closed energy-output operator gives a complete
graph form and a positive self-adjoint representing Hamiltonian. Physical
applications must supply the operator and prove closedness and density. -/
import UnifiedTheory.Audit.KFCausalFormHamiltonian
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClosedGraphForm
noncomputable section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

structure Data (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] where
  operator : H →ₗ.[ℂ] K
  closed : operator.IsClosed
  dense : Dense (operator.domain : Set H)

def energyGraph (D : Data H K) : Submodule ℂ (WithLp 2 (H × K)) :=
  D.operator.graph.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toLinearMap

theorem energyGraph_closed (D : Data H K) : IsClosed (energyGraph D : Set (WithLp 2 (H × K))) :=
  D.closed.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H K).continuous

abbrev FormSpace (D : Data H K) := energyGraph D
instance formSpaceComplete [CompleteSpace H] [CompleteSpace K] (D : Data H K) : CompleteSpace (FormSpace D) :=
  (energyGraph_closed D).completeSpace_coe

def embedding (D : Data H K) : FormSpace D →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H K).comp (energyGraph D).subtypeL
def energyOutput (D : Data H K) : FormSpace D →L[ℂ] K :=
  (WithLp.sndL 2 ℂ H K).comp (energyGraph D).subtypeL

theorem embedding_injective (D : Data H K) : Function.Injective (embedding D) := by
  intro x y hxy
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  apply Prod.ext hxy
  exact D.operator.mem_graph_snd_inj' x.property y.property hxy

theorem embedding_contraction (D : Data H K) (x : FormSpace D) : ‖embedding D x‖ ≤ ‖x‖ :=
  WithLp.norm_fst_le H x.val

def graphVector (D : Data H K) (x : D.operator.domain) : FormSpace D :=
  ⟨WithLp.toLp 2 ((x:H),D.operator x),D.operator.mem_graph x⟩

theorem graphVector_embedding (D : Data H K) (x : D.operator.domain) : embedding D (graphVector D x)=x := rfl
theorem graphVector_output (D : Data H K) (x : D.operator.domain) : energyOutput D (graphVector D x)=D.operator x := rfl

theorem embedding_dense (D : Data H K) : DenseRange (embedding D) := by
  apply D.dense.mono
  intro x hx
  exact ⟨graphVector D ⟨x,hx⟩,rfl⟩

theorem form_norm_identity (D : Data H K) (x : FormSpace D) :
    ‖x‖^2=‖embedding D x‖^2+‖energyOutput D x‖^2 := WithLp.prod_norm_sq_eq_of_L2 x.val

theorem form_inner_identity (D : Data H K) (x y : FormSpace D) :
    inner ℂ x y=inner ℂ (embedding D x) (embedding D y)+inner ℂ (energyOutput D x) (energyOutput D y) := rfl

variable [CompleteSpace H] [CompleteSpace K]

def hamiltonian (D : Data H K) : H →ₗ.[ℂ] H :=
  KFCausalFormHamiltonian.hamiltonian (embedding D) (embedding_injective D) (embedding_dense D)

theorem hamiltonian_selfAdjoint (D : Data H K) : IsSelfAdjoint (hamiltonian D) :=
  KFCausalFormHamiltonian.hamiltonian_selfAdjoint _ _ _

theorem hamiltonian_closed (D : Data H K) : (hamiltonian D).IsClosed :=
  (hamiltonian_selfAdjoint D).isClosed

theorem hamiltonian_dense (D : Data H K) : Dense ((hamiltonian D).domain : Set H) :=
  (hamiltonian_selfAdjoint D).dense_domain

theorem hamiltonian_positive (D : Data H K) (x : (hamiltonian D).domain) :
    0 ≤ (inner ℂ (hamiltonian D x) (x:H)).re :=
  KFCausalFormHamiltonian.hamiltonian_positive _ _ _ (embedding_contraction D) x

def formLift (D : Data H K) (x : (hamiltonian D).domain) : FormSpace D :=
  KFCausalFormHamiltonian.formLift _ _ _ x

theorem embedding_formLift (D : Data H K) (x : (hamiltonian D).domain) : embedding D (formLift D x)=x :=
  KFCausalFormHamiltonian.embedding_formLift _ _ _ x

theorem hamiltonian_represents_form (D : Data H K) (x : (hamiltonian D).domain) (v : FormSpace D) :
    inner ℂ (energyOutput D (formLift D x)) (energyOutput D v)=
      inner ℂ (hamiltonian D x) (embedding D v) := by
  have hp := KFCausalFormHamiltonian.hamiltonian_form_pairing
    (embedding D) (embedding_injective D) (embedding_dense D) x v
  change inner ℂ (formLift D x) v-inner ℂ (x:H) (embedding D v)=_ at hp
  rw [form_inner_identity,embedding_formLift,add_sub_cancel_left] at hp
  exact hp

theorem hamiltonian_energy (D : Data H K) (x : (hamiltonian D).domain) :
    (inner ℂ (hamiltonian D x) (x:H)).re=‖energyOutput D (formLift D x)‖^2 := by
  have hp := hamiltonian_represents_form D x (formLift D x)
  rw [embedding_formLift] at hp
  rw [← hp]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem hamiltonian_domain_characterization (D : Data H K) (u : FormSpace D) (y : H) :
    (∃ hx : embedding D u ∈ (hamiltonian D).domain, hamiltonian D ⟨embedding D u,hx⟩=y) ↔
      ∀ v, inner ℂ (energyOutput D u) (energyOutput D v)=inner ℂ y (embedding D v) := by
  constructor
  · rintro ⟨hx,hy⟩ v
    have hl : formLift D ⟨embedding D u,hx⟩=u :=
      embedding_injective D (embedding_formLift D _)
    have hp := hamiltonian_represents_form D ⟨embedding D u,hx⟩ v
    rwa [hl,hy] at hp
  · intro hq
    have hq' : ∀ v, inner ℂ u v-inner ℂ (embedding D u) (embedding D v)=inner ℂ y (embedding D v) := by
      intro v
      rw [form_inner_identity,add_sub_cancel_left,hq v]
    exact ⟨KFCausalFormHamiltonian.variational_mem_domain _ (embedding_injective D) (embedding_dense D) u y hq',
      KFCausalFormHamiltonian.variational_value _ (embedding_injective D) (embedding_dense D) u y hq'⟩

#print axioms energyGraph_closed
#print axioms embedding_injective
#print axioms embedding_contraction
#print axioms graphVector_embedding
#print axioms graphVector_output
#print axioms embedding_dense
#print axioms form_norm_identity
#print axioms form_inner_identity
#print axioms hamiltonian_selfAdjoint
#print axioms hamiltonian_closed
#print axioms hamiltonian_dense
#print axioms hamiltonian_positive
#print axioms embedding_formLift
#print axioms hamiltonian_represents_form
#print axioms hamiltonian_energy
#print axioms hamiltonian_domain_characterization

end
end UnifiedTheory.Audit.KFCausalClosedGraphForm
