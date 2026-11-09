/- The completed energy form space embeds injectively and densely into
the physical homogeneous Hilbert space. Its embedding is a contraction,
supplying the concrete input for the Hamiltonian representation step. -/
import UnifiedTheory.Audit.KFCausalRegularizedClosedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedFormDomain
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedClosedForm

abbrev FormSpace (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) := energyGraph ε hε hbar coupling t

instance formSpaceComplete (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    CompleteSpace (FormSpace ε hε hbar coupling t) := energyGraph_complete ε hε hbar coupling t

def embedding (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    FormSpace ε hε hbar coupling t →L[ℂ] Hilbert :=
  (WithLp.fstL 2 ℂ Hilbert Output).comp (energyGraph ε hε hbar coupling t).subtypeL

def energyOutput (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    FormSpace ε hε hbar coupling t →L[ℂ] Output :=
  (WithLp.sndL 2 ℂ Hilbert Output).comp (energyGraph ε hε hbar coupling t).subtypeL

theorem embedding_injective (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    Function.Injective (embedding ε hε hbar coupling t) := by
  intro x y hxy
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  apply Prod.ext hxy
  exact (jointClosed ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp t)).mem_graph_snd_inj'
    x.property y.property hxy

theorem embedding_contraction (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : FormSpace ε hε hbar coupling t) : ‖embedding ε hε hbar coupling t x‖ ≤ ‖x‖ :=
  WithLp.norm_fst_le Hilbert x.val

theorem embedding_norm_le_one (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    ‖embedding ε hε hbar coupling t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using embedding_contraction ε hε hbar coupling t x

theorem embedding_dense (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    DenseRange (embedding ε hε hbar coupling t) := by
  have hd : Dense (formDomain ε hε hbar : Set Hilbert) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (dense_form_domain ε hε hbar)
  apply hd.mono
  rintro _ ⟨f,rfl⟩
  refine ⟨⟨WithLp.toLp 2 (coreToHilbert ε hε hbar f,
    coreToJoint ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp t) f),?_⟩,rfl⟩
  exact joint_contains_core ε hε hbar _ _ f

theorem form_norm_identity (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : FormSpace ε hε hbar coupling t) :
    ‖x‖^2=‖embedding ε hε hbar coupling t x‖^2+‖energyOutput ε hε hbar coupling t x‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 x.val

#print axioms embedding_injective
#print axioms embedding_contraction
#print axioms embedding_dense
#print axioms form_norm_identity

end
end UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
