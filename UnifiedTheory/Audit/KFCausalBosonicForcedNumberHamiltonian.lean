/- A concrete self-adjoint forced number Hamiltonian N + lambda*(a+a†),
constructed from its completed form and identified on the occupation core.
This is a proved comparison model, not dΓ of the repository's general H(t). -/
import UnifiedTheory.Audit.KFCausalBosonicNumberForm
import UnifiedTheory.Audit.KFCausalLinearFieldFormPerturbation

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalBosonicForcedNumberHamiltonian
noncomputable section
open KFCausalBosonicOccupationSpace KFCausalBosonicCCR KFCausalBosonicNumberEstimate
open KFCausalBosonicBoundedDiagonal KFCausalBosonicNumberForm
variable {ι : Type*}

theorem embedding_symmetric : (embedding (ι := ι)).toLinearMap.IsSymmetric :=
  multiplier_symmetric weight 1 zero_le_one weight_bound

theorem lift_balance (u : Core ι) :
    embed (liftCore u) - embedding (embed u) =
      embedding (embed (diagonal (fun n => (particleCount n : ℝ)) u)) := by
  apply lp.ext
  funext n
  simp only [lp.coeFn_sub, Pi.sub_apply, embedding_apply, embed_apply, liftCore, diagonal_apply]
  have hw : (weight n)⁻¹ - weight n = (particleCount n : ℝ)*weight n := by
    have he := weight_identity n
    apply (mul_left_inj' (weight_pos n).ne').mp
    rw [sub_mul, inv_mul_cancel₀ (weight_pos n).ne']
    nlinarith
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hw
  push_cast at hc
  push_cast
  rw [← sub_mul, hc]
  ring

theorem free_core_pairing (u : Core ι) (v : Fock ι) :
    inner ℂ (embed (liftCore u)) v - inner ℂ (embed u) (embedding v) =
      inner ℂ (embed (diagonal (fun n => (particleCount n : ℝ)) u)) (embedding v) := by
  have hs : inner ℂ (embedding (embed u)) v = inner ℂ (embed u) (embedding v) :=
    embedding_symmetric (embed u) v
  rw [← hs, ← inner_sub_left, lift_balance]
  exact embedding_symmetric _ _

theorem annihilation_liftCore (i : ι) (u : Core ι) :
    annihilationForm i (embed (liftCore u)) = embed (annihilation i u) := by
  rw [annihilationForm_core]
  change embed (annihilation i (diagonal weight (liftCore u))) = _
  have he : diagonal weight (liftCore u) = u :=
    embed_injective ((embedding_core (liftCore u)).symm.trans (embedding_liftCore u))
  rw [he]

theorem creation_form_pairing (i : ι) (u : Core ι) (v : Fock ι) :
    inner ℂ (embed u) (annihilationForm i v) =
      inner ℂ (embed (creation i u)) (embedding v) := by
  refine (core_dense (ι := ι)).induction_on v ?_ ?_
  · exact isClosed_eq (continuous_const.inner (annihilationForm i).continuous)
      (continuous_const.inner embedding.continuous)
  · intro w
    rw [annihilationForm_core, embedding_core]
    exact (creation_annihilation_adjoint i u (diagonal weight w)).symm

def hamiltonian (i : ι) (g : ℝ) : Fock ι →ₗ.[ℂ] Fock ι :=
  KFCausalLinearFieldFormPerturbation.hamiltonian embedding (annihilationForm i) g
    (annihilationForm_square_bound i) embedding_injective embedding_dense

theorem hamiltonian_selfAdjoint (i : ι) (g : ℝ) : IsSelfAdjoint (hamiltonian i g) :=
  KFCausalLinearFieldFormPerturbation.hamiltonian_selfAdjoint _ _ _ _ _ _

theorem variational_graph (i : ι) (g : ℝ) (u v : Fock ι) :
    (embedding u,v) ∈ (hamiltonian i g).graph ↔
      ∀ w : Fock ι, inner ℂ u w - inner ℂ (embedding u) (embedding w) +
        (g : ℂ)*(inner ℂ (embedding u) (annihilationForm i w) +
          inner ℂ (annihilationForm i u) (embedding w)) = inner ℂ v (embedding w) :=
  KFCausalLinearFieldFormPerturbation.variational_graph _ _ _ _ _ _ _ _

theorem core_graph (i : ι) (g : ℝ) (u : Core ι) :
    (embed u, embed (diagonal (fun n => (particleCount n : ℝ)) u + (g : ℂ) • field i u)) ∈
      (hamiltonian i g).graph := by
  rw [← embedding_liftCore u]
  apply (variational_graph i g _ _).mpr
  intro v
  rw [embedding_liftCore, free_core_pairing, annihilation_liftCore, creation_form_pairing]
  simp only [map_add, map_smul, inner_add_left, inner_smul_left, Complex.conj_ofReal,
    field, LinearMap.add_apply]

theorem lower_bound (i : ι) (g : ℝ) (u y : Fock ι)
    (hg : (embedding u,y) ∈ (hamiltonian i g).graph) :
    -(2*g^2)*‖embedding u‖^2 ≤ (inner ℂ y (embedding u)).re :=
  KFCausalLinearFieldFormPerturbation.lower_bound _ _ _ _ _ _ embedding_contracts u y hg

end
end UnifiedTheory.Audit.KFCausalBosonicForcedNumberHamiltonian
