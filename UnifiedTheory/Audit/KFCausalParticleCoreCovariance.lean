/- The iterated Hamiltonian sum intertwines every particle permutation
on its dense tensor domain. Dual numbers encode the product-rule pairing. -/
import UnifiedTheory.Audit.KFCausalParticleDomainTensors
import UnifiedTheory.Audit.KFCausalParticlePermutations
import Mathlib.Algebra.TrivSqZeroExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalParticleCoreCovariance
noncomputable section
open KFCausalClosedGraphForm KFCausalCompletedTensor KFCausalTensorParticleSectors
open KFCausalParticlePureTensors KFCausalParticlePermutations KFCausalParticleDomainTensors

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def oneJet (D : Data H K) (v : (hamiltonian D).domain) (w : H) : TrivSqZeroExt ℂ ℂ :=
  (inner ℂ (v : H) w, inner ℂ (hamiltonian D v) w)

def pairingJet (D : Data H K) (n : ℕ) (v : Tuple D n) (w : Fin (n + 1) → H) :
    TrivSqZeroExt ℂ ℂ :=
  (inner ℂ (inputTuple D n v) (pureTuple D n w),
    inner ℂ (actionTuple D n v) (pureTuple D n w))

theorem pairingJet_product (D : Data H K) (n : ℕ) (v : Tuple D n) (w : Fin (n + 1) → H) :
    pairingJet D n v w = ∏ i, oneJet D (v i) (w i) := by
  induction n with
  | zero => simp [pairingJet, oneJet, inputTuple, pureTuple, actionTuple]
  | succ n hn =>
    rw [Fin.prod_univ_castSucc, ← hn]
    apply Prod.ext
    · change inner ℂ (pure _ H (inputTuple D n (fun i => v i.castSucc)) (v (Fin.last (n + 1)) : H))
        (pure _ H (pureTuple D n (fun i => w i.castSucc)) (w (Fin.last (n + 1)))) = _
      rw [pure_inner]
      rfl
    · change inner ℂ (pure _ H (actionTuple D n (fun i => v i.castSucc)) (v (Fin.last (n + 1)) : H) +
        pure _ H (inputTuple D n (fun i => v i.castSucc)) (hamiltonian D (v (Fin.last (n + 1)))))
        (pure _ H (pureTuple D n (fun i => w i.castSucc)) (w (Fin.last (n + 1)))) = _
      rw [inner_add_left, pure_inner, pure_inner]
      change _ = inner ℂ (inputTuple D n (fun i => v i.castSucc)) (pureTuple D n (fun i => w i.castSucc)) *
          inner ℂ (hamiltonian D (v (Fin.last (n + 1)))) (w (Fin.last (n + 1))) +
        inner ℂ (actionTuple D n (fun i => v i.castSucc)) (pureTuple D n (fun i => w i.castSucc)) *
          inner ℂ (v (Fin.last (n + 1)) : H) (w (Fin.last (n + 1)))
      ring

theorem pairing_permute (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (v : Tuple D n) (w : Fin (n + 1) → H) :
    inner ℂ (actionTuple D n (tuplePerm n σ v)) (pureTuple D n (tuplePerm n σ w)) =
      inner ℂ (actionTuple D n v) (pureTuple D n w) := by
  have he : pairingJet D n (tuplePerm n σ v) (tuplePerm n σ w) = pairingJet D n v w := by
    rw [pairingJet_product, pairingJet_product]
    exact Equiv.prod_comp σ.symm (fun i => oneJet D (v i) (w i))
  exact congrArg TrivSqZeroExt.snd he

theorem vector_ext (D : Data H K) (n : ℕ) (x y : (nonemptySector D n).State)
    (hp : ∀ v, inner ℂ x (pureTuple D n v) = inner ℂ y (pureTuple D n v)) : x = y := by
  have he := linear_ext D n (innerSL ℂ x) (innerSL ℂ y) hp
  apply ext_inner_right ℂ
  intro z
  exact congrArg (fun L => L z) he

theorem actionTuple_permute (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (v : Tuple D n) :
    action D n σ (actionTuple D n v) = actionTuple D n (tuplePerm n σ v) := by
  apply vector_ext D n
  intro w
  let z := (tuplePerm n σ).symm w
  have hz : tuplePerm n σ z = w := (tuplePerm n σ).apply_symm_apply w
  rw [← hz, ← action_pure]
  have hi := (action D n σ).inner_map_map (actionTuple D n v) (pureTuple D n z)
  rw [hi, action_pure]
  exact (pairing_permute D n σ v z).symm

def domainPerm (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    KFCausalParticleDomainTensors.Core D n ≃ₗ[ℂ] KFCausalParticleDomainTensors.Core D n :=
  Finsupp.domLCongr (tuplePerm n σ)

theorem input_permute (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (u : KFCausalParticleDomainTensors.Core D n) :
    action D n σ (input D n u) = input D n (domainPerm D n σ u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single v c =>
    simp only [input, domainPerm, Finsupp.domLCongr_single, Finsupp.linearCombination_single, map_smul]
    congr 1
    exact action_pure D n σ (fun i => (v i : H))

theorem output_permute (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (u : KFCausalParticleDomainTensors.Core D n) :
    action D n σ (output D n u) = output D n (domainPerm D n σ u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single v c =>
    simp only [output, domainPerm, Finsupp.domLCongr_single, Finsupp.linearCombination_single, map_smul]
    rw [actionTuple_permute]

end
end UnifiedTheory.Audit.KFCausalParticleCoreCovariance
