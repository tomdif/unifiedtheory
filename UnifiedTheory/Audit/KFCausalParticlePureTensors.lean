/- Pure tensors are total in every completed labelled particle sector.
Their inner products are products of the one-particle inner products. -/
import UnifiedTheory.Audit.KFCausalTensorParticleSectors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalParticlePureTensors
noncomputable section
open scoped TensorProduct
open KFCausalClosedGraphForm KFCausalCompletedTensor KFCausalTensorParticleSectors

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def pureTuple (D : Data H K) : (n : ℕ) → (Fin (n + 1) → H) → (nonemptySector D n).State
  | 0, v => v 0
  | n + 1, v => pure (nonemptySector D n).State H
      (pureTuple D n (fun i => v i.castSucc)) (v (Fin.last (n + 1)))

theorem pureTuple_inner (D : Data H K) (n : ℕ) (v w : Fin (n + 1) → H) :
    inner ℂ (pureTuple D n v) (pureTuple D n w) = ∏ i, inner ℂ (v i) (w i) := by
  induction n with
  | zero => simp [pureTuple]
  | succ n hn =>
    rw [pureTuple, pureTuple, pure_inner, hn]
    exact (Fin.prod_univ_castSucc (fun i => inner ℂ (v i) (w i))).symm

theorem pureTuple_snoc (D : Data H K) (n : ℕ) (v : Fin (n + 1) → H) (y : H) :
    pureTuple D (n + 1) (Fin.snoc v y) =
      pure (nonemptySector D n).State H (pureTuple D n v) y := by
  simp [pureTuple]

theorem total (D : Data H K) (n : ℕ) (S : Submodule ℂ (nonemptySector D n).State)
    (hc : IsClosed (S : Set (nonemptySector D n).State))
    (hp : ∀ v, pureTuple D n v ∈ S) : ∀ x, x ∈ S := by
  induction n with
  | zero => intro x; exact hp (fun _ => x)
  | succ n hn =>
    have ht (x : (nonemptySector D n).State) (y : H) :
        pure (nonemptySector D n).State H x y ∈ S := by
      let L := left (nonemptySector D n).State H y
      have hL : ∀ v, pureTuple D n v ∈ S.comap L.toLinearMap := by
        intro v
        change pure (nonemptySector D n).State H (pureTuple D n v) y ∈ S
        rw [← pureTuple_snoc]
        exact hp (Fin.snoc v y)
      exact hn (S.comap L.toLinearMap) (hc.preimage L.continuous) hL x
    have ha (u : (nonemptySector D n).State ⊗[ℂ] H) :
        includeTensor (nonemptySector D n).State H u ∈ S := by
      induction u using TensorProduct.induction_on with
      | zero => exact S.zero_mem
      | tmul x y => exact ht x y
      | add u v hu hv => simpa only [map_add] using S.add_mem hu hv
    intro x
    exact UniformSpace.Completion.denseRange_coe.induction_on x hc ha

abbrev Core (D : Data H K) (n : ℕ) := (Fin (n + 1) → H) →₀ ℂ

def embedding (D : Data H K) (n : ℕ) : Core D n →ₗ[ℂ] (nonemptySector D n).State :=
  Finsupp.linearCombination ℂ (pureTuple D n)

theorem embedding_single (D : Data H K) (n : ℕ) (v : Fin (n + 1) → H) (c : ℂ) :
    embedding D n (Finsupp.single v c) = c • pureTuple D n v :=
  Finsupp.linearCombination_single _ _ _

theorem embedding_dense (D : Data H K) (n : ℕ) : DenseRange (embedding D n) := by
  apply total D n (embedding D n).range.topologicalClosure
    (embedding D n).range.isClosed_topologicalClosure
  intro v
  apply (embedding D n).range.le_topologicalClosure
  exact ⟨Finsupp.single v 1, by simp [embedding_single]⟩

theorem linear_ext (D : Data H K) (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P Q : (nonemptySector D n).State →L[ℂ] E)
    (hp : ∀ v, P (pureTuple D n v) = Q (pureTuple D n v)) : P = Q := by
  have hker : ∀ v, pureTuple D n v ∈ (P - Q).ker := by
    intro v
    change P (pureTuple D n v) - Q (pureTuple D n v) = 0
    exact sub_eq_zero.mpr (hp v)
  have he := total D n (P - Q).ker (P - Q).isClosed_ker hker
  ext x
  have hh := he x
  change P x - Q x = 0 at hh
  exact sub_eq_zero.mp hh

end
end UnifiedTheory.Audit.KFCausalParticlePureTensors
