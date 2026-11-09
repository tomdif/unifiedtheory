/- A symmetric triangular operator is diagonal after Gram--Schmidt.
This algebraic lemma applies on an invariant polynomial domain; it does not
assert a maximal unbounded-operator domain. -/
import UnifiedTheory.Audit.KFCausalGramSchmidtEigenvectors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSymmetricTriangularGramSchmidt
noncomputable section
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isometry_gramSchmidt {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (F : H →ₗᵢ[ℂ] K) (v : ℕ → H) (n : ℕ) :
    F (gramSchmidt ℂ v n) = gramSchmidt ℂ (fun j => F (v j)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [gramSchmidt_def, gramSchmidt_def]
    simp only [map_sub, map_sum, Submodule.starProjection_singleton, map_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← ih j (Finset.mem_Iio.mp hj), F.inner_map_map, F.norm_map]

theorem isometry_gramSchmidtNormed {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (F : H →ₗᵢ[ℂ] K) (v : ℕ → H) (n : ℕ) :
    F (gramSchmidtNormed ℂ v n) = gramSchmidtNormed ℂ (fun j => F (v j)) n := by
  simp only [gramSchmidtNormed, map_smul, ← isometry_gramSchmidt F v, F.norm_map]

set_option maxHeartbeats 800000 in
theorem diagonal (T : H →ₗ[ℂ] H) (v : ℕ → H) (e : ℕ → ℝ)
    (hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    (htri : ∀ n, T (v n) - (e n : ℂ) • v n ∈
      Submodule.span ℂ (v '' Set.Iio n)) (n : ℕ) :
    T (gramSchmidt ℂ v n) = (e n : ℂ) • gramSchmidt ℂ v n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let G := gramSchmidt ℂ v
    let S := Submodule.span ℂ (G '' Set.Iio n)
    let a (j : ℕ) := inner ℂ (G j) (v n) / (‖G j‖ : ℂ)^2
    have hr : T (G n) - (e n : ℂ) • G n =
        (T (v n) - (e n : ℂ) • v n) -
          ∑ j ∈ Finset.Iio n, a j • ((e j : ℂ) • G j - (e n : ℂ) • G j) := by
      have hg : G n = v n - ∑ j ∈ Finset.Iio n, a j • G j := by
        simpa only [G, a, Submodule.starProjection_singleton, map_pow] using
          gramSchmidt_def ℂ v n
      rw [hg, map_sub, map_sum]
      have hs : (∑ j ∈ Finset.Iio n, T (a j • G j)) =
          ∑ j ∈ Finset.Iio n, a j • ((e j : ℂ) • G j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul, ih j (Finset.mem_Iio.mp hj)]
      rw [hs]
      simp only [smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
      simp only [mul_comm (a _) (e n : ℂ)]
      abel
    have hm : T (G n) - (e n : ℂ) • G n ∈ S := by
      rw [hr]
      apply S.sub_mem
      · simpa only [S, G, span_gramSchmidt_Iio] using htri n
      · apply S.sum_mem
        intro j hj
        apply S.smul_mem
        apply S.sub_mem <;> apply S.smul_mem <;>
          exact Submodule.subset_span ⟨j, Finset.mem_Iio.mp hj, rfl⟩
    have ho : ∀ j < n, inner ℂ (G j) (T (G n) - (e n : ℂ) • G n) = 0 := by
      intro j hj
      rw [inner_sub_right, ← hsym, ih j hj, inner_smul_left, inner_smul_right]
      simp only [G, gramSchmidt_orthogonal ℂ v hj.ne, mul_zero, sub_self]
    have hz : ∀ x ∈ S, inner ℂ x (T (G n) - (e n : ℂ) • G n) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨j, hj, rfl⟩ := hx; exact ho j hj
      | zero => exact inner_zero_left _
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
    exact sub_eq_zero.mp ((inner_self_eq_zero).mp (hz _ hm))

theorem normed_diagonal (T : H →ₗ[ℂ] H) (v : ℕ → H) (e : ℕ → ℝ)
    (hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    (htri : ∀ n, T (v n) - (e n : ℂ) • v n ∈
      Submodule.span ℂ (v '' Set.Iio n)) (n : ℕ) :
    T (gramSchmidtNormed ℂ v n) = (e n : ℂ) • gramSchmidtNormed ℂ v n := by
  rw [gramSchmidtNormed, map_smul, diagonal T v e hsym htri]
  exact smul_comm _ _ _

#print axioms diagonal
#print axioms normed_diagonal
end
end UnifiedTheory.Audit.KFCausalSymmetricTriangularGramSchmidt
