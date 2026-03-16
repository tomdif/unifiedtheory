/-
  LayerA/NullConeGeneral.lean — Null-cone theorem for general n+1 dimensions

  Strategy: restrict to 2D subspaces where the 1+1 theorem applies.
  Two standalone helper lemmas handle the sparse-vector Finset extraction.
-/
import UnifiedTheory.LayerA.NullConeTensor
import UnifiedTheory.LayerA.SparseSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace UnifiedTheory.LayerA.NullConeGeneral

/-! ### Helper 1: Sparse double sum reduction -/

/-- A vector that is nonzero only at positions 0 and j. -/
def sparseVec {n : ℕ} (j : Fin (n + 1)) (s t : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then s else if i = j then t else 0

/-- For the sparse vector, entries outside {0, j} are zero. -/
lemma sparseVec_zero {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) (s t : ℝ)
    (i : Fin (n + 1)) (hi0 : i ≠ 0) (hij : i ≠ j) :
    sparseVec j s t i = 0 := by
  simp [sparseVec, hi0, hij]

/-- sparseVec at 0 is s. -/
lemma sparseVec_at_zero {n : ℕ} (j : Fin (n + 1)) (s t : ℝ) :
    sparseVec j s t 0 = s := if_pos rfl

/-- sparseVec at j is t (when j ≠ 0). -/
lemma sparseVec_at_j {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) (s t : ℝ) :
    sparseVec j s t j = t := by simp [sparseVec, hj]

/-! ### The 2D restriction via sparse vectors -/

/-- **Restriction theorem**: M vanishes on the 2D null restriction.

    For any k, restrict to the (0, k+1) plane using a sparse vector.
    The 1+1 null-cone theorem then applies. -/
theorem restriction_preserves_null {n : ℕ}
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k : Fin n) :
    ∀ v : Fin 2 → ℝ, minkQuad v = 0 →
      genQuad (M 0 0) (M 0 (Fin.succ k)) (M (Fin.succ k) (Fin.succ k)) v = 0 := by
  intro v hv
  -- Use sparse vector: w = sparseVec (Fin.succ k) (v 0) (v 1)
  let w := sparseVec (Fin.succ k) (v 0) (v 1)
  -- w is sparse: nonzero only at 0 and Fin.succ k
  have hw_sparse : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ Fin.succ k → w i = 0 := by
    intro i h0 hk; simp [w, sparseVec, h0, hk]
  -- w(0) = v 0, w(succ k) = v 1
  have hw0 : w 0 = v 0 := by simp [w, sparseVec]
  have hwk : w (Fin.succ k) = v 1 := by
    simp [w, sparseVec, Fin.succ_ne_zero k]
  -- w is null: use sum_pair for the spatial sum
  have hw_null : -(w 0) ^ 2 + ∑ i : Fin n, (w (Fin.succ i)) ^ 2 = 0 := by
    rw [hw0]
    have : ∑ i : Fin n, (w (Fin.succ i)) ^ 2 = (v 1) ^ 2 := by
      -- Use sum_pair with a = k and b = k (degenerate) -- no, need single.
      -- Use: Σ f = f(k) when f(i) = 0 for i ≠ k
      have hk_only : ∀ i : Fin n, i ≠ k → (w (Fin.succ i)) ^ 2 = 0 := by
        intro i hi
        have : w (Fin.succ i) = 0 :=
          hw_sparse (Fin.succ i) (Fin.succ_ne_zero i)
            (fun h => hi (Fin.succ_injective _ h))
        simp [this]
      rw [Finset.sum_eq_single k (fun b _ hb => hk_only b hb)
        (fun hk => absurd (Finset.mem_univ k) hk), hwk]
    rw [this]; simp [minkQuad] at hv; linarith
  -- Apply h_null: full double sum = 0
  have hMw := h_null w hw_null
  -- Use SparseSum: full double sum = 3-term form
  have hcollapse := SparseSum.double_sum_two_support_sym M hSym w 0 (Fin.succ k)
    (Fin.succ_ne_zero k).symm hw_sparse
  rw [hcollapse, hw0, hwk] at hMw
  simp only [genQuad]; linarith

/-! ### Apply the 1+1 null-cone theorem -/

/-- **Cross terms vanish**: M(0, k+1) = 0. -/
theorem cross_terms_vanish {n : ℕ} (hn : 0 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k : Fin n) :
    M 0 (Fin.succ k) = 0 := by
  have h_restrict := restriction_preserves_null M hSym h_null k
  exact (null_cone_coeffs _ _ _ h_restrict).1

/-- **Time-space relation**: M(k+1,k+1) = -M(0,0). -/
theorem time_space_relation {n : ℕ} (hn : 0 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k : Fin n) :
    M (Fin.succ k) (Fin.succ k) = -(M 0 0) := by
  have h_restrict := restriction_preserves_null M hSym h_null k
  exact (null_cone_coeffs _ _ _ h_restrict).2

/-- **Spatial uniformity**: M(k+1,k+1) = M(l+1,l+1). -/
theorem spatial_uniform {n : ℕ} (hn : 0 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k l : Fin n) :
    M (Fin.succ k) (Fin.succ k) = M (Fin.succ l) (Fin.succ l) := by
  linarith [time_space_relation hn M hSym h_null k,
            time_space_relation hn M hSym h_null l]

/-- **Off-diagonal vanishing**: M(k+1, l+1) = 0 for k ≠ l. -/
theorem offdiag_vanish {n : ℕ} (hn : 1 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k l : Fin n) (hkl : k ≠ l) :
    M (Fin.succ k) (Fin.succ l) = 0 := by
  -- Pythagorean trick: vector w with w(0)=5, w(succ k)=3, w(succ l)=4, rest=0.
  -- This is null: -25 + 9 + 16 = 0. The double sum gives 24·M(sk,sl) = 0.
  let sk := Fin.succ k
  let sl := Fin.succ l
  have hsk_ne_zero : sk ≠ 0 := Fin.succ_ne_zero k
  have hsl_ne_zero : sl ≠ 0 := Fin.succ_ne_zero l
  have hsk_ne_sl : sk ≠ sl := by intro h; exact hkl (Fin.succ_injective _ h)
  -- Known results from 2D restrictions
  have h_cross_k := cross_terms_vanish (by omega : 0 < n) M hSym h_null k
  have h_cross_l := cross_terms_vanish (by omega : 0 < n) M hSym h_null l
  have h_diag_k := time_space_relation (by omega : 0 < n) M hSym h_null k
  have h_diag_l := time_space_relation (by omega : 0 < n) M hSym h_null l
  -- Build Pythagorean vector
  let w : Fin (n + 1) → ℝ := fun i =>
    if i = (0 : Fin (n + 1)) then 5 else if i = sk then 3 else if i = sl then 4 else 0
  -- w is 3-sparse
  have hw_sparse : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ sk → i ≠ sl → w i = 0 := by
    intro i h0 hk hl; simp only [w, if_neg h0, if_neg hk, if_neg hl]
  have hw0 : w 0 = 5 := if_pos rfl
  have hwk : w sk = 3 := by
    simp [w, hsk_ne_zero]
  have hwl : w sl = 4 := by
    simp [w, hsl_ne_zero, Ne.symm hsk_ne_sl]
  -- w is null: -25 + 9 + 16 = 0
  have hw_null : -(w 0) ^ 2 + ∑ i : Fin n, (w (Fin.succ i)) ^ 2 = 0 := by
    rw [hw0]
    -- The spatial sum has support only at k and l
    have hsupp : ∀ i : Fin n, i ≠ k → i ≠ l → (w (Fin.succ i)) ^ 2 = 0 := by
      intro i hik hil
      have : w (Fin.succ i) = 0 := hw_sparse (Fin.succ i) (Fin.succ_ne_zero i)
        (fun h => hik (Fin.succ_injective _ h)) (fun h => hil (Fin.succ_injective _ h))
      simp [this]
    rw [SparseSum.sum_pair _ k l hkl hsupp, hwk, hwl]; norm_num
  -- Apply h_null
  have hMw := h_null w hw_null
  -- Expand double sum using 3-support lemma
  have hexpand := SparseSum.double_sum_three_support_sym M hSym w 0 sk sl
    hsk_ne_zero.symm hsl_ne_zero.symm hsk_ne_sl hw_sparse
  rw [hexpand, hw0, hwk, hwl] at hMw
  -- Substitute known values
  rw [h_cross_k, h_cross_l, h_diag_k, h_diag_l] at hMw
  linarith

/-! ### The general null-cone theorem -/

/-- **Null-cone theorem (general n+1, n ≥ 2).** -/
theorem null_cone_general {n : ℕ} (hn : 1 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0)) :
    (∀ k : Fin n, M 0 (Fin.succ k) = 0) ∧
    (∀ k l : Fin n, k ≠ l → M (Fin.succ k) (Fin.succ l) = 0) ∧
    (∀ k l : Fin n, M (Fin.succ k) (Fin.succ k) = M (Fin.succ l) (Fin.succ l)) ∧
    (∀ k : Fin n, M (Fin.succ k) (Fin.succ k) = -(M 0 0)) :=
  ⟨cross_terms_vanish (by omega) M hSym h_null,
   offdiag_vanish hn M hSym h_null,
   spatial_uniform (by omega) M hSym h_null,
   time_space_relation (by omega) M hSym h_null⟩

end UnifiedTheory.LayerA.NullConeGeneral
