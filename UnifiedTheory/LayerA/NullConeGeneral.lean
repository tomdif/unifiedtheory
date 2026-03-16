/-
  LayerA/NullConeGeneral.lean — Null-cone theorem for general n+1 dimensions

  Strategy: restrict to 2D subspaces where the 1+1 theorem applies.
  Two standalone helper lemmas handle the sparse-vector Finset extraction.
-/
import UnifiedTheory.LayerA.NullConeTensor
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

/-- **Sparse double sum lemma**: the double sum of M·w·w over a sparse vector
    reduces to 4 terms when only positions 0 and j are nonzero.

    Σᵢ Σⱼ M(i,k) w(i) w(k) = M(0,0)s² + M(0,j)st + M(j,0)ts + M(j,j)t²

    With symmetry M(0,j) = M(j,0), this is:
    M(0,0)s² + 2M(0,j)st + M(j,j)t² -/
lemma sparse_double_sum {n : ℕ} (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (j : Fin (n + 1)) (hj : j ≠ 0) (s t : ℝ) :
    ∑ a : Fin (n + 1), ∑ b : Fin (n + 1), M a b * sparseVec j s t a * sparseVec j s t b =
    M 0 0 * s * s + 2 * M 0 j * s * t + M j j * t * t := by
  -- Every term with a ∉ {0, j} or b ∉ {0, j} vanishes
  -- because sparseVec is 0 there.
  -- Strategy: split each sum into cases a = 0, a = j, a = other.
  -- Terms with a = other: sparseVec = 0, so term = 0.
  -- Terms with a ∈ {0, j}: split b similarly.
  sorry -- Finset.sum extraction: sparse vector → 4 nonzero terms

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
  -- w is null
  have hw_null : -(w 0) ^ 2 + ∑ i : Fin n, (w (Fin.succ i)) ^ 2 = 0 := by
    sorry -- sparse sum extraction: w nonzero only at 0 and succ k
  -- Apply h_null
  have hMw := h_null w hw_null
  -- hMw: the full double sum = 0
  -- genQuad = the same sum restricted to {0, k+1}
  -- Both equal 0 because the non-{0,k+1} terms vanish (sparse).
  simp only [genQuad]
  -- Goal: M 0 0 * (v 0)² + 2 * M 0 (succ k) * (v 0) * (v 1) +
  --        M (succ k) (succ k) * (v 1)² = 0
  -- This equals hMw (full sum) because all other terms are zero.
  -- We need: full sum = this expression.
  -- Use sparse_double_sum as the key extraction... but it has a sorry.
  -- Alternative: directly prove this special case.
  sorry

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
  -- Use null vectors (1, ..., eₖ/√2 + eₗ/√2, ...) and (1, ..., eₖ/√2 - eₗ/√2, ...)
  -- Their S-values differ by 4·M(k+1,l+1)·(1/2).
  -- Since both are null and both give S = 0, M(k+1,l+1) = 0.
  sorry

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
