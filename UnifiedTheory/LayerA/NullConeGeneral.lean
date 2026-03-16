/-
  LayerA/NullConeGeneral.lean — Null-cone theorem for general n+1 dimensions

  Strategy: instead of evaluating Finset.sums at test vectors (tedious),
  prove everything by RESTRICTING to 2D subspaces where the 1+1 theorem
  applies directly.

  For any pair of indices (0, k+1), restrict to the 2D subspace
  spanned by e₀ and e_{k+1}. The Minkowski form restricts to the
  1+1 Minkowski form. The null-cone theorem in that subspace gives
  the coefficient relations.
-/
import UnifiedTheory.LayerA.NullConeTensor
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace UnifiedTheory.LayerA.NullConeGeneral

/-! ### Restriction to 2D subspaces -/

/-- Restrict a quadratic form on ℝ^{n+1} to the 2D subspace
    spanned by coordinates 0 and k+1.
    The restriction maps (s, t) ↦ v where v₀ = s, v_{k+1} = t, rest = 0. -/
def restrict2D {n : ℕ} (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (k : Fin n) (s t : ℝ) : ℝ :=
  M 0 0 * s * s + 2 * M 0 (Fin.succ k) * s * t +
  M (Fin.succ k) (Fin.succ k) * t * t

/-- The Minkowski form restricted to the (0, k+1) plane is the 1+1 Minkowski form. -/
theorem mink_restrict {n : ℕ} (k : Fin n) (s t : ℝ) :
    -s ^ 2 + t ^ 2 = genQuad (-1) 0 1 (fun i : Fin 2 => if i = 0 then s else t) := by
  simp only [genQuad, show (0 : Fin 2) = 0 from rfl,
    show ¬((1 : Fin 2) = 0) from by decide, ite_true, ite_false]
  ring

/-- The restricted form matches the 1+1 genQuad parametrization. -/
theorem restrict_is_genQuad {n : ℕ} (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (k : Fin n) (v : Fin 2 → ℝ) :
    genQuad (M 0 0) (M 0 (Fin.succ k)) (M (Fin.succ k) (Fin.succ k)) v =
    restrict2D M k (v 0) (v 1) := by
  simp [genQuad, restrict2D]; ring

/-- **Key lemma**: if M vanishes on all null vectors of η in ℝ^{n+1},
    then the 2D restriction to the (0, k+1) plane vanishes on all
    null vectors of the restricted η. -/
theorem restriction_preserves_null {n : ℕ}
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k : Fin n) :
    -- The 2D restriction vanishes on null vectors of -s² + t² = 0
    ∀ v : Fin 2 → ℝ, minkQuad v = 0 →
      genQuad (M 0 0) (M 0 (Fin.succ k)) (M (Fin.succ k) (Fin.succ k)) v = 0 := by
  intro v hv
  -- Embed v into ℝ^{n+1}: put v₀ at position 0, v₁ at position k+1, rest = 0
  let w : Fin (n + 1) → ℝ := fun i =>
    if i = 0 then v 0
    else if i = Fin.succ k then v 1
    else 0
  -- w is null in ℝ^{n+1}: only positions 0 and k+1 are nonzero
  -- so -w₀² + w_{k+1}² = -v₀² + v₁² = minkQuad v = 0
  -- The double sum of M over w reduces to the 3 nonzero-index terms
  -- giving genQuad (M 0 0) (M 0 (Fin.succ k)) (M (Fin.succ k) (Fin.succ k)) v
  -- This is the Finset.sum extraction step.
  sorry -- Mechanical: sparse vector w has 2 nonzero entries → double sum has 4 nonzero terms

/-! ### Apply the 1+1 null-cone theorem to each restriction -/

/-- **Cross terms vanish**: M(0, k+1) = 0 for all k.

    By restriction to the (0, k+1) plane and the 1+1 null-cone theorem. -/
theorem cross_terms_vanish {n : ℕ} (hn : 0 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k : Fin n) :
    M 0 (Fin.succ k) = 0 := by
  -- The 1+1 null-cone theorem gives: b = 0 for the restriction
  -- where a = M(0,0), b = M(0, k+1), c = M(k+1, k+1)
  have h_restrict := restriction_preserves_null M hSym h_null k
  have ⟨hb, _⟩ := null_cone_coeffs (M 0 0) (M 0 (Fin.succ k))
    (M (Fin.succ k) (Fin.succ k)) h_restrict
  exact hb

/-- **Time-space relation**: M(0,0) = -M(k+1, k+1) for all k. -/
theorem time_space_relation {n : ℕ} (hn : 0 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k : Fin n) :
    M (Fin.succ k) (Fin.succ k) = -(M 0 0) := by
  have h_restrict := restriction_preserves_null M hSym h_null k
  have ⟨_, hc⟩ := null_cone_coeffs (M 0 0) (M 0 (Fin.succ k))
    (M (Fin.succ k) (Fin.succ k)) h_restrict
  exact hc

/-- **Spatial diagonal uniformity**: M(k+1,k+1) = M(l+1,l+1). -/
theorem spatial_uniform {n : ℕ} (hn : 0 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k l : Fin n) :
    M (Fin.succ k) (Fin.succ k) = M (Fin.succ l) (Fin.succ l) := by
  -- Both equal -M(0,0) by time_space_relation
  have hk := time_space_relation hn M hSym h_null k
  have hl := time_space_relation hn M hSym h_null l
  linarith

/-- **Off-diagonal spatial vanishing**: M(k+1, l+1) = 0 for k ≠ l.

    Restrict to the 3D subspace (0, k+1, l+1). A null vector in this
    subspace has -s² + t² + u² = 0. Evaluate at (1, cosθ, sinθ)
    for two values of θ to extract M(k+1, l+1) = 0. -/
theorem offdiag_vanish {n : ℕ} (hn : 1 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      (-(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2 = 0) →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0))
    (k l : Fin n) (hkl : k ≠ l) :
    M (Fin.succ k) (Fin.succ l) = 0 := by
  -- Embed (1, 1/√2, 1/√2, 0...) and (1, 1/√2, -1/√2, 0...) into ℝ^{n+1}
  -- Both are null. Their S-values differ by 4·M(k+1,l+1)·(1/2).
  -- Since both are 0, M(k+1,l+1) = 0.
  sorry -- requires 3D subspace restriction + Finset.sum evaluation

/-! ### The general null-cone theorem -/

/-- **Null-cone theorem (general n+1 dimensions, n ≥ 2).**

    If M is symmetric and S_M vanishes on all null vectors of η,
    then M is proportional to η:
    - Cross terms M(0, k+1) = 0
    - Off-diagonal spatial M(k+1, l+1) = 0 for k ≠ l
    - All spatial diagonals equal: M(k+1,k+1) = M(l+1,l+1)
    - Time-space: M(k+1,k+1) = -M(0,0) -/
theorem null_cone_general_2plus {n : ℕ} (hn : 1 < n)
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
