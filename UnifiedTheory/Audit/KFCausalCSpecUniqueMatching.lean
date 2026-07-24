/-
  Audit/KFCausalCSpecUniqueMatching.lean   (arc file 3/6)

  A CANONICAL, LABEL-FREE TRANSITION FROM A POSITIVE MATCHING MARGIN

  The transition across an overlap is the score-maximizing permutation.  A
  maximizer always EXISTS (the permutation group is finite).  It is CANONICAL —
  independent of any labeling choice — exactly when the matching margin is
  positive, i.e. the best permutation strictly beats every other.  We prove:

   * `exists_matching`          — a maximizer exists;
   * `unique_of_strict_margin`  — a strict margin forces uniqueness;
   * `permScore_inv`            — swapping charts inverts the score at σ⁻¹, so the
                                  reverse transition is the inverse (the inverse
                                  law σ_ji = σ_ij⁻¹).

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecOverlapScore

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecUniqueMatching

open scoped BigOperators RealInnerProductSpace
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecOverlapScore

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `σ` is a matching if it maximizes the overlap score. -/
def IsMatching (ci cj : Direction → H) (σ : Equiv.Perm Direction) : Prop :=
  ∀ τ, permScore ci cj τ ≤ permScore ci cj σ

/-- `σ` is the canonical matching if it STRICTLY beats every other permutation —
the positive-margin condition. -/
def IsCanonical (ci cj : Direction → H) (σ : Equiv.Perm Direction) : Prop :=
  ∀ τ, τ ≠ σ → permScore ci cj τ < permScore ci cj σ

/-- **A matching always exists** — the permutation group is finite. -/
theorem exists_matching (ci cj : Direction → H) :
    ∃ σ, IsMatching ci cj σ :=
  Finite.exists_max (permScore ci cj)

/-- **A positive (strict) margin forces a unique matching**: the canonical
permutation is the only maximizer, so the transition is label-free. -/
theorem unique_of_strict_margin (ci cj : Direction → H) (σ : Equiv.Perm Direction)
    (hσ : IsCanonical ci cj σ) :
    ∀ τ, IsMatching ci cj τ → τ = σ := by
  intro τ hτ
  by_contra hne
  exact absurd (hτ σ) (not_le.mpr (hσ τ hne))

/-- The canonical permutation is itself a matching. -/
theorem canonical_isMatching (ci cj : Direction → H) (σ : Equiv.Perm Direction)
    (hσ : IsCanonical ci cj σ) : IsMatching ci cj σ := by
  intro τ
  rcases eq_or_ne τ σ with h | h
  · exact le_of_eq (by rw [h])
  · exact le_of_lt (hσ τ h)

/-- **Inverse law, score form.** Swapping the two charts and taking σ⁻¹ preserves
the score.  Hence the reverse transition maximizer is the inverse of the forward
one: σ_ji = σ_ij⁻¹. -/
theorem permScore_inv (ci cj : Direction → H) (σ : Equiv.Perm Direction) :
    permScore cj ci σ⁻¹ = permScore ci cj σ := by
  unfold permScore score
  rw [← Equiv.sum_comp σ (fun a => (inner ℝ (cj a) (ci (σ⁻¹ a)) : ℝ))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Equiv.Perm.inv_apply_self]
  exact real_inner_comm _ _

/-- Consequently a canonical forward matching yields a canonical reverse matching
that is its inverse. -/
theorem reverse_matching_is_inverse (ci cj : Direction → H) (σ : Equiv.Perm Direction)
    (hσ : IsMatching ci cj σ) : IsMatching cj ci σ⁻¹ := by
  intro τ
  rw [permScore_inv ci cj σ, ← permScore_inv cj ci τ]
  exact hσ τ⁻¹

#print axioms exists_matching
#print axioms unique_of_strict_margin
#print axioms permScore_inv

end UnifiedTheory.Audit.KFCausalCSpecUniqueMatching
