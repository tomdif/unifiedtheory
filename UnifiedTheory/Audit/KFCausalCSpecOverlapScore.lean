/-
  Audit/KFCausalCSpecOverlapScore.lean   (arc file 2/6)

  OVERLAP MATCHING SCORE FROM THE COMMON CAUSAL CARRIER

  Given two charts' centered continuation profiles `ci cj : Direction → H` on a
  shared overlap carrier `H`, the depth-weighted overlap score is the inner
  product `S(a,b) = ⟪ci a, cj b⟫`.  A candidate transition permutation `σ`
  scores by aligning direction `a` of chart i with `σ a` of chart j:
      permScore σ = Σ_a ⟪ci a, cj (σ a)⟫.

  Provable content: the score is symmetric under swapping the two charts and the
  two directions (`score_symm`), so the whole matching problem is symmetric — the
  seed of the inverse law in file 3.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecContinuationProfile

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecOverlapScore

open scoped BigOperators RealInnerProductSpace
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Overlap score of direction `a` in chart i against direction `b` in chart j. -/
noncomputable def score (ci cj : Direction → H) (a b : Direction) : ℝ :=
  inner ℝ (ci a) (cj b)

/-- **Score symmetry.** Swapping the two charts and the two directions leaves the
score unchanged. -/
theorem score_symm (ci cj : Direction → H) (a b : Direction) :
    score ci cj a b = score cj ci b a :=
  real_inner_comm _ _

/-- Score of a candidate transition permutation. -/
noncomputable def permScore (ci cj : Direction → H) (σ : Equiv.Perm Direction) : ℝ :=
  ∑ a, score ci cj a (σ a)

theorem permScore_def (ci cj : Direction → H) (σ : Equiv.Perm Direction) :
    permScore ci cj σ = ∑ a, inner ℝ (ci a) (cj (σ a)) := rfl

#print axioms score_symm

end UnifiedTheory.Audit.KFCausalCSpecOverlapScore
