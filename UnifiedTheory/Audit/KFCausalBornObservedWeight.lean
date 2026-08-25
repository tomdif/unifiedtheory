/-
  Audit/KFCausalBornObservedWeight.lean

  OBSERVED WEIGHTS FOR AN ARBITRARY BORN-NORMALIZED GROWTH LAW

  The first Gate 3 adapter specialized its weights to one fixed complete-
  chiral law.  This file extracts the mathematical construction: push the
  locally Born-normalized squared transition amplitudes of any finite-
  branching law through a fixed finite observation map.  Nonnegativity and
  unit mass are theorems.

  The harmonic Born-shell specialization is important because it keeps the
  microscopic action-selected running coupling and the downstream Gate 3
  probability weights in the same theory.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornNormalizationTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornObservedWeight

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer

universe u

/-- Push locally Born-normalized transition weights through a finite
observation map whose codomain does not depend on rank. -/
noncomputable def observedBornWeight
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    {ι : Type*} [Fintype ι]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (parentSchedule : (n : ℕ) → RankedGrowthPath Branch n)
    (observe : (n : ℕ) → Branch n → ι)
    (n : ℕ) (i : ι) : ℝ := by
  classical
  exact
    ∑ child : Branch n,
      if observe n child = i then
        Complex.normSq (law.transition n (parentSchedule n) child)
      else 0

/-- Pushforward Born weights are nonnegative. -/
theorem observedBornWeight_nonneg
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    {ι : Type*} [Fintype ι]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (parentSchedule : (n : ℕ) → RankedGrowthPath Branch n)
    (observe : (n : ℕ) → Branch n → ι) :
    ∀ n i, 0 ≤ observedBornWeight law parentSchedule observe n i := by
  classical
  intro n i
  unfold observedBornWeight
  apply Finset.sum_nonneg
  intro child _
  split
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- Total probability is preserved by every total finite observation map. -/
theorem observedBornWeight_sum_one
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    {ι : Type*} [Fintype ι]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (parentSchedule : (n : ℕ) → RankedGrowthPath Branch n)
    (observe : (n : ℕ) → Branch n → ι)
    (n : ℕ) :
    (∑ i : ι, observedBornWeight law parentSchedule observe n i) = 1 := by
  classical
  unfold observedBornWeight
  calc
    (∑ i : ι, ∑ child : Branch n,
        if observe n child = i then
          Complex.normSq (law.transition n (parentSchedule n) child)
        else 0) =
      ∑ child : Branch n, ∑ i : ι,
        if observe n child = i then
          Complex.normSq (law.transition n (parentSchedule n) child)
        else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ child : Branch n,
        Complex.normSq (law.transition n (parentSchedule n) child) := by
          apply Finset.sum_congr rfl
          intro child _
          simp
    _ = 1 := law.bornNormalized n (parentSchedule n)

/-- The unconditional harmonic Born-shell law, viewed through the generic
Born-normalized interface. -/
noncomputable def canonicalHarmonicBornLaw (chirality : Fin 2) :
    RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  canonicalHarmonicBornNormalizedGrowthLaw chirality

/-- Fixed-family Gate 3 weights belonging to the action-selected harmonic
Born-shell law. -/
noncomputable def harmonicObservedBornWeight
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    ℕ → ι → ℝ :=
  observedBornWeight
    (canonicalHarmonicBornLaw chirality) parentSchedule observe

theorem harmonicObservedBornWeight_nonneg
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    ∀ n i,
      0 ≤ harmonicObservedBornWeight
        chirality parentSchedule observe n i := by
  exact observedBornWeight_nonneg
    (canonicalHarmonicBornLaw chirality) parentSchedule observe

theorem harmonicObservedBornWeight_sum_one
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (n : ℕ) :
    (∑ i,
      harmonicObservedBornWeight
        chirality parentSchedule observe n i) = 1 := by
  exact observedBornWeight_sum_one
    (canonicalHarmonicBornLaw chirality) parentSchedule observe n

#print axioms observedBornWeight_nonneg
#print axioms observedBornWeight_sum_one
#print axioms harmonicObservedBornWeight_nonneg
#print axioms harmonicObservedBornWeight_sum_one

end


end UnifiedTheory.Audit.KFCausalBornObservedWeight
