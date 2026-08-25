/-
  Audit/KFCausalCSpecCompleteChiralPositiveRankObservation.lean

  A CAUSAL-ORDER-DERIVED TWO-CELL OBSERVATION AFTER THE ROOT STAGE

  Rank zero is necessarily deterministic.  At every positive rank, however,
  the gregarious (empty precursor) and timid (full precursor) children are
  distinct physical one-element extensions.  This module uses that intrinsic
  distinction to define a fixed `Fin 2` observation: cell one is precisely the
  gregarious child and cell zero contains every other child.

  Exact physical support of the complete-chiral Born weights makes both cells
  strictly positive.  The binary indicator horizon observable consequently
  has strictly positive variance at every positive rank.  Thus the observation
  map and nondegenerate-variance premise can be derived after shifting past the
  deterministic root; the remaining repair dynamics are separate.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecCompleteChiralRankZeroVarianceNoGo
import UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecCompleteChiralPositiveRankObservation

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornPathLaw
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecCompleteChiralStoppableRepairAdapter

/-! ## 1. Intrinsic extreme children -/

/-- A chosen labeled representative of the current unlabeled parent.  All
downstream statements are quotient-invariant. -/
def currentParentRepresentative (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    CardinalCausalOrder n :=
  Classical.choose
    (Quotient.exists_rep (currentUnlabeledCausalOrder n pathPrefix))

theorem currentParentRepresentative_spec (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    Quotient.mk _ (currentParentRepresentative n pathPrefix) =
      currentUnlabeledCausalOrder n pathPrefix :=
  Classical.choose_spec
    (Quotient.exists_rep (currentUnlabeledCausalOrder n pathPrefix))

/-- The gregarious child adds a new event with empty precursor. -/
def canonicalGregariousChild (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    CausalSetGrowthBranch n :=
  causalTransitionTarget (currentParentRepresentative n pathPrefix)
    (emptyCausalPastSet (currentParentRepresentative n pathPrefix))

/-- The timid child adds a new event above the full parent. -/
def canonicalTimidChild (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    CausalSetGrowthBranch n :=
  causalTransitionTarget (currentParentRepresentative n pathPrefix)
    (fullCausalPastSet (currentParentRepresentative n pathPrefix))

theorem canonicalGregariousChild_physical (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    IsPhysicalCausalGrowthStep n pathPrefix
      (canonicalGregariousChild n pathPrefix) := by
  unfold IsPhysicalCausalGrowthStep canonicalGregariousChild
  rw [← currentParentRepresentative_spec]
  exact isUnlabeledOneElementExtension_mk
    (precursor_is_oneElementExtension
      (currentParentRepresentative n pathPrefix)
      (emptyCausalPastSet (currentParentRepresentative n pathPrefix)))

theorem canonicalTimidChild_physical (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    IsPhysicalCausalGrowthStep n pathPrefix
      (canonicalTimidChild n pathPrefix) := by
  unfold IsPhysicalCausalGrowthStep canonicalTimidChild
  rw [← currentParentRepresentative_spec]
  exact isUnlabeledOneElementExtension_mk
    (precursor_is_oneElementExtension
      (currentParentRepresentative n pathPrefix)
      (fullCausalPastSet (currentParentRepresentative n pathPrefix)))

theorem canonicalGregariousChild_ne_timid {n : ℕ} (hn : 0 < n)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    canonicalGregariousChild n pathPrefix ≠
      canonicalTimidChild n pathPrefix := by
  exact empty_and_full_causalTransitionTargets_ne_of_pos hn
    (currentParentRepresentative n pathPrefix)

/-! ## 2. Fixed binary observation and positive cell masses -/

/-- Intrinsic fixed-cell observation: `1` records the unique gregarious child;
`0` records every non-gregarious child. -/
def completeChiralPositiveRankObserve
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (n : ℕ) (child : CausalSetGrowthBranch n) : Fin 2 :=
  if child = canonicalGregariousChild n (parentSchedule n) then 1 else 0

@[simp] theorem completeChiralPositiveRankObserve_gregarious
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (n : ℕ) :
    completeChiralPositiveRankObserve parentSchedule n
      (canonicalGregariousChild n (parentSchedule n)) = 1 := by
  simp [completeChiralPositiveRankObserve]

theorem completeChiralPositiveRankObserve_timid {n : ℕ} (hn : 0 < n)
    (parentSchedule :
      (k : ℕ) → RankedGrowthPath CausalSetGrowthBranch k) :
    completeChiralPositiveRankObserve parentSchedule n
      (canonicalTimidChild n (parentSchedule n)) = 0 := by
  simp [completeChiralPositiveRankObserve,
    (canonicalGregariousChild_ne_timid hn (parentSchedule n)).symm]

theorem completeChiralPositiveRankWeight_one_pos
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (n : ℕ) :
    0 < completeChiralGate3Weight chirality parentSchedule
      (completeChiralPositiveRankObserve parentSchedule) n 1 := by
  classical
  let child := canonicalGregariousChild n (parentSchedule n)
  have hChildWeight :
      0 < completeChiralStageBornWeight chirality n (parentSchedule n) child :=
    (completeChiralStageBornWeight_pos_iff_physical
      chirality n (parentSchedule n) child).2
      (canonicalGregariousChild_physical n (parentSchedule n))
  unfold completeChiralGate3Weight completeChiralObservedBornWeight
  apply lt_of_lt_of_le hChildWeight
  let f : CausalSetGrowthBranch n → ℝ := fun other =>
    if completeChiralPositiveRankObserve parentSchedule n other = 1 then
      completeChiralStageBornWeight chirality n (parentSchedule n) other
    else 0
  have hle : f child ≤ Finset.univ.sum f := by
    apply Finset.single_le_sum
    · intro other _
      dsimp only [f]
      split
      · exact completeChiralStageBornWeight_nonneg
          chirality n (parentSchedule n) other
      · exact le_rfl
    · exact Finset.mem_univ child
  simpa [f, child, completeChiralPositiveRankObserve] using hle

theorem completeChiralPositiveRankWeight_zero_pos
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    {n : ℕ} (hn : 0 < n) :
    0 < completeChiralGate3Weight chirality parentSchedule
      (completeChiralPositiveRankObserve parentSchedule) n 0 := by
  classical
  let child := canonicalTimidChild n (parentSchedule n)
  have hChildWeight :
      0 < completeChiralStageBornWeight chirality n (parentSchedule n) child :=
    (completeChiralStageBornWeight_pos_iff_physical
      chirality n (parentSchedule n) child).2
      (canonicalTimidChild_physical n (parentSchedule n))
  unfold completeChiralGate3Weight completeChiralObservedBornWeight
  apply lt_of_lt_of_le hChildWeight
  let f : CausalSetGrowthBranch n → ℝ := fun other =>
    if completeChiralPositiveRankObserve parentSchedule n other = 0 then
      completeChiralStageBornWeight chirality n (parentSchedule n) other
    else 0
  have hle : f child ≤ Finset.univ.sum f := by
    apply Finset.single_le_sum
    · intro other _
      dsimp only [f]
      split
      · exact completeChiralStageBornWeight_nonneg
          chirality n (parentSchedule n) other
      · exact le_rfl
    · exact Finset.mem_univ child
  simpa [f, child, completeChiralPositiveRankObserve,
    (canonicalGregariousChild_ne_timid hn (parentSchedule n)).symm] using hle

/-! ## 3. Derived nondegenerate horizon variance -/

/-- The binary observable distinguishing the two observation cells. -/
def binaryHorizonObservable (i : Fin 2) : ℝ :=
  if i = 1 then 1 else 0

/-- A normalized distribution with positive mass in both binary cells has
strictly positive variance for the binary indicator observable. -/
theorem binaryHorizonObservable_variance_pos
    (w : Fin 2 → ℝ)
    (hzero : 0 < w 0) (hone : 0 < w 1)
    (hsum : ∑ i, w i = 1) :
    0 < variance w binaryHorizonObservable := by
  have hsum' : w 0 + w 1 = 1 := by
    simpa [Fin.sum_univ_two] using hsum
  unfold variance covariance expectation binaryHorizonObservable
  simp
  nlinarith

/-- At every positive causal rank, the order-derived binary observation and
binary horizon observable have nonzero (indeed strictly positive) Born
variance. -/
theorem completeChiralPositiveRank_variance_pos
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    {n : ℕ} (hn : 0 < n) :
    0 < variance
      (completeChiralGate3Weight chirality parentSchedule
        (completeChiralPositiveRankObserve parentSchedule) n)
      binaryHorizonObservable := by
  apply binaryHorizonObservable_variance_pos
  · exact completeChiralPositiveRankWeight_zero_pos
      chirality parentSchedule hn
  · exact completeChiralPositiveRankWeight_one_pos
      chirality parentSchedule n
  · exact completeChiralGate3Weight_sum_one chirality parentSchedule
      (completeChiralPositiveRankObserve parentSchedule) n

theorem completeChiralPositiveRank_variance_ne_zero
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    {n : ℕ} (hn : 0 < n) :
    variance
      (completeChiralGate3Weight chirality parentSchedule
        (completeChiralPositiveRankObserve parentSchedule) n)
      binaryHorizonObservable ≠ 0 :=
  ne_of_gt (completeChiralPositiveRank_variance_pos
    chirality parentSchedule hn)

#print axioms canonicalGregariousChild_ne_timid
#print axioms completeChiralPositiveRankWeight_zero_pos
#print axioms completeChiralPositiveRankWeight_one_pos
#print axioms completeChiralPositiveRank_variance_pos
#print axioms completeChiralPositiveRank_variance_ne_zero

end

end UnifiedTheory.Audit.KFCausalCSpecCompleteChiralPositiveRankObservation
