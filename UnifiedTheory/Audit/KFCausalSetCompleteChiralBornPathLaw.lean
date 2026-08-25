/-
  Audit/KFCausalSetCompleteChiralBornPathLaw.lean

  FINITE PATH LAW FROM THE COMPLETE-CHIRAL STAGEWISE BORN WEIGHTS

  The stagewise squared-modulus weights are already nonnegative, normalized,
  and supported exactly on physical one-element extensions.  This module takes
  their recursive product along ranked growth paths.  It proves nonnegativity,
  exact one-step marginal/projective consistency, and unit total mass at every
  finite depth.

  It also fixes one prefix-coherent physical parent schedule by recursively
  choosing a member of the nonempty physical-successor fiber.  This removes
  the need to postulate unrelated parents at different ranks.  The choice is a
  canonical Lean term, not a new dynamical selection principle.

  Scope remains finite causal growth.  A fixed observation map into the Gate 3
  cell family and a microscopic supplier of the stoppable repair dynamics are
  still external.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetCompleteChiralBornPathLaw

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights

/-! ## 1. Finite complete-chiral Born path probabilities -/

/-- Product of the normalized complete-chiral stage weights along a finite
ranked causal-growth path. -/
def completeChiralFinitePathProbability (chirality : Fin 2) :
    ∀ n : ℕ, RankedGrowthPath CausalSetGrowthBranch n → ℝ
  | 0, _ => 1
  | n + 1, path =>
      completeChiralFinitePathProbability chirality n path.1 *
        completeChiralStageBornWeight chirality n path.1 path.2

@[simp]
theorem completeChiralFinitePathProbability_zero
    (chirality : Fin 2)
    (path : RankedGrowthPath CausalSetGrowthBranch 0) :
    completeChiralFinitePathProbability chirality 0 path = 1 := rfl

@[simp]
theorem completeChiralFinitePathProbability_snoc
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    completeChiralFinitePathProbability chirality (n + 1)
        (pathPrefix, child) =
      completeChiralFinitePathProbability chirality n pathPrefix *
        completeChiralStageBornWeight chirality n pathPrefix child := rfl

/-- Every finite complete-chiral Born path probability is nonnegative. -/
theorem completeChiralFinitePathProbability_nonneg
    (chirality : Fin 2) :
    ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      0 ≤ completeChiralFinitePathProbability chirality n path
  | 0, path => by
      rw [completeChiralFinitePathProbability_zero]
      norm_num
  | n + 1, path => by
      rcases path with ⟨pathPrefix, child⟩
      exact mul_nonneg
        (completeChiralFinitePathProbability_nonneg chirality n pathPrefix)
        (completeChiralStageBornWeight_nonneg
          chirality n pathPrefix child)

/-- Marginalizing all one-step children returns the probability of their
common prefix. -/
theorem completeChiralFinitePathProbability_sum_children
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    (∑ child : CausalSetGrowthBranch n,
      completeChiralFinitePathProbability chirality (n + 1)
        (pathPrefix, child)) =
      completeChiralFinitePathProbability chirality n pathPrefix := by
  simp only [completeChiralFinitePathProbability_snoc]
  rw [← Finset.mul_sum,
    completeChiralStageBornWeight_sum_one, mul_one]

/-- Exact one-step projectivity for every finite event of path prefixes. -/
theorem completeChiralFinitePathProbability_sum_refine
    (chirality : Fin 2) (n : ℕ)
    (event : Finset (RankedGrowthPath CausalSetGrowthBranch n)) :
    ∑ path ∈ refineRankedGrowthEvent event,
        completeChiralFinitePathProbability chirality (n + 1) path =
      ∑ pathPrefix ∈ event,
        completeChiralFinitePathProbability chirality n pathPrefix := by
  classical
  change ∑ path ∈
      event ×ˢ (Finset.univ : Finset (CausalSetGrowthBranch n)),
      completeChiralFinitePathProbability chirality n path.1 *
        completeChiralStageBornWeight chirality n path.1 path.2 = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro pathPrefix _
  exact completeChiralFinitePathProbability_sum_children
    chirality n pathPrefix

/-- The complete-chiral Born path probabilities have total mass one at every
finite depth. -/
theorem completeChiralFinitePathProbability_sum_univ
    (chirality : Fin 2) : ∀ n : ℕ,
    (∑ path : RankedGrowthPath CausalSetGrowthBranch n,
      completeChiralFinitePathProbability chirality n path) = 1
  | 0 => by
      change ∑ _path : PUnit, (1 : ℝ) = 1
      simp
  | n + 1 => by
      classical
      rw [← refineRankedGrowthEvent_univ
        (Branch := CausalSetGrowthBranch) n]
      rw [completeChiralFinitePathProbability_sum_refine]
      exact completeChiralFinitePathProbability_sum_univ chirality n

/-- The finite path law has exact physical support, not merely nonnegative
physical support. -/
theorem completeChiralFinitePathProbability_pos_iff_physical
    (chirality : Fin 2) :
    ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      0 < completeChiralFinitePathProbability chirality n path ↔
        IsPhysicalCausalGrowthPath n path
  | 0, path => by
      simp [IsPhysicalCausalGrowthPath]
  | n + 1, path => by
      change
        0 < completeChiralFinitePathProbability chirality n path.1 *
            completeChiralStageBornWeight chirality n path.1 path.2 ↔
          IsPhysicalCausalGrowthPath n path.1 ∧
            IsPhysicalCausalGrowthStep n path.1 path.2
      constructor
      · intro hproduct
        have hprefix_nonneg :=
          completeChiralFinitePathProbability_nonneg chirality n path.1
        have hweight_nonneg :=
          completeChiralStageBornWeight_nonneg
            chirality n path.1 path.2
        have hprefix_pos :
            0 < completeChiralFinitePathProbability chirality n path.1 := by
          by_contra hnot
          have hzero :
              completeChiralFinitePathProbability chirality n path.1 = 0 :=
            le_antisymm (le_of_not_gt hnot) hprefix_nonneg
          rw [hzero, zero_mul] at hproduct
          exact (lt_irrefl 0) hproduct
        have hweight_pos :
            0 < completeChiralStageBornWeight
              chirality n path.1 path.2 := by
          by_contra hnot
          have hzero :
              completeChiralStageBornWeight chirality n path.1 path.2 = 0 :=
            le_antisymm (le_of_not_gt hnot) hweight_nonneg
          rw [hzero, mul_zero] at hproduct
          exact (lt_irrefl 0) hproduct
        exact
          ⟨(completeChiralFinitePathProbability_pos_iff_physical
              chirality n path.1).1 hprefix_pos,
            (completeChiralStageBornWeight_pos_iff_physical
              chirality n path.1 path.2).1 hweight_pos⟩
      · rintro ⟨hprefix, hstep⟩
        exact mul_pos
          ((completeChiralFinitePathProbability_pos_iff_physical
            chirality n path.1).2 hprefix)
          ((completeChiralStageBornWeight_pos_iff_physical
            chirality n path.1 path.2).2 hstep)

/-! ## 2. A prefix-coherent physical parent schedule -/

/-- A fixed physical successor chosen from the provably nonempty successor
fiber of a given prefix. -/
def canonicalPhysicalSuccessor (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    CausalSetGrowthBranch n :=
  Classical.choose (physicalCausalSuccessors_nonempty n pathPrefix)

theorem canonicalPhysicalSuccessor_mem (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    canonicalPhysicalSuccessor n pathPrefix ∈
      physicalCausalSuccessors n pathPrefix := by
  exact Classical.choose_spec
    (physicalCausalSuccessors_nonempty n pathPrefix)

theorem canonicalPhysicalSuccessor_isPhysical (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    IsPhysicalCausalGrowthStep n pathPrefix
      (canonicalPhysicalSuccessor n pathPrefix) := by
  simpa [physicalCausalSuccessors] using
    canonicalPhysicalSuccessor_mem n pathPrefix

/-- One prefix-coherent parent at every rank, built by adjoining the chosen
physical successor to the preceding parent. -/
def canonicalPhysicalParentSchedule :
    (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n
  | 0 => PUnit.unit
  | n + 1 =>
      (canonicalPhysicalParentSchedule n,
        canonicalPhysicalSuccessor n (canonicalPhysicalParentSchedule n))

@[simp]
theorem canonicalPhysicalParentSchedule_zero :
    canonicalPhysicalParentSchedule 0 = PUnit.unit := rfl

@[simp]
theorem canonicalPhysicalParentSchedule_succ (n : ℕ) :
    canonicalPhysicalParentSchedule (n + 1) =
      (canonicalPhysicalParentSchedule n,
        canonicalPhysicalSuccessor n (canonicalPhysicalParentSchedule n)) :=
  rfl

/-- The schedule at rank `n` is definitionally the prefix of its rank
`n + 1` continuation. -/
theorem canonicalPhysicalParentSchedule_prefix (n : ℕ) :
    (canonicalPhysicalParentSchedule (n + 1)).1 =
      canonicalPhysicalParentSchedule n := by
  rfl

/-- Every selected step in the coherent schedule is a physical one-element
extension. -/
theorem canonicalPhysicalParentSchedule_step_physical (n : ℕ) :
    IsPhysicalCausalGrowthStep n (canonicalPhysicalParentSchedule n)
      (canonicalPhysicalParentSchedule (n + 1)).2 := by
  exact canonicalPhysicalSuccessor_isPhysical
    n (canonicalPhysicalParentSchedule n)

/-- Hence every finite scheduled parent is a physical causal-growth path. -/
theorem canonicalPhysicalParentSchedule_isPhysical : ∀ n : ℕ,
    IsPhysicalCausalGrowthPath n (canonicalPhysicalParentSchedule n)
  | 0 => by
      simp [IsPhysicalCausalGrowthPath]
  | n + 1 => by
      exact
        ⟨canonicalPhysicalParentSchedule_isPhysical n,
          canonicalPhysicalParentSchedule_step_physical n⟩

/-- The canonical scheduled path consequently has strictly positive Born
probability for either chirality at every finite depth. -/
theorem canonicalPhysicalParentSchedule_probability_pos
    (chirality : Fin 2) (n : ℕ) :
    0 < completeChiralFinitePathProbability chirality n
      (canonicalPhysicalParentSchedule n) := by
  exact
    (completeChiralFinitePathProbability_pos_iff_physical chirality n
      (canonicalPhysicalParentSchedule n)).2
      (canonicalPhysicalParentSchedule_isPhysical n)

#print axioms completeChiralFinitePathProbability_nonneg
#print axioms completeChiralFinitePathProbability_sum_refine
#print axioms completeChiralFinitePathProbability_sum_univ
#print axioms completeChiralFinitePathProbability_pos_iff_physical
#print axioms canonicalPhysicalParentSchedule_step_physical
#print axioms canonicalPhysicalParentSchedule_isPhysical
#print axioms canonicalPhysicalParentSchedule_probability_pos

end

end UnifiedTheory.Audit.KFCausalSetCompleteChiralBornPathLaw
