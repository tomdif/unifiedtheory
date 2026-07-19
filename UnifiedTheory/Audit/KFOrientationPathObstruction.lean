/-
  Audit/KFOrientationPathObstruction.lean

  TWO-PATH ORIENTATION COUNTERTERM OBSTRUCTION

  A single nonzero coarse-graining defect is removable by redefining its
  endpoint operator.  This file therefore compares two certified quotient
  paths with a fixed microscopic orientation operator and one shared infrared
  counterterm.  Their accumulated defects disagree exactly, so no common
  endpoint correction closes both paths.

  The file also records the necessary scope correction: if arbitrary
  counterterms are allowed at every object, choosing the negative native
  operator trivializes the entire sector.  The obstruction is meaningful only
  after a microscopic normalization condition is fixed.
-/

import UnifiedTheory.Audit.KFOrientationDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationPathObstruction

open UnifiedTheory.LayerB.NoBackgroundSpace
open UnifiedTheory.LayerB.KFFinitePoset
open UnifiedTheory.Audit.OrderSensitiveObservables
open UnifiedTheory.Audit.KFSpectralCoarseGraining
open UnifiedTheory.Audit.KFMultirankCoarseGraining
open UnifiedTheory.Audit.KFOrientationDefect

/-! ## 1. Two certified quotient paths -/

/-- Two totally ordered events, used as the shared infrared endpoint. -/
def chainTwo : FinPoset where
  n := 2
  hn := by decide
  rel := fun i j => decide (i.val ≤ j.val)
  refl := by decide
  antisymm := by decide
  trans := by decide

@[simp]
theorem chainTwo_rel_apply (i j : Fin 2) :
    chainTwo.rel i j = decide (i.val ≤ j.val) := rfl

/-- First path: retain event zero and merge the last two events at the
four-to-three step. -/
def chainFourBlock13 : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- Second path: merge the first two events at the four-to-three step. -/
def chainFourBlock22 : Fin 4 → Fin 3 := ![0, 0, 1, 2]

/-- Shared three-to-two step: retain the first event and merge the upper two. -/
def chainThreeBlock12 : Fin 3 → Fin 2 := ![0, 1, 1]

def chainFourToChainThree13 : OrderCoarseGraining where
  fine := chainFour
  coarse := chainThree
  block := chainFourBlock13
  block_surjective := by decide
  relation_iff := by decide

def chainFourToChainThree22 : OrderCoarseGraining where
  fine := chainFour
  coarse := chainThree
  block := chainFourBlock22
  block_surjective := by decide
  relation_iff := by decide

def chainThreeToChainTwo : OrderCoarseGraining where
  fine := chainThree
  coarse := chainTwo
  block := chainThreeBlock12
  block_surjective := by decide
  relation_iff := by decide

/-- Promote a total event quotient to the partial-map API used by chamber
fiber transport. -/
def totalPartialBlock {m n : Type*} (block : m → n) : m → Option n :=
  fun i => some (block i)

/-- Composite path with endpoint fiber sizes `(1,3)`. -/
def chainFourPath13 : Fin 4 → Option (Fin 2) :=
  composePartialBlock (totalPartialBlock chainFourBlock13)
    (totalPartialBlock chainThreeBlock12)

/-- Composite path with endpoint fiber sizes `(2,2)`. -/
def chainFourPath22 : Fin 4 → Option (Fin 2) :=
  composePartialBlock (totalPartialBlock chainFourBlock22)
    (totalPartialBlock chainThreeBlock12)

theorem chainFourPath13_apply :
    chainFourPath13 = ![some 0, some 1, some 1, some 1] := by
  funext i
  fin_cases i <;> rfl

theorem chainFourPath22_apply :
    chainFourPath22 = ![some 0, some 0, some 1, some 1] := by
  funext i
  fin_cases i <;> rfl

theorem chainFour_paths_distinct : chainFourPath13 ≠ chainFourPath22 := by
  intro h
  have h1 := congrFun h 1
  norm_num [chainFourPath13, chainFourPath22, composePartialBlock,
    totalPartialBlock, chainFourBlock13, chainFourBlock22,
    chainThreeBlock12] at h1

/-! ## 2. Rank-one orientation operators -/

/-- Event-indexed form of the generic rank-one orientation channel. -/
def orientationRankOne (P : FinPoset) :
    Matrix (Fin P.n) (Fin P.n) ℚ :=
  fun i j => kFOrientationAtRank P 1
    (singletonChamber P i) (singletonChamber P j)

theorem orientationRankOne_apply (P : FinPoset) (i j : Fin P.n) :
    orientationRankOne P i j =
      orderKernel P i j - orderKernel P j i := by
  simp [orientationRankOne, kFOrientationAtRank, zetaBlock,
    singletonChamber]

def chainFourOrientationRankOne : Matrix (Fin 4) (Fin 4) ℚ :=
  !![ 0,  1,  1,  1;
     -1,  0,  1,  1;
     -1, -1,  0,  1;
     -1, -1, -1,  0]

def chainTwoOrientationRankOne : Matrix (Fin 2) (Fin 2) ℚ :=
  !![ 0, 1;
     -1, 0]

theorem chainFour_orientationRankOne_matrix :
    orientationRankOne chainFour = chainFourOrientationRankOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orientationRankOne_apply, orderKernel,
      chainFour_rel_apply, chainFourOrientationRankOne, Fin.ext_iff]

theorem chainTwo_orientationRankOne_matrix :
    orientationRankOne chainTwo = chainTwoOrientationRankOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orientationRankOne_apply, orderKernel,
      chainTwo_rel_apply, chainTwoOrientationRankOne, Fin.ext_iff]

/-! ## 3. Exact accumulated path defects -/

theorem chainFourPath13_pushforward :
    pushForwardMatrix chainFourPath13 chainFourOrientationRankOne =
      (3 : ℚ) • chainTwoOrientationRankOne := by
  rw [chainFourPath13_apply]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp_rw [pushForwardMatrix, Finset.sum_fin_eq_sum_range]
  all_goals
    norm_num [chainFourOrientationRankOne,
      chainTwoOrientationRankOne, Finset.sum_range_succ, Fin.ext_iff]

theorem chainFourPath22_pushforward :
    pushForwardMatrix chainFourPath22 chainFourOrientationRankOne =
      (4 : ℚ) • chainTwoOrientationRankOne := by
  rw [chainFourPath22_apply]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp_rw [pushForwardMatrix, Finset.sum_fin_eq_sum_range]
  all_goals
    norm_num [chainFourOrientationRankOne,
      chainTwoOrientationRankOne, Finset.sum_range_succ, Fin.ext_iff]

def chainFourPath13Defect : Matrix (Fin 2) (Fin 2) ℚ :=
  orientationDefect chainFourPath13 1
    (orientationRankOne chainFour) (orientationRankOne chainTwo)

def chainFourPath22Defect : Matrix (Fin 2) (Fin 2) ℚ :=
  orientationDefect chainFourPath22 1
    (orientationRankOne chainFour) (orientationRankOne chainTwo)

theorem chainFourPath13_defect_exact :
    chainFourPath13Defect = (2 : ℚ) • chainTwoOrientationRankOne := by
  rw [chainFourPath13Defect, orientationDefect_eq_pushForwardMatrix,
    chainFour_orientationRankOne_matrix,
    chainTwo_orientationRankOne_matrix,
    chainFourPath13_pushforward]
  module

theorem chainFourPath22_defect_exact :
    chainFourPath22Defect = (3 : ℚ) • chainTwoOrientationRankOne := by
  rw [chainFourPath22Defect, orientationDefect_eq_pushForwardMatrix,
    chainFour_orientationRankOne_matrix,
    chainTwo_orientationRankOne_matrix,
    chainFourPath22_pushforward]
  module

theorem chainFourPath13_defect_at_weight (weight : ℚ) :
    orientationDefect chainFourPath13 weight
      (orientationRankOne chainFour) (orientationRankOne chainTwo) =
        (3 * weight - 1) • chainTwoOrientationRankOne := by
  rw [orientationDefect_eq_pushForwardMatrix,
    chainFour_orientationRankOne_matrix,
    chainTwo_orientationRankOne_matrix,
    chainFourPath13_pushforward]
  module

theorem chainFourPath22_defect_at_weight (weight : ℚ) :
    orientationDefect chainFourPath22 weight
      (orientationRankOne chainFour) (orientationRankOne chainTwo) =
        (4 * weight - 1) • chainTwoOrientationRankOne := by
  rw [orientationDefect_eq_pushForwardMatrix,
    chainFour_orientationRankOne_matrix,
    chainTwo_orientationRankOne_matrix,
    chainFourPath22_pushforward]
  module

theorem chainFour_path_defects_ne_of_weight_ne_zero
    (weight : ℚ) (hWeight : weight ≠ 0) :
    orientationDefect chainFourPath13 weight
      (orientationRankOne chainFour) (orientationRankOne chainTwo) ≠
    orientationDefect chainFourPath22 weight
      (orientationRankOne chainFour) (orientationRankOne chainTwo) := by
  rw [chainFourPath13_defect_at_weight,
    chainFourPath22_defect_at_weight]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [chainTwoOrientationRankOne] at h01
  apply hWeight
  linarith

theorem chainFour_path_defects_ne :
    chainFourPath13Defect ≠ chainFourPath22Defect := by
  exact chainFour_path_defects_ne_of_weight_ne_zero 1 (by norm_num)

/-! ## 4. Counterterm scope and the two-path obstruction -/

/-- Without a normalization condition, arbitrary endpoint counterterms make
every defect trivial by erasing both native operators. -/
theorem unrestricted_counterterms_trivialize
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ) :
    orientationDefect block weight (fine + -fine) (coarse + -coarse) = 0 := by
  simp [orientationDefect, incidencePushForward]

/-- Add one shared infrared counterterm while keeping the microscopic
operator fixed. -/
def infraredCorrectedDefect {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse counterterm : Matrix n n ℚ) :
    Matrix n n ℚ :=
  orientationDefect block weight fine (coarse + counterterm)

theorem infraredCorrectedDefect_eq
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse counterterm : Matrix n n ℚ) :
    infraredCorrectedDefect block weight fine coarse counterterm =
      orientationDefect block weight fine coarse - counterterm := by
  simp [infraredCorrectedDefect, orientationDefect]
  module

theorem no_common_ir_counterterm_of_defects_ne
    {m n : Type*} [Fintype m] [DecidableEq n]
    (left right : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ)
    (hne : orientationDefect left weight fine coarse ≠
      orientationDefect right weight fine coarse) :
    ¬ ∃ counterterm : Matrix n n ℚ,
      infraredCorrectedDefect left weight fine coarse counterterm = 0 ∧
      infraredCorrectedDefect right weight fine coarse counterterm = 0 := by
  rintro ⟨counterterm, hLeft, hRight⟩
  rw [infraredCorrectedDefect_eq, sub_eq_zero] at hLeft hRight
  exact hne (hLeft.trans hRight.symm)

/-- With the ultraviolet orientation operator fixed, the `(1,3)` and `(2,2)`
quotient paths cannot both be closed by one operator assigned to their common
two-chain endpoint. -/
theorem chainFour_two_path_no_common_ir_counterterm :
    ¬ ∃ counterterm : Matrix (Fin 2) (Fin 2) ℚ,
      infraredCorrectedDefect chainFourPath13 1
        (orientationRankOne chainFour) (orientationRankOne chainTwo)
        counterterm = 0 ∧
      infraredCorrectedDefect chainFourPath22 1
        (orientationRankOne chainFour) (orientationRankOne chainTwo)
        counterterm = 0 :=
  no_common_ir_counterterm_of_defects_ne _ _ _ _ _
    chainFour_path_defects_ne

theorem chainFour_two_path_no_common_ir_counterterm_of_weight_ne_zero
    (weight : ℚ) (hWeight : weight ≠ 0) :
    ¬ ∃ counterterm : Matrix (Fin 2) (Fin 2) ℚ,
      infraredCorrectedDefect chainFourPath13 weight
        (orientationRankOne chainFour) (orientationRankOne chainTwo)
        counterterm = 0 ∧
      infraredCorrectedDefect chainFourPath22 weight
        (orientationRankOne chainFour) (orientationRankOne chainTwo)
        counterterm = 0 :=
  no_common_ir_counterterm_of_defects_ne _ _ _ _ _
    (chainFour_path_defects_ne_of_weight_ne_zero weight hWeight)

/-! ## 5. Cocycle expansions along the certified paths -/

theorem chainFourPath13_cocycle :
    chainFourPath13Defect =
      incidencePushForward (totalPartialBlock chainThreeBlock12)
        (orientationDefect (totalPartialBlock chainFourBlock13) 1
          (orientationRankOne chainFour) (orientationRankOne chainThree)) +
      orientationDefect (totalPartialBlock chainThreeBlock12) 1
        (orientationRankOne chainThree) (orientationRankOne chainTwo) := by
  simpa [chainFourPath13Defect, chainFourPath13] using
    orientationDefect_compose
      (totalPartialBlock chainFourBlock13)
      (totalPartialBlock chainThreeBlock12) 1 1
      (orientationRankOne chainFour) (orientationRankOne chainThree)
      (orientationRankOne chainTwo)

theorem chainFourPath22_cocycle :
    chainFourPath22Defect =
      incidencePushForward (totalPartialBlock chainThreeBlock12)
        (orientationDefect (totalPartialBlock chainFourBlock22) 1
          (orientationRankOne chainFour) (orientationRankOne chainThree)) +
      orientationDefect (totalPartialBlock chainThreeBlock12) 1
        (orientationRankOne chainThree) (orientationRankOne chainTwo) := by
  simpa [chainFourPath22Defect, chainFourPath22] using
    orientationDefect_compose
      (totalPartialBlock chainFourBlock22)
      (totalPartialBlock chainThreeBlock12) 1 1
      (orientationRankOne chainFour) (orientationRankOne chainThree)
      (orientationRankOne chainTwo)

/-! ## 6. Master finite obstruction -/

theorem fixed_uv_two_path_orientation_obstruction :
    chainFourPath13 ≠ chainFourPath22
    ∧ pushForwardMatrix chainFourPath13 chainFourOrientationRankOne =
      (3 : ℚ) • chainTwoOrientationRankOne
    ∧ pushForwardMatrix chainFourPath22 chainFourOrientationRankOne =
      (4 : ℚ) • chainTwoOrientationRankOne
    ∧ ∀ weight : ℚ, weight ≠ 0 →
      ¬ ∃ counterterm : Matrix (Fin 2) (Fin 2) ℚ,
        infraredCorrectedDefect chainFourPath13 weight
          (orientationRankOne chainFour) (orientationRankOne chainTwo)
          counterterm = 0 ∧
        infraredCorrectedDefect chainFourPath22 weight
          (orientationRankOne chainFour) (orientationRankOne chainTwo)
          counterterm = 0 := by
  exact ⟨chainFour_paths_distinct,
    chainFourPath13_pushforward,
    chainFourPath22_pushforward,
    chainFour_two_path_no_common_ir_counterterm_of_weight_ne_zero⟩

/-! ## Trust regression -/

#print axioms chainFourPath13_pushforward
#print axioms chainFourPath22_pushforward
#print axioms chainFour_path_defects_ne
#print axioms chainFour_path_defects_ne_of_weight_ne_zero
#print axioms unrestricted_counterterms_trivialize
#print axioms chainFour_two_path_no_common_ir_counterterm
#print axioms chainFour_two_path_no_common_ir_counterterm_of_weight_ne_zero
#print axioms chainFourPath13_cocycle
#print axioms fixed_uv_two_path_orientation_obstruction

end UnifiedTheory.Audit.KFOrientationPathObstruction
