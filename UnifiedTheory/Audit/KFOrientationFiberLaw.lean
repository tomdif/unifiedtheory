/-
  Audit/KFOrientationFiberLaw.lean

  FIBER-PRODUCT LAW AND RANK-LIFT OBSTRUCTION

  Rank-one orientation transport through an ordered quotient is controlled
  exactly by products of fiber cardinalities.  On three coarse blocks this
  yields an iff theorem: scalar closure is equivalent to equal fibers.

  The law produces a certified three-step recurrence.  Its direct rank-two
  lift then fails even for uniform event fibers: determinant interlacing
  generates a long-range chamber coupling absent from the native operator.
-/

import UnifiedTheory.Audit.KFOrientationCouplingFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationFiberLaw

open UnifiedTheory.LayerB.NoBackgroundSpace
open UnifiedTheory.LayerB.KFFinitePoset
open UnifiedTheory.Audit.KFHigherRank
open UnifiedTheory.Audit.KFSpectralCoarseGraining
open UnifiedTheory.Audit.KFMultirankCoarseGraining
open UnifiedTheory.Audit.KFOrientationDefect
open UnifiedTheory.Audit.KFOrientationPathObstruction
open UnifiedTheory.Audit.KFOrientationCouplingFlow

/-! ## 1. General rank-one fiber-product law -/

/-- The canonical skew orientation matrix of a finite total order. -/
def orderedOrientation (α : Type*) [LinearOrder α] : Matrix α α ℚ :=
  fun i j => if i < j then 1 else if j < i then -1 else 0

/-- Cardinality of one block fiber. -/
def fiberCard {α β : Type*} [Fintype α] [DecidableEq β]
    (block : α → β) (a : β) : ℕ :=
  (Finset.univ.filter fun i => block i = a).card

theorem orderedOrientation_skew (α : Type*) [LinearOrder α] :
    (orderedOrientation α).transpose = -orderedOrientation α := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hji
  · simp [Matrix.transpose_apply, orderedOrientation, hij,
      not_lt_of_ge (le_of_lt hij)]
  · subst j
    simp [Matrix.transpose_apply, orderedOrientation]
  · simp [Matrix.transpose_apply, orderedOrientation, hji,
      not_lt_of_ge (le_of_lt hji)]

/-- The native rank-one determinant channel on any explicitly total finite
poset is the canonical total-order orientation matrix. -/
theorem orientationRankOne_eq_orderedOrientation_of_total
    (P : FinPoset)
    (hrel : ∀ i j, P.rel i j = decide (i ≤ j)) :
    orientationRankOne P = orderedOrientation (Fin P.n) := by
  ext i j
  rw [orientationRankOne_apply]
  simp only [orderKernel]
  rw [hrel, hrel]
  rcases lt_trichotomy i j with hij | hij | hji
  · simp [orderedOrientation, hij, le_of_lt hij, not_le_of_gt hij]
  · subst j
    simp [orderedOrientation]
  · simp [orderedOrientation, hji, le_of_lt hji, not_le_of_gt hji]

/-- A block has ordered fibers when every element of a lower image fiber
precedes every element of a higher image fiber. -/
def HasOrderedFibers {α β : Type*} [LT α] [LT β]
    (block : α → β) : Prop :=
  ∀ i j, block i < block j → i < j

/-- On every upper coarse edge, the transported rank-one orientation coupling
is exactly the product of the two fiber cardinalities. -/
theorem rankOne_fiber_product_upper
    {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]
    (block : α → β) (hOrdered : HasOrderedFibers block)
    {a b : β} (hab : a < b) :
    pushForwardMatrix (totalPartialBlock block) (orderedOrientation α) a b =
      (fiberCard block a : ℚ) * fiberCard block b := by
  classical
  simp only [pushForwardMatrix, totalPartialBlock, Option.some.injEq]
  calc
    (∑ i, ∑ j,
      if block i = a ∧ block j = b then orderedOrientation α i j else 0) =
        ∑ i, ∑ j, if block i = a ∧ block j = b then (1 : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs with h
      · rw [orderedOrientation, if_pos]
        exact hOrdered i j (by simpa [h.1, h.2] using hab)
      · rfl
    _ = (fiberCard block a : ℚ) * fiberCard block b := by
      calc
        (∑ i, ∑ j, if block i = a ∧ block j = b then (1 : ℚ) else 0) =
            (∑ i, if block i = a then (1 : ℚ) else 0) *
              ∑ j, if block j = b then (1 : ℚ) else 0 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hi : block i = a <;> by_cases hj : block j = b <;>
            simp [hi, hj]
        _ = (fiberCard block a : ℚ) * fiberCard block b := by
          simp [fiberCard]

/-- Full matrix form of the fiber-product law.  Diagonal cancellation follows
from skewness; lower entries follow from the upper formula by transposition. -/
theorem rankOne_fiber_product
    {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]
    (block : α → β) (hOrdered : HasOrderedFibers block)
    (a b : β) :
    pushForwardMatrix (totalPartialBlock block) (orderedOrientation α) a b =
      (fiberCard block a : ℚ) * fiberCard block b *
        orderedOrientation β a b := by
  classical
  rcases lt_trichotomy a b with hab | hab | hba
  · rw [rankOne_fiber_product_upper block hOrdered hab]
    simp [orderedOrientation, hab]
  · subst b
    have hSkew := pushForwardMatrix_skew
      (totalPartialBlock block) (orderedOrientation α)
      (orderedOrientation_skew α)
    have hDiag := congrFun (congrFun hSkew a) a
    change pushForwardMatrix (totalPartialBlock block)
      (orderedOrientation α) a a =
        -pushForwardMatrix (totalPartialBlock block)
          (orderedOrientation α) a a at hDiag
    simp only [orderedOrientation, lt_self_iff_false, ↓reduceIte, mul_zero]
    linarith
  · have hSkew := pushForwardMatrix_skew
      (totalPartialBlock block) (orderedOrientation α)
      (orderedOrientation_skew α)
    have hEntry := congrFun (congrFun hSkew b) a
    change pushForwardMatrix (totalPartialBlock block)
      (orderedOrientation α) a b =
        -pushForwardMatrix (totalPartialBlock block)
          (orderedOrientation α) b a at hEntry
    rw [hEntry, rankOne_fiber_product_upper block hOrdered hba]
    simp [orderedOrientation, hba, not_lt_of_ge (le_of_lt hba), mul_comm]

theorem fiberCard_pos_iff {α β : Type*} [Fintype α] [DecidableEq β]
    (block : α → β) (a : β) :
    0 < fiberCard block a ↔ ∃ i, block i = a := by
  classical
  constructor
  · intro h
    rw [fiberCard, Finset.card_pos] at h
    rcases h with ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  · rintro ⟨i, hi⟩
    rw [fiberCard, Finset.card_pos]
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩

/-! ## 2. Exact three-block scalar-closure criterion -/

/-- For a surjective ordered quotient onto three blocks, some scalar closes
the rank-one orientation ansatz if and only if all three fibers have equal
cardinality. -/
theorem finThree_scalar_closure_iff_uniform
    {α : Type*} [Fintype α] [LinearOrder α]
    (block : α → Fin 3) (hOrdered : HasOrderedFibers block)
    (hSurjective : Function.Surjective block) :
    (∃ weight : ℚ,
      weight • pushForwardMatrix (totalPartialBlock block)
        (orderedOrientation α) = orderedOrientation (Fin 3)) ↔
      fiberCard block 0 = fiberCard block 1 ∧
        fiberCard block 1 = fiberCard block 2 := by
  classical
  constructor
  · rintro ⟨weight, hClosed⟩
    have h01 := congrFun (congrFun hClosed 0) 1
    have h02 := congrFun (congrFun hClosed 0) 2
    have h12 := congrFun (congrFun hClosed 1) 2
    change weight * pushForwardMatrix (totalPartialBlock block)
      (orderedOrientation α) 0 1 = orderedOrientation (Fin 3) 0 1 at h01
    change weight * pushForwardMatrix (totalPartialBlock block)
      (orderedOrientation α) 0 2 = orderedOrientation (Fin 3) 0 2 at h02
    change weight * pushForwardMatrix (totalPartialBlock block)
      (orderedOrientation α) 1 2 = orderedOrientation (Fin 3) 1 2 at h12
    rw [rankOne_fiber_product_upper block hOrdered (by decide)] at h01
    rw [rankOne_fiber_product_upper block hOrdered (by decide)] at h02
    rw [rankOne_fiber_product_upper block hOrdered (by decide)] at h12
    change weight * ((fiberCard block 0 : ℚ) * fiberCard block 1) = 1 at h01
    change weight * ((fiberCard block 0 : ℚ) * fiberCard block 2) = 1 at h02
    change weight * ((fiberCard block 1 : ℚ) * fiberCard block 2) = 1 at h12
    have h0 : 0 < (fiberCard block 0 : ℚ) := by
      exact_mod_cast (fiberCard_pos_iff block 0).2 (hSurjective 0)
    have h1 : 0 < (fiberCard block 1 : ℚ) := by
      exact_mod_cast (fiberCard_pos_iff block 1).2 (hSurjective 1)
    have h2 : 0 < (fiberCard block 2 : ℚ) := by
      exact_mod_cast (fiberCard_pos_iff block 2).2 (hSurjective 2)
    have h01q : (fiberCard block 0 : ℚ) = fiberCard block 1 := by
      nlinarith
    have h12q : (fiberCard block 1 : ℚ) = fiberCard block 2 := by
      nlinarith
    constructor
    · exact_mod_cast h01q
    · exact_mod_cast h12q
  · rintro ⟨h01, h12⟩
    have h0 : 0 < fiberCard block 0 :=
      (fiberCard_pos_iff block 0).2 (hSurjective 0)
    have h0q : (fiberCard block 0 : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt h0)
    have h2q : (fiberCard block 2 : ℚ) ≠ 0 := by
      rw [← h12, ← h01]
      exact h0q
    refine ⟨1 / ((fiberCard block 0 : ℚ) ^ 2), ?_⟩
    ext a b
    change (1 / ((fiberCard block 0 : ℚ) ^ 2)) *
      pushForwardMatrix (totalPartialBlock block)
        (orderedOrientation α) a b = orderedOrientation (Fin 3) a b
    rw [rankOne_fiber_product block hOrdered]
    fin_cases a <;> fin_cases b <;>
      simp [orderedOrientation, Fin.ext_iff, h01, h12] <;>
      field_simp [h2q]

/-! ## 3. A certified three-step recurrence -/

def chainTwelve : FinPoset where
  n := 12
  hn := by decide
  rel := fun i j => decide (i ≤ j)
  refl := by decide
  antisymm := by decide
  trans := by decide

@[simp]
theorem chainTwelve_rel_apply (i j : Fin 12) :
    chainTwelve.rel i j = decide (i ≤ j) := rfl

def chainTwelveToSixBlock : Fin 12 → Fin 6 :=
  ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5]

def chainTwelveToSix : OrderCoarseGraining where
  fine := chainTwelve
  coarse := chainSix
  block := chainTwelveToSixBlock
  block_surjective := by decide
  relation_iff := by decide

def chainTwelveToSixPartial : Fin 12 → Option (Fin 6) :=
  totalPartialBlock chainTwelveToSixBlock

def chainSixUniformToTwoPath : Fin 6 → Option (Fin 2) :=
  composePartialBlock
    (totalPartialBlock chainSixUniformBlock)
    (totalPartialBlock chainThreeBlock12)

def chainTwelveToTwoPath : Fin 12 → Option (Fin 2) :=
  composePartialBlock chainTwelveToSixPartial chainSixUniformToTwoPath

theorem chainTwelveToSix_ordered :
    HasOrderedFibers chainTwelveToSixBlock := by
  rw [HasOrderedFibers]
  decide

theorem chainSixUniform_ordered :
    HasOrderedFibers chainSixUniformBlock := by
  rw [HasOrderedFibers]
  decide

theorem chainThreeToTwo_ordered :
    HasOrderedFibers chainThreeBlock12 := by
  rw [HasOrderedFibers]
  decide

theorem chainTwelveToSix_fiberCard (a : Fin 6) :
    fiberCard chainTwelveToSixBlock a = 2 := by
  fin_cases a <;> decide

theorem chainSixUniform_fiberCard (a : Fin 3) :
    fiberCard chainSixUniformBlock a = 2 := by
  fin_cases a <;> decide

theorem chainThreeToTwo_fiberCard_zero :
    fiberCard chainThreeBlock12 0 = 1 := by
  decide

theorem chainThreeToTwo_fiberCard_one :
    fiberCard chainThreeBlock12 1 = 2 := by
  decide

theorem chainTwelveToSix_pushforward :
    pushForwardMatrix chainTwelveToSixPartial (orderedOrientation (Fin 12)) =
      (4 : ℚ) • orderedOrientation (Fin 6) := by
  ext a b
  rw [chainTwelveToSixPartial,
    rankOne_fiber_product chainTwelveToSixBlock chainTwelveToSix_ordered,
    chainTwelveToSix_fiberCard, chainTwelveToSix_fiberCard]
  change (2 : ℚ) * 2 * orderedOrientation (Fin 6) a b =
    4 * orderedOrientation (Fin 6) a b
  ring

theorem chainSixUniform_ordered_pushforward :
    pushForwardMatrix (totalPartialBlock chainSixUniformBlock)
      (orderedOrientation (Fin 6)) =
        (4 : ℚ) • orderedOrientation (Fin 3) := by
  ext a b
  rw [rankOne_fiber_product chainSixUniformBlock chainSixUniform_ordered,
    chainSixUniform_fiberCard, chainSixUniform_fiberCard]
  change (2 : ℚ) * 2 * orderedOrientation (Fin 3) a b =
    4 * orderedOrientation (Fin 3) a b
  ring

theorem chainThreeToTwo_ordered_pushforward :
    pushForwardMatrix (totalPartialBlock chainThreeBlock12)
      (orderedOrientation (Fin 3)) =
        (2 : ℚ) • orderedOrientation (Fin 2) := by
  ext a b
  rw [rankOne_fiber_product chainThreeBlock12 chainThreeToTwo_ordered]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one] <;>
    simp only [chainThreeToTwo_fiberCard_zero,
      chainThreeToTwo_fiberCard_one] <;>
    norm_num [orderedOrientation, Fin.ext_iff]

theorem chainSixUniformToTwo_ordered_pushforward :
    pushForwardMatrix chainSixUniformToTwoPath
      (orderedOrientation (Fin 6)) =
        (8 : ℚ) • orderedOrientation (Fin 2) := by
  rw [chainSixUniformToTwoPath, pushForwardMatrix_compose,
    chainSixUniform_ordered_pushforward, pushForwardMatrix_smul,
    chainThreeToTwo_ordered_pushforward]
  module

/-- Three quotient arrows multiply their coupling factors exactly:
`4 * 4 * 2 = 32`. -/
theorem chainTwelve_three_step_pushforward :
    pushForwardMatrix chainTwelveToTwoPath (orderedOrientation (Fin 12)) =
      (32 : ℚ) • orderedOrientation (Fin 2) := by
  rw [chainTwelveToTwoPath, pushForwardMatrix_compose,
    chainTwelveToSix_pushforward, pushForwardMatrix_smul,
    chainSixUniformToTwo_ordered_pushforward]
  module

theorem chainTwelve_three_step_closed :
    orientationDefect chainTwelveToTwoPath (1 / 32 : ℚ)
      (orderedOrientation (Fin 12)) (orderedOrientation (Fin 2)) = 0 := by
  apply (orientationDefect_eq_zero_iff_closed _ _ _ _).2
  rw [chainTwelve_three_step_pushforward]
  module

theorem chainTwelve_orientationRankOne_eq_ordered :
    orientationRankOne chainTwelve = orderedOrientation (Fin 12) :=
  orientationRankOne_eq_orderedOrientation_of_total chainTwelve
    (fun _ _ => rfl)

theorem chainSix_orientationRankOne_eq_ordered :
    orientationRankOne chainSix = orderedOrientation (Fin 6) :=
  orientationRankOne_eq_orderedOrientation_of_total chainSix
    (fun _ _ => rfl)

theorem chainTwo_orientationRankOne_eq_ordered :
    orientationRankOne chainTwo = orderedOrientation (Fin 2) :=
  orientationRankOne_eq_orderedOrientation_of_total chainTwo
    (fun _ _ => rfl)

theorem chainTwelve_three_step_native_pushforward :
    pushForwardMatrix chainTwelveToTwoPath (orientationRankOne chainTwelve) =
      (32 : ℚ) • orientationRankOne chainTwo := by
  rw [chainTwelve_orientationRankOne_eq_ordered,
    chainTwo_orientationRankOne_eq_ordered]
  exact chainTwelve_three_step_pushforward

theorem chainTwelve_three_step_native_closed :
    orientationDefect chainTwelveToTwoPath (1 / 32 : ℚ)
      (orientationRankOne chainTwelve) (orientationRankOne chainTwo) = 0 := by
  rw [chainTwelve_orientationRankOne_eq_ordered,
    chainTwo_orientationRankOne_eq_ordered]
  exact chainTwelve_three_step_closed

/-! ## 4. Uniform event fibers fail after lifting to rank two -/

/-- The fifteen increasing event pairs on the six-chain. -/
def rankTwoPointSix : Fin 15 → Fin 2 → Fin 6 :=
  ![![0, 1], ![0, 2], ![0, 3], ![0, 4], ![0, 5],
    ![1, 2], ![1, 3], ![1, 4], ![1, 5], ![2, 3],
    ![2, 4], ![2, 5], ![3, 4], ![3, 5], ![4, 5]]

theorem rankTwoPointSix_strict (k : Fin 15) :
    StrictMono (rankTwoPointSix k) := by
  fin_cases k <;> decide

def rankTwoChamberSix (k : Fin 15) : Chamber chainSix 2 :=
  ⟨rankTwoPointSix k, rankTwoPointSix_strict k⟩

def chainSixOrientationOperatorRankTwo : Matrix (Fin 15) (Fin 15) ℚ :=
  fun i j => kFOrientationAtRank chainSix 2
    (rankTwoChamberSix i) (rankTwoChamberSix j)

def chainSixOrientationRankTwo : Matrix (Fin 15) (Fin 15) ℚ :=
  !![ 0,  1,  1,  1,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
     -1,  0,  1,  1,  1,  1,  1,  1,  1,  0,  0,  0,  0,  0,  0;
     -1, -1,  0,  1,  1,  0,  1,  1,  1,  1,  1,  1,  0,  0,  0;
     -1, -1, -1,  0,  1,  0,  0,  1,  1,  0,  1,  1,  1,  1,  0;
     -1, -1, -1, -1,  0,  0,  0,  0,  1,  0,  0,  1,  0,  1,  1;
      0, -1,  0,  0,  0,  0,  1,  1,  1,  0,  0,  0,  0,  0,  0;
      0, -1, -1,  0,  0, -1,  0,  1,  1,  1,  1,  1,  0,  0,  0;
      0, -1, -1, -1,  0, -1, -1,  0,  1,  0,  1,  1,  1,  1,  0;
      0, -1, -1, -1, -1, -1, -1, -1,  0,  0,  0,  1,  0,  1,  1;
      0,  0, -1,  0,  0,  0, -1,  0,  0,  0,  1,  1,  0,  0,  0;
      0,  0, -1, -1,  0,  0, -1, -1,  0, -1,  0,  1,  1,  1,  0;
      0,  0, -1, -1, -1,  0, -1, -1, -1, -1, -1,  0,  0,  1,  1;
      0,  0,  0, -1,  0,  0,  0, -1,  0,  0, -1,  0,  0,  1,  0;
      0,  0,  0, -1, -1,  0,  0, -1, -1,  0, -1, -1, -1,  0,  1;
      0,  0,  0,  0, -1,  0,  0,  0, -1,  0,  0, -1,  0, -1,  0]

set_option maxHeartbeats 2000000 in
-- The explicit 15-by-15 determinant normalization has 225 finite cases.
set_option maxRecDepth 10000 in
theorem chainSix_rankTwo_orientation_matrix :
    chainSixOrientationOperatorRankTwo = chainSixOrientationRankTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chainSixOrientationOperatorRankTwo,
      chainSixOrientationRankTwo,
      rankTwoChamberSix, rankTwoPointSix,
      kFOrientationAtRank_two_apply, orderKernel,
      chainSix_rel_apply, Matrix.det_fin_two, Fin.ext_iff]

/-- Rank-two chambers wholly inside one event fiber collapse.  Every surviving
coarse chamber has four fine preimages. -/
def chainSixUniformRankTwoBlock : Fin 15 → Option (Fin 3) :=
  ![none, some 0, some 0, some 1, some 1,
    some 0, some 0, some 1, some 1, none,
    some 2, some 2, some 2, some 2, none]

/-- The generated long-range coupling between coarse chambers `01` and `12`. -/
def chainSixUniformRankTwoGenerated : Matrix (Fin 3) (Fin 3) ℚ :=
  !![ 0, 0,  4;
      0, 0,  0;
     -4, 0,  0]

theorem chainSixUniformRankTwoGenerated_nonzero :
    chainSixUniformRankTwoGenerated ≠ 0 := by
  intro h
  have h02 := congrFun (congrFun h 0) 2
  change (4 : ℚ) = 0 at h02
  norm_num at h02

set_option maxHeartbeats 2000000 in
-- The exact 15-to-3 fiber sum expands 2,025 finite summands.
set_option maxRecDepth 10000 in
theorem chainSixUniform_rankTwo_pushforward :
    pushForwardMatrix chainSixUniformRankTwoBlock
      chainSixOrientationOperatorRankTwo =
        (12 : ℚ) • chainThreeOrientationRankTwo +
          chainSixUniformRankTwoGenerated := by
  rw [chainSix_rankTwo_orientation_matrix]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp_rw [pushForwardMatrix, Finset.sum_fin_eq_sum_range]
  all_goals
    norm_num [chainSixUniformRankTwoBlock,
      chainSixOrientationRankTwo,
      chainThreeOrientationRankTwo,
      chainSixUniformRankTwoGenerated,
      Finset.sum_range_succ, Fin.ext_iff]
    simp
    norm_num

theorem chainSixUniform_rankTwo_normalized :
    (1 / 12 : ℚ) •
      pushForwardMatrix chainSixUniformRankTwoBlock
        chainSixOrientationOperatorRankTwo =
      chainThreeOrientationRankTwo +
        (1 / 12 : ℚ) • chainSixUniformRankTwoGenerated := by
  rw [chainSixUniform_rankTwo_pushforward]
  module

/-- Equal event fibers are sufficient for rank-one scalar closure but not for
the rank-two determinant orientation channel. -/
theorem chainSixUniform_rankTwo_no_scalar_closure :
    ¬ ∃ weight : ℚ,
      weight • pushForwardMatrix chainSixUniformRankTwoBlock
        chainSixOrientationOperatorRankTwo = chainThreeOrientationRankTwo := by
  rw [chainSixUniform_rankTwo_pushforward]
  rintro ⟨weight, h⟩
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  norm_num [chainThreeOrientationRankTwo,
    chainSixUniformRankTwoGenerated] at h01 h02
  change weight * 4 = 0 at h02
  linarith

/-! ## 5. Master rank-split theorem -/

theorem fiber_law_three_step_and_rank_lift_obstruction :
    pushForwardMatrix chainTwelveToTwoPath (orientationRankOne chainTwelve) =
      (32 : ℚ) • orientationRankOne chainTwo
    ∧ orientationDefect chainTwelveToTwoPath (1 / 32 : ℚ)
      (orientationRankOne chainTwelve) (orientationRankOne chainTwo) = 0
    ∧ pushForwardMatrix chainSixUniformRankTwoBlock
      chainSixOrientationOperatorRankTwo =
        (12 : ℚ) • chainThreeOrientationRankTwo +
          chainSixUniformRankTwoGenerated
    ∧ ¬ ∃ weight : ℚ,
      weight • pushForwardMatrix chainSixUniformRankTwoBlock
        chainSixOrientationOperatorRankTwo = chainThreeOrientationRankTwo := by
  exact ⟨chainTwelve_three_step_native_pushforward,
    chainTwelve_three_step_native_closed,
    chainSixUniform_rankTwo_pushforward,
    chainSixUniform_rankTwo_no_scalar_closure⟩

/-! ## Trust regression -/

#print axioms rankOne_fiber_product
#print axioms finThree_scalar_closure_iff_uniform
#print axioms chainTwelve_three_step_native_pushforward
#print axioms chainTwelve_three_step_native_closed
#print axioms chainSix_rankTwo_orientation_matrix
#print axioms chainSixUniform_rankTwo_pushforward
#print axioms chainSixUniform_rankTwo_no_scalar_closure
#print axioms fiber_law_three_step_and_rank_lift_obstruction

end UnifiedTheory.Audit.KFOrientationFiberLaw
