/-
  Audit/KFOrientationDefect.lean

  GENERIC ORIENTATION COARSE-GRAINING DEFECT

  This file abstracts the nonzero residual found in the exact diamond quotient.
  It treats a partial chamber block map as an incidence matrix, defines the
  normalized failure of pushforward to agree with recomputation, and proves
  the structural laws needed to iterate the enlarged orientation sector.
-/

import UnifiedTheory.Audit.KFMultirankCoarseGraining

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationDefect

open UnifiedTheory.Audit.KFMultirankCoarseGraining

/-! ## 1. Partial block maps as incidence matrices -/

/-- Incidence matrix of a partial fine-to-coarse block map.  A collapsed fine
index contributes a zero column. -/
def blockIncidence {m n : Type*} [DecidableEq n]
    (block : m → Option n) : Matrix n m ℚ :=
  fun a i => if block i = some a then 1 else 0

/-- Matrix form of fiber summation. -/
def incidencePushForward {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (M : Matrix m m ℚ) : Matrix n n ℚ :=
  blockIncidence block * M * (blockIncidence block).transpose

theorem incidencePushForward_eq_pushForwardMatrix
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (M : Matrix m m ℚ) :
    incidencePushForward block M = pushForwardMatrix block M := by
  ext a b
  simp only [incidencePushForward, Matrix.mul_apply, blockIncidence,
    Matrix.transpose_apply, pushForwardMatrix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : block i = some a <;>
    by_cases hj : block j = some b <;>
      simp [hi, hj]

/-! ## 2. Functoriality of partial block maps -/

/-- Composition of partial block maps.  A fine index remains collapsed once
any stage maps it to `none`. -/
def composePartialBlock {m n p : Type*}
    (fineToMiddle : m → Option n) (middleToCoarse : n → Option p) :
    m → Option p :=
  fun i => (fineToMiddle i).bind middleToCoarse

theorem blockIncidence_compose
    {m n p : Type*} [Fintype n] [DecidableEq n] [DecidableEq p]
    (fineToMiddle : m → Option n) (middleToCoarse : n → Option p) :
    blockIncidence (composePartialBlock fineToMiddle middleToCoarse) =
      blockIncidence middleToCoarse * blockIncidence fineToMiddle := by
  ext a i
  cases hfi : fineToMiddle i with
  | none =>
      simp [blockIncidence, composePartialBlock, Matrix.mul_apply, hfi]
  | some x =>
      simp [blockIncidence, composePartialBlock, Matrix.mul_apply, hfi]

theorem incidencePushForward_compose
    {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p]
    (fineToMiddle : m → Option n) (middleToCoarse : n → Option p)
    (M : Matrix m m ℚ) :
    incidencePushForward
        (composePartialBlock fineToMiddle middleToCoarse) M =
      incidencePushForward middleToCoarse
        (incidencePushForward fineToMiddle M) := by
  simp only [incidencePushForward,
    blockIncidence_compose fineToMiddle middleToCoarse,
    Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem pushForwardMatrix_compose
    {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p]
    (fineToMiddle : m → Option n) (middleToCoarse : n → Option p)
    (M : Matrix m m ℚ) :
    pushForwardMatrix
        (composePartialBlock fineToMiddle middleToCoarse) M =
      pushForwardMatrix middleToCoarse
        (pushForwardMatrix fineToMiddle M) := by
  rw [← incidencePushForward_eq_pushForwardMatrix,
    incidencePushForward_compose,
    incidencePushForward_eq_pushForwardMatrix,
    incidencePushForward_eq_pushForwardMatrix]

theorem incidencePushForward_sub
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (M N : Matrix m m ℚ) :
    incidencePushForward block (M - N) =
      incidencePushForward block M - incidencePushForward block N := by
  simp [incidencePushForward, Matrix.mul_sub, Matrix.sub_mul]

theorem incidencePushForward_add
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (M N : Matrix m m ℚ) :
    incidencePushForward block (M + N) =
      incidencePushForward block M + incidencePushForward block N := by
  simp [incidencePushForward, Matrix.mul_add, Matrix.add_mul]

theorem incidencePushForward_smul
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ) (M : Matrix m m ℚ) :
    incidencePushForward block (weight • M) =
      weight • incidencePushForward block M := by
  simp [incidencePushForward, Matrix.mul_smul, Matrix.smul_mul]

theorem pushForwardMatrix_smul
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ) (M : Matrix m m ℚ) :
    pushForwardMatrix block (weight • M) =
      weight • pushForwardMatrix block M := by
  rw [← incidencePushForward_eq_pushForwardMatrix,
    incidencePushForward_smul,
    incidencePushForward_eq_pushForwardMatrix]

/-! ## 3. Relabeling covariance -/

/-- Transport a partial block map through changes of fine and coarse index
coordinates. -/
def relabelPartialBlock {m m' n n' : Type*}
    (fineEquiv : m ≃ m') (coarseEquiv : n ≃ n')
    (block : m → Option n) : m' → Option n' :=
  fun i => (block (fineEquiv.symm i)).map coarseEquiv

theorem blockIncidence_relabel
    {m m' n n' : Type*} [DecidableEq n] [DecidableEq n']
    (fineEquiv : m ≃ m') (coarseEquiv : n ≃ n')
    (block : m → Option n) :
    blockIncidence (relabelPartialBlock fineEquiv coarseEquiv block) =
      Matrix.reindex coarseEquiv fineEquiv (blockIncidence block) := by
  ext a i
  have hiff :
      (block (fineEquiv.symm i)).map coarseEquiv = some a ↔
        block (fineEquiv.symm i) = some (coarseEquiv.symm a) := by
    rw [Option.map_eq_some_iff]
    constructor
    · rintro ⟨x, hx, hxa⟩
      have heq : x = coarseEquiv.symm a := by
        apply coarseEquiv.injective
        simpa using hxa
      simpa [heq] using hx
    · intro h
      exact ⟨coarseEquiv.symm a, h, coarseEquiv.apply_symm_apply a⟩
  simp only [blockIncidence, relabelPartialBlock, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  by_cases h : (block (fineEquiv.symm i)).map coarseEquiv = some a
  · simp [hiff.mp h]
  · have hn : block (fineEquiv.symm i) ≠ some (coarseEquiv.symm a) :=
      fun heq => h (hiff.mpr heq)
    simp [h, hn]

theorem incidencePushForward_relabel
    {m m' n n' : Type*} [Fintype m] [Fintype m']
    [DecidableEq n] [DecidableEq n']
    (fineEquiv : m ≃ m') (coarseEquiv : n ≃ n')
    (block : m → Option n) (M : Matrix m m ℚ) :
    incidencePushForward
        (relabelPartialBlock fineEquiv coarseEquiv block)
        (Matrix.reindex fineEquiv fineEquiv M) =
      Matrix.reindex coarseEquiv coarseEquiv
        (incidencePushForward block M) := by
  simp only [incidencePushForward,
    blockIncidence_relabel fineEquiv coarseEquiv block,
    Matrix.transpose_reindex]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

/-! ## 4. The normalized orientation defect -/

/-- Failure of normalized fiber transport to agree with the orientation
operator independently recomputed on the coarse carrier. -/
def orientationDefect {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ) : Matrix n n ℚ :=
  weight • incidencePushForward block fine - coarse

/-- Change in the defect caused purely by redefining the fine and coarse
endpoint operators. -/
def orientationCoboundary {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fineCounterterm : Matrix m m ℚ)
    (coarseCounterterm : Matrix n n ℚ) : Matrix n n ℚ :=
  weight • incidencePushForward block fineCounterterm - coarseCounterterm

/-- Endpoint operator redefinitions shift the orientation defect by the
corresponding coboundary. -/
theorem orientationDefect_add_counterterms
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ)
    (fineCounterterm : Matrix m m ℚ)
    (coarseCounterterm : Matrix n n ℚ) :
    orientationDefect block weight
        (fine + fineCounterterm) (coarse + coarseCounterterm) =
      orientationDefect block weight fine coarse +
        orientationCoboundary block weight
          fineCounterterm coarseCounterterm := by
  rw [orientationDefect, orientationDefect, orientationCoboundary,
    incidencePushForward_add]
  module

theorem orientationDefect_eq_pushForwardMatrix
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ) :
    orientationDefect block weight fine coarse =
      weight • pushForwardMatrix block fine - coarse := by
  rw [orientationDefect, incidencePushForward_eq_pushForwardMatrix]

/-- The defect vanishes exactly when the chosen operator ansatz is closed
under the normalized blocking step. -/
theorem orientationDefect_eq_zero_iff_closed
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ) :
    orientationDefect block weight fine coarse = 0 ↔
      weight • pushForwardMatrix block fine = coarse := by
  rw [orientationDefect_eq_pushForwardMatrix]
  exact sub_eq_zero

theorem incidencePushForward_transpose
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (M : Matrix m m ℚ) :
    (incidencePushForward block M).transpose =
      incidencePushForward block M.transpose := by
  simp [incidencePushForward, Matrix.transpose_mul, Matrix.mul_assoc]

theorem incidencePushForward_skew
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (M : Matrix m m ℚ)
    (hM : M.transpose = -M) :
    (incidencePushForward block M).transpose =
      -incidencePushForward block M := by
  rw [incidencePushForward_transpose, hM]
  simp [incidencePushForward]

/-- Fiber pushforward preserves antisymmetry. -/
theorem pushForwardMatrix_skew
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (M : Matrix m m ℚ)
    (hM : M.transpose = -M) :
    (pushForwardMatrix block M).transpose = -pushForwardMatrix block M := by
  simpa only [incidencePushForward_eq_pushForwardMatrix] using
    incidencePushForward_skew block M hM

/-- A normalized coarse-graining defect remains in the antisymmetric
orientation sector. -/
theorem orientationDefect_skew
    {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ)
    (hFine : fine.transpose = -fine)
    (hCoarse : coarse.transpose = -coarse) :
    (orientationDefect block weight fine coarse).transpose =
      -orientationDefect block weight fine coarse := by
  rw [orientationDefect, Matrix.transpose_sub, Matrix.transpose_smul,
    incidencePushForward_skew block fine hFine, hCoarse]
  module

/-- Coordinate changes of both chamber carriers transport the defect by
matrix reindexing.  Its vanishing and nonvanishing are therefore independent
of chamber labels. -/
theorem orientationDefect_relabel
    {m m' n n' : Type*} [Fintype m] [Fintype m']
    [DecidableEq n] [DecidableEq n']
    (fineEquiv : m ≃ m') (coarseEquiv : n ≃ n')
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ) :
    orientationDefect
        (relabelPartialBlock fineEquiv coarseEquiv block) weight
        (Matrix.reindex fineEquiv fineEquiv fine)
        (Matrix.reindex coarseEquiv coarseEquiv coarse) =
      Matrix.reindex coarseEquiv coarseEquiv
        (orientationDefect block weight fine coarse) := by
  rw [orientationDefect, orientationDefect,
    incidencePushForward_relabel]
  ext a b
  rfl

theorem orientationDefect_relabel_nonzero_iff
    {m m' n n' : Type*} [Fintype m] [Fintype m']
    [DecidableEq n] [DecidableEq n']
    (fineEquiv : m ≃ m') (coarseEquiv : n ≃ n')
    (block : m → Option n) (weight : ℚ)
    (fine : Matrix m m ℚ) (coarse : Matrix n n ℚ) :
    orientationDefect
        (relabelPartialBlock fineEquiv coarseEquiv block) weight
        (Matrix.reindex fineEquiv fineEquiv fine)
        (Matrix.reindex coarseEquiv coarseEquiv coarse) ≠ 0 ↔
      orientationDefect block weight fine coarse ≠ 0 := by
  rw [orientationDefect_relabel]
  constructor
  · intro hReindexed hZero
    apply hReindexed
    ext a b
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, hZero]
  · intro hOriginal hReindexed
    apply hOriginal
    apply (Matrix.reindex coarseEquiv coarseEquiv).injective
    simpa using hReindexed

/-! ## 5. Composition law -/

/-- Successive normalized defects obey an affine cocycle law.  The defect of
the composite quotient is the transported first defect plus the second defect.
The composite normalization is the product of the step normalizations. -/
theorem orientationDefect_compose
    {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p]
    (fineToMiddle : m → Option n) (middleToCoarse : n → Option p)
    (fineWeight middleWeight : ℚ)
    (fine : Matrix m m ℚ) (middle : Matrix n n ℚ)
    (coarse : Matrix p p ℚ) :
    orientationDefect
        (composePartialBlock fineToMiddle middleToCoarse)
        (fineWeight * middleWeight) fine coarse =
      middleWeight • incidencePushForward middleToCoarse
        (orientationDefect fineToMiddle fineWeight fine middle) +
      orientationDefect middleToCoarse middleWeight middle coarse := by
  rw [orientationDefect, orientationDefect, orientationDefect,
    incidencePushForward_compose,
    incidencePushForward_sub, incidencePushForward_smul]
  module

/-- Coboundaries obey the same weighted composition law, so endpoint
redefinitions are compatible with successive blocking. -/
theorem orientationCoboundary_compose
    {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p]
    (fineToMiddle : m → Option n) (middleToCoarse : n → Option p)
    (fineWeight middleWeight : ℚ)
    (fineCounterterm : Matrix m m ℚ)
    (middleCounterterm : Matrix n n ℚ)
    (coarseCounterterm : Matrix p p ℚ) :
    orientationCoboundary
        (composePartialBlock fineToMiddle middleToCoarse)
        (fineWeight * middleWeight) fineCounterterm coarseCounterterm =
      middleWeight • incidencePushForward middleToCoarse
        (orientationCoboundary fineToMiddle fineWeight
          fineCounterterm middleCounterterm) +
      orientationCoboundary middleToCoarse middleWeight
        middleCounterterm coarseCounterterm := by
  rw [orientationCoboundary, orientationCoboundary,
    orientationCoboundary, incidencePushForward_compose,
    incidencePushForward_sub, incidencePushForward_smul]
  module

theorem orientationDefect_compose_of_closed
    {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p]
    (fineToMiddle : m → Option n) (middleToCoarse : n → Option p)
    (fineWeight middleWeight : ℚ)
    (fine : Matrix m m ℚ) (middle : Matrix n n ℚ)
    (coarse : Matrix p p ℚ)
    (hFine : orientationDefect fineToMiddle fineWeight fine middle = 0)
    (hMiddle : orientationDefect middleToCoarse middleWeight middle coarse = 0) :
    orientationDefect
        (composePartialBlock fineToMiddle middleToCoarse)
        (fineWeight * middleWeight) fine coarse = 0 := by
  rw [orientationDefect_compose, hFine, hMiddle]
  simp [incidencePushForward]

/-! ## 6. Exact diamond defect -/

open UnifiedTheory.Audit.KFHigherRank

theorem diamondOrientationOperatorRankTwo_skew :
    diamondOrientationOperatorRankTwo.transpose =
      -diamondOrientationOperatorRankTwo := by
  rw [diamond_rankTwo_orientation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diamondOrientationRankTwo]

theorem chainThreeOrientationOperatorRankTwo_skew :
    chainThreeOrientationOperatorRankTwo.transpose =
      -chainThreeOrientationOperatorRankTwo := by
  rw [chainThree_rankTwo_orientation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chainThreeOrientationRankTwo]

/-- The generic defect specializes exactly to the unit long-range orientation
operator found in the diamond quotient. -/
theorem diamond_orientationDefect_exact :
    orientationDefect diamondRankTwoBlock (1 / 2 : ℚ)
      diamondOrientationOperatorRankTwo
      chainThreeOrientationOperatorRankTwo =
        (1 / 2 : ℚ) • generatedLongRangeOrientation := by
  rw [orientationDefect_eq_pushForwardMatrix,
    diamond_orientation_operator_tracks_through_blocking]
  module

theorem diamond_orientationDefect_nonzero :
    orientationDefect diamondRankTwoBlock (1 / 2 : ℚ)
      diamondOrientationOperatorRankTwo
      chainThreeOrientationOperatorRankTwo ≠ 0 := by
  rw [diamond_orientationDefect_exact]
  intro h
  have h02 := congrFun (congrFun h 0) 2
  change (1 / 2 : ℚ) * 2 = 0 at h02
  norm_num at h02

theorem diamond_orientationDefect_skew :
    (orientationDefect diamondRankTwoBlock (1 / 2 : ℚ)
      diamondOrientationOperatorRankTwo
      chainThreeOrientationOperatorRankTwo).transpose =
        -orientationDefect diamondRankTwoBlock (1 / 2 : ℚ)
          diamondOrientationOperatorRankTwo
          chainThreeOrientationOperatorRankTwo :=
  orientationDefect_skew _ _ _ _
    diamondOrientationOperatorRankTwo_skew
    chainThreeOrientationOperatorRankTwo_skew

/-- The exact benchmark stated through the generic closure criterion. -/
theorem diamond_normalized_orientation_not_closed :
    (1 / 2 : ℚ) • pushForwardMatrix diamondRankTwoBlock
      diamondOrientationOperatorRankTwo ≠
        chainThreeOrientationOperatorRankTwo := by
  intro hClosed
  apply diamond_orientationDefect_nonzero
  exact (orientationDefect_eq_zero_iff_closed _ _ _ _).2 hClosed

/-! ## Trust regression -/

#print axioms incidencePushForward_compose
#print axioms orientationDefect_skew
#print axioms orientationDefect_relabel
#print axioms orientationDefect_relabel_nonzero_iff
#print axioms orientationDefect_compose
#print axioms pushForwardMatrix_skew
#print axioms orientationDefect_add_counterterms
#print axioms orientationCoboundary_compose
#print axioms diamond_orientationDefect_exact
#print axioms diamond_orientationDefect_nonzero

end UnifiedTheory.Audit.KFOrientationDefect
