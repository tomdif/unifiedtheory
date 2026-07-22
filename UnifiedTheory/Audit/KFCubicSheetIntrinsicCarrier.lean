/-
  Audit/KFCubicSheetIntrinsicCarrier.lean

  INTRINSIC THREE-SHEET CARRIER AND PROJECTIVE VECTOR AMPLITUDES

  The marked-sheet rank-two construction is intrinsic.  For any finite sheet
  type S, its carrier is the zero-sum subspace of S -> C.  When |S|=3, every
  marked sheet determines a canonical regular-simplex vertex

      v_s(t) = delta_{s,t} - 1/3.

  This file proves that the construction is equivariant, not invariant:
  bijections transport vertices and preserve their Gram form, while the only
  vector fixed by every sheet permutation is zero.  It also isolates the
  dynamics-independent projective theorem.  A projectively compatible family
  of finite-dimensional vector amplitudes, together with one normalized base
  total, induces Hermitian, finitely biadditive, strongly positive, normalized,
  projectively consistent event kernels.

  No causal-set birth-to-sheet assignment is asserted here.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCubicMarkedSheetRankTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCubicMarkedSheetRankTwo

universe u v

/-! ## 1. The label-free zero-sum carrier -/

/-- The intrinsic sheet-distinguishing carrier on a finite sheet type. -/
def ZeroSumCarrier (S : Type u) [Fintype S] : Submodule ℂ (S → ℂ) where
  carrier := { state | ∑ sheet, state sheet = 0 }
  zero_mem' := by simp
  add_mem' := fun {first second} hFirst hSecond => by
    change (∑ sheet, (first + second) sheet) = 0
    change (∑ sheet, first sheet) = 0 at hFirst
    change (∑ sheet, second sheet) = 0 at hSecond
    simp only [Pi.add_apply, Finset.sum_add_distrib, hFirst, hSecond,
      add_zero]
  smul_mem' := fun scalar {state} hState => by
    change (∑ sheet, (scalar • state) sheet) = 0
    change (∑ sheet, state sheet) = 0 at hState
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hState, mul_zero]

@[simp]
theorem zeroSumCarrier_mem_iff {S : Type u} [Fintype S] (state : S → ℂ) :
    state ∈ ZeroSumCarrier S ↔ ∑ sheet, state sheet = 0 :=
  by rfl

/-- Hermitian Gram pairing, in the repository's linear-first convention. -/
def zeroSumCarrierInner {S : Type u} [Fintype S]
    (first second : ZeroSumCarrier S) : ℂ :=
  ∑ sheet, first.1 sheet * star (second.1 sheet)

/-- Transport sheet amplitudes along a bijection. -/
def transportZeroSumCarrier {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] (relabeling : S ≃ T) :
    ZeroSumCarrier S ≃ₗ[ℂ] ZeroSumCarrier T where
  toFun state :=
    ⟨fun sheet => state.1 (relabeling.symm sheet), by
      rw [zeroSumCarrier_mem_iff]
      rw [Equiv.sum_comp relabeling.symm state.1]
      exact (zeroSumCarrier_mem_iff state.1).1 state.2⟩
  invFun state :=
    ⟨fun sheet => state.1 (relabeling sheet), by
      rw [zeroSumCarrier_mem_iff]
      rw [Equiv.sum_comp relabeling state.1]
      exact (zeroSumCarrier_mem_iff state.1).1 state.2⟩
  left_inv state := by
    apply Subtype.ext
    funext sheet
    simp
  right_inv state := by
    apply Subtype.ext
    funext sheet
    simp
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar state := by
    apply Subtype.ext
    rfl

/-- Bijections preserve the intrinsic Gram pairing. -/
theorem zeroSumCarrierInner_transport {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] (relabeling : S ≃ T)
    (first second : ZeroSumCarrier S) :
    zeroSumCarrierInner (transportZeroSumCarrier relabeling first)
        (transportZeroSumCarrier relabeling second) =
      zeroSumCarrierInner first second := by
  unfold zeroSumCarrierInner transportZeroSumCarrier
  exact Equiv.sum_comp relabeling.symm
    (fun sheet => first.1 sheet * star (second.1 sheet))

/-! ## 2. Canonical regular-simplex sheet vertices -/

/-- The unnormalized simplex vertex associated with a marked sheet. -/
def sheetVertexFunction {S : Type u} [Fintype S] [DecidableEq S]
    (sheet : S) : S → ℂ :=
  fun other => (if other = sheet then 1 else 0) - 1 / 3

/-- Kronecker coordinate used by the intrinsic sheet vertices. -/
def sheetDelta {S : Type u} [DecidableEq S] (sheet other : S) : ℂ :=
  if other = sheet then 1 else 0

@[simp]
theorem sheetDelta_sum {S : Type u} [Fintype S] [DecidableEq S]
    (sheet : S) :
    ∑ other, sheetDelta sheet other = 1 := by
  simp [sheetDelta]

theorem sheetDelta_product_sum {S : Type u}
    [Fintype S] [DecidableEq S] (first second : S) :
    ∑ other, sheetDelta first other * sheetDelta second other =
      if first = second then 1 else 0 := by
  by_cases hEqual : first = second
  · subst second
    simp [sheetDelta]
  · have hReverse : ¬ second = first := by exact fun h => hEqual h.symm
    simp [sheetDelta, hEqual, hReverse]

theorem sheetVertexFunction_sum_zero {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (sheet : S) :
    ∑ other, sheetVertexFunction sheet other = 0 := by
  classical
  simp [sheetVertexFunction, Finset.sum_sub_distrib, hCard]

/-- A marked sheet canonically determines a point of the zero-sum carrier. -/
def sheetVertex {S : Type u} [Fintype S] [DecidableEq S]
    (hCard : Fintype.card S = 3) (sheet : S) : ZeroSumCarrier S :=
  ⟨sheetVertexFunction sheet,
    (zeroSumCarrier_mem_iff _).2 (sheetVertexFunction_sum_zero hCard sheet)⟩

@[simp]
theorem sheetVertex_apply_self {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (sheet : S) :
    (sheetVertex hCard sheet).1 sheet = 2 / 3 := by
  simp [sheetVertex, sheetVertexFunction]
  ring

@[simp]
theorem sheetVertex_apply_ne {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    {sheet other : S} (hDifferent : other ≠ sheet) :
    (sheetVertex hCard sheet).1 other = -1 / 3 := by
  simp [sheetVertex, sheetVertexFunction, hDifferent]
  ring_nf

/-- The three canonical vertices sum to zero. -/
theorem sheetVertex_sum_zero {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3) :
    ∑ sheet, sheetVertex hCard sheet = 0 := by
  apply Subtype.ext
  funext other
  simp [sheetVertex, sheetVertexFunction, Finset.sum_sub_distrib, hCard]

/-- Exact Gram law for the unnormalized simplex vertices. -/
theorem sheetVertex_inner {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (first second : S) :
    zeroSumCarrierInner (sheetVertex hCard first) (sheetVertex hCard second) =
      if first = second then 2 / 3 else -1 / 3 := by
  classical
  have hPointwise (other : S) :
      ((sheetVertex hCard first).1 other) *
          star ((sheetVertex hCard second).1 other) =
        sheetDelta first other * sheetDelta second other
          - sheetDelta first other * (1 / 3)
          - sheetDelta second other * (1 / 3) + 1 / 9 := by
    by_cases hFirst : other = first <;>
      by_cases hSecond : other = second <;>
      simp_all [sheetVertex, sheetVertexFunction, sheetDelta] <;> ring
  unfold zeroSumCarrierInner
  rw [Finset.sum_congr rfl (fun other _hOther => hPointwise other)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ]
  rw [sheetDelta_product_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [sheetDelta_sum, sheetDelta_sum]
  simp [hCard]
  by_cases hEqual : first = second <;> simp [hEqual] <;> ring

/-- The vertices reconstruct every vector in the zero-sum carrier. -/
theorem sheetVertex_reconstruction {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (state : ZeroSumCarrier S) :
    ∑ sheet, state.1 sheet • sheetVertex hCard sheet = state := by
  apply Subtype.ext
  funext other
  have hZero : ∑ sheet, state.1 sheet = 0 :=
    (zeroSumCarrier_mem_iff state.1).1 state.2
  simp only [Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    Pi.smul_apply, smul_eq_mul, sheetVertex, sheetVertexFunction]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  simp [hZero]

/-- Consequently the canonical vertices span the entire intrinsic carrier. -/
theorem sheetVertex_span_eq_top {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3) :
    Submodule.span ℂ (Set.range (sheetVertex hCard)) = ⊤ := by
  apply top_unique
  intro state _hState
  rw [← sheetVertex_reconstruction hCard state]
  exact Submodule.sum_mem _ (fun sheet _hSheet =>
    Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self sheet)))

/-! ## 2a. Normalization and exact complex dimension -/

/-- Canonical real normalization taking simplex vertices to unit norm. -/
def sheetVertexNormalization : ℝ := Real.sqrt (3 / 2)

theorem sheetVertexNormalization_sq : sheetVertexNormalization ^ 2 = 3 / 2 := by
  unfold sheetVertexNormalization
  exact Real.sq_sqrt (by norm_num)

/-- The normalized vertex associated with a marked sheet. -/
def normalizedSheetVertex {S : Type u} [Fintype S] [DecidableEq S]
    (hCard : Fintype.card S = 3) (sheet : S) : ZeroSumCarrier S :=
  (sheetVertexNormalization : ℂ) • sheetVertex hCard sheet

theorem zeroSumCarrierInner_real_smul {S : Type u} [Fintype S]
    (scalar : ℝ) (first second : ZeroSumCarrier S) :
    zeroSumCarrierInner ((scalar : ℂ) • first) ((scalar : ℂ) • second) =
      ((scalar : ℂ) ^ 2) * zeroSumCarrierInner first second := by
  unfold zeroSumCarrierInner
  rw [Finset.sum_congr rfl]
  · rw [← Finset.mul_sum]
  · intro sheet _hSheet
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
    rw [StarMul.star_mul]
    rw [show star (scalar : ℂ) = (scalar : ℂ) from
      Complex.conj_ofReal scalar]
    ring

/-- The normalized vertices have the regular-simplex Gram law. -/
theorem normalizedSheetVertex_inner {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (first second : S) :
    zeroSumCarrierInner (normalizedSheetVertex hCard first)
        (normalizedSheetVertex hCard second) =
      if first = second then 1 else -1 / 2 := by
  rw [normalizedSheetVertex, normalizedSheetVertex,
    zeroSumCarrierInner_real_smul, sheetVertex_inner]
  have hSquareComplex : ((sheetVertexNormalization : ℂ) ^ 2) = 3 / 2 := by
    calc
      ((sheetVertexNormalization : ℂ) ^ 2) =
          ((sheetVertexNormalization ^ 2 : ℝ) : ℂ) := by norm_num
      _ = (((3 / 2 : ℝ)) : ℂ) := by rw [sheetVertexNormalization_sq]
      _ = 3 / 2 := by norm_num
  rw [hSquareComplex]
  by_cases hEqual : first = second <;> simp [hEqual]

/-- Canonical Gram matrix of the three normalized marked-sheet directions. -/
def normalizedSheetGram {S : Type u} [Fintype S] [DecidableEq S]
    (hCard : Fintype.card S = 3) : Matrix S S ℂ :=
  fun first second => zeroSumCarrierInner
    (normalizedSheetVertex hCard first) (normalizedSheetVertex hCard second)

theorem normalizedSheetGram_exact {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (first second : S) :
    normalizedSheetGram hCard first second =
      if first = second then 1 else -1 / 2 :=
  normalizedSheetVertex_inner hCard first second

/-- The canonical simplex Gram matrix is positive semidefinite. -/
theorem normalizedSheetGram_posSemidef {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3) :
    (normalizedSheetGram hCard).PosSemidef := by
  let column : Matrix S S ℂ := fun sheet coordinate =>
    (normalizedSheetVertex hCard sheet).1 coordinate
  have hPositive : (column * column.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose column
  have hGram : normalizedSheetGram hCard = column * column.conjTranspose := by
    ext first second
    simp [normalizedSheetGram, zeroSumCarrierInner, column,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hGram]
  exact hPositive

/-- Linear coordinates on the zero-sum carrier of `Fin 3`. -/
def zeroSumFinThreeCoordinateLinearEquiv :
    ZeroSumCarrier (Fin 3) ≃ₗ[ℂ] StandardSheetCoordinates where
  toFun state := standardSheetToCoordinates state.1
  invFun coordinates :=
    ⟨standardSheetFromCoordinates coordinates, by
      rw [zeroSumCarrier_mem_iff]
      exact standardSheetFromCoordinates_sum_zero coordinates⟩
  left_inv state := by
    apply Subtype.ext
    apply standardSheetFromToCoordinates
    exact (zeroSumCarrier_mem_iff state.1).1 state.2
  right_inv := standardSheetToFromCoordinates
  map_add' first second := by
    funext coordinate
    fin_cases coordinate <;>
      simp [standardSheetToCoordinates]
  map_smul' scalar state := by
    funext coordinate
    fin_cases coordinate <;>
      simp [standardSheetToCoordinates]

/-- Any marking of a three-element sheet type identifies its intrinsic carrier
linearly with two complex coordinates. -/
def intrinsicCarrierCoordinateLinearEquiv {S : Type u}
    [Fintype S] (marking : S ≃ Fin 3) :
    ZeroSumCarrier S ≃ₗ[ℂ] StandardSheetCoordinates :=
  (transportZeroSumCarrier marking).trans zeroSumFinThreeCoordinateLinearEquiv

/-- Exact rank statement: the intrinsic three-sheet standard carrier has
complex dimension two. -/
theorem zeroSumCarrier_finrank_eq_two {S : Type u}
    [Fintype S] (marking : S ≃ Fin 3) :
    Module.finrank ℂ (ZeroSumCarrier S) = 2 := by
  rw [LinearEquiv.finrank_eq (intrinsicCarrierCoordinateLinearEquiv marking)]
  simp [StandardSheetCoordinates]

/-- Relabeling transports the vertex attached to a mark, rather than fixing
its coordinate vector. -/
theorem transport_sheetVertex {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (relabeling : S ≃ T) (hCard : Fintype.card S = 3) (sheet : S) :
    transportZeroSumCarrier relabeling (sheetVertex hCard sheet) =
      sheetVertex ((Fintype.card_congr relabeling).symm.trans hCard) (relabeling sheet) := by
  apply Subtype.ext
  funext other
  change sheetVertexFunction sheet (relabeling.symm other) =
    sheetVertexFunction (relabeling sheet) other
  unfold sheetVertexFunction
  simp [Equiv.symm_apply_eq]

/-! ## 3. Equivariant, not invariant -/

/-- The standard carrier has no nonzero vector invariant under every sheet
permutation. -/
theorem fixed_by_all_sheet_permutations_eq_zero {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (state : ZeroSumCarrier S)
    (hFixed : ∀ relabeling : Equiv.Perm S,
      transportZeroSumCarrier relabeling state = state) :
    state = 0 := by
  have hCardPositive : 0 < Fintype.card S := by omega
  obtain ⟨base⟩ := Fintype.card_pos_iff.mp hCardPositive
  have hConstant : ∀ first second : S, state.1 first = state.1 second := by
    intro first second
    by_cases hEqual : first = second
    · subst second
      rfl
    · have hSwap := congrArg (fun value => value.1 first)
          (hFixed (Equiv.swap first second))
      simpa [transportZeroSumCarrier, Equiv.swap_apply_def, hEqual] using hSwap.symm
  have hBaseZero : state.1 base = 0 := by
    have hSum : ∑ sheet : S, state.1 base = 0 := by
      calc
        ∑ sheet : S, state.1 base = ∑ sheet : S, state.1 sheet := by
          apply Finset.sum_congr rfl
          intro sheet _hSheet
          exact hConstant base sheet
        _ = 0 := (zeroSumCarrier_mem_iff state.1).1 state.2
    simpa [hCard] using hSum
  apply Subtype.ext
  funext sheet
  rw [hConstant sheet base, hBaseZero]
  rfl

/-! ## 4. Abstract finite-dimensional vector kernels -/

/-- Linear-first Hermitian pairing on finite coordinate vectors. -/
def finiteVectorInner {Coordinate : Type v} [Fintype Coordinate]
    (first second : Coordinate → ℂ) : ℂ :=
  ∑ coordinate, first coordinate * star (second coordinate)

/-- Atomic Gram kernel of a finite-coordinate vector amplitude. -/
def vectorAmplitudeKernel {History : Type u} {Coordinate : Type v}
    [Fintype Coordinate] (amplitude : History → Coordinate → ℂ) :
    GrowthDecoherenceFunctional History :=
  fun first second => finiteVectorInner (amplitude first) (amplitude second)

theorem vectorAmplitudeKernel_hermitian
    {History : Type u} {Coordinate : Type v} [Fintype Coordinate]
    (amplitude : History → Coordinate → ℂ) :
    IsHermitianGrowthFunctional (vectorAmplitudeKernel amplitude) := by
  intro first second
  unfold vectorAmplitudeKernel finiteVectorInner
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro coordinate _hCoordinate
  simp
  ring

/-- Finite-coordinate vector amplitudes generate strongly positive kernels. -/
theorem vectorAmplitudeKernel_stronglyPositive
    {History : Type u} {Coordinate : Type v} [Fintype Coordinate]
    (amplitude : History → Coordinate → ℂ) :
    IsStronglyPositiveGrowthFunctional (vectorAmplitudeKernel amplitude) := by
  intro n sample
  let column : Matrix (Fin n) Coordinate ℂ :=
    fun i coordinate => amplitude (sample i) coordinate
  have hPositive : (column * column.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose column
  have hKernel :
      (fun i j => vectorAmplitudeKernel amplitude (sample i) (sample j)) =
        column * column.conjTranspose := by
    ext i j
    simp [vectorAmplitudeKernel, finiteVectorInner, column,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hKernel]
  exact hPositive

/-- Vector amplitude of a finite history event. -/
def vectorEventAmplitude {History : Type u} {Coordinate : Type v}
    (amplitude : History → Coordinate → ℂ) (event : Finset History) :
    Coordinate → ℂ :=
  fun coordinate => ∑ history ∈ event, amplitude history coordinate

theorem vector_event_decoherence_eq_inner
    {History : Type u} {Coordinate : Type v} [Fintype Coordinate]
    (amplitude : History → Coordinate → ℂ) (first second : Finset History) :
    growthEventDecoherence (vectorAmplitudeKernel amplitude) first second =
      finiteVectorInner (vectorEventAmplitude amplitude first)
        (vectorEventAmplitude amplitude second) := by
  classical
  unfold growthEventDecoherence vectorAmplitudeKernel finiteVectorInner
  calc
    (∑ history ∈ first, ∑ other ∈ second, ∑ coordinate,
        amplitude history coordinate * star (amplitude other coordinate)) =
        ∑ coordinate, ∑ history ∈ first, ∑ other ∈ second,
          amplitude history coordinate * star (amplitude other coordinate) := by
      calc
        (∑ history ∈ first, ∑ other ∈ second, ∑ coordinate,
            amplitude history coordinate * star (amplitude other coordinate)) =
            ∑ history ∈ first, ∑ coordinate, ∑ other ∈ second,
              amplitude history coordinate * star (amplitude other coordinate) := by
          apply Finset.sum_congr rfl
          intro history _hHistory
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ coordinate,
        (∑ history ∈ first, amplitude history coordinate) *
          star (∑ other ∈ second, amplitude other coordinate) := by
      apply Finset.sum_congr rfl
      intro coordinate _hCoordinate
      rw [star_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro history _hHistory
      rw [Finset.mul_sum]
    _ = _ := rfl

/-- Strong positivity survives the finite-event extension. -/
theorem vectorEventDecoherence_stronglyPositive
    {History : Type u} {Coordinate : Type v} [Fintype Coordinate]
    (amplitude : History → Coordinate → ℂ) :
    IsStronglyPositiveGrowthFunctional
      (growthEventDecoherence (vectorAmplitudeKernel amplitude)) := by
  have hKernel :
      growthEventDecoherence (vectorAmplitudeKernel amplitude) =
        vectorAmplitudeKernel (vectorEventAmplitude amplitude) := by
    funext first second
    exact vector_event_decoherence_eq_inner amplitude first second
  rw [hKernel]
  exact vectorAmplitudeKernel_stronglyPositive _

/-! ## 5. Projective vector-amplitude systems -/

/-- A finite-depth history system with explicit exhaustive refinement maps. -/
structure FiniteHistoryRefinement (History : ℕ → Type u)
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)] where
  parent : ∀ n, History (n + 1) → History n

/-- Pull a finite event forward through one exhaustive refinement. -/
def refineFiniteEvent {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    (refinement : FiniteHistoryRefinement History) (n : ℕ)
    (event : Finset (History n)) : Finset (History (n + 1)) :=
  Finset.univ.filter (fun fine => refinement.parent n fine ∈ event)

@[simp]
theorem refineFiniteEvent_univ {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    (refinement : FiniteHistoryRefinement History) (n : ℕ) :
    refineFiniteEvent refinement n Finset.univ = Finset.univ := by
  ext fine
  simp [refineFiniteEvent]

/-- Atomic projective consistency for a vector-amplitude family. -/
def IsProjectivelyConsistentVectorAmplitude
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : Type v} [Fintype Coordinate]
    (refinement : FiniteHistoryRefinement History)
    (amplitude : ∀ n, History n → Coordinate → ℂ) : Prop :=
  ∀ n coarse coordinate,
    amplitude n coarse coordinate =
      ∑ fine ∈ Finset.univ.filter
        (fun fine : History (n + 1) => refinement.parent n fine = coarse),
        amplitude (n + 1) fine coordinate

/-- Atomic projective consistency sums to event-amplitude consistency. -/
theorem vectorEventAmplitude_projective
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : Type v} [Fintype Coordinate]
    (refinement : FiniteHistoryRefinement History)
    (amplitude : ∀ n, History n → Coordinate → ℂ)
    (hProjective : IsProjectivelyConsistentVectorAmplitude refinement amplitude)
    (n : ℕ) (event : Finset (History n)) :
    vectorEventAmplitude (amplitude n) event =
      vectorEventAmplitude (amplitude (n + 1))
        (refineFiniteEvent refinement n event) := by
  funext coordinate
  classical
  simp only [vectorEventAmplitude]
  simp_rw [hProjective n]
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ event
    (refinement.parent n) (fun fine => amplitude (n + 1) fine coordinate)

/-- Projective vector amplitudes induce exactly projective event kernels. -/
theorem vectorEventDecoherence_projective
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : Type v} [Fintype Coordinate]
    (refinement : FiniteHistoryRefinement History)
    (amplitude : ∀ n, History n → Coordinate → ℂ)
    (hProjective : IsProjectivelyConsistentVectorAmplitude refinement amplitude)
    (n : ℕ) (first second : Finset (History n)) :
    growthEventDecoherence (vectorAmplitudeKernel (amplitude (n + 1)))
        (refineFiniteEvent refinement n first)
        (refineFiniteEvent refinement n second) =
      growthEventDecoherence (vectorAmplitudeKernel (amplitude n))
        first second := by
  rw [vector_event_decoherence_eq_inner,
    vector_event_decoherence_eq_inner,
    ← vectorEventAmplitude_projective refinement amplitude hProjective n first,
    ← vectorEventAmplitude_projective refinement amplitude hProjective n second]

/-- Unit norm of the total vector amplitude is exactly decoherence-functional
normalization. -/
theorem vectorAmplitudeKernel_normalized_iff
    {History : Type u} [Fintype History]
    {Coordinate : Type v} [Fintype Coordinate]
    (amplitude : History → Coordinate → ℂ) :
    IsNormalizedGrowthFunctional (vectorAmplitudeKernel amplitude) ↔
      finiteVectorInner (vectorEventAmplitude amplitude Finset.univ)
        (vectorEventAmplitude amplitude Finset.univ) = 1 := by
  unfold IsNormalizedGrowthFunctional
  change growthEventDecoherence (vectorAmplitudeKernel amplitude)
    Finset.univ Finset.univ = 1 ↔ _
  rw [vector_event_decoherence_eq_inner]

/-! ## 6. Projective consistency with equivariant sheet transport -/

/-- Pull a fine coordinate vector back along a bijective relabeling. -/
def transportFiniteVector {Coarse : Type u} {Fine : Type v}
    (transport : Coarse ≃ Fine) (state : Fine → ℂ) : Coarse → ℂ :=
  fun coordinate => state (transport coordinate)

/-- Coordinate relabeling is a Gram isometry. -/
theorem finiteVectorInner_transport {Coarse : Type u} {Fine : Type v}
    [Fintype Coarse] [Fintype Fine] (transport : Coarse ≃ Fine)
    (first second : Fine → ℂ) :
    finiteVectorInner (transportFiniteVector transport first)
        (transportFiniteVector transport second) =
      finiteVectorInner first second := by
  unfold finiteVectorInner transportFiniteVector
  exact Equiv.sum_comp transport
    (fun coordinate => first coordinate * star (second coordinate))

/-- Bijections identifying the carrier coordinates at adjacent depths. For
intrinsic three-sheet carriers these are induced by sheet relabelings. -/
structure FiniteCoordinateTransport (Coordinate : ℕ → Type v)
    [∀ n, Fintype (Coordinate n)] where
  toFine : ∀ n, Coordinate n ≃ Coordinate (n + 1)

/-- Projective consistency with explicit equivariant coordinate transport. -/
def IsTransportedProjectiveVectorAmplitude
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : ℕ → Type v} [∀ n, Fintype (Coordinate n)]
    (refinement : FiniteHistoryRefinement History)
    (transport : FiniteCoordinateTransport Coordinate)
    (amplitude : ∀ n, History n → Coordinate n → ℂ) : Prop :=
  ∀ n coarse coordinate,
    amplitude n coarse coordinate =
      ∑ fine ∈ Finset.univ.filter
        (fun fine : History (n + 1) => refinement.parent n fine = coarse),
        amplitude (n + 1) fine (transport.toFine n coordinate)

/-- Atomic consistency with sheet transport implies event-amplitude
consistency with the same transport. -/
theorem transportedVectorEventAmplitude_projective
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : ℕ → Type v} [∀ n, Fintype (Coordinate n)]
    (refinement : FiniteHistoryRefinement History)
    (transport : FiniteCoordinateTransport Coordinate)
    (amplitude : ∀ n, History n → Coordinate n → ℂ)
    (hProjective : IsTransportedProjectiveVectorAmplitude
      refinement transport amplitude)
    (n : ℕ) (event : Finset (History n)) :
    vectorEventAmplitude (amplitude n) event =
      transportFiniteVector (transport.toFine n)
        (vectorEventAmplitude (amplitude (n + 1))
          (refineFiniteEvent refinement n event)) := by
  funext coordinate
  classical
  simp only [vectorEventAmplitude, transportFiniteVector]
  simp_rw [hProjective n]
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ event
    (refinement.parent n)
    (fun fine => amplitude (n + 1) fine (transport.toFine n coordinate))

/-- Equivariant projective amplitudes give exactly projective decoherence
kernels; coordinate representatives change, but the Gram entry does not. -/
theorem transportedVectorEventDecoherence_projective
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : ℕ → Type v} [∀ n, Fintype (Coordinate n)]
    (refinement : FiniteHistoryRefinement History)
    (transport : FiniteCoordinateTransport Coordinate)
    (amplitude : ∀ n, History n → Coordinate n → ℂ)
    (hProjective : IsTransportedProjectiveVectorAmplitude
      refinement transport amplitude)
    (n : ℕ) (first second : Finset (History n)) :
    growthEventDecoherence (vectorAmplitudeKernel (amplitude (n + 1)))
        (refineFiniteEvent refinement n first)
        (refineFiniteEvent refinement n second) =
      growthEventDecoherence (vectorAmplitudeKernel (amplitude n))
        first second := by
  rw [vector_event_decoherence_eq_inner,
    vector_event_decoherence_eq_inner,
    transportedVectorEventAmplitude_projective refinement transport amplitude
      hProjective n first,
    transportedVectorEventAmplitude_projective refinement transport amplitude
      hProjective n second,
    finiteVectorInner_transport]

/-- The unit-norm condition propagates exactly between adjacent depths. -/
theorem transportedTotalVectorNorm_projective
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : ℕ → Type v} [∀ n, Fintype (Coordinate n)]
    (refinement : FiniteHistoryRefinement History)
    (transport : FiniteCoordinateTransport Coordinate)
    (amplitude : ∀ n, History n → Coordinate n → ℂ)
    (hProjective : IsTransportedProjectiveVectorAmplitude
      refinement transport amplitude) (n : ℕ) :
    finiteVectorInner (vectorEventAmplitude (amplitude n) Finset.univ)
        (vectorEventAmplitude (amplitude n) Finset.univ) =
      finiteVectorInner
        (vectorEventAmplitude (amplitude (n + 1)) Finset.univ)
        (vectorEventAmplitude (amplitude (n + 1)) Finset.univ) := by
  have hAmplitude := transportedVectorEventAmplitude_projective
    refinement transport amplitude hProjective n Finset.univ
  rw [refineFiniteEvent_univ] at hAmplitude
  rw [hAmplitude, finiteVectorInner_transport]

/-- One base normalization therefore normalizes every finite depth. -/
theorem transportedTotalVectorNorm_eq_base
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : ℕ → Type v} [∀ n, Fintype (Coordinate n)]
    (refinement : FiniteHistoryRefinement History)
    (transport : FiniteCoordinateTransport Coordinate)
    (amplitude : ∀ n, History n → Coordinate n → ℂ)
    (hProjective : IsTransportedProjectiveVectorAmplitude
      refinement transport amplitude) (n : ℕ) :
    finiteVectorInner (vectorEventAmplitude (amplitude n) Finset.univ)
        (vectorEventAmplitude (amplitude n) Finset.univ) =
      finiteVectorInner (vectorEventAmplitude (amplitude 0) Finset.univ)
        (vectorEventAmplitude (amplitude 0) Finset.univ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← ih]
      exact (transportedTotalVectorNorm_projective
        refinement transport amplitude hProjective n).symm

/-- Capstone: the mathematical projective layer is independent of any
microscopic causal assignment. -/
theorem projectiveVectorAmplitude_induces_consistent_positive_kernels
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : Type v} [Fintype Coordinate]
    (refinement : FiniteHistoryRefinement History)
    (amplitude : ∀ n, History n → Coordinate → ℂ)
    (hProjective : IsProjectivelyConsistentVectorAmplitude refinement amplitude)
    (hNormalized : ∀ n,
      finiteVectorInner (vectorEventAmplitude (amplitude n) Finset.univ)
        (vectorEventAmplitude (amplitude n) Finset.univ) = 1) :
    (∀ n, IsHermitianGrowthFunctional
      (vectorAmplitudeKernel (amplitude n)))
      ∧ (∀ n, IsStronglyPositiveGrowthFunctional
        (vectorAmplitudeKernel (amplitude n)))
      ∧ (∀ n, IsNormalizedGrowthFunctional
        (vectorAmplitudeKernel (amplitude n)))
      ∧ (∀ n (first second : Finset (History n)),
        growthEventDecoherence (vectorAmplitudeKernel (amplitude (n + 1)))
            (refineFiniteEvent refinement n first)
            (refineFiniteEvent refinement n second) =
          growthEventDecoherence (vectorAmplitudeKernel (amplitude n))
            first second) := by
  exact ⟨fun n => vectorAmplitudeKernel_hermitian (amplitude n),
    fun n => vectorAmplitudeKernel_stronglyPositive (amplitude n),
    fun n => (vectorAmplitudeKernel_normalized_iff (amplitude n)).2
      (hNormalized n),
    vectorEventDecoherence_projective refinement amplitude hProjective⟩

/-- Strong capstone with changing sheet coordinates: equivariance, not a
fixed coordinate vector, is sufficient for a normalized projective family. -/
theorem transportedProjectiveVectorAmplitude_induces_consistent_positive_kernels
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : ℕ → Type v} [∀ n, Fintype (Coordinate n)]
    (refinement : FiniteHistoryRefinement History)
    (transport : FiniteCoordinateTransport Coordinate)
    (amplitude : ∀ n, History n → Coordinate n → ℂ)
    (hProjective : IsTransportedProjectiveVectorAmplitude
      refinement transport amplitude)
    (hNormalized : ∀ n,
      finiteVectorInner (vectorEventAmplitude (amplitude n) Finset.univ)
        (vectorEventAmplitude (amplitude n) Finset.univ) = 1) :
    (∀ n, IsHermitianGrowthFunctional
      (vectorAmplitudeKernel (amplitude n)))
      ∧ (∀ n, IsStronglyPositiveGrowthFunctional
        (growthEventDecoherence (vectorAmplitudeKernel (amplitude n))))
      ∧ (∀ n, IsNormalizedGrowthFunctional
        (vectorAmplitudeKernel (amplitude n)))
      ∧ (∀ n (first second : Finset (History n)),
        growthEventDecoherence (vectorAmplitudeKernel (amplitude (n + 1)))
            (refineFiniteEvent refinement n first)
            (refineFiniteEvent refinement n second) =
          growthEventDecoherence (vectorAmplitudeKernel (amplitude n))
            first second) := by
  exact ⟨fun n => vectorAmplitudeKernel_hermitian (amplitude n),
    fun n => vectorEventDecoherence_stronglyPositive (amplitude n),
    fun n => (vectorAmplitudeKernel_normalized_iff (amplitude n)).2
      (hNormalized n),
    transportedVectorEventDecoherence_projective refinement transport amplitude
      hProjective⟩

/-- A single normalized base vector is enough: projective equivariant
transport propagates normalization to the whole family. -/
theorem transportedProjectiveVectorAmplitude_of_base_normalized
    {History : ℕ → Type u}
    [∀ n, Fintype (History n)] [∀ n, DecidableEq (History n)]
    {Coordinate : ℕ → Type v} [∀ n, Fintype (Coordinate n)]
    (refinement : FiniteHistoryRefinement History)
    (transport : FiniteCoordinateTransport Coordinate)
    (amplitude : ∀ n, History n → Coordinate n → ℂ)
    (hProjective : IsTransportedProjectiveVectorAmplitude
      refinement transport amplitude)
    (hBaseNormalized :
      finiteVectorInner (vectorEventAmplitude (amplitude 0) Finset.univ)
        (vectorEventAmplitude (amplitude 0) Finset.univ) = 1) :
    (∀ n, IsHermitianGrowthFunctional
      (vectorAmplitudeKernel (amplitude n)))
      ∧ (∀ n, IsStronglyPositiveGrowthFunctional
        (growthEventDecoherence (vectorAmplitudeKernel (amplitude n))))
      ∧ (∀ n, IsNormalizedGrowthFunctional
        (vectorAmplitudeKernel (amplitude n)))
      ∧ (∀ n (first second : Finset (History n)),
        growthEventDecoherence (vectorAmplitudeKernel (amplitude (n + 1)))
            (refineFiniteEvent refinement n first)
            (refineFiniteEvent refinement n second) =
          growthEventDecoherence (vectorAmplitudeKernel (amplitude n))
            first second) := by
  apply transportedProjectiveVectorAmplitude_induces_consistent_positive_kernels
    refinement transport amplitude hProjective
  intro n
  rw [transportedTotalVectorNorm_eq_base
    refinement transport amplitude hProjective n]
  exact hBaseNormalized

#print axioms zeroSumCarrierInner_transport
#print axioms sheetVertex_sum_zero
#print axioms sheetVertex_inner
#print axioms sheetVertex_reconstruction
#print axioms sheetVertex_span_eq_top
#print axioms normalizedSheetVertex_inner
#print axioms normalizedSheetGram_posSemidef
#print axioms zeroSumCarrier_finrank_eq_two
#print axioms transport_sheetVertex
#print axioms fixed_by_all_sheet_permutations_eq_zero
#print axioms vectorAmplitudeKernel_stronglyPositive
#print axioms vectorEventDecoherence_stronglyPositive
#print axioms vectorEventDecoherence_projective
#print axioms projectiveVectorAmplitude_induces_consistent_positive_kernels
#print axioms transportedVectorEventDecoherence_projective
#print axioms transportedProjectiveVectorAmplitude_induces_consistent_positive_kernels
#print axioms transportedProjectiveVectorAmplitude_of_base_normalized

end

end UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier
