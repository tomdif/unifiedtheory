/-
  Audit/KFCubicSheetFrameRigidity.lean

  TIGHT FRAME, CANONICAL MIXED STATE, S3 RIGIDITY, AND MONODROMY

  The intrinsic three-sheet carrier admits no nonzero permutation-fixed pure
  vector, but it does admit canonical permutation-invariant operator data.
  This file proves:

  * the unnormalized sheet vertices form a Parseval tight frame;
  * normalized sheet projectors average to one half of the identity;
  * the rescaled projectors form a canonical three-outcome POVM;
  * every endomorphism of the standard `Fin 3` carrier commuting with all
    sheet permutations is a scalar;
  * the half-identity is therefore the unique invariant operator with unit
    intrinsic frame trace;
  * a global transported sheet section forces every loop monodromy to fix the
    selected sheet, so a fixed-point-free loop is an exact obstruction.

  These are operator and bundle-level constraints.  They do not construct a
  causal transfer law or choose a sheet for an unlabeled birth.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCubicSheetFrameRigidity

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier

universe u v

/-! ## 1. Rank-one carrier operators -/

theorem zeroSumCarrierInner_add_left {S : Type u} [Fintype S]
    (first second third : ZeroSumCarrier S) :
    zeroSumCarrierInner (first + second) third =
      zeroSumCarrierInner first third + zeroSumCarrierInner second third := by
  unfold zeroSumCarrierInner
  simp only [Submodule.coe_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem zeroSumCarrierInner_smul_left {S : Type u} [Fintype S]
    (scalar : ℂ) (first second : ZeroSumCarrier S) :
    zeroSumCarrierInner (scalar • first) second =
      scalar * zeroSumCarrierInner first second := by
  unfold zeroSumCarrierInner
  simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
    mul_assoc]
  rw [← Finset.mul_sum]

theorem zeroSumCarrierInner_smul_right_real {S : Type u} [Fintype S]
    (scalar : ℝ) (first second : ZeroSumCarrier S) :
    zeroSumCarrierInner first ((scalar : ℂ) • second) =
      (scalar : ℂ) * zeroSumCarrierInner first second := by
  unfold zeroSumCarrierInner
  rw [Finset.sum_congr rfl]
  · rw [← Finset.mul_sum]
  · intro sheet _hSheet
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
    rw [StarMul.star_mul]
    rw [show star (scalar : ℂ) = (scalar : ℂ) from
      Complex.conj_ofReal scalar]
    ring

theorem zeroSumCarrierInner_conj_symm {S : Type u} [Fintype S]
    (first second : ZeroSumCarrier S) :
    zeroSumCarrierInner second first =
      star (zeroSumCarrierInner first second) := by
  unfold zeroSumCarrierInner
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro sheet _hSheet
  rw [StarMul.star_mul, star_star]

/-- Rank-one operator `|vector><vector|` in the linear-first convention. -/
def carrierRankOne {S : Type u} [Fintype S]
    (vector : ZeroSumCarrier S) : Module.End ℂ (ZeroSumCarrier S) where
  toFun state := zeroSumCarrierInner state vector • vector
  map_add' first second := by
    rw [zeroSumCarrierInner_add_left, add_smul]
  map_smul' scalar state := by
    rw [zeroSumCarrierInner_smul_left, SemigroupAction.mul_smul]
    simp

@[simp]
theorem carrierRankOne_apply {S : Type u} [Fintype S]
    (vector state : ZeroSumCarrier S) :
    carrierRankOne vector state = zeroSumCarrierInner state vector • vector :=
  rfl

/-! ## 2. The canonical tight frame -/

/-- Pairing any carrier state against the vertex of sheet `s` extracts its
`s`-coordinate. -/
theorem zeroSumCarrierInner_sheetVertex {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (state : ZeroSumCarrier S) (sheet : S) :
    zeroSumCarrierInner state (sheetVertex hCard sheet) = state.1 sheet := by
  have hZero : ∑ other, state.1 other = 0 :=
    (zeroSumCarrier_mem_iff state.1).1 state.2
  unfold zeroSumCarrierInner
  have hPointwise (other : S) :
      state.1 other * star ((sheetVertex hCard sheet).1 other) =
        state.1 other * ((if other = sheet then 1 else 0) - 1 / 3) := by
    by_cases hEqual : other = sheet <;>
      simp [sheetVertex, sheetVertexFunction, hEqual]
  rw [Finset.sum_congr rfl (fun other _hOther => hPointwise other)]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp [hZero]

/-- The unnormalized vertices resolve the identity on the carrier. -/
theorem sheetVertex_tightFrame {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (state : ZeroSumCarrier S) :
    ∑ sheet, carrierRankOne (sheetVertex hCard sheet) state = state := by
  simp_rw [carrierRankOne_apply,
    zeroSumCarrierInner_sheetVertex hCard state]
  exact sheetVertex_reconstruction hCard state

/-- Operator form of the Parseval frame identity. -/
theorem sum_sheetVertex_projector_eq_id {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3) :
    ∑ sheet, carrierRankOne (sheetVertex hCard sheet) =
      LinearMap.id := by
  apply LinearMap.ext
  intro state
  simpa using sheetVertex_tightFrame hCard state

/-- Projector onto a normalized canonical sheet direction. -/
def normalizedSheetProjector {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (sheet : S) : Module.End ℂ (ZeroSumCarrier S) :=
  carrierRankOne (normalizedSheetVertex hCard sheet)

theorem zeroSumCarrierInner_normalizedSheetVertex {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (state : ZeroSumCarrier S) (sheet : S) :
    zeroSumCarrierInner state (normalizedSheetVertex hCard sheet) =
      (sheetVertexNormalization : ℂ) * state.1 sheet := by
  rw [normalizedSheetVertex,
    zeroSumCarrierInner_smul_right_real,
    zeroSumCarrierInner_sheetVertex]

/-- The normalized vertices form a tight frame with frame constant `3/2`. -/
theorem normalizedSheetVertex_tightFrame {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (state : ZeroSumCarrier S) :
    ∑ sheet, normalizedSheetProjector hCard sheet state =
      (3 / 2 : ℂ) • state := by
  have hSquareComplex : ((sheetVertexNormalization : ℂ) ^ 2) = 3 / 2 := by
    calc
      ((sheetVertexNormalization : ℂ) ^ 2) =
          ((sheetVertexNormalization ^ 2 : ℝ) : ℂ) := by norm_num
      _ = (((3 / 2 : ℝ)) : ℂ) := by rw [sheetVertexNormalization_sq]
      _ = 3 / 2 := by norm_num
  simp_rw [normalizedSheetProjector, carrierRankOne_apply,
    zeroSumCarrierInner_normalizedSheetVertex,
    normalizedSheetVertex, smul_smul]
  have hProduct : (sheetVertexNormalization : ℂ) *
      (sheetVertexNormalization : ℂ) = 3 / 2 := by
    simpa [pow_two] using hSquareComplex
  calc
    (∑ sheet, (sheetVertexNormalization * state.1 sheet *
        sheetVertexNormalization) • sheetVertex hCard sheet) =
        (3 / 2 : ℂ) •
          ∑ sheet, state.1 sheet • sheetVertex hCard sheet := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro sheet _hSheet
      rw [show (sheetVertexNormalization : ℂ) * state.1 sheet *
          (sheetVertexNormalization : ℂ) =
            ((sheetVertexNormalization : ℂ) *
              (sheetVertexNormalization : ℂ)) * state.1 sheet by ring,
        hProduct, SemigroupAction.mul_smul]
    _ = (3 / 2 : ℂ) • state := by
      rw [sheetVertex_reconstruction]

theorem sum_normalizedSheetProjector {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3) :
    ∑ sheet, normalizedSheetProjector hCard sheet =
      (3 / 2 : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro state
  simpa using normalizedSheetVertex_tightFrame hCard state

/-! ## 3. Canonical unlabeled state and symmetric measurement -/

/-- Uniform mixture over the three marked-sheet pure states. -/
def unlabeledSheetDensity {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3) :
    Module.End ℂ (ZeroSumCarrier S) :=
  (1 / 3 : ℂ) • ∑ sheet, normalizedSheetProjector hCard sheet

/-- The canonical unlabeled state is exactly the maximally mixed half-identity. -/
theorem unlabeledSheetDensity_eq_half_id {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3) :
    unlabeledSheetDensity hCard = (1 / 2 : ℂ) • LinearMap.id := by
  rw [unlabeledSheetDensity, sum_normalizedSheetProjector]
  apply LinearMap.ext
  intro state
  simp
  module

/-- Canonical three-outcome symmetric effect associated with sheet `s`. -/
def sheetPOVMEffect {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (sheet : S) : Module.End ℂ (ZeroSumCarrier S) :=
  (2 / 3 : ℂ) • normalizedSheetProjector hCard sheet

/-- The three sheet effects resolve the identity. -/
theorem sum_sheetPOVMEffect_eq_id {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3) :
    ∑ sheet, sheetPOVMEffect hCard sheet = LinearMap.id := by
  rw [show (∑ sheet, sheetPOVMEffect hCard sheet) =
      (2 / 3 : ℂ) • ∑ sheet, normalizedSheetProjector hCard sheet by
    simp [sheetPOVMEffect, Finset.smul_sum]]
  rw [sum_normalizedSheetProjector]
  apply LinearMap.ext
  intro state
  simp
  module

#print axioms sum_sheetVertex_projector_eq_id
#print axioms sum_normalizedSheetProjector
#print axioms unlabeledSheetDensity_eq_half_id
#print axioms sum_sheetPOVMEffect_eq_id

/-! ## 4. Full sheet symmetry rigidifies linear evolution -/

/-- The standard carrier of an abstract three-sheet set, in a fixed `Fin 3`
coordinate chart used only for the elementary commutant calculation. -/
abbrev FinThreeCarrier := ZeroSumCarrier (Fin 3)

abbrev FinThreeCarrierEnd := Module.End ℂ FinThreeCarrier

theorem finThree_card : Fintype.card (Fin 3) = 3 := by simp

/-- An endomorphism is fully sheet-symmetric when it intertwines every
permutation of the three sheets. -/
def CommutesWithFinThreeSheetPermutations
    (operator : FinThreeCarrierEnd) : Prop :=
  ∀ relabeling : Equiv.Perm (Fin 3), ∀ state : FinThreeCarrier,
    operator (transportZeroSumCarrier relabeling state) =
      transportZeroSumCarrier relabeling (operator state)

theorem transport_finThree_sheetVertex
    (relabeling : Equiv.Perm (Fin 3)) (sheet : Fin 3) :
    transportZeroSumCarrier relabeling
        (sheetVertex finThree_card sheet) =
      sheetVertex finThree_card (relabeling sheet) := by
  simpa only using transport_sheetVertex relabeling finThree_card sheet

/-- The line through the vertex at sheet zero is exactly the subspace fixed
by swapping the other two sheets. -/
theorem fixed_by_swap_one_two_is_vertex_zero_line
    (state : FinThreeCarrier)
    (hFixed : transportZeroSumCarrier (Equiv.swap (1 : Fin 3) 2) state =
      state) :
    state = ((3 / 2 : ℂ) * state.1 0) •
      sheetVertex finThree_card (0 : Fin 3) := by
  have hOneTwo : state.1 1 = state.1 2 := by
    have hCoordinate := congrArg (fun value : FinThreeCarrier => value.1 1)
      hFixed
    simpa [transportZeroSumCarrier, Equiv.swap_apply_def] using hCoordinate.symm
  have hZeroSum : state.1 0 + state.1 1 + state.1 2 = 0 := by
    simpa [Fin.sum_univ_three] using
      (zeroSumCarrier_mem_iff state.1).1 state.2
  apply Subtype.ext
  funext sheet
  fin_cases sheet
  · change state.1 0 = ((3 / 2 : ℂ) * state.1 0) *
        (sheetVertex finThree_card (0 : Fin 3)).1 0
    rw [sheetVertex_apply_self]
    ring
  · change state.1 1 = ((3 / 2 : ℂ) * state.1 0) *
        (sheetVertex finThree_card (0 : Fin 3)).1 1
    rw [sheetVertex_apply_ne finThree_card (sheet := (0 : Fin 3))
      (other := (1 : Fin 3)) (by decide)]
    linear_combination (1 / 2 : ℂ) * hZeroSum + (1 / 2 : ℂ) * hOneTwo
  · change state.1 2 = ((3 / 2 : ℂ) * state.1 0) *
        (sheetVertex finThree_card (0 : Fin 3)).1 2
    rw [sheetVertex_apply_ne finThree_card (sheet := (0 : Fin 3))
      (other := (2 : Fin 3)) (by decide)]
    linear_combination (1 / 2 : ℂ) * hZeroSum - (1 / 2 : ℂ) * hOneTwo

/-- Elementary Schur rigidity for the standard three-sheet representation:
every linear endomorphism commuting with all sheet permutations is scalar.

This is proved directly, without importing representation-theory
classification. -/
theorem finThreeCarrier_commutant_is_scalar
    (operator : FinThreeCarrierEnd)
    (hCommutes : CommutesWithFinThreeSheetPermutations operator) :
    ∃ scalar : ℂ, operator = scalar • LinearMap.id := by
  let vertexZero : FinThreeCarrier := sheetVertex finThree_card 0
  let scalar : ℂ := (3 / 2 : ℂ) * (operator vertexZero).1 0
  have hVertexZeroFixed :
      transportZeroSumCarrier (Equiv.swap (1 : Fin 3) 2) vertexZero =
        vertexZero := by
    rw [transport_finThree_sheetVertex]
    rfl
  have hImageFixed :
      transportZeroSumCarrier (Equiv.swap (1 : Fin 3) 2)
          (operator vertexZero) = operator vertexZero := by
    rw [← hCommutes (Equiv.swap (1 : Fin 3) 2) vertexZero,
      hVertexZeroFixed]
  have hZeroImage : operator vertexZero = scalar • vertexZero := by
    exact fixed_by_swap_one_two_is_vertex_zero_line
      (operator vertexZero) hImageFixed
  have hEveryVertex (sheet : Fin 3) :
      operator (sheetVertex finThree_card sheet) =
        scalar • sheetVertex finThree_card sheet := by
    let relabeling : Equiv.Perm (Fin 3) := Equiv.swap 0 sheet
    have hMovesZero : relabeling 0 = sheet := by
      simp [relabeling]
    have hTransport : transportZeroSumCarrier relabeling vertexZero =
        sheetVertex finThree_card sheet := by
      rw [transport_finThree_sheetVertex]
      rw [hMovesZero]
    calc
      operator (sheetVertex finThree_card sheet) =
          operator (transportZeroSumCarrier relabeling vertexZero) := by
            rw [hTransport]
      _ = transportZeroSumCarrier relabeling (operator vertexZero) :=
        hCommutes relabeling vertexZero
      _ = transportZeroSumCarrier relabeling (scalar • vertexZero) := by
        rw [hZeroImage]
      _ = scalar • transportZeroSumCarrier relabeling vertexZero := by
        exact (transportZeroSumCarrier relabeling).map_smul scalar vertexZero
      _ = scalar • sheetVertex finThree_card sheet := by rw [hTransport]
  refine ⟨scalar, ?_⟩
  apply LinearMap.ext
  intro state
  calc
    operator state = operator
        (∑ sheet, state.1 sheet • sheetVertex finThree_card sheet) := by
      rw [sheetVertex_reconstruction]
    _ = ∑ sheet, state.1 sheet •
        operator (sheetVertex finThree_card sheet) := by
      simp only [map_sum, map_smul]
    _ = ∑ sheet, state.1 sheet •
        (scalar • sheetVertex finThree_card sheet) := by
      apply Finset.sum_congr rfl
      intro sheet _hSheet
      rw [hEveryVertex]
    _ = scalar • ∑ sheet,
        state.1 sheet • sheetVertex finThree_card sheet := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro sheet _hSheet
      module
    _ = scalar • state := by rw [sheetVertex_reconstruction]
    _ = (scalar • LinearMap.id) state := by simp

/-! ## 5. The unique fully symmetric normalized operator -/

/-- Trace reconstructed from the intrinsic normalized tight frame.  The
factor `2/3` compensates for its frame constant. -/
def finThreeFrameTrace (operator : FinThreeCarrierEnd) : ℂ :=
  (2 / 3 : ℂ) * ∑ sheet : Fin 3,
    zeroSumCarrierInner
      (operator (normalizedSheetVertex finThree_card sheet))
      (normalizedSheetVertex finThree_card sheet)

theorem finThreeFrameTrace_scalar_id (scalar : ℂ) :
    finThreeFrameTrace (scalar • LinearMap.id) = 2 * scalar := by
  unfold finThreeFrameTrace
  simp only [LinearMap.smul_apply, LinearMap.id_apply,
    zeroSumCarrierInner_smul_left,
    normalizedSheetVertex_inner, if_pos]
  norm_num [Fin.sum_univ_three]
  ring

theorem unlabeledSheetDensity_finThree_frameTrace :
    finThreeFrameTrace (unlabeledSheetDensity finThree_card) = 1 := by
  rw [unlabeledSheetDensity_eq_half_id,
    finThreeFrameTrace_scalar_id]
  norm_num

theorem unlabeledSheetDensity_finThree_commutes :
    CommutesWithFinThreeSheetPermutations
      (unlabeledSheetDensity finThree_card) := by
  rw [unlabeledSheetDensity_eq_half_id]
  intro relabeling state
  simp

/-- Quadratic-form positivity in the carrier's linear-first Hermitian
convention. -/
def CarrierOperatorNonnegative {S : Type u} [Fintype S]
    (operator : Module.End ℂ (ZeroSumCarrier S)) : Prop :=
  ∀ state : ZeroSumCarrier S,
    0 ≤ (zeroSumCarrierInner (operator state) state).re

theorem carrierRankOne_nonnegative {S : Type u} [Fintype S]
    (vector : ZeroSumCarrier S) :
    CarrierOperatorNonnegative (carrierRankOne vector) := by
  intro state
  rw [carrierRankOne_apply, zeroSumCarrierInner_smul_left,
    zeroSumCarrierInner_conj_symm]
  let amplitude : ℂ := zeroSumCarrierInner vector state
  change 0 ≤ (star amplitude * amplitude).re
  have hNorm : star amplitude * amplitude =
      ((Complex.normSq amplitude : ℝ) : ℂ) := by
    rw [mul_comm]
    convert Complex.mul_conj amplitude using 1
  rw [hNorm]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg amplitude

theorem sheetPOVMEffect_nonnegative {S : Type u}
    [Fintype S] [DecidableEq S] (hCard : Fintype.card S = 3)
    (sheet : S) :
    CarrierOperatorNonnegative (sheetPOVMEffect hCard sheet) := by
  intro state
  unfold sheetPOVMEffect
  simp only [LinearMap.smul_apply]
  rw [zeroSumCarrierInner_smul_left]
  norm_num [Complex.mul_re]
  exact carrierRankOne_nonnegative
    (normalizedSheetVertex hCard sheet) state

theorem zeroSumCarrierInner_self_eq_normSq_sum
    (state : FinThreeCarrier) :
    zeroSumCarrierInner state state =
      ((∑ sheet : Fin 3, Complex.normSq (state.1 sheet) : ℝ) : ℂ) := by
  unfold zeroSumCarrierInner
  calc
    (∑ sheet, state.1 sheet * star (state.1 sheet)) =
        ∑ sheet, ((Complex.normSq (state.1 sheet) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro sheet _hSheet
      convert Complex.mul_conj (state.1 sheet) using 1
    _ = ((∑ sheet, Complex.normSq (state.1 sheet) : ℝ) : ℂ) := by
      simp

/-- The canonical unlabeled operator is positive as well as normalized. -/
theorem unlabeledSheetDensity_finThree_nonnegative :
    CarrierOperatorNonnegative (unlabeledSheetDensity finThree_card) := by
  intro state
  rw [unlabeledSheetDensity_eq_half_id]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [zeroSumCarrierInner_smul_left,
    zeroSumCarrierInner_self_eq_normSq_sum]
  have hSum : 0 ≤ ∑ sheet : Fin 3, Complex.normSq (state.1 sheet) :=
    Finset.sum_nonneg fun sheet _hSheet => Complex.normSq_nonneg _
  norm_num [Complex.mul_re]
  exact hSum

/-- The maximally mixed state is unique: any unit-frame-trace operator that
commutes with every sheet permutation equals the uniform vertex mixture.

Positivity is deliberately not needed for the uniqueness argument, so the
statement applies in particular to every normalized invariant density
operator. -/
theorem invariant_frameTrace_one_eq_unlabeledSheetDensity
    (operator : FinThreeCarrierEnd)
    (hCommutes : CommutesWithFinThreeSheetPermutations operator)
    (hTrace : finThreeFrameTrace operator = 1) :
    operator = unlabeledSheetDensity finThree_card := by
  obtain ⟨scalar, hScalar⟩ :=
    finThreeCarrier_commutant_is_scalar operator hCommutes
  have hScalarValue : scalar = 1 / 2 := by
    rw [hScalar, finThreeFrameTrace_scalar_id] at hTrace
    linear_combination (1 / 2 : ℂ) * hTrace
  rw [hScalar, hScalarValue, unlabeledSheetDensity_eq_half_id]

/-! ## 6. Global sheet choices and monodromy obstruction -/

universe w

/-- Abstract monodromy data for a family of sheet sets.  Only loop transport
is retained because that is all that is needed to state the obstruction to a
global deterministic sheet marking. -/
structure SheetMonodromyData (Base : Type u) where
  Sheet : Base → Type v
  Loop : Base → Type w
  monodromy : ∀ base, Loop base → Equiv.Perm (Sheet base)

/-- A transported deterministic sheet choice: one sheet in every fiber,
compatible with transport around every loop.  This is the section condition
for the sheet local system at the level relevant to monodromy. -/
structure TransportedSheetSection {Base : Type u}
    (system : SheetMonodromyData Base) where
  choice : ∀ base, system.Sheet base
  loop_compatible : ∀ base (loop : system.Loop base),
    system.monodromy base loop (choice base) = choice base

/-- Every loop monodromy must fix the sheet selected by a transported global
section. -/
theorem globalSheetSection_forces_monodromy_fixed
    {Base : Type u} {system : SheetMonodromyData Base}
    (sheetSection : TransportedSheetSection system)
    (base : Base) (loop : system.Loop base) :
    system.monodromy base loop (sheetSection.choice base) =
      sheetSection.choice base :=
  sheetSection.loop_compatible base loop

/-- A single fixed-point-free monodromy loop is an exact obstruction to a
global deterministic sheet choice.  Notice the deliberately sharp premise:
a merely nonidentity permutation need not be fixed-point-free. -/
theorem fixedPointFree_monodromy_no_globalSheetSection
    {Base : Type u} {system : SheetMonodromyData Base}
    (base : Base) (loop : system.Loop base)
    (hFixedPointFree : ∀ sheet : system.Sheet base,
      system.monodromy base loop sheet ≠ sheet) :
    ¬ Nonempty (TransportedSheetSection system) := by
  rintro ⟨sheetSection⟩
  exact hFixedPointFree (sheetSection.choice base)
    (globalSheetSection_forces_monodromy_fixed sheetSection base loop)

#print axioms finThreeCarrier_commutant_is_scalar
#print axioms unlabeledSheetDensity_finThree_nonnegative
#print axioms sheetPOVMEffect_nonnegative
#print axioms invariant_frameTrace_one_eq_unlabeledSheetDensity
#print axioms fixedPointFree_monodromy_no_globalSheetSection

end

end UnifiedTheory.Audit.KFCubicSheetFrameRigidity
