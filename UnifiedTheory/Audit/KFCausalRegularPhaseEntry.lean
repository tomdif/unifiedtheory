/-
  Audit/KFCausalRegularPhaseEntry.lean

  PHYSICAL ENTRY INTO THE THREE-DIRECTION REGULAR PHASE

  The determinant-sheet law cannot exist at every causal-growth rank, but
  physical maximal-element growth can reach its Boolean three-cube seed.  We
  enumerate the eight cube cells by their three-bit masks.  Prefixes of this
  enumeration are causal orders and every successive prefix is a genuine
  one-element maximal extension.  The rank-eight prefix is order-isomorphic
  to the Boolean tangent cube and therefore carries exactly three intrinsic
  diamond directions.

  Cardinality also proves that rank eight is the unique rank at which the
  complete causal order itself can be the elementary Boolean cube.  But
  sequential growth never rewrites relations among old events, so the cube
  persists as an embedded protected suborder through every later physical
  birth.  This is the precise local meaning in which the regular phase can
  remain after its onset.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularPhaseEntry

noncomputable section

open UnifiedTheory.Audit.KFCausalProduct3SheetBridge
open UnifiedTheory.Audit.KFCausalDiamondDirectionCover
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary

/-! ## 1. Binary enumeration of the Boolean cube -/

/-- The three-bit mask of an index below eight, regarded as a Boolean-cube
cell. -/
def cubeBitset (index : Fin 8) : TangentCube3 :=
  {direction | Nat.testBit index.val direction.val = true}

theorem cubeBitset_injective : Function.Injective cubeBitset := by
  intro first second hEqual
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hBit : bit < 3
  · have hAt := Set.ext_iff.mp hEqual ⟨bit, hBit⟩
    simpa [cubeBitset] using hAt
  · have hThreeLe : 3 ≤ bit := by omega
    have hEightLe : 8 ≤ 2 ^ bit := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ bit := Nat.pow_le_pow_right (by omega) hThreeLe
    rw [Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le first.isLt hEightLe),
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le second.isLt hEightLe)]

theorem cubeBitset_bijective : Function.Bijective cubeBitset := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨cubeBitset_injective, ?_⟩
  simp [TangentCube3]

/-- Binary masks give a canonical equivalence between eight birth slots and
the eight cells of the Boolean tangent cube. -/
def cubeBitsetEquiv : Fin 8 ≃ TangentCube3 :=
  Equiv.ofBijective cubeBitset cubeBitset_bijective

@[simp]
theorem cubeBitsetEquiv_apply (index : Fin 8) :
    cubeBitsetEquiv index = cubeBitset index := rfl

/-- Embed a prefix slot into the full eight-cell enumeration. -/
def cubePrefixIndex {n : ℕ} (h : n ≤ 8) (index : Fin n) : Fin 8 :=
  ⟨index.val, lt_of_lt_of_le index.isLt h⟩

/-- The causal order on the first `n` binary masks. -/
def cubePrefixOrder (n : ℕ) (h : n ≤ 8) : CardinalCausalOrder n where
  rel first second := decide
    (cubeBitset (cubePrefixIndex h first) ⊆
      cubeBitset (cubePrefixIndex h second))
  refl := by
    intro index
    simp
  antisymm := by
    intro first second hFirstSecond hSecondFirst
    have hFirstSecond' :
        cubeBitset (cubePrefixIndex h first) ⊆
          cubeBitset (cubePrefixIndex h second) := by
      exact of_decide_eq_true hFirstSecond
    have hSecondFirst' :
        cubeBitset (cubePrefixIndex h second) ⊆
          cubeBitset (cubePrefixIndex h first) := by
      exact of_decide_eq_true hSecondFirst
    have hMasks := Set.Subset.antisymm hFirstSecond' hSecondFirst'
    have hIndices := cubeBitset_injective hMasks
    apply Fin.ext
    exact congrArg (fun index : Fin 8 => index.val) hIndices
  trans := by
    intro first second third hFirstSecond hSecondThird
    apply decide_eq_true
    exact Set.Subset.trans (of_decide_eq_true hFirstSecond)
      (of_decide_eq_true hSecondThird)

/-- Bitwise subset implies ordinary numeric order for three-bit masks.  This
is what makes binary enumeration a topological birth order. -/
theorem cubeBitset_subset_implies_val_le
    {first second : Fin 8}
    (hSubset : cubeBitset first ⊆ cubeBitset second) :
    first.val ≤ second.val := by
  apply Nat.le_of_testBit
  intro bit hFirstBit
  by_cases hBit : bit < 3
  · have hMember : ⟨bit, hBit⟩ ∈ cubeBitset first := by
      simpa [cubeBitset] using hFirstBit
    have hSecondMember := hSubset hMember
    simpa [cubeBitset] using hSecondMember
  · have hThreeLe : 3 ≤ bit := by omega
    have hEightLe : 8 ≤ 2 ^ bit := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ bit := Nat.pow_le_pow_right (by omega) hThreeLe
    have hFalse := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le first.isLt hEightLe)
    rw [hFalse] at hFirstBit
    contradiction

/-! ## 2. Every prefix step is a physical maximal birth -/

theorem cubePrefixOrder_oneElementExtension
    (n : ℕ) (h : n < 8) :
    IsLabeledOneElementExtension
      (cubePrefixOrder n (Nat.le_of_lt h))
      (cubePrefixOrder (n + 1) h) := by
  constructor
  · intro first second
    change decide
        (cubeBitset
            (cubePrefixIndex (Nat.le_of_lt h) first) ⊆
          cubeBitset
            (cubePrefixIndex (Nat.le_of_lt h) second)) =
      decide
        (cubeBitset (cubePrefixIndex h first.castSucc) ⊆
          cubeBitset (cubePrefixIndex h second.castSucc))
    congr 2
  · intro old
    change decide
      (cubeBitset (cubePrefixIndex h (Fin.last n)) ⊆
        cubeBitset (cubePrefixIndex h old.castSucc)) = false
    apply decide_eq_false
    intro hSubset
    have hNumeric := cubeBitset_subset_implies_val_le hSubset
    simp [cubePrefixIndex] at hNumeric
    omega

/-- The prefix transition descends to a physical unlabeled growth edge. -/
theorem cubePrefixOrder_unlabeledExtension
    (n : ℕ) (h : n < 8) :
    IsUnlabeledOneElementExtension
      (Quotient.mk _ (cubePrefixOrder n (Nat.le_of_lt h)))
      (Quotient.mk _ (cubePrefixOrder (n + 1) h)) := by
  exact isUnlabeledOneElementExtension_mk
    (cubePrefixOrder_oneElementExtension n h)

/-! ## 3. The physical rank-eight endpoint is exactly the regular cube -/

/-- At rank eight the prefix enumeration is order-isomorphic to the Boolean
tangent cube. -/
def cubePrefixEightOrderIso :
    CausalOrderPoint (cubePrefixOrder 8 (by omega)) ≃o TangentCube3 where
  toEquiv := cubeBitsetEquiv
  map_rel_iff' := by
    intro first second
    change (cubeBitset first ⊆ cubeBitset second) ↔
      decide (cubeBitset first ⊆ cubeBitset second) = true
    exact decide_eq_true_iff.symm

/-- The physical rank-eight representative therefore has exactly three
intrinsic diamond directions. -/
theorem cubePrefixEight_supportsThreeIntrinsicDirections :
    SupportsThreeIntrinsicDirections
      (CausalOrderPoint (cubePrefixOrder 8 (by omega))) := by
  exact ⟨(transportLocalCausalDirection cubePrefixEightOrderIso).trans
    cubeLocalDirectionEquivFin3⟩

/-- Being the complete elementary Boolean cube fixes the causal-set rank to
eight. -/
def IsExactBooleanCubePhase {n : ℕ} (P : CardinalCausalOrder n) : Prop :=
  Nonempty (CausalOrderPoint P ≃o TangentCube3)

instance causalOrderPointFintype {n : ℕ} (P : CardinalCausalOrder n) :
    Fintype (CausalOrderPoint P) :=
  inferInstanceAs (Fintype (Fin n))

theorem exactBooleanCubePhase_rank_eq_eight {n : ℕ}
    (P : CardinalCausalOrder n) (hCube : IsExactBooleanCubePhase P) :
    n = 8 := by
  rcases hCube with ⟨equiv⟩
  have hCard := Fintype.card_congr equiv.toEquiv
  simpa [CausalOrderPoint, TangentCube3] using hCard

/-- One more physical birth cannot preserve the *complete-causet* exact-cube
property.  The determinant phase must persist locally, not by freezing the
entire universe at eight events. -/
theorem exactBooleanCubePhase_not_preserved_by_one_birth
    (child : CardinalCausalOrder 9) :
    ¬ IsExactBooleanCubePhase child := by
  intro hCube
  have hRank := exactBooleanCubePhase_rank_eq_eight child hCube
  omega

/-! ## 4. The regular seed persists inside every later causet -/

/-- A causal order contains the exact Boolean cube as a labeled embedded
suborder.  No claim is made that the remaining events are themselves regular. -/
def ContainsBooleanCubeSeed {n : ℕ} (P : CardinalCausalOrder n) : Prop :=
  ∃ embedding : Fin 8 ↪ Fin n,
    ∀ first second,
      P.rel (embedding first) (embedding second) =
        (cubePrefixOrder 8 (by omega)).rel first second

/-- At onset, the complete rank-eight causet is its own embedded seed. -/
theorem cubePrefixEight_containsBooleanCubeSeed :
    ContainsBooleanCubeSeed (cubePrefixOrder 8 (by omega)) := by
  refine ⟨Function.Embedding.refl (Fin 8), ?_⟩
  intro first second
  rfl

/-- Every physical maximal-element birth preserves every already embedded
Boolean seed, because the transition law preserves all old relations. -/
theorem oneElementExtension_preservesBooleanCubeSeed
    {n : ℕ} {parent : CardinalCausalOrder n}
    {child : CardinalCausalOrder (n + 1)}
    (hExtension : IsLabeledOneElementExtension parent child)
    (hSeed : ContainsBooleanCubeSeed parent) :
    ContainsBooleanCubeSeed child := by
  rcases hSeed with ⟨embedding, hEmbedding⟩
  let liftedEmbedding : Fin 8 ↪ Fin (n + 1) :=
    { toFun := fun index => (embedding index).castSucc
      inj' := by
        intro first second hEqual
        apply embedding.injective
        apply Fin.ext
        exact congrArg (fun index : Fin (n + 1) => index.val) hEqual }
  refine ⟨liftedEmbedding, ?_⟩
  intro first second
  exact (hExtension.1 (embedding first) (embedding second)).trans
    (hEmbedding first second)

/-- In particular, *every* physical birth out of the rank-eight onset causet
retains an exact embedded regular seed, even though the nine-event child is no
longer globally the cube. -/
theorem every_birth_after_rankEight_preserves_regularSeed
    (child : CardinalCausalOrder 9)
    (hExtension : IsLabeledOneElementExtension
      (cubePrefixOrder 8 (by omega)) child) :
    ContainsBooleanCubeSeed child :=
  oneElementExtension_preservesBooleanCubeSeed hExtension
    cubePrefixEight_containsBooleanCubeSeed

/-- **Physical onset capstone.** There is a chain of genuine physical prefix
births from every rank below eight to the next, and its rank-eight endpoint is
the exact three-direction Boolean seed. -/
theorem physicalGrowth_enters_threeDirectionPhase_at_rankEight :
    (∀ n : ℕ, (h : n < 8) →
      IsUnlabeledOneElementExtension
        (Quotient.mk _ (cubePrefixOrder n (Nat.le_of_lt h)))
        (Quotient.mk _ (cubePrefixOrder (n + 1) h)))
      ∧ IsExactBooleanCubePhase (cubePrefixOrder 8 (by omega))
      ∧ ContainsBooleanCubeSeed (cubePrefixOrder 8 (by omega))
      ∧ SupportsThreeIntrinsicDirections
        (CausalOrderPoint (cubePrefixOrder 8 (by omega))) := by
  exact ⟨cubePrefixOrder_unlabeledExtension,
    ⟨cubePrefixEightOrderIso⟩,
    cubePrefixEight_containsBooleanCubeSeed,
    cubePrefixEight_supportsThreeIntrinsicDirections⟩

#print axioms cubePrefixOrder_oneElementExtension
#print axioms cubePrefixEight_supportsThreeIntrinsicDirections
#print axioms exactBooleanCubePhase_rank_eq_eight
#print axioms exactBooleanCubePhase_not_preserved_by_one_birth
#print axioms oneElementExtension_preservesBooleanCubeSeed
#print axioms every_birth_after_rankEight_preserves_regularSeed
#print axioms physicalGrowth_enters_threeDirectionPhase_at_rankEight

end

end UnifiedTheory.Audit.KFCausalRegularPhaseEntry
