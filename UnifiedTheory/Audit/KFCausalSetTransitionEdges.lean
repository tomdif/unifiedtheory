/-
  Audit/KFCausalSetTransitionEdges.lean

  COMPLETE RIDEOUT--SORKIN TRANSITION-EDGE KINEMATICS

  The vertices of sequential growth are unlabeled finite causal sets, but the
  original Rideout--Sorkin Markov sum deliberately counts distinct precursor
  sets of a labeled representative as distinct transition slots, even when an
  automorphism of the parent relates them.  Consequently the correct object
  is not merely the set of unlabeled children and it is not a quotient of
  precursor sets by parent automorphisms.

  This file formalizes the resulting two-level structure:

  * a transition slot is a downward-closed precursor set in a labeled parent;
  * adjoining a new maximal event constructs its child causal order;
  * parent relabelings act bijectively on slots and preserve their targets;
  * an unlabeled link is a physical parent-child pair;
  * its Rideout--Sorkin multiplicity is the cardinality of the target fiber;
  * that multiplicity is independent of every chosen representative;
  * the multiplicity-weighted sum over unlabeled children is exactly the raw
    sum over distinct precursor transition slots.

  Thus covariance lives on the vertices and amplitudes, while the Markov sum
  retains the distinguishability convention used in the classical theorem.
-/

import UnifiedTheory.Audit.KFCausalSetSequentialGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetTransitionEdges

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth

/-! ## 1. Precursor transition slots -/

/-- A precursor is a past set of the parent: membership is downward closed
under the causal order.  Boolean membership keeps the type finite without
adding any ambient-space structure. -/
structure CausalPastSet {n : ℕ} (parent : CardinalCausalOrder n) where
  mem : Fin n → Bool
  downwardClosed : ∀ x y : Fin n,
    mem x = true → parent.rel y x = true → mem y = true

@[ext]
theorem CausalPastSet.ext {n : ℕ} {parent : CardinalCausalOrder n}
    {first second : CausalPastSet parent}
    (hMem : first.mem = second.mem) : first = second := by
  cases first
  cases second
  cases hMem
  rfl

instance causalPastSetFinite {n : ℕ} (parent : CardinalCausalOrder n) :
    Finite (CausalPastSet parent) := by
  let encode : CausalPastSet parent → (Fin n → Bool) := CausalPastSet.mem
  exact Finite.of_injective encode (fun _ _ h => CausalPastSet.ext h)

noncomputable instance causalPastSetFintype {n : ℕ}
    (parent : CardinalCausalOrder n) : Fintype (CausalPastSet parent) :=
  Fintype.ofFinite _

noncomputable instance causalPastSetDecidableEq {n : ℕ}
    (parent : CardinalCausalOrder n) : DecidableEq (CausalPastSet parent) :=
  Classical.decEq _

/-- The empty past set gives the gregarious birth. -/
def emptyCausalPastSet {n : ℕ}
    (parent : CardinalCausalOrder n) : CausalPastSet parent where
  mem := fun _ => false
  downwardClosed := by simp

/-- The full parent gives the timid birth. -/
def fullCausalPastSet {n : ℕ}
    (parent : CardinalCausalOrder n) : CausalPastSet parent where
  mem := fun _ => true
  downwardClosed := by simp

/-- The number of ancestors in a transition precursor (`omega` in the
Rideout--Sorkin notation). -/
def CausalPastSet.ancestorCount {n : ℕ} {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) : ℕ :=
  Nat.card {i : Fin n // past.mem i = true}

/-- Maximality internal to a precursor. -/
def CausalPastSet.IsMaximal {n : ℕ} {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) (i : Fin n) : Prop :=
  past.mem i = true ∧
    ∀ j : Fin n, past.mem j = true → parent.rel i j = true → j = i

/-- The number of maximal precursor elements (`m` in the
Rideout--Sorkin notation). -/
def CausalPastSet.maximalCount {n : ℕ} {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) : ℕ :=
  Nat.card {i : Fin n // past.IsMaximal i}

/-! ## 2. Relabeling covariance of precursor slots -/

/-- Transport a precursor along a certified parent order isomorphism. -/
def CausalPastSet.relabel {n : ℕ} {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j))
    (past : CausalPastSet parent) : CausalPastSet parent' where
  mem := fun i => past.mem (equivalence.symm i)
  downwardClosed := by
    intro x y hx hyx
    apply past.downwardClosed (equivalence.symm x) (equivalence.symm y) hx
    have hTransport := hRel (equivalence.symm y) (equivalence.symm x)
    have hTransport' :
        parent.rel (equivalence.symm y) (equivalence.symm x) =
          parent'.rel y x := by
      simpa using hTransport
    exact hTransport'.trans hyx

/-- Relabeling is a bijection of the complete finite precursor alphabets. -/
def causalPastSetEquivOfIsomorphism {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j)) :
    CausalPastSet parent ≃ CausalPastSet parent' where
  toFun := CausalPastSet.relabel equivalence hRel
  invFun := CausalPastSet.relabel equivalence.symm (by
    intro i j
    simpa using (hRel (equivalence.symm i) (equivalence.symm j)).symm)
  left_inv := by
    intro past
    ext i
    simp [CausalPastSet.relabel]
  right_inv := by
    intro past
    ext i
    simp [CausalPastSet.relabel]

theorem causalPastSet_relabel_ancestorCount {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j))
    (past : CausalPastSet parent) :
    (past.relabel equivalence hRel).ancestorCount = past.ancestorCount := by
  let coordinateEquiv :
      {i : Fin n // past.mem i = true} ≃
        {i : Fin n // (past.relabel equivalence hRel).mem i = true} := {
    toFun i := ⟨equivalence i, by
      simpa [CausalPastSet.relabel] using i.property⟩
    invFun i := ⟨equivalence.symm i, by
      simpa [CausalPastSet.relabel] using i.property⟩
    left_inv := by intro i; apply Subtype.ext; simp
    right_inv := by intro i; apply Subtype.ext; simp }
  exact (Nat.card_congr coordinateEquiv).symm

theorem causalPastSet_relabel_isMaximal_iff {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j))
    (past : CausalPastSet parent) (i : Fin n) :
    (past.relabel equivalence hRel).IsMaximal (equivalence i) ↔
      past.IsMaximal i := by
  constructor
  · rintro ⟨hi, hMax⟩
    refine ⟨by simpa [CausalPastSet.relabel] using hi, ?_⟩
    intro j hj hij
    have hj' : (past.relabel equivalence hRel).mem (equivalence j) = true := by
      simpa [CausalPastSet.relabel] using hj
    have hij' : parent'.rel (equivalence i) (equivalence j) = true := by
      simpa [hRel i j] using hij
    exact equivalence.injective (hMax (equivalence j) hj' hij')
  · rintro ⟨hi, hMax⟩
    refine ⟨by simpa [CausalPastSet.relabel] using hi, ?_⟩
    intro j hj hij
    apply equivalence.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply hMax (equivalence.symm j)
    · simpa [CausalPastSet.relabel] using hj
    · have hTransport := hRel i (equivalence.symm j)
      have hTransport' :
          parent.rel i (equivalence.symm j) =
            parent'.rel (equivalence i) j := by
        simpa using hTransport
      exact hTransport'.trans hij

theorem causalPastSet_relabel_maximalCount {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j))
    (past : CausalPastSet parent) :
    (past.relabel equivalence hRel).maximalCount = past.maximalCount := by
  let maximalEquiv :
      {i : Fin n // past.IsMaximal i} ≃
        {i : Fin n // (past.relabel equivalence hRel).IsMaximal i} := {
    toFun i := ⟨equivalence i,
      (causalPastSet_relabel_isMaximal_iff
        equivalence hRel past i).2 i.property⟩
    invFun i := ⟨equivalence.symm i,
      (causalPastSet_relabel_isMaximal_iff equivalence hRel past
        (equivalence.symm i)).1 (by simpa using i.property)⟩
    left_inv := by intro i; apply Subtype.ext; simp
    right_inv := by intro i; apply Subtype.ext; simp }
  exact (Nat.card_congr maximalEquiv).symm

/-! ## 3. The child generated by a precursor -/

/-- Relation obtained by adjoining one new maximal element whose complete
past is `past`. -/
def precursorExtensionRel {n : ℕ} (parent : CardinalCausalOrder n)
    (past : CausalPastSet parent) (i j : Fin n ⊕ Fin 1) : Bool :=
  match i, j with
  | Sum.inl a, Sum.inl b => parent.rel a b
  | Sum.inl a, Sum.inr _ => past.mem a
  | Sum.inr _, Sum.inl _ => false
  | Sum.inr _, Sum.inr _ => true

/-- The labeled child generated by one Rideout--Sorkin transition slot. -/
def precursorOneElementExtension {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    CardinalCausalOrder (n + 1) where
  rel := fun i j => precursorExtensionRel parent past
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  refl := by
    intro i
    cases hi : finSumFinEquiv.symm i <;>
      simp [precursorExtensionRel, parent.refl]
  antisymm := by
    intro i j hij hji
    apply finSumFinEquiv.symm.injective
    cases hi : finSumFinEquiv.symm i with
    | inl a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b =>
            congr 1
            exact parent.antisymm a b
              (by simpa [precursorExtensionRel, hi, hj] using hij)
              (by simpa [precursorExtensionRel, hi, hj] using hji)
        | inr b => simp [precursorExtensionRel, hi, hj] at hji
    | inr a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b => simp [precursorExtensionRel, hi, hj] at hij
        | inr b =>
            congr 1
            exact Subsingleton.elim a b
  trans := by
    intro i j k hij hjk
    cases hi : finSumFinEquiv.symm i with
    | inl a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b =>
            cases hk : finSumFinEquiv.symm k with
            | inl c =>
                exact parent.trans a b c
                  (by simpa [precursorExtensionRel, hi, hj] using hij)
                  (by simpa [precursorExtensionRel, hj, hk] using hjk)
            | inr c =>
                apply past.downwardClosed b a
                · simpa [precursorExtensionRel, hj, hk] using hjk
                · simpa [precursorExtensionRel, hi, hj] using hij
        | inr b =>
            cases hk : finSumFinEquiv.symm k with
            | inl c => simp [precursorExtensionRel, hj, hk] at hjk
            | inr c => simpa [precursorExtensionRel, hi, hj, hk] using hij
    | inr a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b => simp [precursorExtensionRel, hi, hj] at hij
        | inr b =>
            cases hk : finSumFinEquiv.symm k with
            | inl c => simp [precursorExtensionRel, hj, hk] at hjk
            | inr c => simp [precursorExtensionRel]

theorem precursor_is_oneElementExtension {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    IsLabeledOneElementExtension parent
      (precursorOneElementExtension parent past) := by
  constructor
  · intro i j
    simp [precursorOneElementExtension, precursorExtensionRel]
  · intro i
    simp [precursorOneElementExtension, precursorExtensionRel]

/-- Extend a permutation of the old events by fixing the newborn event. -/
def extendCausalPermutation {n : ℕ} (equivalence : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr equivalence (Equiv.refl (Fin 1))).trans finSumFinEquiv)

/-- Relabeling the parent and precursor relabels, but does not change, the
generated unlabeled child. -/
theorem precursorOneElementExtension_isomorphic_relabel {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j))
    (past : CausalPastSet parent) :
    CardinalCausalOrderIsomorphic
      (precursorOneElementExtension parent past)
      (precursorOneElementExtension parent'
        (past.relabel equivalence hRel)) := by
  refine ⟨extendCausalPermutation equivalence, ?_⟩
  intro i j
  cases hi : finSumFinEquiv.symm i with
  | inl a =>
      cases hj : finSumFinEquiv.symm j with
      | inl b => simp [precursorOneElementExtension, precursorExtensionRel,
          extendCausalPermutation, hi, hj, hRel]
      | inr b => simp [precursorOneElementExtension, precursorExtensionRel,
          extendCausalPermutation, CausalPastSet.relabel, hi, hj]
  | inr a =>
      cases hj : finSumFinEquiv.symm j with
      | inl b => simp [precursorOneElementExtension, precursorExtensionRel,
          extendCausalPermutation, hi, hj]
      | inr b => simp [precursorOneElementExtension, precursorExtensionRel,
          extendCausalPermutation, hi, hj]

/-! ## 4. Every physical birth is generated by a precursor -/

/-- Recover the complete precursor from an already-certified labeled maximal
birth. -/
def causalPastSetOfLabeledExtension {n : ℕ}
    (parent : CardinalCausalOrder n) (child : CardinalCausalOrder (n + 1))
    (hExtension : IsLabeledOneElementExtension parent child) :
    CausalPastSet parent where
  mem := fun i => child.rel i.castSucc (Fin.last n)
  downwardClosed := by
    intro x y hx hyx
    have hyxChild : child.rel y.castSucc x.castSucc = true :=
      (hExtension.1 y x).trans hyx
    exact child.trans y.castSucc x.castSucc (Fin.last n) hyxChild hx

/-- Precursor extraction is an exact inverse to constructing a certified
labeled birth. -/
theorem precursorOneElementExtension_recovers {n : ℕ}
    (parent : CardinalCausalOrder n) (child : CardinalCausalOrder (n + 1))
    (hExtension : IsLabeledOneElementExtension parent child) :
    precursorOneElementExtension parent
      (causalPastSetOfLabeledExtension parent child hExtension) = child := by
  apply CardinalCausalOrder.ext
  funext i j
  cases hi : finSumFinEquiv.symm i with
  | inl a =>
      have hi' : i = a.castSucc := by
        have h := congrArg finSumFinEquiv hi
        simpa using h
      cases hj : finSumFinEquiv.symm j with
      | inl b =>
          have hj' : j = b.castSucc := by
            have h := congrArg finSumFinEquiv hj
            simpa using h
          subst i
          subst j
          simpa [precursorOneElementExtension, precursorExtensionRel]
            using (hExtension.1 a b).symm
      | inr b =>
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          have hj' : j = Fin.last n := by
            have h := congrArg finSumFinEquiv hj
            simpa using h
          subst i
          subst j
          simp [precursorOneElementExtension, precursorExtensionRel,
            causalPastSetOfLabeledExtension]
  | inr a =>
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      have hi' : i = Fin.last n := by
        have h := congrArg finSumFinEquiv hi
        simpa using h
      cases hj : finSumFinEquiv.symm j with
      | inl b =>
          have hj' : j = b.castSucc := by
            have h := congrArg finSumFinEquiv hj
            simpa using h
          subst i
          subst j
          simpa [precursorOneElementExtension, precursorExtensionRel]
            using (hExtension.2 b).symm
      | inr b =>
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          have hj' : j = Fin.last n := by
            have h := congrArg finSumFinEquiv hj
            simpa using h
          subst i
          subst j
          simpa [precursorOneElementExtension, precursorExtensionRel]
            using (child.refl (Fin.last n)).symm

/-! ## 5. Transition fibers and representative-independent multiplicity -/

/-- The unlabeled child reached by one raw precursor transition slot. -/
def causalTransitionTarget {n : ℕ} (parent : CardinalCausalOrder n)
    (past : CausalPastSet parent) : UnlabeledCardinalCausalOrder (n + 1) :=
  Quotient.mk _ (precursorOneElementExtension parent past)

theorem causalTransitionTarget_relabel {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j))
    (past : CausalPastSet parent) :
    causalTransitionTarget parent'
        (past.relabel equivalence hRel) =
      causalTransitionTarget parent past := by
  exact (unlabeledCardinalOrder_eq_of_isomorphic
    (precursorOneElementExtension_isomorphic_relabel
      equivalence hRel past)).symm

/-- All distinct precursor slots in one labeled representative that land at a
fixed unlabeled child. -/
abbrev LabeledCausalTransitionFiber {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :=
  {past : CausalPastSet parent // causalTransitionTarget parent past = child}

/-- Relabeling gives a target-preserving bijection of complete transition
fibers. -/
def causalTransitionFiberEquivOfIsomorphism {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j))
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    LabeledCausalTransitionFiber parent child ≃
      LabeledCausalTransitionFiber parent' child := by
  let pastEquiv := causalPastSetEquivOfIsomorphism equivalence hRel
  let hRelSymm : ∀ i j,
      parent'.rel i j =
        parent.rel (equivalence.symm i) (equivalence.symm j) := by
    intro i j
    simpa using (hRel (equivalence.symm i) (equivalence.symm j)).symm
  exact {
    toFun := fun past => ⟨pastEquiv past, by
      exact (causalTransitionTarget_relabel
        equivalence hRel past).trans past.property⟩
    invFun := fun past => ⟨pastEquiv.symm past, by
      exact (causalTransitionTarget_relabel equivalence.symm hRelSymm past).trans
        past.property⟩
    left_inv := by
      intro past
      apply Subtype.ext
      exact pastEquiv.left_inv past
    right_inv := by
      intro past
      apply Subtype.ext
      exact pastEquiv.right_inv past }

/-- The coefficient attached to an unlabeled link when the parent is
represented by `parent`: the number of distinct raw precursor sets producing
that child. -/
def labeledCausalTransitionMultiplicity {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℕ :=
  Fintype.card (LabeledCausalTransitionFiber parent child)

theorem labeledCausalTransitionMultiplicity_eq_of_isomorphic {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (hIso : CardinalCausalOrderIsomorphic parent parent')
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    labeledCausalTransitionMultiplicity parent child =
      labeledCausalTransitionMultiplicity parent' child := by
  obtain ⟨equivalence, hRel⟩ := hIso
  exact Fintype.card_congr
    (causalTransitionFiberEquivOfIsomorphism equivalence hRel child)

/-- **Rideout--Sorkin link multiplicity.**  This descends the precursor-fiber
cardinality to an unlabeled parent. -/
def causalTransitionMultiplicity {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℕ :=
  Quotient.lift
    (fun parentRep => labeledCausalTransitionMultiplicity parentRep child)
    (fun _ _ hIso =>
      labeledCausalTransitionMultiplicity_eq_of_isomorphic hIso child)
    parent

@[simp]
theorem causalTransitionMultiplicity_mk {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    causalTransitionMultiplicity (Quotient.mk _ parent) child =
      labeledCausalTransitionMultiplicity parent child := rfl

/-- A labeled multiplicity is positive exactly for a physical unlabeled
parent-child link. -/
theorem labeledCausalTransitionMultiplicity_pos_iff {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    0 < labeledCausalTransitionMultiplicity parent child ↔
      IsUnlabeledOneElementExtension (Quotient.mk _ parent) child := by
  constructor
  · intro hPositive
    obtain ⟨past⟩ := Fintype.card_pos_iff.mp hPositive
    rw [← past.property]
    exact isUnlabeledOneElementExtension_mk
      (precursor_is_oneElementExtension parent past)
  · rintro ⟨parentRep, childRep, hParent, hChild, hExtension⟩
    let past := causalPastSetOfLabeledExtension
      parentRep childRep hExtension
    have hTarget : causalTransitionTarget parentRep past = child := by
      unfold causalTransitionTarget
      rw [precursorOneElementExtension_recovers]
      exact hChild
    have hPositiveRep :
        0 < labeledCausalTransitionMultiplicity parentRep child :=
      Fintype.card_pos_iff.mpr ⟨⟨past, hTarget⟩⟩
    have hIso : CardinalCausalOrderIsomorphic parentRep parent :=
      Quotient.exact hParent
    rw [labeledCausalTransitionMultiplicity_eq_of_isomorphic hIso child]
      at hPositiveRep
    exact hPositiveRep

/-- The invariant multiplicity is positive exactly on the physical extension
graph. -/
theorem causalTransitionMultiplicity_pos_iff {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    0 < causalTransitionMultiplicity parent child ↔
      IsUnlabeledOneElementExtension parent child := by
  refine Quotient.inductionOn parent ?_
  intro parentRep
  exact labeledCausalTransitionMultiplicity_pos_iff parentRep child

theorem causalTransitionMultiplicity_ne_zero_iff {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    causalTransitionMultiplicity parent child ≠ 0 ↔
      IsUnlabeledOneElementExtension parent child := by
  rw [← Nat.pos_iff_ne_zero, causalTransitionMultiplicity_pos_iff]

theorem causalTransitionMultiplicity_eq_zero_of_not_physical {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (hNotPhysical : ¬ IsUnlabeledOneElementExtension parent child) :
    causalTransitionMultiplicity parent child = 0 := by
  by_contra hNonzero
  exact hNotPhysical
    ((causalTransitionMultiplicity_ne_zero_iff parent child).mp hNonzero)

/-! ## 6. Unlabeled links with retained transition multiplicity -/

/-- A link in `poscau`: two unlabeled causal sets separated by one physical
maximal birth.  Raw precursor slots are not quotient objects; their number is
stored by `causalTransitionMultiplicity`. -/
structure UnlabeledCausalTransitionLink (n : ℕ) where
  parent : UnlabeledCardinalCausalOrder n
  child : UnlabeledCardinalCausalOrder (n + 1)
  physical : IsUnlabeledOneElementExtension parent child

@[ext]
theorem UnlabeledCausalTransitionLink.ext {n : ℕ}
    {first second : UnlabeledCausalTransitionLink n}
    (hParent : first.parent = second.parent)
    (hChild : first.child = second.child) : first = second := by
  cases first
  cases second
  cases hParent
  cases hChild
  rfl

instance unlabeledCausalTransitionLinkFinite (n : ℕ) :
    Finite (UnlabeledCausalTransitionLink n) := by
  let encode : UnlabeledCausalTransitionLink n →
      UnlabeledCardinalCausalOrder n ×
        UnlabeledCardinalCausalOrder (n + 1) :=
    fun link => (link.parent, link.child)
  exact Finite.of_injective encode (by
    intro first second h
    exact UnlabeledCausalTransitionLink.ext
      (congrArg Prod.fst h) (congrArg Prod.snd h))

noncomputable instance unlabeledCausalTransitionLinkFintype (n : ℕ) :
    Fintype (UnlabeledCausalTransitionLink n) := Fintype.ofFinite _

noncomputable instance unlabeledCausalTransitionLinkDecidableEq (n : ℕ) :
    DecidableEq (UnlabeledCausalTransitionLink n) := Classical.decEq _

/-- The coefficient of an unlabeled link in the Rideout--Sorkin Markov sum. -/
def UnlabeledCausalTransitionLink.multiplicity {n : ℕ}
    (link : UnlabeledCausalTransitionLink n) : ℕ :=
  causalTransitionMultiplicity link.parent link.child

theorem UnlabeledCausalTransitionLink.multiplicity_pos {n : ℕ}
    (link : UnlabeledCausalTransitionLink n) : 0 < link.multiplicity :=
  (causalTransitionMultiplicity_pos_iff link.parent link.child).2
    link.physical

/-- All physical unlabeled links leaving one parent. -/
def outgoingCausalTransitionLinks {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    Finset (UnlabeledCausalTransitionLink n) := by
  classical
  exact Finset.univ.filter (fun link => link.parent = parent)

theorem outgoingCausalTransitionLinks_nonempty {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    (outgoingCausalTransitionLinks parent).Nonempty := by
  obtain ⟨child, hPhysical⟩ := unlabeled_oneElementExtension_exists parent
  let link : UnlabeledCausalTransitionLink n :=
    ⟨parent, child, hPhysical⟩
  exact ⟨link, by simp [outgoingCausalTransitionLinks, link]⟩

/-! ## 7. The exact multiplicity-weighted Markov sum -/

/-- The defining fiber identity: summing a child-dependent value over every
distinct precursor transition is the same as summing it over unlabeled links
with the Rideout--Sorkin multiplicity coefficient. -/
theorem rideoutSorkin_multiplicity_weighted_sum {n : ℕ}
    (parent : CardinalCausalOrder n)
    (value : UnlabeledCardinalCausalOrder (n + 1) → ℂ) :
    (∑ child,
        (causalTransitionMultiplicity
          (Quotient.mk _ parent) child : ℂ) * value child) =
      ∑ past : CausalPastSet parent,
        value (causalTransitionTarget parent past) := by
  classical
  calc
    (∑ child,
        (causalTransitionMultiplicity
          (Quotient.mk _ parent) child : ℂ) * value child) =
        ∑ child,
          ∑ _past : LabeledCausalTransitionFiber parent child,
            value child := by
      apply Finset.sum_congr rfl
      intro child _
      simp only [causalTransitionMultiplicity_mk,
        labeledCausalTransitionMultiplicity]
      simp [nsmul_eq_mul]
    _ = ∑ past : CausalPastSet parent,
          value (causalTransitionTarget parent past) :=
      Fintype.sum_fiberwise'
        (g := causalTransitionTarget parent) (f := value)

/-- The Markov normalization rule written with unlabeled links and
multiplicity is equivalent to normalization over every distinct precursor
transition slot. -/
theorem rideoutSorkin_markov_normalized_iff {n : ℕ}
    (parent : CardinalCausalOrder n)
    (transition : UnlabeledCardinalCausalOrder (n + 1) → ℂ) :
    (∑ child,
        (causalTransitionMultiplicity
          (Quotient.mk _ parent) child : ℂ) * transition child) = 1 ↔
      (∑ past : CausalPastSet parent,
        transition (causalTransitionTarget parent past)) = 1 := by
  rw [rideoutSorkin_multiplicity_weighted_sum]

/-! ## 8. The multiplicity-corrected uniform growth law -/

/-- Total number of distinct precursor transition slots leaving an unlabeled
parent. -/
def totalCausalTransitionMultiplicity {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) : ℕ :=
  ∑ child : UnlabeledCardinalCausalOrder (n + 1),
    causalTransitionMultiplicity parent child

theorem totalCausalTransitionMultiplicity_pos {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    0 < totalCausalTransitionMultiplicity parent := by
  obtain ⟨child, hPhysical⟩ := unlabeled_oneElementExtension_exists parent
  have hChildPositive : 0 < causalTransitionMultiplicity parent child :=
    (causalTransitionMultiplicity_pos_iff parent child).2 hPhysical
  have hChildLe : causalTransitionMultiplicity parent child ≤
      totalCausalTransitionMultiplicity parent := by
    unfold totalCausalTransitionMultiplicity
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ child)
  exact hChildPositive.trans_le hChildLe

/-- Uniform probability on raw precursor transition slots, aggregated onto the
unlabeled child-state graph.  Links with larger multiplicity receive the
correspondingly larger total probability. -/
def uniformRideoutSorkinAggregatedTransition {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  (causalTransitionMultiplicity parent child : ℂ) /
    (totalCausalTransitionMultiplicity parent : ℂ)

theorem uniformRideoutSorkinAggregatedTransition_normalized {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    ∑ child, uniformRideoutSorkinAggregatedTransition parent child = 1 := by
  unfold uniformRideoutSorkinAggregatedTransition
  rw [← Finset.sum_div]
  have hCastSum :
      (∑ child : UnlabeledCardinalCausalOrder (n + 1),
        (causalTransitionMultiplicity parent child : ℂ)) =
        (totalCausalTransitionMultiplicity parent : ℂ) := by
    simp [totalCausalTransitionMultiplicity]
  rw [hCastSum]
  exact div_self (Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (totalCausalTransitionMultiplicity_pos parent)))

theorem uniformRideoutSorkinAggregatedTransition_eq_zero_of_not_physical
    {n : ℕ} (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (hNotPhysical : ¬ IsUnlabeledOneElementExtension parent child) :
    uniformRideoutSorkinAggregatedTransition parent child = 0 := by
  simp [uniformRideoutSorkinAggregatedTransition,
    causalTransitionMultiplicity_eq_zero_of_not_physical
      parent child hNotPhysical]

/-- The corrected real baseline on ranked causal-set paths: uniform on
Rideout--Sorkin precursor slots, not uniform on isomorphism classes of
children. -/
def uniformRideoutSorkinCausalSetGrowthLaw :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := fun n pathPrefix child =>
    uniformRideoutSorkinAggregatedTransition
      (currentUnlabeledCausalOrder n pathPrefix) child
  normalized := fun n pathPrefix =>
    uniformRideoutSorkinAggregatedTransition_normalized
      (currentUnlabeledCausalOrder n pathPrefix)

/-! ## 9. A nontrivial multiplicity benchmark -/

/-- The `n`-element antichain as a fixed-cardinality causal order. -/
def cardinalCausalAntichain (n : ℕ) : CardinalCausalOrder n where
  rel := fun i j => decide (i = j)
  refl := by simp
  antisymm := by
    intro i j hij _
    simpa using hij
  trans := by
    intro i j k hij hjk
    have hij' : i = j := of_decide_eq_true hij
    have hjk' : j = k := of_decide_eq_true hjk
    exact decide_eq_true (hij'.trans hjk')

/-- A singleton precursor in an antichain. -/
def singletonAntichainPast {n : ℕ} (a : Fin n) :
    CausalPastSet (cardinalCausalAntichain n) where
  mem := fun i => decide (i = a)
  downwardClosed := by
    intro x y hx hyx
    have hx' : x = a := of_decide_eq_true hx
    have hyx' : y = x := of_decide_eq_true hyx
    exact decide_eq_true (hyx'.trans hx')

/-- The two singleton births of a two-antichain are distinct transition slots
but land at the same unlabeled child. -/
theorem twoAntichain_singleton_targets_equal :
    causalTransitionTarget (cardinalCausalAntichain 2)
        (singletonAntichainPast (0 : Fin 2)) =
      causalTransitionTarget (cardinalCausalAntichain 2)
        (singletonAntichainPast (1 : Fin 2)) := by
  let swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hRel : ∀ i j : Fin 2,
      (cardinalCausalAntichain 2).rel i j =
        (cardinalCausalAntichain 2).rel (swap i) (swap j) := by
    intro i j
    simp [cardinalCausalAntichain, swap]
  have hPast :
      (singletonAntichainPast (0 : Fin 2)).relabel swap hRel =
        singletonAntichainPast (1 : Fin 2) := by
    ext i
    fin_cases i <;>
      simp [CausalPastSet.relabel, singletonAntichainPast, swap]
  rw [← hPast]
  exact (causalTransitionTarget_relabel swap hRel
    (singletonAntichainPast (0 : Fin 2))).symm

theorem twoAntichain_singleton_pasts_ne :
    singletonAntichainPast (0 : Fin 2) ≠
      singletonAntichainPast (1 : Fin 2) := by
  intro hEqual
  have hMem := congrArg CausalPastSet.mem hEqual
  have hAtZero := congrFun hMem (0 : Fin 2)
  norm_num [singletonAntichainPast] at hAtZero

/-- First certified nontrivial Markov coefficient: the link obtained by
adjoining an event above either singleton of the two-antichain has
multiplicity at least two. -/
theorem twoAntichain_transition_multiplicity_at_least_two :
    2 ≤ causalTransitionMultiplicity
      (Quotient.mk _ (cardinalCausalAntichain 2))
      (causalTransitionTarget (cardinalCausalAntichain 2)
        (singletonAntichainPast (0 : Fin 2))) := by
  let parent := cardinalCausalAntichain 2
  let child := causalTransitionTarget parent
    (singletonAntichainPast (0 : Fin 2))
  let first : LabeledCausalTransitionFiber parent child :=
    ⟨singletonAntichainPast (0 : Fin 2), rfl⟩
  let second : LabeledCausalTransitionFiber parent child :=
    ⟨singletonAntichainPast (1 : Fin 2), by
      exact twoAntichain_singleton_targets_equal.symm⟩
  have hDistinct : first ≠ second := by
    intro hEqual
    apply twoAntichain_singleton_pasts_ne
    exact congrArg Subtype.val hEqual
  let twoSlots : Fin 2 → LabeledCausalTransitionFiber parent child :=
    ![first, second]
  have hInjective : Function.Injective twoSlots := by
    intro i j hEqual
    fin_cases i <;> fin_cases j <;>
      simp_all [twoSlots]
  have hCard := Fintype.card_le_of_injective twoSlots hInjective
  simpa [parent, child, labeledCausalTransitionMultiplicity] using hCard

/-- Capstone for the complete transition-edge kinematics. -/
theorem complete_rideoutSorkin_transition_edge_kinematics :
    (∀ (n : ℕ) (parent : CardinalCausalOrder n),
      Nonempty (CausalPastSet parent))
      ∧ (∀ (n : ℕ) (parent parent' : CardinalCausalOrder n),
          CardinalCausalOrderIsomorphic parent parent' →
          ∃ equivalence : CausalPastSet parent ≃ CausalPastSet parent',
            ∀ past,
              causalTransitionTarget parent' (equivalence past) =
                  causalTransitionTarget parent past
                ∧ (equivalence past).ancestorCount = past.ancestorCount
                ∧ (equivalence past).maximalCount = past.maximalCount)
      ∧ (∀ (n : ℕ) (parent : UnlabeledCardinalCausalOrder n)
          (child : UnlabeledCardinalCausalOrder (n + 1)),
          0 < causalTransitionMultiplicity parent child ↔
            IsUnlabeledOneElementExtension parent child)
      ∧ (∀ (n : ℕ) (parent : CardinalCausalOrder n)
          (value : UnlabeledCardinalCausalOrder (n + 1) → ℂ),
          (∑ child,
              (causalTransitionMultiplicity
                (Quotient.mk _ parent) child : ℂ) * value child) =
            ∑ past : CausalPastSet parent,
              value (causalTransitionTarget parent past))
      ∧ (∀ (n : ℕ) (parent : UnlabeledCardinalCausalOrder n),
          ∑ child,
            uniformRideoutSorkinAggregatedTransition parent child = 1)
      ∧ 2 ≤ causalTransitionMultiplicity
          (Quotient.mk _ (cardinalCausalAntichain 2))
          (causalTransitionTarget (cardinalCausalAntichain 2)
            (singletonAntichainPast (0 : Fin 2))) := by
  refine ⟨fun _ parent => ⟨emptyCausalPastSet parent⟩, ?_,
    (fun _ parent child =>
      causalTransitionMultiplicity_pos_iff parent child),
    (fun _ parent value =>
      rideoutSorkin_multiplicity_weighted_sum parent value),
    (fun _ parent =>
      uniformRideoutSorkinAggregatedTransition_normalized parent),
    twoAntichain_transition_multiplicity_at_least_two⟩
  intro n parent parent' hIso
  obtain ⟨equivalence, hRel⟩ := hIso
  exact ⟨causalPastSetEquivOfIsomorphism equivalence hRel,
    fun past => ⟨causalTransitionTarget_relabel equivalence hRel past,
      causalPastSet_relabel_ancestorCount equivalence hRel past,
      causalPastSet_relabel_maximalCount equivalence hRel past⟩⟩

#print axioms precursor_is_oneElementExtension
#print axioms precursorOneElementExtension_isomorphic_relabel
#print axioms precursorOneElementExtension_recovers
#print axioms causalTransitionMultiplicity_pos_iff
#print axioms rideoutSorkin_multiplicity_weighted_sum
#print axioms uniformRideoutSorkinAggregatedTransition_normalized
#print axioms twoAntichain_transition_multiplicity_at_least_two
#print axioms complete_rideoutSorkin_transition_edge_kinematics

end


end UnifiedTheory.Audit.KFCausalSetTransitionEdges
