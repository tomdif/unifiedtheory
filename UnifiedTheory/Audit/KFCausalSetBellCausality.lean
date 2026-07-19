/-
  Audit/KFCausalSetBellCausality.lean

  CANONICAL SPECTATOR DELETION AND COMPLEX BELL CAUSALITY

  This file continues the complete Rideout--Sorkin transition-edge
  kinematics.  For two precursor alternatives above one parent, the relevant
  subcauset is their union.  Restricting the parent and both precursors to that
  finite induced order deletes every spectator canonically up to the already
  formalized order-isomorphism gauge.

  Complex edge amplitudes are functions on raw precursor slots, covariant
  under parent relabeling.  The zero-safe Bell equation is stated without
  division by cross multiplication against the canonical reduction.
-/

import UnifiedTheory.Audit.KFCausalSetTransitionEdges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetBellCausality

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges

/-! ## 1. Union of two precursor past sets -/

/-- Union of past sets is again a past set. -/
def causalPastSetUnion {n : ℕ} {parent : CardinalCausalOrder n}
    (first second : CausalPastSet parent) : CausalPastSet parent where
  mem := fun i => first.mem i || second.mem i
  downwardClosed := by
    intro x y hx hyx
    simp only [Bool.or_eq_true] at hx ⊢
    rcases hx with hFirst | hSecond
    · exact Or.inl (first.downwardClosed x y hFirst hyx)
    · exact Or.inr (second.downwardClosed x y hSecond hyx)

@[simp]
theorem causalPastSetUnion_mem {n : ℕ} {parent : CardinalCausalOrder n}
    (first second : CausalPastSet parent) (i : Fin n) :
    (causalPastSetUnion first second).mem i = true ↔
      first.mem i = true ∨ second.mem i = true := by
  simp [causalPastSetUnion]

/-- The finite type of events retained by one past set. -/
abbrev CausalPastSetSupport {n : ℕ} {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) :=
  {i : Fin n // past.mem i = true}

noncomputable instance causalPastSetSupportFintype {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    Fintype (CausalPastSetSupport past) := Fintype.ofFinite _

/-- A finite coordinate system on a precursor support.  The particular
enumeration is gauge; all outputs below are used through unlabeled quotient
objects or explicit equivalences. -/
def causalPastSetSupportEquiv {n : ℕ} {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) :
    Fin past.ancestorCount ≃ CausalPastSetSupport past := by
  unfold CausalPastSet.ancestorCount
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.equivFin (CausalPastSetSupport past)).symm

/-! ## 2. Canonical induced parent and restricted precursor -/

/-- Induced causal order on the support of `relevant`. -/
def inducedCausalOrderOnPast {n : ℕ} (parent : CardinalCausalOrder n)
    (relevant : CausalPastSet parent) :
    CardinalCausalOrder relevant.ancestorCount where
  rel := fun i j => parent.rel
    (causalPastSetSupportEquiv relevant i).val
      (causalPastSetSupportEquiv relevant j).val
  refl := by
    intro i
    exact parent.refl _
  antisymm := by
    intro i j hij hji
    apply (causalPastSetSupportEquiv relevant).injective
    apply Subtype.ext
    exact parent.antisymm _ _ hij hji
  trans := by
    intro i j k hij hjk
    exact parent.trans _ _ _ hij hjk

/-- Restrict any past set of `parent` to the induced order on `relevant`. -/
def restrictCausalPastSetTo {n : ℕ} {parent : CardinalCausalOrder n}
    (relevant past : CausalPastSet parent) :
    CausalPastSet (inducedCausalOrderOnPast parent relevant) where
  mem := fun i => past.mem (causalPastSetSupportEquiv relevant i).val
  downwardClosed := by
    intro x y hx hyx
    exact past.downwardClosed _ _ hx hyx

/-! ## 3. Canonical spectator deletion -/

/-- Two raw alternatives above one labeled parent. -/
structure CausalTransitionAlternativePair where
  rank : ℕ
  parent : CardinalCausalOrder rank
  first : CausalPastSet parent
  second : CausalPastSet parent

/-- Events that can affect the relative amplitude of the two alternatives. -/
def CausalTransitionAlternativePair.relevant
    (pair : CausalTransitionAlternativePair) : CausalPastSet pair.parent :=
  causalPastSetUnion pair.first pair.second

/-- Delete every spectator outside the union of the two precursor sets. -/
def CausalTransitionAlternativePair.deleteSpectators
    (pair : CausalTransitionAlternativePair) :
    CausalTransitionAlternativePair where
  rank := pair.relevant.ancestorCount
  parent := inducedCausalOrderOnPast pair.parent pair.relevant
  first := restrictCausalPastSetTo pair.relevant pair.first
  second := restrictCausalPastSetTo pair.relevant pair.second

/-- After deletion, the union of the two reduced precursors is the full
reduced parent: no spectator remains. -/
theorem deleteSpectators_relevant_full
    (pair : CausalTransitionAlternativePair) (i : Fin pair.deleteSpectators.rank) :
    pair.deleteSpectators.relevant.mem i = true := by
  change (pair.first.mem (causalPastSetSupportEquiv pair.relevant i).val ||
    pair.second.mem (causalPastSetSupportEquiv pair.relevant i).val) = true
  rw [Bool.or_eq_true]
  exact (causalPastSetUnion_mem pair.first pair.second
    (causalPastSetSupportEquiv pair.relevant i).val).mp
      (causalPastSetSupportEquiv pair.relevant i).property

/-- A precursor lies inside the relevant union. -/
theorem first_mem_relevant {pair : CausalTransitionAlternativePair}
    {i : Fin pair.rank} (hi : pair.first.mem i = true) :
    pair.relevant.mem i = true := by
  exact (causalPastSetUnion_mem pair.first pair.second i).2 (Or.inl hi)

theorem second_mem_relevant {pair : CausalTransitionAlternativePair}
    {i : Fin pair.rank} (hi : pair.second.mem i = true) :
    pair.relevant.mem i = true := by
  exact (causalPastSetUnion_mem pair.first pair.second i).2 (Or.inr hi)

/-- Restriction gives a bijection between the original first precursor and
its reduced copy. -/
def firstSupportEquivReduced (pair : CausalTransitionAlternativePair) :
    CausalPastSetSupport pair.first ≃
      CausalPastSetSupport pair.deleteSpectators.first where
  toFun i := by
    let relevantEvent : CausalPastSetSupport pair.relevant :=
      ⟨i.val, first_mem_relevant i.property⟩
    let reducedIndex := (causalPastSetSupportEquiv pair.relevant).symm relevantEvent
    exact ⟨reducedIndex, by
      change pair.first.mem
        (causalPastSetSupportEquiv pair.relevant reducedIndex).val = true
      simpa [reducedIndex, relevantEvent] using i.property⟩
  invFun i := ⟨(causalPastSetSupportEquiv pair.relevant i.val).val, i.property⟩
  left_inv := by
    intro i
    apply Subtype.ext
    simp
  right_inv := by
    intro i
    apply Subtype.ext
    simp

def secondSupportEquivReduced (pair : CausalTransitionAlternativePair) :
    CausalPastSetSupport pair.second ≃
      CausalPastSetSupport pair.deleteSpectators.second where
  toFun i := by
    let relevantEvent : CausalPastSetSupport pair.relevant :=
      ⟨i.val, second_mem_relevant i.property⟩
    let reducedIndex := (causalPastSetSupportEquiv pair.relevant).symm relevantEvent
    exact ⟨reducedIndex, by
      change pair.second.mem
        (causalPastSetSupportEquiv pair.relevant reducedIndex).val = true
      simpa [reducedIndex, relevantEvent] using i.property⟩
  invFun i := ⟨(causalPastSetSupportEquiv pair.relevant i.val).val, i.property⟩
  left_inv := by
    intro i
    apply Subtype.ext
    simp
  right_inv := by
    intro i
    apply Subtype.ext
    simp

theorem deleteSpectators_first_ancestorCount
    (pair : CausalTransitionAlternativePair) :
    pair.deleteSpectators.first.ancestorCount = pair.first.ancestorCount := by
  exact (Nat.card_congr (firstSupportEquivReduced pair)).symm

theorem deleteSpectators_second_ancestorCount
    (pair : CausalTransitionAlternativePair) :
    pair.deleteSpectators.second.ancestorCount = pair.second.ancestorCount := by
  exact (Nat.card_congr (secondSupportEquivReduced pair)).symm

/-! ## 4. The complete Rideout--Sorkin signature survives deletion -/

/-- The original and reduced first alternatives have equivalent sets of
maximal precursor events.  This is stronger than cardinality preservation:
the equivalence is induced by the actual support inclusion. -/
def firstMaximalEquivReduced (pair : CausalTransitionAlternativePair) :
    {i : Fin pair.rank // pair.first.IsMaximal i} ≃
      {i : Fin pair.deleteSpectators.rank //
        pair.deleteSpectators.first.IsMaximal i} where
  toFun i := by
    let relevantEvent : CausalPastSetSupport pair.relevant :=
      ⟨i.val, first_mem_relevant i.property.1⟩
    let reducedIndex := (causalPastSetSupportEquiv pair.relevant).symm relevantEvent
    refine ⟨reducedIndex, ?_⟩
    constructor
    · change pair.first.mem
        (causalPastSetSupportEquiv pair.relevant reducedIndex).val = true
      simpa [reducedIndex, relevantEvent] using i.property.1
    · intro j hj hRel
      change pair.parent.rel
        (causalPastSetSupportEquiv pair.relevant reducedIndex).val
        (causalPastSetSupportEquiv pair.relevant j).val = true at hRel
      have hOriginal :
          (causalPastSetSupportEquiv pair.relevant j).val = i.val := by
        apply i.property.2
        · exact hj
        · simpa [reducedIndex, relevantEvent] using hRel
      apply (causalPastSetSupportEquiv pair.relevant).injective
      apply Subtype.ext
      simpa [reducedIndex, relevantEvent] using hOriginal
  invFun i := by
    refine ⟨(causalPastSetSupportEquiv pair.relevant i.val).val, ?_⟩
    constructor
    · exact i.property.1
    · intro j hj hRel
      let relevantEvent : CausalPastSetSupport pair.relevant :=
        ⟨j, first_mem_relevant hj⟩
      let reducedIndex :=
        (causalPastSetSupportEquiv pair.relevant).symm relevantEvent
      have hReduced : reducedIndex = i.val := by
        apply i.property.2
        · change pair.first.mem
            (causalPastSetSupportEquiv pair.relevant reducedIndex).val = true
          simpa [reducedIndex, relevantEvent] using hj
        · change pair.parent.rel
            (causalPastSetSupportEquiv pair.relevant i.val).val
            (causalPastSetSupportEquiv pair.relevant reducedIndex).val = true
          simpa [reducedIndex, relevantEvent] using hRel
      have hSupports := congrArg
        (fun k : Fin pair.deleteSpectators.rank =>
          (causalPastSetSupportEquiv pair.relevant k).val) hReduced
      simpa [reducedIndex, relevantEvent] using hSupports
  left_inv := by
    intro i
    apply Subtype.ext
    simp
  right_inv := by
    intro i
    apply Subtype.ext
    simp

/-- The second alternative has the analogous maximal-event equivalence. -/
def secondMaximalEquivReduced (pair : CausalTransitionAlternativePair) :
    {i : Fin pair.rank // pair.second.IsMaximal i} ≃
      {i : Fin pair.deleteSpectators.rank //
        pair.deleteSpectators.second.IsMaximal i} where
  toFun i := by
    let relevantEvent : CausalPastSetSupport pair.relevant :=
      ⟨i.val, second_mem_relevant i.property.1⟩
    let reducedIndex := (causalPastSetSupportEquiv pair.relevant).symm relevantEvent
    refine ⟨reducedIndex, ?_⟩
    constructor
    · change pair.second.mem
        (causalPastSetSupportEquiv pair.relevant reducedIndex).val = true
      simpa [reducedIndex, relevantEvent] using i.property.1
    · intro j hj hRel
      change pair.parent.rel
        (causalPastSetSupportEquiv pair.relevant reducedIndex).val
        (causalPastSetSupportEquiv pair.relevant j).val = true at hRel
      have hOriginal :
          (causalPastSetSupportEquiv pair.relevant j).val = i.val := by
        apply i.property.2
        · exact hj
        · simpa [reducedIndex, relevantEvent] using hRel
      apply (causalPastSetSupportEquiv pair.relevant).injective
      apply Subtype.ext
      simpa [reducedIndex, relevantEvent] using hOriginal
  invFun i := by
    refine ⟨(causalPastSetSupportEquiv pair.relevant i.val).val, ?_⟩
    constructor
    · exact i.property.1
    · intro j hj hRel
      let relevantEvent : CausalPastSetSupport pair.relevant :=
        ⟨j, second_mem_relevant hj⟩
      let reducedIndex :=
        (causalPastSetSupportEquiv pair.relevant).symm relevantEvent
      have hReduced : reducedIndex = i.val := by
        apply i.property.2
        · change pair.second.mem
            (causalPastSetSupportEquiv pair.relevant reducedIndex).val = true
          simpa [reducedIndex, relevantEvent] using hj
        · change pair.parent.rel
            (causalPastSetSupportEquiv pair.relevant i.val).val
            (causalPastSetSupportEquiv pair.relevant reducedIndex).val = true
          simpa [reducedIndex, relevantEvent] using hRel
      have hSupports := congrArg
        (fun k : Fin pair.deleteSpectators.rank =>
          (causalPastSetSupportEquiv pair.relevant k).val) hReduced
      simpa [reducedIndex, relevantEvent] using hSupports
  left_inv := by
    intro i
    apply Subtype.ext
    simp
  right_inv := by
    intro i
    apply Subtype.ext
    simp

theorem deleteSpectators_first_maximalCount
    (pair : CausalTransitionAlternativePair) :
    pair.deleteSpectators.first.maximalCount = pair.first.maximalCount := by
  exact (Nat.card_congr (firstMaximalEquivReduced pair)).symm

theorem deleteSpectators_second_maximalCount
    (pair : CausalTransitionAlternativePair) :
    pair.deleteSpectators.second.maximalCount = pair.second.maximalCount := by
  exact (Nat.card_congr (secondMaximalEquivReduced pair)).symm

/-- Spectator deletion preserves the complete pair of transition signatures
`(omega,m)` used by Rideout--Sorkin dynamics. -/
theorem deleteSpectators_preserves_transition_signatures
    (pair : CausalTransitionAlternativePair) :
    (pair.deleteSpectators.first.ancestorCount,
      pair.deleteSpectators.first.maximalCount) =
        (pair.first.ancestorCount, pair.first.maximalCount) ∧
    (pair.deleteSpectators.second.ancestorCount,
      pair.deleteSpectators.second.maximalCount) =
        (pair.second.ancestorCount, pair.second.maximalCount) := by
  constructor <;> apply Prod.ext
  · exact deleteSpectators_first_ancestorCount pair
  · exact deleteSpectators_first_maximalCount pair
  · exact deleteSpectators_second_ancestorCount pair
  · exact deleteSpectators_second_maximalCount pair

/-! ## 5. Covariant complex amplitudes on raw transition edges -/

/-- A complex amplitude on each *raw precursor slot*.  Covariance says that
changing the labels of an isomorphic parent does not change the amplitude.
The raw slots are deliberately not quotiented by automorphisms: their
multiplicity is part of the Rideout--Sorkin Markov sum. -/
structure CovariantComplexCausalEdgeAmplitude where
  amplitude : ∀ {n : ℕ} (parent : CardinalCausalOrder n),
    CausalPastSet parent → ℂ
  covariant : ∀ {n : ℕ} {parent parent' : CardinalCausalOrder n}
    (equivalence : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (equivalence i) (equivalence j))
    (past : CausalPastSet parent),
    amplitude parent' (past.relabel equivalence hRel) = amplitude parent past

/-- Every complex function of the complete Rideout--Sorkin signature
`(omega,m)` defines a covariant edge-amplitude law. -/
def rideoutSorkinSignatureAmplitude (weight : ℕ → ℕ → ℂ) :
    CovariantComplexCausalEdgeAmplitude where
  amplitude := fun _ past => weight past.ancestorCount past.maximalCount
  covariant := by
    intro n parent parent' equivalence hRel past
    rw [causalPastSet_relabel_ancestorCount equivalence hRel past,
      causalPastSet_relabel_maximalCount equivalence hRel past]

/-- Ancestor-local amplitudes form a particularly transparent infinite
subfamily of the signature-local laws. -/
def ancestorLocalCausalEdgeAmplitude (weight : ℕ → ℂ) :
    CovariantComplexCausalEdgeAmplitude :=
  rideoutSorkinSignatureAmplitude (fun omega _m => weight omega)

/-- The raw one-step partition amplitude above a labeled parent. -/
def causalEdgeAmplitudePartition (law : CovariantComplexCausalEdgeAmplitude)
    {n : ℕ} (parent : CardinalCausalOrder n) : ℂ :=
  ∑ past : CausalPastSet parent, law.amplitude parent past

/-- Amplitudes landing on the same unlabeled child add coherently.  This is
the complex analogue of the classical multiplicity coefficient. -/
def labeledAggregatedCausalEdgeAmplitude
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  ∑ past : LabeledCausalTransitionFiber parent child,
    law.amplitude parent past.val

/-- Coherent child aggregation loses no raw transition amplitude. -/
theorem sum_labeledAggregatedCausalEdgeAmplitude
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (∑ child : UnlabeledCardinalCausalOrder (n + 1),
      labeledAggregatedCausalEdgeAmplitude law parent child) =
        causalEdgeAmplitudePartition law parent := by
  classical
  exact Fintype.sum_fiberwise
    (causalTransitionTarget parent) (law.amplitude parent)

/-- The coherent amplitude attached to an unlabeled child is independent of
the chosen labeled representative of its parent. -/
theorem labeledAggregatedCausalEdgeAmplitude_eq_of_isomorphic
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (hIso : CardinalCausalOrderIsomorphic parent parent')
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    labeledAggregatedCausalEdgeAmplitude law parent' child =
      labeledAggregatedCausalEdgeAmplitude law parent child := by
  classical
  obtain ⟨equivalence, hRel⟩ := hIso
  let fiberEquiv :=
    causalTransitionFiberEquivOfIsomorphism equivalence hRel child
  unfold labeledAggregatedCausalEdgeAmplitude
  rw [← fiberEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro past _
  exact law.covariant equivalence hRel past.val

/-- The raw partition amplitude is also independent of the chosen labeled
representative. -/
theorem causalEdgeAmplitudePartition_eq_of_isomorphic
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (hIso : CardinalCausalOrderIsomorphic parent parent') :
    causalEdgeAmplitudePartition law parent' =
      causalEdgeAmplitudePartition law parent := by
  classical
  obtain ⟨equivalence, hRel⟩ := hIso
  let pastEquiv := causalPastSetEquivOfIsomorphism equivalence hRel
  unfold causalEdgeAmplitudePartition
  rw [← pastEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro past _
  exact law.covariant equivalence hRel past

/-- Coherent child amplitude descended to an unlabeled parent. -/
def unlabeledAggregatedCausalEdgeAmplitude
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  Quotient.lift
    (fun parentRep =>
      labeledAggregatedCausalEdgeAmplitude law parentRep child)
    (fun _ _ hIso =>
      (labeledAggregatedCausalEdgeAmplitude_eq_of_isomorphic
        law hIso child).symm)
    parent

/-- Raw partition amplitude descended to an unlabeled parent. -/
def unlabeledCausalEdgeAmplitudePartition
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) : ℂ :=
  Quotient.lift
    (causalEdgeAmplitudePartition law)
    (fun _ _ hIso =>
      (causalEdgeAmplitudePartition_eq_of_isomorphic law hIso).symm)
    parent

@[simp]
theorem unlabeledAggregatedCausalEdgeAmplitude_mk
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    unlabeledAggregatedCausalEdgeAmplitude law (Quotient.mk _ parent) child =
      labeledAggregatedCausalEdgeAmplitude law parent child := rfl

@[simp]
theorem unlabeledCausalEdgeAmplitudePartition_mk
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : CardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition law (Quotient.mk _ parent) =
      causalEdgeAmplitudePartition law parent := rfl

theorem sum_unlabeledAggregatedCausalEdgeAmplitude
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    (∑ child : UnlabeledCardinalCausalOrder (n + 1),
      unlabeledAggregatedCausalEdgeAmplitude law parent child) =
        unlabeledCausalEdgeAmplitudePartition law parent := by
  refine Quotient.inductionOn parent ?_
  intro parentRep
  exact sum_labeledAggregatedCausalEdgeAmplitude law parentRep

/-- Totalized normalization: use the coherent complex edge law when its
partition amplitude is nonzero, and the multiplicity-corrected uniform law at
an exceptional zero.  This produces a normalized law without assuming a
global zero-free theorem. -/
def totalizedNormalizedCausalEdgeAmplitude
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  if unlabeledCausalEdgeAmplitudePartition law parent = 0 then
    uniformRideoutSorkinAggregatedTransition parent child
  else
    unlabeledAggregatedCausalEdgeAmplitude law parent child /
      unlabeledCausalEdgeAmplitudePartition law parent

theorem totalizedNormalizedCausalEdgeAmplitude_sum_one
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    ∑ child : UnlabeledCardinalCausalOrder (n + 1),
      totalizedNormalizedCausalEdgeAmplitude law parent child = 1 := by
  classical
  by_cases hZero : unlabeledCausalEdgeAmplitudePartition law parent = 0
  · simp [totalizedNormalizedCausalEdgeAmplitude, hZero,
      uniformRideoutSorkinAggregatedTransition_normalized]
  · simp only [totalizedNormalizedCausalEdgeAmplitude, hZero, if_false,
      ← Finset.sum_div]
    rw [sum_unlabeledAggregatedCausalEdgeAmplitude,
      div_self hZero]

/-- Every covariant raw-edge amplitude therefore defines an unconditional
normalized ranked causal-set growth law. -/
def totalizedCausalEdgeGrowthLaw
    (law : CovariantComplexCausalEdgeAmplitude) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := fun n pathPrefix child =>
    totalizedNormalizedCausalEdgeAmplitude law
      (currentUnlabeledCausalOrder n pathPrefix) child
  normalized := fun n pathPrefix =>
    totalizedNormalizedCausalEdgeAmplitude_sum_one law
      (currentUnlabeledCausalOrder n pathPrefix)

/-- Normalize the coherently aggregated child amplitudes whenever the raw
partition amplitude is nonzero. -/
def normalizedLabeledAggregatedCausalEdgeAmplitude
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  labeledAggregatedCausalEdgeAmplitude law parent child /
    causalEdgeAmplitudePartition law parent

theorem normalizedLabeledAggregatedCausalEdgeAmplitude_sum_one
    (law : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : CardinalCausalOrder n)
    (hNonzero : causalEdgeAmplitudePartition law parent ≠ 0) :
    ∑ child : UnlabeledCardinalCausalOrder (n + 1),
      normalizedLabeledAggregatedCausalEdgeAmplitude law parent child = 1 := by
  simp only [normalizedLabeledAggregatedCausalEdgeAmplitude,
    ← Finset.sum_div]
  rw [sum_labeledAggregatedCausalEdgeAmplitude, div_self hNonzero]

/-! ## 6. Canonical zero-safe complex Bell causality -/

/-- Division-free equality of two complex amplitude ratios.  Cross
multiplication remains meaningful even when one or more amplitudes vanish. -/
def ZeroSafeComplexBellRatio (first second reducedFirst reducedSecond : ℂ) :
    Prop :=
  first * reducedSecond = second * reducedFirst

/-- Bell causality using the canonical deletion of all spectator events. -/
def IsCanonicallyBellCausal (law : CovariantComplexCausalEdgeAmplitude) : Prop :=
  ∀ pair : CausalTransitionAlternativePair,
    ZeroSafeComplexBellRatio
      (law.amplitude pair.parent pair.first)
      (law.amplitude pair.parent pair.second)
      (law.amplitude pair.deleteSpectators.parent
        pair.deleteSpectators.first)
      (law.amplitude pair.deleteSpectators.parent
        pair.deleteSpectators.second)

/-- A simple sufficient condition for canonical Bell causality: deleting
spectators leaves the amplitude of each of the two alternatives unchanged. -/
def IsSpectatorIndependent (law : CovariantComplexCausalEdgeAmplitude) : Prop :=
  ∀ pair : CausalTransitionAlternativePair,
    law.amplitude pair.parent pair.first =
        law.amplitude pair.deleteSpectators.parent
          pair.deleteSpectators.first ∧
      law.amplitude pair.parent pair.second =
        law.amplitude pair.deleteSpectators.parent
          pair.deleteSpectators.second

theorem spectatorIndependent_implies_canonicalBellCausal
    (law : CovariantComplexCausalEdgeAmplitude)
    (hIndependent : IsSpectatorIndependent law) :
    IsCanonicallyBellCausal law := by
  intro pair
  obtain ⟨hFirst, hSecond⟩ := hIndependent pair
  unfold ZeroSafeComplexBellRatio
  rw [← hFirst, ← hSecond]
  exact mul_comm _ _

/-- The entire two-parameter Rideout--Sorkin signature family is spectator
independent because canonical deletion preserves both `omega` and `m`. -/
theorem rideoutSorkinSignatureAmplitude_spectatorIndependent
    (weight : ℕ → ℕ → ℂ) :
    IsSpectatorIndependent (rideoutSorkinSignatureAmplitude weight) := by
  intro pair
  constructor
  · change weight pair.first.ancestorCount pair.first.maximalCount =
      weight pair.deleteSpectators.first.ancestorCount
        pair.deleteSpectators.first.maximalCount
    rw [deleteSpectators_first_ancestorCount,
      deleteSpectators_first_maximalCount]
  · change weight pair.second.ancestorCount pair.second.maximalCount =
      weight pair.deleteSpectators.second.ancestorCount
        pair.deleteSpectators.second.maximalCount
    rw [deleteSpectators_second_ancestorCount,
      deleteSpectators_second_maximalCount]

theorem rideoutSorkinSignatureAmplitude_canonicalBellCausal
    (weight : ℕ → ℕ → ℂ) :
    IsCanonicallyBellCausal (rideoutSorkinSignatureAmplitude weight) :=
  spectatorIndependent_implies_canonicalBellCausal _
    (rideoutSorkinSignatureAmplitude_spectatorIndependent weight)

/-- Exact classification *inside the complete `(omega,m)`-local ansatz*:
canonical zero-safe Bell causality imposes no further constraint at all. -/
theorem rideoutSorkinSignatureAmplitude_canonicalBellCausal_iff
    (weight : ℕ → ℕ → ℂ) :
    IsCanonicallyBellCausal (rideoutSorkinSignatureAmplitude weight) ↔ True := by
  exact iff_true_intro
    (rideoutSorkinSignatureAmplitude_canonicalBellCausal weight)

/-! ## 7. Independent-composition locality and its exact residual freedom -/

/-- Candidate microscopic locality law: the amplitude of an independently
composed pair of transition signatures is the product of their amplitudes.
This is strictly stronger than spectator independence and Bell causality. -/
def IsMultiplicativeSignatureWeight (weight : ℕ → ℕ → ℂ) : Prop :=
  weight 0 0 = 1 ∧
    ∀ omega₁ maximal₁ omega₂ maximal₂,
      weight (omega₁ + omega₂) (maximal₁ + maximal₂) =
        weight omega₁ maximal₁ * weight omega₂ maximal₂

/-- The general separable character of the additive signature monoid. -/
def multiplicativeSignatureWeight (ancestorPhase maximalPhase : ℂ) :
    ℕ → ℕ → ℂ :=
  fun omega maximal => ancestorPhase ^ omega * maximalPhase ^ maximal

theorem multiplicativeSignatureWeight_isMultiplicative
    (ancestorPhase maximalPhase : ℂ) :
    IsMultiplicativeSignatureWeight
      (multiplicativeSignatureWeight ancestorPhase maximalPhase) := by
  constructor
  · simp [multiplicativeSignatureWeight]
  · intro omega₁ maximal₁ omega₂ maximal₂
    simp only [multiplicativeSignatureWeight, pow_add]
    ring

private theorem multiplicativeSignatureWeight_ancestor_axis
    {weight : ℕ → ℕ → ℂ} (hWeight : IsMultiplicativeSignatureWeight weight) :
    ∀ omega : ℕ, weight omega 0 = weight 1 0 ^ omega
  | 0 => by simpa using hWeight.1
  | omega + 1 => by
      rw [pow_succ]
      have hCompose := hWeight.2 omega 0 1 0
      norm_num at hCompose
      rw [hCompose, multiplicativeSignatureWeight_ancestor_axis hWeight omega]

private theorem multiplicativeSignatureWeight_maximal_axis
    {weight : ℕ → ℕ → ℂ} (hWeight : IsMultiplicativeSignatureWeight weight) :
    ∀ maximal : ℕ, weight 0 maximal = weight 0 1 ^ maximal
  | 0 => by simpa using hWeight.1
  | maximal + 1 => by
      rw [pow_succ]
      have hCompose := hWeight.2 0 maximal 0 1
      norm_num at hCompose
      rw [hCompose, multiplicativeSignatureWeight_maximal_axis hWeight maximal]

/-- **Character classification.**  Independent-composition locality collapses
an arbitrary two-variable Bell-causal weight to exactly two elementary complex
couplings, but does not select their values. -/
theorem multiplicativeSignatureWeight_classification
    {weight : ℕ → ℕ → ℂ} (hWeight : IsMultiplicativeSignatureWeight weight)
    (omega maximal : ℕ) :
    weight omega maximal =
      weight 1 0 ^ omega * weight 0 1 ^ maximal := by
  have hCompose := hWeight.2 omega 0 0 maximal
  norm_num at hCompose
  rw [hCompose,
    multiplicativeSignatureWeight_ancestor_axis hWeight omega,
    multiplicativeSignatureWeight_maximal_axis hWeight maximal]

theorem isMultiplicativeSignatureWeight_iff
    (weight : ℕ → ℕ → ℂ) :
    IsMultiplicativeSignatureWeight weight ↔
      ∀ omega maximal,
        weight omega maximal =
          weight 1 0 ^ omega * weight 0 1 ^ maximal := by
  constructor
  · exact fun hWeight =>
      multiplicativeSignatureWeight_classification hWeight
  · intro hCharacter
    constructor
    · simpa using hCharacter 0 0
    · intro omega₁ maximal₁ omega₂ maximal₂
      rw [hCharacter (omega₁ + omega₂) (maximal₁ + maximal₂),
        hCharacter omega₁ maximal₁, hCharacter omega₂ maximal₂]
      simp only [pow_add]
      ring

/-- Every independently compositional signature law remains canonically
Bell-causal; composition reduces functional freedom but Bell adds no equation
for the two surviving complex couplings. -/
theorem multiplicativeSignatureWeight_gives_canonicalBellCausal
    {weight : ℕ → ℕ → ℂ} (_hWeight : IsMultiplicativeSignatureWeight weight) :
    IsCanonicallyBellCausal (rideoutSorkinSignatureAmplitude weight) :=
  rideoutSorkinSignatureAmplitude_canonicalBellCausal weight

/-- The two elementary couplings are genuine parameters of the character
family at the signature-weight level. -/
theorem multiplicativeSignatureWeight_parameter_injective :
    Function.Injective
      (fun phases : ℂ × ℂ =>
        multiplicativeSignatureWeight phases.1 phases.2) := by
  rintro ⟨ancestor₁, maximal₁⟩ ⟨ancestor₂, maximal₂⟩ hEqual
  have hAncestor := congrFun (congrFun hEqual 1) 0
  have hMaximal := congrFun (congrFun hEqual 0) 1
  change ancestor₁ ^ 1 * maximal₁ ^ 0 =
    ancestor₂ ^ 1 * maximal₂ ^ 0 at hAncestor
  change ancestor₁ ^ 0 * maximal₁ ^ 1 =
    ancestor₂ ^ 0 * maximal₂ ^ 1 at hMaximal
  simp only [pow_one, pow_zero, mul_one, one_mul] at hAncestor hMaximal
  exact Prod.ext hAncestor hMaximal

/-- Even Bell causality plus independent-composition locality leaves an
injective two-complex-parameter family.  A further microscopic boundary law
must fix the elementary ancestor and maximal-event amplitudes. -/
theorem bell_and_composition_leave_two_complex_couplings :
    Function.Injective
      (fun phases : ℂ × ℂ =>
        multiplicativeSignatureWeight phases.1 phases.2)
      ∧ ∀ phases : ℂ × ℂ,
        IsMultiplicativeSignatureWeight
          (multiplicativeSignatureWeight phases.1 phases.2)
      ∧ IsCanonicallyBellCausal
          (rideoutSorkinSignatureAmplitude
            (multiplicativeSignatureWeight phases.1 phases.2)) := by
  exact ⟨multiplicativeSignatureWeight_parameter_injective,
    fun phases =>
      ⟨multiplicativeSignatureWeight_isMultiplicative phases.1 phases.2,
        rideoutSorkinSignatureAmplitude_canonicalBellCausal _⟩⟩

/-! ## 8. A minimal chiral boundary law -/

/-- Reflection exchanges the two microscopic chirality sectors. -/
def reflectedMicroscopicChirality (chirality : Fin 2) : Fin 2 :=
  if chirality = 0 then 1 else 0

/-- A maximal precursor event contributes a chirality-aligned quarter-turn
phase.  This is the smallest boundary datum compatible with the already
derived `±i` orientation holonomy. -/
def chiralMaximalEventPhase (chirality : Fin 2) : ℂ :=
  if chirality = 0 then Complex.I else -Complex.I

/-- Candidate microscopic character: trivial ancestor phase and one chiral
quarter turn per maximal precursor event. -/
def chiralMultiplicativeSignatureWeight (chirality : Fin 2) :
    ℕ → ℕ → ℂ :=
  multiplicativeSignatureWeight 1 (chiralMaximalEventPhase chirality)

theorem chiralMultiplicativeSignatureWeight_isMultiplicative
    (chirality : Fin 2) :
    IsMultiplicativeSignatureWeight
      (chiralMultiplicativeSignatureWeight chirality) :=
  multiplicativeSignatureWeight_isMultiplicative _ _

theorem chiralMultiplicativeSignatureAmplitude_isBellCausal
    (chirality : Fin 2) :
    IsCanonicallyBellCausal
      (rideoutSorkinSignatureAmplitude
        (chiralMultiplicativeSignatureWeight chirality)) :=
  rideoutSorkinSignatureAmplitude_canonicalBellCausal _

/-- Once independent composition, the ancestor gauge, and the elementary
chiral quarter-turn are fixed, the complete signature weight is unique. -/
theorem chiralMultiplicativeSignatureWeight_unique
    (chirality : Fin 2) (weight : ℕ → ℕ → ℂ)
    (hMultiplicative : IsMultiplicativeSignatureWeight weight)
    (hAncestor : weight 1 0 = 1)
    (hMaximal : weight 0 1 = chiralMaximalEventPhase chirality) :
    weight = chiralMultiplicativeSignatureWeight chirality := by
  funext omega maximal
  rw [multiplicativeSignatureWeight_classification
      hMultiplicative omega maximal,
    hAncestor, hMaximal]
  simp [chiralMultiplicativeSignatureWeight,
    multiplicativeSignatureWeight]

/-- Reflection complex-conjugates the microscopic character and swaps its
chirality sign. -/
theorem chiralMultiplicativeSignatureWeight_reflection
    (chirality : Fin 2) (omega maximal : ℕ) :
    star (chiralMultiplicativeSignatureWeight chirality omega maximal) =
      chiralMultiplicativeSignatureWeight
        (reflectedMicroscopicChirality chirality) omega maximal := by
  fin_cases chirality <;>
    simp [chiralMultiplicativeSignatureWeight,
      multiplicativeSignatureWeight, chiralMaximalEventPhase,
      reflectedMicroscopicChirality]

/-! ## 9. What Bell causality actually classifies -/

@[simp]
theorem fullCausalPastSet_ancestorCount {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (fullCausalPastSet parent).ancestorCount = n := by
  unfold CausalPastSet.ancestorCount
  simp [fullCausalPastSet]

/-- Ancestor-local Bell-causal laws contain a faithful copy of the full
function space `ℕ → ℂ`; Bell causality therefore cannot select one complex
microdynamics without additional dynamical input. -/
theorem ancestorLocalCausalEdgeAmplitude_injective :
    Function.Injective ancestorLocalCausalEdgeAmplitude := by
  intro first second hEqual
  funext n
  have hAtFull := congrArg
    (fun law : CovariantComplexCausalEdgeAmplitude =>
      law.amplitude (cardinalCausalAntichain n)
        (fullCausalPastSet (cardinalCausalAntichain n))) hEqual
  simpa [ancestorLocalCausalEdgeAmplitude,
    rideoutSorkinSignatureAmplitude] using hAtFull

/-- **Bell underdetermination theorem.**  There are infinitely many distinct
covariant, zero-safe Bell-causal complex transition laws: indeed every
sequence of complex ancestor weights gives one, injectively. -/
theorem canonicalBellCausal_contains_injective_ancestor_family :
    Function.Injective ancestorLocalCausalEdgeAmplitude ∧
      ∀ weight : ℕ → ℂ,
        IsCanonicallyBellCausal (ancestorLocalCausalEdgeAmplitude weight) := by
  exact ⟨ancestorLocalCausalEdgeAmplitude_injective,
    fun weight => rideoutSorkinSignatureAmplitude_canonicalBellCausal
      (fun omega _m => weight omega)⟩

#print axioms deleteSpectators_relevant_full
#print axioms deleteSpectators_first_ancestorCount
#print axioms deleteSpectators_preserves_transition_signatures
#print axioms labeledAggregatedCausalEdgeAmplitude_eq_of_isomorphic
#print axioms sum_unlabeledAggregatedCausalEdgeAmplitude
#print axioms normalizedLabeledAggregatedCausalEdgeAmplitude_sum_one
#print axioms totalizedNormalizedCausalEdgeAmplitude_sum_one
#print axioms rideoutSorkinSignatureAmplitude_canonicalBellCausal
#print axioms rideoutSorkinSignatureAmplitude_canonicalBellCausal_iff
#print axioms multiplicativeSignatureWeight_classification
#print axioms bell_and_composition_leave_two_complex_couplings
#print axioms chiralMultiplicativeSignatureWeight_unique
#print axioms chiralMultiplicativeSignatureWeight_reflection
#print axioms canonicalBellCausal_contains_injective_ancestor_family

end


end UnifiedTheory.Audit.KFCausalSetBellCausality
