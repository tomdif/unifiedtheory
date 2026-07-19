/-
  Audit/KFCausalSetChiralGrowth.lean

  THE FIRST CAUSAL BIRTH DERIVES THE ORIENTATION QUARTER TURN

  The one-event causal set has exactly two precursor slots: the empty past and
  the full past.  If their unnormalized amplitudes are `1` and `b`, local
  normalization gives `1/(1+b)` and `b/(1+b)`.  Requiring the two resulting
  causal children to have equal Born weight forces `b = ±i`.

  This file then feeds the selected chiral character into the totalized
  covariant raw-edge growth law and constructs its explicit depth-two cylinder
  partition.  The induced kernel is the corresponding pure orientation
  endpoint; reflection swaps the two signs.
-/

import UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralGrowth

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetOrientationRestriction
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

/-! ## 1. Balance derives the elementary quarter turn -/

/-- Unit elementary weight together with balanced normalization of `1+b`
forces a purely imaginary quarter-turn phase. -/
theorem unit_and_balanced_sum_forces_quarter_turn
    (b : ℂ)
    (hUnit : Complex.normSq b = 1)
    (hBalancedSum : Complex.normSq (1 + b) = 2) :
    b = Complex.I ∨ b = -Complex.I := by
  have hUnit' : b.re * b.re + b.im * b.im = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hUnit
  have hBalancedSum' :
      (1 + b.re) * (1 + b.re) + b.im * b.im = 2 := by
    simpa [Complex.normSq_apply, pow_two] using hBalancedSum
  have hReal : b.re = 0 := by nlinarith
  have hImaginarySq : b.im * b.im = 1 := by nlinarith
  have hImaginary : b.im = 1 ∨ b.im = -1 := by
    rcases (mul_self_eq_one_iff.mp hImaginarySq) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hImaginary with hPositive | hNegative
  · left
    apply Complex.ext
    · simpa [hReal]
    · simpa [hPositive]
  · right
    apply Complex.ext
    · simpa [hReal]
    · simpa [hNegative]

/-- Operational form: if the two normalized causal-birth amplitudes have equal
Born weight `1/2`, their unnormalized relative amplitude is `±i`. -/
theorem balanced_normalized_binary_birth_forces_quarter_turn
    (b : ℂ) (hPartition : 1 + b ≠ 0)
    (hEmptyBalanced : Complex.normSq (1 / (1 + b)) = 1 / 2)
    (hFullBalanced : Complex.normSq (b / (1 + b)) = 1 / 2) :
    b = Complex.I ∨ b = -Complex.I := by
  have hDenominator : Complex.normSq (1 + b) ≠ 0 := by
    intro hZero
    exact hPartition (Complex.normSq_eq_zero.mp hZero)
  have hSum : Complex.normSq (1 + b) = 2 := by
    rw [Complex.normSq_div, Complex.normSq_one] at hEmptyBalanced
    field_simp [hDenominator] at hEmptyBalanced
    linarith
  have hUnit : Complex.normSq b = 1 := by
    rw [Complex.normSq_div, hSum] at hFullBalanced
    linarith
  exact unit_and_balanced_sum_forces_quarter_turn b hUnit hSum

/-! ## 2. The two raw precursor slots at rank one -/

/-- The only possible past set on the one-event antichain. -/
def rankOneCausalPast (member : Bool) :
    CausalPastSet (cardinalCausalAntichain 1) where
  mem := fun _ => member
  downwardClosed := by
    intro x y hx _
    fin_cases x
    fin_cases y
    exact hx

/-- Past sets of the one-event parent are exactly one Boolean choice. -/
def rankOneCausalPastEquiv :
    CausalPastSet (cardinalCausalAntichain 1) ≃ Bool where
  toFun past := past.mem 0
  invFun := rankOneCausalPast
  left_inv := by
    intro past
    apply CausalPastSet.ext
    funext i
    fin_cases i
    rfl
  right_inv := by
    intro member
    rfl

@[simp]
theorem rankOneCausalPast_false_maximalCount :
    (rankOneCausalPast false).maximalCount = 0 := by
  unfold CausalPastSet.maximalCount
  simp [CausalPastSet.IsMaximal, rankOneCausalPast]

@[simp]
theorem rankOneCausalPast_true_maximalCount :
    (rankOneCausalPast true).maximalCount = 1 := by
  unfold CausalPastSet.maximalCount
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro first second
    apply Subtype.ext
    exact Subsingleton.elim first.val second.val
  · refine ⟨⟨0, ?_⟩⟩
    simp [CausalPastSet.IsMaximal, rankOneCausalPast,
      cardinalCausalAntichain]

@[simp]
theorem rankOneCausalPast_false_ancestorCount :
    (rankOneCausalPast false).ancestorCount = 0 := by
  unfold CausalPastSet.ancestorCount
  simp [rankOneCausalPast]

@[simp]
theorem rankOneCausalPast_true_ancestorCount :
    (rankOneCausalPast true).ancestorCount = 1 := by
  unfold CausalPastSet.ancestorCount
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro first second
    apply Subtype.ext
    exact Subsingleton.elim first.val second.val
  · exact ⟨⟨0, rfl⟩⟩

/-! ## 3. The selected full causal growth law -/

/-- Covariant raw-edge law selected by one microscopic chirality sector. -/
def chiralCausalEdgeAmplitude (chirality : Fin 2) :
    CovariantComplexCausalEdgeAmplitude :=
  rideoutSorkinSignatureAmplitude
    (chiralMultiplicativeSignatureWeight chirality)

/-- Totalized normalized growth: it follows the chiral character wherever its
local partition is nonzero and falls back to the uniform precursor law only at
an exceptional zero. -/
def chiralCausalSetGrowthLaw (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  totalizedCausalEdgeGrowthLaw (chiralCausalEdgeAmplitude chirality)

/-- At the first nontrivial parent the raw partition is exactly `1 ± i`. -/
theorem chiral_rankOne_partition (chirality : Fin 2) :
    causalEdgeAmplitudePartition (chiralCausalEdgeAmplitude chirality)
        (cardinalCausalAntichain 1) =
      1 + chiralMaximalEventPhase chirality := by
  classical
  unfold causalEdgeAmplitudePartition
  calc
    (∑ past : CausalPastSet (cardinalCausalAntichain 1),
        (chiralCausalEdgeAmplitude chirality).amplitude
          (cardinalCausalAntichain 1) past) =
        ∑ member : Bool,
          (chiralCausalEdgeAmplitude chirality).amplitude
            (cardinalCausalAntichain 1) (rankOneCausalPast member) := by
      apply Fintype.sum_equiv rankOneCausalPastEquiv
      intro past
      congr 2
      exact rankOneCausalPastEquiv.symm_apply_apply past |>.symm
    _ = 1 + chiralMaximalEventPhase chirality := by
      simp [chiralCausalEdgeAmplitude,
        rideoutSorkinSignatureAmplitude,
        chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight, add_comm]

theorem chiral_rankOne_partition_ne_zero (chirality : Fin 2) :
    causalEdgeAmplitudePartition (chiralCausalEdgeAmplitude chirality)
      (cardinalCausalAntichain 1) ≠ 0 := by
  rw [chiral_rankOne_partition]
  intro hZero
  have hReal := congrArg Complex.re hZero
  fin_cases chirality <;> norm_num [chiralMaximalEventPhase] at hReal

/-! ## 4. The phase survives the unlabeled child quotient -/

theorem rankOneCausalPast_cases
    (past : CausalPastSet (cardinalCausalAntichain 1)) :
    past = rankOneCausalPast false ∨
      past = rankOneCausalPast true := by
  cases hMember : past.mem 0 with
  | false =>
      left
      apply CausalPastSet.ext
      funext i
      fin_cases i
      simpa [rankOneCausalPast] using hMember
  | true =>
      right
      apply CausalPastSet.ext
      funext i
      fin_cases i
      simpa [rankOneCausalPast] using hMember

/-- The two-event antichain obtained from the empty precursor. -/
def rankOneGregariousChild : UnlabeledCardinalCausalOrder 2 :=
  causalTransitionTarget (cardinalCausalAntichain 1)
    (rankOneCausalPast false)

/-- The two-event chain obtained from the full precursor. -/
def rankOneTimidChild : UnlabeledCardinalCausalOrder 2 :=
  causalTransitionTarget (cardinalCausalAntichain 1)
    (rankOneCausalPast true)

/-- Empty and full precursors remain distinct after quotienting by genuine
order isomorphism: the former produces an antichain and the latter a chain. -/
theorem rankOne_children_ne :
    rankOneGregariousChild ≠ rankOneTimidChild := by
  intro hEqual
  have hIso : CardinalCausalOrderIsomorphic
      (precursorOneElementExtension (cardinalCausalAntichain 1)
        (rankOneCausalPast false))
      (precursorOneElementExtension (cardinalCausalAntichain 1)
        (rankOneCausalPast true)) :=
    Quotient.exact hEqual
  obtain ⟨equivalence, hRel⟩ := hIso
  let oldPreimage : Fin 2 := equivalence.symm 0
  let newPreimage : Fin 2 := equivalence.symm 1
  have hDistinct : oldPreimage ≠ newPreimage := by
    intro h
    have := congrArg equivalence h
    simpa [oldPreimage, newPreimage] using this
  have hTransport := hRel oldPreimage newPreimage
  have hRightBase :
      (precursorOneElementExtension (cardinalCausalAntichain 1)
        (rankOneCausalPast true)).rel
          0 1 = true := by decide
  have hRight :
      (precursorOneElementExtension (cardinalCausalAntichain 1)
        (rankOneCausalPast true)).rel
          (equivalence oldPreimage) (equivalence newPreimage) = true := by
    simpa [oldPreimage, newPreimage] using hRightBase
  have hOnlyReflexive : ∀ i j : Fin 2,
      (precursorOneElementExtension (cardinalCausalAntichain 1)
        (rankOneCausalPast false)).rel i j = true → i = j := by
    intro i j hij
    apply (finSumFinEquiv (m := 1) (n := 1)).symm.injective
    rcases hi : (finSumFinEquiv (m := 1) (n := 1)).symm i with old | old <;>
      rcases hj : (finSumFinEquiv (m := 1) (n := 1)).symm j with new | new
    · have hOldNew : old = new := by
        simpa [precursorOneElementExtension, precursorExtensionRel,
          hi, hj, cardinalCausalAntichain] using hij
      simpa [hi, hj, hOldNew]
    · simp [precursorOneElementExtension, precursorExtensionRel,
        hi, hj, rankOneCausalPast] at hij
    · simp [precursorOneElementExtension, precursorExtensionRel,
        hi, hj] at hij
    · congr
      exact Subsingleton.elim old new
  have hLeftTrue :
      (precursorOneElementExtension (cardinalCausalAntichain 1)
        (rankOneCausalPast false)).rel oldPreimage newPreimage = true :=
    hTransport.trans hRight
  exact hDistinct (hOnlyReflexive oldPreimage newPreimage hLeftTrue)

private theorem rankOne_gregarious_fiber_unique :
    ∀ transition : LabeledCausalTransitionFiber
        (cardinalCausalAntichain 1) rankOneGregariousChild,
      transition.val = rankOneCausalPast false := by
  intro transition
  rcases rankOneCausalPast_cases transition.val with hEmpty | hFull
  · exact hEmpty
  · exfalso
    apply rankOne_children_ne
    exact transition.property.symm.trans
      (congrArg (causalTransitionTarget (cardinalCausalAntichain 1)) hFull)

private theorem rankOne_timid_fiber_unique :
    ∀ transition : LabeledCausalTransitionFiber
        (cardinalCausalAntichain 1) rankOneTimidChild,
      transition.val = rankOneCausalPast true := by
  intro transition
  rcases rankOneCausalPast_cases transition.val with hEmpty | hFull
  · exfalso
    apply rankOne_children_ne
    exact (congrArg (causalTransitionTarget (cardinalCausalAntichain 1))
      hEmpty).symm.trans transition.property
  · exact hFull

theorem chiral_rankOne_gregarious_aggregate (chirality : Fin 2) :
    labeledAggregatedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude chirality)
        (cardinalCausalAntichain 1) rankOneGregariousChild = 1 := by
  classical
  let chosen : LabeledCausalTransitionFiber
      (cardinalCausalAntichain 1) rankOneGregariousChild :=
    ⟨rankOneCausalPast false, rfl⟩
  letI : Unique (LabeledCausalTransitionFiber
      (cardinalCausalAntichain 1) rankOneGregariousChild) := ⟨⟨chosen⟩, by
      intro transition
      apply Subtype.ext
      exact rankOne_gregarious_fiber_unique transition⟩
  unfold labeledAggregatedCausalEdgeAmplitude
  rw [Fintype.sum_unique]
  rw [Unique.default_eq chosen]
  simp [chosen, chiralCausalEdgeAmplitude,
    rideoutSorkinSignatureAmplitude,
    chiralMultiplicativeSignatureWeight,
    multiplicativeSignatureWeight]

theorem chiral_rankOne_timid_aggregate (chirality : Fin 2) :
    labeledAggregatedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude chirality)
        (cardinalCausalAntichain 1) rankOneTimidChild =
      chiralMaximalEventPhase chirality := by
  classical
  let chosen : LabeledCausalTransitionFiber
      (cardinalCausalAntichain 1) rankOneTimidChild :=
    ⟨rankOneCausalPast true, rfl⟩
  letI : Unique (LabeledCausalTransitionFiber
      (cardinalCausalAntichain 1) rankOneTimidChild) := ⟨⟨chosen⟩, by
      intro transition
      apply Subtype.ext
      exact rankOne_timid_fiber_unique transition⟩
  unfold labeledAggregatedCausalEdgeAmplitude
  rw [Fintype.sum_unique]
  rw [Unique.default_eq chosen]
  simp [chosen, chiralCausalEdgeAmplitude,
    rideoutSorkinSignatureAmplitude,
    chiralMultiplicativeSignatureWeight,
    multiplicativeSignatureWeight]

/-- There is exactly one unlabeled causal order on one event. -/
theorem unlabeledCardinalCausalOrder_one_unique
    (parent : UnlabeledCardinalCausalOrder 1) :
    parent = Quotient.mk _ (cardinalCausalAntichain 1) := by
  refine Quotient.inductionOn parent ?_
  intro parentRep
  apply unlabeledCardinalOrder_eq_of_isomorphic
  refine ⟨Equiv.refl _, ?_⟩
  intro i j
  fin_cases i
  fin_cases j
  simpa [cardinalCausalAntichain] using parentRep.refl 0

theorem chiral_rankOne_gregarious_transition
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (chiralCausalSetGrowthLaw chirality).transition 1 pathPrefix
        rankOneGregariousChild =
      1 / (1 + chiralMaximalEventPhase chirality) := by
  unfold chiralCausalSetGrowthLaw totalizedCausalEdgeGrowthLaw
  change totalizedNormalizedCausalEdgeAmplitude
      (chiralCausalEdgeAmplitude chirality)
      (currentUnlabeledCausalOrder 1 pathPrefix)
      rankOneGregariousChild = _
  rw [unlabeledCardinalCausalOrder_one_unique
    (currentUnlabeledCausalOrder 1 pathPrefix)]
  have hPhase : 1 + chiralMaximalEventPhase chirality ≠ 0 := by
    intro hZero
    apply chiral_rankOne_partition_ne_zero chirality
    rw [chiral_rankOne_partition]
    exact hZero
  simp only [totalizedNormalizedCausalEdgeAmplitude,
    unlabeledCausalEdgeAmplitudePartition_mk,
    unlabeledAggregatedCausalEdgeAmplitude_mk,
    chiral_rankOne_partition, hPhase, if_false,
    chiral_rankOne_gregarious_aggregate]

theorem chiral_rankOne_timid_transition
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (chiralCausalSetGrowthLaw chirality).transition 1 pathPrefix
        rankOneTimidChild =
      chiralMaximalEventPhase chirality /
        (1 + chiralMaximalEventPhase chirality) := by
  unfold chiralCausalSetGrowthLaw totalizedCausalEdgeGrowthLaw
  change totalizedNormalizedCausalEdgeAmplitude
      (chiralCausalEdgeAmplitude chirality)
      (currentUnlabeledCausalOrder 1 pathPrefix)
      rankOneTimidChild = _
  rw [unlabeledCardinalCausalOrder_one_unique
    (currentUnlabeledCausalOrder 1 pathPrefix)]
  have hPhase : 1 + chiralMaximalEventPhase chirality ≠ 0 := by
    intro hZero
    apply chiral_rankOne_partition_ne_zero chirality
    rw [chiral_rankOne_partition]
    exact hZero
  simp only [totalizedNormalizedCausalEdgeAmplitude,
    unlabeledCausalEdgeAmplitudePartition_mk,
    unlabeledAggregatedCausalEdgeAmplitude_mk,
    chiral_rankOne_partition, hPhase, if_false,
    chiral_rankOne_timid_aggregate]

/-- The two selected elementary phases square to minus one. -/
theorem chiralMaximalEventPhase_mul_self (chirality : Fin 2) :
    chiralMaximalEventPhase chirality *
        chiralMaximalEventPhase chirality = -1 := by
  fin_cases chirality <;>
    norm_num [chiralMaximalEventPhase, Complex.I_mul_I]

private theorem chiral_phase_partition_ne_zero (chirality : Fin 2) :
    1 + chiralMaximalEventPhase chirality ≠ 0 := by
  intro hZero
  apply chiral_rankOne_partition_ne_zero chirality
  rw [chiral_rankOne_partition]
  exact hZero

/-- Closed form of the normalized full-precursor amplitude. -/
theorem chiral_normalized_timid_amplitude (chirality : Fin 2) :
    chiralMaximalEventPhase chirality /
        (1 + chiralMaximalEventPhase chirality) =
      (1 + chiralMaximalEventPhase chirality) / 2 := by
  apply (div_eq_iff (chiral_phase_partition_ne_zero chirality)).2
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  calc
    chiralMaximalEventPhase chirality * 2 =
        1 + 2 * chiralMaximalEventPhase chirality +
          chiralMaximalEventPhase chirality *
            chiralMaximalEventPhase chirality := by
      rw [chiralMaximalEventPhase_mul_self]
      ring
    _ = (1 + chiralMaximalEventPhase chirality) ^ 2 := by ring
    _ = (1 + chiralMaximalEventPhase chirality) *
        (1 + chiralMaximalEventPhase chirality) := by rw [pow_two]

/-- Closed form of the normalized empty-precursor amplitude. -/
theorem chiral_normalized_gregarious_amplitude (chirality : Fin 2) :
    1 / (1 + chiralMaximalEventPhase chirality) =
      (1 - chiralMaximalEventPhase chirality) / 2 := by
  apply (div_eq_iff (chiral_phase_partition_ne_zero chirality)).2
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  calc
    1 * 2 = 1 - chiralMaximalEventPhase chirality *
        chiralMaximalEventPhase chirality := by
      rw [chiralMaximalEventPhase_mul_self]
      ring
    _ = (1 - chiralMaximalEventPhase chirality) *
        (1 + chiralMaximalEventPhase chirality) := by ring

/-! ## 5. The depth-two cylinder restriction -/

/-- At depth two, sector zero records the timid (full-precursor) birth.  This
ordering aligns the induced coherence sign with the microscopic phase. -/
def chiralRankTwoTimidSector :
    Finset (RankedGrowthPath CausalSetGrowthBranch 2) :=
  (Finset.univ : Finset
      (RankedGrowthPath CausalSetGrowthBranch 1)) ×ˢ
    {rankOneTimidChild}

/-- The complementary cylinder event contains the gregarious birth (and all
zero-amplitude non-successors). -/
def chiralRankTwoGregariousSector :
    Finset (RankedGrowthPath CausalSetGrowthBranch 2) :=
  Finset.univ \ chiralRankTwoTimidSector

/-- Complete two-sector coarse graining of unlabeled depth-two histories. -/
def chiralRankTwoCoarseGraining : OrientationCylinderCoarseGraining where
  depth := 2
  sector := fun orientation =>
    if orientation = 0 then chiralRankTwoTimidSector
    else chiralRankTwoGregariousSector
  disjoint := by
    have hOne : (1 : Fin 2) ≠ 0 := by decide
    simp only [if_pos, hOne, if_false]
    exact Finset.disjoint_sdiff
  exhaustive := by
    have hOne : (1 : Fin 2) ≠ 0 := by decide
    simp only [if_pos, hOne, if_false]
    simp [chiralRankTwoGregariousSector]

@[simp]
theorem chiralRankTwoCoarseGraining_sector_zero :
    chiralRankTwoCoarseGraining.sector 0 = chiralRankTwoTimidSector := by
  simp [chiralRankTwoCoarseGraining]

@[simp]
theorem chiralRankTwoCoarseGraining_sector_one :
    chiralRankTwoCoarseGraining.sector 1 =
      chiralRankTwoGregariousSector := by
  have hOne : (1 : Fin 2) ≠ 0 := by decide
  simp [chiralRankTwoCoarseGraining, hOne]

/-- The full-precursor cylinder amplitude is the normalized chiral phase. -/
theorem chiral_rankTwo_timid_event_amplitude (chirality : Fin 2) :
    ∑ path ∈ chiralRankTwoTimidSector,
        finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path =
      chiralMaximalEventPhase chirality /
        (1 + chiralMaximalEventPhase chirality) := by
  classical
  unfold chiralRankTwoTimidSector
  have hProduct := Finset.sum_product
    (Finset.univ : Finset
      (RankedGrowthPath CausalSetGrowthBranch 1))
    ({rankOneTimidChild} : Finset (CausalSetGrowthBranch 1))
    (finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2)
  calc
    (∑ path ∈
          (Finset.univ : Finset
            (RankedGrowthPath CausalSetGrowthBranch 1)) ×ˢ
            ({rankOneTimidChild} : Finset (CausalSetGrowthBranch 1)),
          finiteRankedPathAmplitude
            (chiralCausalSetGrowthLaw chirality) 2 path) =
        (∑ pathPrefix ∈ (Finset.univ : Finset
            (RankedGrowthPath CausalSetGrowthBranch 1)),
          ∑ child ∈ ({rankOneTimidChild} :
              Finset (CausalSetGrowthBranch 1)),
            finiteRankedPathAmplitude
              (chiralCausalSetGrowthLaw chirality) 2 (pathPrefix, child)) := by
        simpa only [RankedGrowthPath] using hProduct
    _ = chiralMaximalEventPhase chirality /
        (1 + chiralMaximalEventPhase chirality) := by
      simp_rw [Finset.sum_singleton, finiteRankedPathAmplitude_snoc,
        chiral_rankOne_timid_transition]
      rw [← Finset.sum_mul]
      simp [finiteRankedPathAmplitude_sum_univ]

/-- The complementary cylinder amplitude is the normalized empty-precursor
amplitude.  This uses total normalization, so it also covers all formally
available but zero-amplitude non-successor branches. -/
theorem chiral_rankTwo_gregarious_event_amplitude (chirality : Fin 2) :
    ∑ path ∈ chiralRankTwoGregariousSector,
        finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path =
      1 / (1 + chiralMaximalEventPhase chirality) := by
  classical
  let amplitude := finiteRankedPathAmplitude
    (chiralCausalSetGrowthLaw chirality) 2
  have hDisjoint : Disjoint chiralRankTwoTimidSector
      chiralRankTwoGregariousSector := by
    exact Finset.disjoint_sdiff
  have hExhaustive : chiralRankTwoTimidSector ∪
      chiralRankTwoGregariousSector = Finset.univ := by
    simp [chiralRankTwoGregariousSector]
  have hUnion := Finset.sum_union hDisjoint (f := amplitude)
  rw [hExhaustive] at hUnion
  have hTotal : ∑ path, amplitude path = 1 :=
    finiteRankedPathAmplitude_sum_univ
      (chiralCausalSetGrowthLaw chirality) 2
  have hTimid := chiral_rankTwo_timid_event_amplitude chirality
  change (∑ path ∈ chiralRankTwoGregariousSector, amplitude path) = _
  have hPhase : 1 + chiralMaximalEventPhase chirality ≠ 0 := by
    intro hZero
    apply chiral_rankOne_partition_ne_zero chirality
    rw [chiral_rankOne_partition]
    exact hZero
  rw [hTimid, hTotal] at hUnion
  calc
    (∑ path ∈ chiralRankTwoGregariousSector, amplitude path) =
        1 - chiralMaximalEventPhase chirality /
          (1 + chiralMaximalEventPhase chirality) := by
      calc
        (∑ path ∈ chiralRankTwoGregariousSector, amplitude path) =
            (chiralMaximalEventPhase chirality /
                (1 + chiralMaximalEventPhase chirality) +
              ∑ path ∈ chiralRankTwoGregariousSector, amplitude path) -
                chiralMaximalEventPhase chirality /
                  (1 + chiralMaximalEventPhase chirality) := by ring
        _ = 1 - chiralMaximalEventPhase chirality /
            (1 + chiralMaximalEventPhase chirality) := by rw [← hUnion]
    _ = 1 / (1 + chiralMaximalEventPhase chirality) := by
      field_simp [hPhase] <;> ring

theorem chiral_rankTwo_sector_event_amplitude
    (chirality orientation : Fin 2) :
    ∑ path ∈ chiralRankTwoCoarseGraining.sector orientation,
        finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path =
      if orientation = 0 then
        chiralMaximalEventPhase chirality /
          (1 + chiralMaximalEventPhase chirality)
      else
        1 / (1 + chiralMaximalEventPhase chirality) := by
  by_cases hZero : orientation = 0
  · subst orientation
    simpa using chiral_rankTwo_timid_event_amplitude chirality
  · have hSector : chiralRankTwoCoarseGraining.sector orientation =
        chiralRankTwoGregariousSector := by
      simp [chiralRankTwoCoarseGraining, hZero]
    rw [hSector]
    simpa [hZero] using
      chiral_rankTwo_gregarious_event_amplitude chirality

/-- The complete unlabeled growth law induces exactly the pure orientation
kernel selected by its microscopic chirality at the first branching depth. -/
theorem chiral_inducedOrientationKernel_exact (chirality : Fin 2) :
    inducedOrientationKernel (chiralCausalSetGrowthLaw chirality)
        chiralRankTwoCoarseGraining =
      balancedHistoryKernel
        (chiralBoundaryOrientationParameter chirality) := by
  ext first second
  change growthEventDecoherence
      (finiteRankedDepthDecoherence
        (chiralCausalSetGrowthLaw chirality) 2)
      (chiralRankTwoCoarseGraining.sector first)
      (chiralRankTwoCoarseGraining.sector second) = _
  unfold finiteRankedDepthDecoherence
  rw [amplitude_growthEventDecoherence_eq]
  let selectedAmplitude : Fin 2 → ℂ := fun orientation =>
    if orientation = 0 then
      (1 + chiralMaximalEventPhase chirality) / 2
    else
      (1 - chiralMaximalEventPhase chirality) / 2
  have hFirst :
      (∑ path ∈ chiralRankTwoCoarseGraining.sector first,
        finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path) =
      selectedAmplitude first := by
    rw [chiral_rankTwo_sector_event_amplitude]
    unfold selectedAmplitude
    split
    · exact chiral_normalized_timid_amplitude chirality
    · exact chiral_normalized_gregarious_amplitude chirality
  have hSecond :
      (∑ path ∈ chiralRankTwoCoarseGraining.sector second,
        finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path) =
      selectedAmplitude second := by
    rw [chiral_rankTwo_sector_event_amplitude]
    unfold selectedAmplitude
    split
    · exact chiral_normalized_timid_amplitude chirality
    · exact chiral_normalized_gregarious_amplitude chirality
  calc
    _ = selectedAmplitude first * star (selectedAmplitude second) :=
      congrArg₂ (fun firstAmplitude secondAmplitude : ℂ =>
        firstAmplitude * star secondAmplitude) hFirst hSecond
    _ = balancedHistoryKernel
        (chiralBoundaryOrientationParameter chirality) first second := by
      by_cases hFirstZero : first = 0
      · subst first
        by_cases hSecondZero : second = 0
        · subst second
          fin_cases chirality <;>
            norm_num [selectedAmplitude, balancedHistoryKernel,
              chiralBoundaryOrientationParameter, chiralMaximalEventPhase,
              chiral_normalized_timid_amplitude,
              chiral_normalized_gregarious_amplitude, Complex.ext_iff]
        · rw [Fin.eq_one_of_ne_zero second hSecondZero]
          fin_cases chirality <;>
            norm_num [selectedAmplitude, balancedHistoryKernel,
              chiralBoundaryOrientationParameter, chiralMaximalEventPhase,
              chiral_normalized_timid_amplitude,
              chiral_normalized_gregarious_amplitude, Complex.ext_iff]
      · rw [Fin.eq_one_of_ne_zero first hFirstZero]
        by_cases hSecondZero : second = 0
        · subst second
          fin_cases chirality <;>
            norm_num [selectedAmplitude, balancedHistoryKernel,
              chiralBoundaryOrientationParameter, chiralMaximalEventPhase,
              chiral_normalized_timid_amplitude,
              chiral_normalized_gregarious_amplitude, Complex.ext_iff]
        · rw [Fin.eq_one_of_ne_zero second hSecondZero]
          fin_cases chirality <;>
            norm_num [selectedAmplitude, balancedHistoryKernel,
              chiralBoundaryOrientationParameter, chiralMaximalEventPhase,
              chiral_normalized_timid_amplitude,
              chiral_normalized_gregarious_amplitude, Complex.ext_iff]

theorem chiralRankTwoCoarseGraining_balanced (chirality : Fin 2) :
    chiralRankTwoCoarseGraining.IsBalanced
      (chiralCausalSetGrowthLaw chirality) := by
  unfold OrientationCylinderCoarseGraining.IsBalanced
  rw [chiral_inducedOrientationKernel_exact]
  norm_num [balancedHistoryKernel]

theorem chiral_inducedOrientationParameter_exact (chirality : Fin 2) :
    inducedOrientationParameter (chiralCausalSetGrowthLaw chirality)
        chiralRankTwoCoarseGraining =
      chiralBoundaryOrientationParameter chirality := by
  unfold inducedOrientationParameter
  rw [chiral_inducedOrientationKernel_exact]
  norm_num [balancedHistoryKernel]

/-- Capstone: a local balance law selects `±i`; the corresponding normalized,
projectively consistent unlabeled growth law realizes the matching pure
orientation kernel on its first nontrivial cylinder partition. -/
theorem microscopic_balance_derives_chiral_orientation_endpoint :
    (∀ b : ℂ, 1 + b ≠ 0 →
      Complex.normSq (1 / (1 + b)) = 1 / 2 →
      Complex.normSq (b / (1 + b)) = 1 / 2 →
      b = Complex.I ∨ b = -Complex.I)
      ∧ (∀ chirality : Fin 2,
        chiralRankTwoCoarseGraining.IsBalanced
            (chiralCausalSetGrowthLaw chirality)
          ∧ inducedOrientationKernel (chiralCausalSetGrowthLaw chirality)
              chiralRankTwoCoarseGraining =
            balancedHistoryKernel
              (chiralBoundaryOrientationParameter chirality)
          ∧ |chiralBoundaryOrientationParameter chirality| = 1 / 2) := by
  exact ⟨balanced_normalized_binary_birth_forces_quarter_turn,
    fun chirality => ⟨chiralRankTwoCoarseGraining_balanced chirality,
      chiral_inducedOrientationKernel_exact chirality,
      chiralBoundaryOrientationParameter_endpoint chirality⟩⟩

#print axioms balanced_normalized_binary_birth_forces_quarter_turn
#print axioms chiral_rankOne_partition
#print axioms rankOne_children_ne
#print axioms chiral_rankTwo_timid_event_amplitude
#print axioms chiral_inducedOrientationKernel_exact
#print axioms microscopic_balance_derives_chiral_orientation_endpoint

end

end UnifiedTheory.Audit.KFCausalSetChiralGrowth
