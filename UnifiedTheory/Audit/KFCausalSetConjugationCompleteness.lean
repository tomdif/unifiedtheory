/-
  Audit/KFCausalSetConjugationCompleteness.lean

  COMPLEX-CONJUGATION COMPLETENESS OF CHIRAL SEQUENTIAL GROWTH

  The two microscopic quarter-turn laws are not independent dynamics.
  Complex conjugation exchanges them before normalization, through the
  exceptional uniform fallback, along every finite path, and on the quotient
  algebra of infinite cylinder events.  Their real quantum measures are
  consequently identical at every refinement depth.

  The maximal-birth source is also not a second geometric channel: it is
  definitionally the reflection-odd volume residual at the newborn.  Geometry
  supplies an interior source and the balanced quantum response retains only
  its sign, landing on the pure conjugate boundary pair.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality
import UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetConjugationCompleteness

noncomputable section

open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
open UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness
open UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality

/-! ## 1. Conjugation before and after normalization -/

@[simp]
theorem reflectedMicroscopicChirality_involutive (chirality : Fin 2) :
    reflectedMicroscopicChirality
        (reflectedMicroscopicChirality chirality) = chirality := by
  fin_cases chirality <;> norm_num [reflectedMicroscopicChirality]

theorem chiralCausalEdgeAmplitude_star (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    star ((chiralCausalEdgeAmplitude chirality).amplitude parent past) =
      (chiralCausalEdgeAmplitude
        (reflectedMicroscopicChirality chirality)).amplitude parent past := by
  exact chiralMultiplicativeSignatureWeight_reflection chirality
    past.ancestorCount past.maximalCount

theorem chiral_causalEdgeAmplitudePartition_star (chirality : Fin 2)
    {n : ℕ} (parent : CardinalCausalOrder n) :
    star (causalEdgeAmplitudePartition
        (chiralCausalEdgeAmplitude chirality) parent) =
      causalEdgeAmplitudePartition
        (chiralCausalEdgeAmplitude
          (reflectedMicroscopicChirality chirality)) parent := by
  classical
  unfold causalEdgeAmplitudePartition
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro past _
  exact chiralCausalEdgeAmplitude_star chirality parent past

theorem chiral_labeledAggregatedCausalEdgeAmplitude_star
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    star (labeledAggregatedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude chirality) parent child) =
      labeledAggregatedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude
          (reflectedMicroscopicChirality chirality)) parent child := by
  classical
  unfold labeledAggregatedCausalEdgeAmplitude
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro past _
  exact chiralCausalEdgeAmplitude_star chirality parent past.val

theorem chiral_unlabeledAggregatedCausalEdgeAmplitude_star
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    star (unlabeledAggregatedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude chirality) parent child) =
      unlabeledAggregatedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude
          (reflectedMicroscopicChirality chirality)) parent child := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact chiral_labeledAggregatedCausalEdgeAmplitude_star
    chirality parentRepresentative child

theorem chiral_unlabeledCausalEdgeAmplitudePartition_star
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    star (unlabeledCausalEdgeAmplitudePartition
        (chiralCausalEdgeAmplitude chirality) parent) =
      unlabeledCausalEdgeAmplitudePartition
        (chiralCausalEdgeAmplitude
          (reflectedMicroscopicChirality chirality)) parent := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact chiral_causalEdgeAmplitudePartition_star
    chirality parentRepresentative

@[simp]
theorem uniformRideoutSorkinAggregatedTransition_star {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    star (uniformRideoutSorkinAggregatedTransition parent child) =
      uniformRideoutSorkinAggregatedTransition parent child := by
  simp [uniformRideoutSorkinAggregatedTransition]

theorem chiral_totalizedNormalizedCausalEdgeAmplitude_star
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    star (totalizedNormalizedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude chirality) parent child) =
      totalizedNormalizedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude
          (reflectedMicroscopicChirality chirality)) parent child := by
  classical
  have hPartition :=
    chiral_unlabeledCausalEdgeAmplitudePartition_star chirality parent
  by_cases hZero : unlabeledCausalEdgeAmplitudePartition
      (chiralCausalEdgeAmplitude chirality) parent = 0
  · have hReflectedZero : unlabeledCausalEdgeAmplitudePartition
        (chiralCausalEdgeAmplitude
          (reflectedMicroscopicChirality chirality)) parent = 0 := by
      rw [← hPartition, hZero]
      simp
    unfold totalizedNormalizedCausalEdgeAmplitude
    rw [if_pos hZero, if_pos hReflectedZero]
    exact uniformRideoutSorkinAggregatedTransition_star parent child
  · have hReflectedNonzero : unlabeledCausalEdgeAmplitudePartition
        (chiralCausalEdgeAmplitude
          (reflectedMicroscopicChirality chirality)) parent ≠ 0 := by
      intro hReflectedZero
      apply hZero
      have hStarZero : star (unlabeledCausalEdgeAmplitudePartition
          (chiralCausalEdgeAmplitude chirality) parent) = 0 :=
        hPartition.trans hReflectedZero
      simpa using congrArg star hStarZero
    unfold totalizedNormalizedCausalEdgeAmplitude
    rw [if_neg hZero, if_neg hReflectedNonzero]
    simp only [div_eq_mul_inv, star_mul', star_inv₀]
    rw [chiral_unlabeledAggregatedCausalEdgeAmplitude_star, hPartition]

theorem chiralCausalSetGrowthLaw_transition_star (chirality : Fin 2)
    {n : ℕ} (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    star ((chiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child) =
      (chiralCausalSetGrowthLaw
        (reflectedMicroscopicChirality chirality)).transition
          n pathPrefix child := by
  exact chiral_totalizedNormalizedCausalEdgeAmplitude_star chirality
    (currentUnlabeledCausalOrder n pathPrefix) child

/-! ## 2. The conjugation diagram at every finite depth -/

theorem chiral_finiteRankedPathAmplitude_star (chirality : Fin 2) :
    ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      star (finiteRankedPathAmplitude
          (chiralCausalSetGrowthLaw chirality) n path) =
        finiteRankedPathAmplitude
          (chiralCausalSetGrowthLaw
            (reflectedMicroscopicChirality chirality)) n path
  | 0, path => by simp
  | n + 1, path => by
      rcases path with ⟨pathPrefix, branch⟩
      rw [finiteRankedPathAmplitude_snoc,
        finiteRankedPathAmplitude_snoc, star_mul']
      rw [chiral_finiteRankedPathAmplitude_star chirality n pathPrefix,
        chiralCausalSetGrowthLaw_transition_star]

theorem chiral_finiteRankedDepthDecoherence_star (chirality : Fin 2)
    (n : ℕ) (first second : RankedGrowthPath CausalSetGrowthBranch n) :
    star (finiteRankedDepthDecoherence
        (chiralCausalSetGrowthLaw chirality) n first second) =
      finiteRankedDepthDecoherence
        (chiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)) n first second := by
  unfold finiteRankedDepthDecoherence amplitudeDecoherence
  rw [star_mul']
  simp only [star_star]
  rw [chiral_finiteRankedPathAmplitude_star,
    chiral_finiteRankedPathAmplitude_star]
  simp [reflectedMicroscopicChirality_involutive]

theorem chiral_finiteGrowthEventDecoherence_star (chirality : Fin 2)
    (n : ℕ)
    (first second : Finset (RankedGrowthPath CausalSetGrowthBranch n)) :
    star (growthEventDecoherence
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw chirality) n) first second) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw
            (reflectedMicroscopicChirality chirality)) n) first second := by
  classical
  unfold growthEventDecoherence
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro history hHistory
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro other hOther
  exact chiral_finiteRankedDepthDecoherence_star
    chirality n history other

/-- The two sectors assign the same real quantum measure to every finite
event, not only to individual histories. -/
theorem chiral_finiteGrowthQuantumMeasure_eq (chirality : Fin 2)
    (n : ℕ)
    (event : Finset (RankedGrowthPath CausalSetGrowthBranch n)) :
    growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw chirality) n) event =
      growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw
            (reflectedMicroscopicChirality chirality)) n) event := by
  unfold growthQuantumMeasure
  rw [← chiral_finiteGrowthEventDecoherence_star]
  simp

/-- Conjugation commutes with every finite number of refinement layers. -/
theorem chiral_conjugation_commutes_with_refinement (chirality : Fin 2)
    (n : ℕ)
    (first second : Finset (RankedGrowthPath CausalSetGrowthBranch n))
    (steps : ℕ) :
    star (growthEventDecoherence
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw chirality) (n + steps))
        (refineRankedGrowthEventBy first steps)
        (refineRankedGrowthEventBy second steps)) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw
            (reflectedMicroscopicChirality chirality)) n) first second := by
  rw [chiral_finiteGrowthEventDecoherence_star]
  exact finiteRankedDepthDecoherence_projective_by
    (chiralCausalSetGrowthLaw
      (reflectedMicroscopicChirality chirality)) n first second steps

/-! ## 3. Descent to complete unlabeled cylinder histories -/

theorem chiral_rankedCylinderPresentationAmplitude_star
    (chirality : Fin 2)
    (cylinder : RankedCylinderPresentation CausalSetGrowthBranch) :
    star (rankedCylinderPresentationAmplitude
        (chiralCausalSetGrowthLaw chirality) cylinder) =
      rankedCylinderPresentationAmplitude
        (chiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)) cylinder := by
  classical
  unfold rankedCylinderPresentationAmplitude
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro path hPath
  exact chiral_finiteRankedPathAmplitude_star
    chirality cylinder.depth path

theorem chiral_infiniteRankedCylinderAmplitude_star
    (chirality : Fin 2)
    (event : InfiniteRankedCylinderEvent CausalSetGrowthBranch) :
    star (infiniteRankedCylinderAmplitude
        (chiralCausalSetGrowthLaw chirality) event) =
      infiniteRankedCylinderAmplitude
        (chiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)) event := by
  refine Quotient.inductionOn event ?_
  intro cylinder
  exact chiral_rankedCylinderPresentationAmplitude_star chirality cylinder

theorem chiral_infiniteRankedCylinderDecoherence_star
    (chirality : Fin 2)
    (first second : InfiniteRankedCylinderEvent CausalSetGrowthBranch) :
    star (infiniteRankedCylinderDecoherence
        (chiralCausalSetGrowthLaw chirality) first second) =
      infiniteRankedCylinderDecoherence
        (chiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)) first second := by
  unfold infiniteRankedCylinderDecoherence amplitudeDecoherence
  rw [star_mul']
  simp only [star_star]
  rw [chiral_infiniteRankedCylinderAmplitude_star,
    chiral_infiniteRankedCylinderAmplitude_star]
  simp [reflectedMicroscopicChirality_involutive]

/-- All real cylinder-event weights agree in the two conjugate sectors. -/
theorem chiral_infiniteRankedCylinderQuantumMeasure_eq
    (chirality : Fin 2)
    (event : InfiniteRankedCylinderEvent CausalSetGrowthBranch) :
    infiniteRankedCylinderQuantumMeasure
        (chiralCausalSetGrowthLaw chirality) event =
      infiniteRankedCylinderQuantumMeasure
        (chiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)) event := by
  unfold infiniteRankedCylinderQuantumMeasure
  rw [← chiral_infiniteRankedCylinderDecoherence_star]
  simp

/-! ## 4. One explicit complete equivalence contract -/

/-- Exact scope in which the two sectors are the same theory.  The history
and event maps are identities; scalar amplitudes and off-diagonal
decoherence data are conjugated.  Every real event measure is fixed, and the
diagram commutes with arbitrary finite refinement before descending to the
infinite-cylinder quotient. -/
structure IsCompleteChiralConjugationEquivalence (chirality : Fin 2) : Prop where
  transition : ∀ {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n),
    star ((chiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child) =
      (chiralCausalSetGrowthLaw
        (reflectedMicroscopicChirality chirality)).transition
          n pathPrefix child
  finitePath : ∀ (n : ℕ)
    (path : RankedGrowthPath CausalSetGrowthBranch n),
    star (finiteRankedPathAmplitude
        (chiralCausalSetGrowthLaw chirality) n path) =
      finiteRankedPathAmplitude
        (chiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)) n path
  finiteEvent : ∀ (n : ℕ)
    (first second : Finset (RankedGrowthPath CausalSetGrowthBranch n)),
    star (growthEventDecoherence
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw chirality) n) first second) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw
            (reflectedMicroscopicChirality chirality)) n) first second
  finiteMeasure : ∀ (n : ℕ)
    (event : Finset (RankedGrowthPath CausalSetGrowthBranch n)),
    growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw chirality) n) event =
      growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw
            (reflectedMicroscopicChirality chirality)) n) event
  refinement : ∀ (n : ℕ)
    (first second : Finset (RankedGrowthPath CausalSetGrowthBranch n))
    (steps : ℕ),
    star (growthEventDecoherence
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw chirality) (n + steps))
        (refineRankedGrowthEventBy first steps)
        (refineRankedGrowthEventBy second steps)) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (chiralCausalSetGrowthLaw
            (reflectedMicroscopicChirality chirality)) n) first second
  infiniteCylinder : ∀
    (first second : InfiniteRankedCylinderEvent CausalSetGrowthBranch),
    star (infiniteRankedCylinderDecoherence
        (chiralCausalSetGrowthLaw chirality) first second) =
      infiniteRankedCylinderDecoherence
        (chiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)) first second
  infiniteMeasure : ∀
    (event : InfiniteRankedCylinderEvent CausalSetGrowthBranch),
    infiniteRankedCylinderQuantumMeasure
        (chiralCausalSetGrowthLaw chirality) event =
      infiniteRankedCylinderQuantumMeasure
        (chiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)) event

theorem completeChiralConjugationEquivalence (chirality : Fin 2) :
    IsCompleteChiralConjugationEquivalence chirality where
  transition := chiralCausalSetGrowthLaw_transition_star chirality
  finitePath := chiral_finiteRankedPathAmplitude_star chirality
  finiteEvent := chiral_finiteGrowthEventDecoherence_star chirality
  finiteMeasure := chiral_finiteGrowthQuantumMeasure_eq chirality
  refinement := chiral_conjugation_commutes_with_refinement chirality
  infiniteCylinder :=
    chiral_infiniteRankedCylinderDecoherence_star chirality
  infiniteMeasure :=
    chiral_infiniteRankedCylinderQuantumMeasure_eq chirality

/-- Sector labels are gauge-related when they are equal or exchanged by the
complete conjugation equivalence above. -/
def AreChiralCylinderGaugeEquivalent (first second : Fin 2) : Prop :=
  first = second ∨ second = reflectedMicroscopicChirality first

theorem areChiralCylinderGaugeEquivalent_all (first second : Fin 2) :
    AreChiralCylinderGaugeEquivalent first second := by
  fin_cases first <;> fin_cases second <;>
    simp [AreChiralCylinderGaugeEquivalent,
      reflectedMicroscopicChirality]

def chiralCylinderGaugeSetoid : Setoid (Fin 2) where
  r := AreChiralCylinderGaugeEquivalent
  iseqv := by
    constructor
    · intro chirality
      exact Or.inl rfl
    · intro first second _h
      exact areChiralCylinderGaugeEquivalent_all second first
    · intro first second third _hFirst _hSecond
      exact areChiralCylinderGaugeEquivalent_all first third

/-- The physical cylinder sector after quotienting the global conjugation
convention. -/
def ChiralCylinderGaugeSector := Quotient chiralCylinderGaugeSetoid

/-- There is one conjugation-gauge orbit, not two physical cylinder theories. -/
theorem chiralCylinderGaugeSector_unique
    (first second : ChiralCylinderGaugeSector) : first = second := by
  refine Quotient.inductionOn₂ first second ?_
  intro firstRepresentative secondRepresentative
  exact Quotient.sound
    (areChiralCylinderGaugeEquivalent_all
      firstRepresentative secondRepresentative)

instance : Subsingleton ChiralCylinderGaugeSector :=
  ⟨chiralCylinderGaugeSector_unique⟩

/-! ## 5. The geometric source and quantum response are one pipeline -/

/-- The growth-arrow source is exactly the previously defined geometric
orientation residual evaluated at the newborn.  This holds at every rank,
not just for the numerical `1/6` witness. -/
theorem maximalBirthSource_eq_geometricOrientationResidual {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    maximalBirthOrientationSourceQ parent past =
      causalOrientationDensityQ
        (precursorOneElementExtension parent past) (Fin.last n) := by
  rfl

/-- Consequently every finite-rank birth source is strictly inside the
balanced positivity interval. -/
theorem maximalBirthSource_strictInterior {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    |maximalBirthOrientationSourceQ parent past| < (1 : ℚ) / 2 := by
  exact causalOrientationDensityQ_strictInterior
    (precursorOneElementExtension parent past) (Fin.last n)

/-- The full-precursor extension of the two-chain is the three-chain. -/
theorem chainTwoFullBirth_child_eq_chainThree :
    precursorOneElementExtension (cardinalCausalChain 2)
        (fullCausalPastSet (cardinalCausalChain 2)) =
      cardinalCausalChain 3 := by
  apply CardinalCausalOrder.ext
  decide

/-- Rank-three check: the newborn residual of the three-chain is again
`1/6`. -/
theorem chainThreeNewborn_source_exact :
    maximalBirthOrientationSourceQ (cardinalCausalChain 2)
        (fullCausalPastSet (cardinalCausalChain 2)) = (1 : ℚ) / 6 := by
  unfold maximalBirthOrientationSourceQ
  rw [chainTwoFullBirth_child_eq_chainThree]
  rw [causalOrientationDensityQ_chain_last]
  norm_num

/-- Adding a future-maximal newborn does not alter any old event's inclusive
past. -/
theorem precursorExtension_old_pastVolumeQ {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    (i : Fin n) :
    causalPastVolumeQ (precursorOneElementExtension parent past) i.castSucc =
      causalPastVolumeQ parent i := by
  unfold causalPastVolumeQ
  rw [Fin.sum_univ_castSucc]
  simp [precursorOneElementExtension, precursorExtensionRel]

/-- Exact incidence-volume update under a maximal birth. -/
theorem precursorExtension_totalCausalPastVolumeQ {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    totalCausalPastVolumeQ (precursorOneElementExtension parent past) =
      totalCausalPastVolumeQ parent + 1 + precursorPopulationQ past := by
  unfold totalCausalPastVolumeQ
  rw [Fin.sum_univ_castSucc]
  simp_rw [precursorExtension_old_pastVolumeQ]
  rw [precursorExtension_newborn_pastVolumeQ]
  ring

/-- A different rank-three child already has a different source magnitude:
the two-antichain with a common newborn maximum gives `1/5`.  Thus the exact
source/residual identity is universal, while `1/6` itself is not. -/
theorem antichainTwoFullBirth_source_exact :
    maximalBirthOrientationSourceQ (cardinalCausalAntichain 2)
        (fullCausalPastSet (cardinalCausalAntichain 2)) = (1 : ℚ) / 5 := by
  rw [maximalBirthOrientationSourceQ_formula]
  rw [precursorExtension_totalCausalPastVolumeQ]
  have hParentVolume :
      totalCausalPastVolumeQ (cardinalCausalAntichain 2) = 2 := by
    unfold totalCausalPastVolumeQ
    simp_rw [causalPastVolumeQ_antichain]
    norm_num
  rw [hParentVolume]
  norm_num [precursorPopulationQ, fullCausalPastSet]

/-- The physically invariant statement is the correlation, not the names of
the conjugate signs: reversing the causal arrow and the transported chirality
together leaves their product unchanged at every refinement depth. -/
theorem growthArrow_chirality_lock_conjugationInvariant {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    (steps : ℕ) :
    ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) *
        inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
          (chiralRankTwoCoarseGraining.refineBy steps) =
      ((reflectedMaximalBirthOrientationSourceQ parent past : ℚ) : ℝ) *
        inducedCylinderChiralitySign causalReflectedOrientationGrowthLaw
          (chiralRankTwoCoarseGraining.refineBy steps) := by
  rw [causalPositiveOrientationGrowthLaw_sign_transport,
    causalReflectedOrientationGrowthLaw_sign_transport,
    reflectedMaximalBirthOrientationSourceQ_eq_neg]
  push_cast
  ring

/-! ## 6. Completeness statement -/

/-- **Conjugation-completeness theorem.**  On the complete unlabeled cylinder
theory, the two chiral characters form one gauge orbit.  Both representatives
are normalized by construction, Hermitian and strongly positive; their full
decoherence functionals are complex conjugates, every real cylinder quantum
measure agrees, and the equivalence commutes with arbitrary finite
refinement.  The invariant remnant is the arrow/chirality correlation.

This theorem does not identify complex conjugation with a complex-linear
map, nor does it claim a continuum CP theorem.  Its exact scope is the
real-event operational algebra and the reflection-covariant finite structures
formalized in this repository. -/
theorem sequentialGrowthChirality_conjugationCompleteness :
    IsCompleteChiralConjugationEquivalence 1
      ∧ reflectedMicroscopicChirality (1 : Fin 2) = 0
      ∧ IsHermitianGrowthFunctional
          (infiniteRankedCylinderDecoherence
            causalPositiveOrientationGrowthLaw)
      ∧ IsHermitianGrowthFunctional
          (infiniteRankedCylinderDecoherence
            causalReflectedOrientationGrowthLaw)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            causalPositiveOrientationGrowthLaw)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            causalReflectedOrientationGrowthLaw)
      ∧ (∀ first second : ChiralCylinderGaugeSector, first = second)
      ∧ (∀ {n : ℕ} (parent : CardinalCausalOrder n)
          (past : CausalPastSet parent) (steps : ℕ),
        ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) *
            inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
              (chiralRankTwoCoarseGraining.refineBy steps) =
          ((reflectedMaximalBirthOrientationSourceQ parent past : ℚ) : ℝ) *
            inducedCylinderChiralitySign
              causalReflectedOrientationGrowthLaw
              (chiralRankTwoCoarseGraining.refineBy steps)) := by
  refine ⟨completeChiralConjugationEquivalence 1, by
      norm_num [reflectedMicroscopicChirality],
    infiniteRankedCylinderDecoherence_hermitian _,
    infiniteRankedCylinderDecoherence_hermitian _,
    infiniteRankedCylinderDecoherence_stronglyPositive _,
    infiniteRankedCylinderDecoherence_stronglyPositive _,
    chiralCylinderGaugeSector_unique, ?_⟩
  intro n parent past steps
  exact growthArrow_chirality_lock_conjugationInvariant parent past steps

#print axioms chiral_totalizedNormalizedCausalEdgeAmplitude_star
#print axioms chiral_conjugation_commutes_with_refinement
#print axioms chiral_infiniteRankedCylinderDecoherence_star
#print axioms chiral_infiniteRankedCylinderQuantumMeasure_eq
#print axioms completeChiralConjugationEquivalence
#print axioms chiralCylinderGaugeSector_unique
#print axioms maximalBirthSource_eq_geometricOrientationResidual
#print axioms chainThreeNewborn_source_exact
#print axioms antichainTwoFullBirth_source_exact
#print axioms growthArrow_chirality_lock_conjugationInvariant
#print axioms sequentialGrowthChirality_conjugationCompleteness

end

end UnifiedTheory.Audit.KFCausalSetConjugationCompleteness
