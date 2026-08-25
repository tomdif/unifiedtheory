/-
  Audit/KFTOEGate1HarmonicBornShellSelection.lean

  AN ACTION-SELECTED, BI-NORMALIZED ALTERNATIVE GATE 1

  The original Gate 1 support record is hard-coded to the fixed Liouville
  zero-freeness witness.  The intrinsic selection audit instead derives a
  rank-running harmonic pair coupling from the unique exchangeable,
  unit-normalized vacuum spectator action.  The repository also already has
  an unconditional Born-shell completion of that same harmonic law.

  This module ties those two pieces together as one microscopic-law
  certificate: the action selects the raw harmonic schedule, and the
  independently defined canonical positive-radial Born-shell construction
  completes that schedule.  The resulting law is simultaneously

  * coherently normalized and Born normalized at every parent;
  * supported on genuine one-element causal extensions;
  * projective for both diagonal Born events and coherent cylinder events;
  * strongly positive and normalized on the infinite cylinder algebra; and
  * reflection-conjugate between the two chiral sectors.

  The underlying uncorrected harmonic signature law has exact full physical
  support, so its displayed 140-step CSpec atlas path is nonzero.  The honest
  remaining bridge for the Born-shell law is narrower: prove that the radial
  Born correction does not zero any of those 140 particular transitions.
  A final equivalence theorem isolates exactly that finite target.

  The fixed-coupling Gate 1 selection proposition cannot simply be reused:
  the action-selected rank-two effective coupling is `49/16`, provably not
  the fixed Liouville effective coupling.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetIntrinsicPairCouplingSelection
import UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
import UnifiedTheory.Audit.KFTOEGate1OrderCouplingSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection

noncomputable section

open scoped BigOperators ComplexConjugate
open Filter Topology
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
open UnifiedTheory.Audit.KFCausalSetIntrinsicPairCouplingSelection
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalTransitionFiberSignature
open UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent
open UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFCausalRegularPhaseEntry
open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Audit.KFTOEGate1OrderCouplingSelection

/-! ## 1. Full physical support of the selected raw running law -/

/-- Every physical quotient child has nonzero coherently aggregated amplitude
for the harmonic running coupling.  Fiber-signature rigidity prevents
cancellation; positivity of the harmonic coupling supplies raw support. -/
theorem harmonic_unlabeledAggregatedAmplitude_ne_zero_of_physical
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (hPhysical : IsUnlabeledOneElementExtension parent child) :
    unlabeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude
          (harmonicCriticalPairCoupling n) chirality)
        parent child ≠ 0 := by
  refine Quotient.inductionOn parent ?_ hPhysical
  intro parentRep hPhysicalRep
  rw [unlabeledAggregatedCausalEdgeAmplitude_mk]
  have hMultiplicity :
      0 < labeledCausalTransitionMultiplicity parentRep child :=
    (labeledCausalTransitionMultiplicity_pos_iff parentRep child).2
      hPhysicalRep
  obtain ⟨base⟩ := Fintype.card_pos_iff.mp hMultiplicity
  rw [← base.property]
  exact labeledAggregatedInteractingChiralAmplitude_at_target_ne_zero
    (ne_of_gt (lt_trans zero_lt_one
      (harmonicCriticalPairCoupling_gt_one n)))
    chirality parentRep base

/-- Exact support classification for the uncorrected action-selected harmonic
law. -/
theorem harmonicCriticalTransition_ne_zero_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
          n pathPrefix child ≠ 0 ↔
      IsPhysicalCausalGrowthStep n pathPrefix child := by
  constructor
  · intro hNonzero
    by_contra hNotPhysical
    exact hNonzero
      (harmonicCriticalTransition_eq_zero_of_not_physical chirality
        (currentUnlabeledCausalOrder n pathPrefix) child hNotPhysical)
  · intro hPhysical
    change harmonicCriticalTransition chirality
      (currentUnlabeledCausalOrder n pathPrefix) child ≠ 0
    unfold harmonicCriticalTransition
    exact div_ne_zero
      (harmonic_unlabeledAggregatedAmplitude_ne_zero_of_physical
        chirality (currentUnlabeledCausalOrder n pathPrefix) child hPhysical)
      (harmonicCritical_unlabeled_partition_ne_zero chirality
        (currentUnlabeledCausalOrder n pathPrefix))

/-- In particular, every transition of the displayed CSpec atlas path is
nonzero under the action-selected raw harmonic law. -/
theorem harmonicCritical_atlasTransition_ne_zero
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition n
        (atlasStepPrefix n hnext) (atlasStepChild n hnext) ≠ 0 := by
  exact (harmonicCriticalTransition_ne_zero_iff_physical
    chirality n (atlasStepPrefix n hnext) (atlasStepChild n hnext)).2
      (atlasStep_isPhysical n hnext)

/-! ## 2. The unconditional selected Born-shell law -/

/-- Exact action-derived coupling statement used by the alternative Gate 1.
It includes the entire schedule, its rank-two effective value, and its
infrared fixed point. -/
def IntrinsicVacuumHarmonicPairSelection : Prop :=
  microscopicSpectatorPairCoupling
      canonicalVacuumSpectatorCausalAction = harmonicCriticalPairCoupling
    ∧ microscopicSpectatorEffectivePairCoupling
        canonicalVacuumSpectatorCausalAction 2 = 49 / 16
    ∧ Tendsto
        (microscopicSpectatorEffectivePairCoupling
          canonicalVacuumSpectatorCausalAction) atTop (nhds 1)

theorem intrinsicVacuumHarmonicPairSelection_closed :
    IntrinsicVacuumHarmonicPairSelection := by
  exact ⟨microscopicSpectatorPairCoupling_eq_harmonic
      canonicalVacuumSpectatorCausalAction,
    microscopicSpectatorEffectivePairCoupling_rankTwo
      canonicalVacuumSpectatorCausalAction,
    microscopicSpectatorEffectivePairCoupling_tendsto_one
      canonicalVacuumSpectatorCausalAction⟩

/-- Law-level replacement for the fixed-coupling Gate 1 support record.  Every
growth-law field refers to the harmonic schedule selected by the vacuum action
and its separately defined canonical Born-shell completion.  The final
positive-frequency handedness field is an independent orientation certificate;
it is bundled here but is not derived from the harmonic transition law. -/
structure Gate1HarmonicBornShellLawClosed (chirality : Fin 2) : Prop where
  vacuumActionUnique :
    ∀ action : VacuumSpectatorCausalAction,
      action = canonicalVacuumSpectatorCausalAction
  pairSelection : IntrinsicVacuumHarmonicPairSelection
  rawPhysicalSupport :
    ∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      (harmonicCriticalCausalSetGrowthLaw chirality).transition
            n pathPrefix child ≠ 0 ↔
        IsPhysicalCausalGrowthStep n pathPrefix child
  coherentNormalized :
    ∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      ∑ child,
        (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
          n pathPrefix child = 1
  bornNormalized :
    ∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      ∑ child,
        Complex.normSq
          ((canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
            n pathPrefix child) = 1
  physicalSupport :
    ∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      ¬ IsPhysicalCausalGrowthStep n pathPrefix child →
        (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
          n pathPrefix child = 0
  bornCylinderProjective :
    ∀ (n : ℕ) (event :
        Finset (RankedGrowthPath CausalSetGrowthBranch n)),
      finiteBornEventProbability
          (canonicalHarmonicBornNormalizedGrowthLaw chirality) (n + 1)
          (refineRankedGrowthEvent event) =
        finiteBornEventProbability
          (canonicalHarmonicBornNormalizedGrowthLaw chirality) n event
  coherentCylinderProjective :
    ∀ (n : ℕ) (event₁ event₂ :
        Finset (RankedGrowthPath CausalSetGrowthBranch n)),
      growthEventDecoherence
          (finiteRankedDepthDecoherence
            (canonicalHarmonicCriticalBornShellGrowthLaw chirality) (n + 1))
          (refineRankedGrowthEvent event₁)
          (refineRankedGrowthEvent event₂) =
        growthEventDecoherence
          (finiteRankedDepthDecoherence
            (canonicalHarmonicCriticalBornShellGrowthLaw chirality) n)
          event₁ event₂
  finiteFunctionalNormalized :
    ∀ n, IsNormalizedGrowthFunctional
      (finiteRankedDepthDecoherence
        (canonicalHarmonicCriticalBornShellGrowthLaw chirality) n)
  infiniteStronglyPositive :
    IsStronglyPositiveGrowthFunctional
      (infiniteRankedCylinderDecoherence
        (canonicalHarmonicCriticalBornShellGrowthLaw chirality))
  infiniteNormalized :
    infiniteRankedCylinderDecoherence
        (canonicalHarmonicCriticalBornShellGrowthLaw chirality)
        (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
        (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1
  reflectionConjugate :
    ∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      star
          ((canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
            n pathPrefix child) =
        (canonicalHarmonicCriticalBornShellGrowthLaw
          (reflectedMicroscopicChirality chirality)).transition
            n pathPrefix child
  positiveFrequencyHandedness : Gate1PositiveFrequencyHandednessClosed

/-- No-argument Gate 1 law capstone: the canonical vacuum action selects the
raw harmonic schedule, while the canonical positive-radial construction closes
the normalization, support, projectivity, positivity, and reflection fields.
The bundled handedness field is supplied by its separate orientation theorem. -/
theorem gate1HarmonicBornShellLaw_closed (chirality : Fin 2) :
    Gate1HarmonicBornShellLawClosed chirality := by
  have hAll := canonicalHarmonicCriticalBornShell_all_rank chirality
  have hPromotion := canonicalHarmonicCriticalBornShell_promotion chirality
  have hTwo := canonicalHarmonicBornLaw_two_consistencies chirality
  exact
    ⟨vacuumSpectatorCausalAction_unique,
      intrinsicVacuumHarmonicPairSelection_closed,
      harmonicCriticalTransition_ne_zero_iff_physical chirality,
      hAll.1,
      (canonicalHarmonicBornNormalizedGrowthLaw chirality).bornNormalized,
      hAll.2.2,
      hTwo.1,
      hTwo.2,
      hPromotion.1,
      hPromotion.2.2.1,
      hPromotion.2.2.2,
      star_canonicalHarmonicCriticalBornShellTransition chirality,
      gate1_positiveFrequencyHandedness_closed⟩

/-! ## 3. Exact compatibility boundary with the old Gate 1 -/

/-- The action-selected rank-two value cannot satisfy the old proposition
that equates it to the fixed Liouville effective coupling. -/
theorem intrinsicRankTwoSelection_not_fixedCanonicalSelection :
    ¬ CanonicalTwoAntichainAmplitudeSelection
      (microscopicSpectatorEffectivePairCoupling
        canonicalVacuumSpectatorCausalAction 2) := by
  intro hOld
  have hEqual :=
    (canonicalTwoAntichainAmplitudeSelection_iff
      (microscopicSpectatorEffectivePairCoupling
        canonicalVacuumSpectatorCausalAction 2)).1 hOld
  exact
    (canonicalEffectivePairCoupling_ne_microscopicRankTwo
      canonicalVacuumSpectatorCausalAction) hEqual.symm

/-! ## 4. What the positive radial correction can and cannot erase -/

/-- A non-root causal parent has at least the distinct gregarious and timid
successors.  Thus its explicit Born-shell representative uses the square-root
branch rather than the singleton fallback. -/
theorem physicalCausalSuccessors_card_gt_one_of_pos
    {n : ℕ} (hn : 0 < n)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    1 < (physicalCausalSuccessors n pathPrefix).card := by
  generalize hParent :
    currentUnlabeledCausalOrder n pathPrefix = parentQuotient
  obtain ⟨parent, rfl⟩ := Quotient.exists_rep parentQuotient
  let emptyChild :=
    causalTransitionTarget parent (emptyCausalPastSet parent)
  let fullChild :=
    causalTransitionTarget parent (fullCausalPastSet parent)
  have hEmptyPhysical : IsUnlabeledOneElementExtension
      (Quotient.mk _ parent) emptyChild :=
    isUnlabeledOneElementExtension_mk
      (precursor_is_oneElementExtension parent (emptyCausalPastSet parent))
  have hFullPhysical : IsUnlabeledOneElementExtension
      (Quotient.mk _ parent) fullChild :=
    isUnlabeledOneElementExtension_mk
      (precursor_is_oneElementExtension parent (fullCausalPastSet parent))
  rw [Finset.one_lt_card]
  refine ⟨emptyChild, ?_, fullChild, ?_, ?_⟩
  · simpa [physicalCausalSuccessors, IsPhysicalCausalGrowthStep,
      hParent] using hEmptyPhysical
  · simpa [physicalCausalSuccessors, IsPhysicalCausalGrowthStep,
      hParent] using hFullPhysical
  · exact empty_and_full_causalTransitionTargets_ne_of_pos hn parent

/-- On every genuinely branching parent, the canonical explicit radial scale
is a strictly positive real number. -/
theorem explicitHarmonicCriticalBornShellScale_re_pos_of_pos
    (chirality : Fin 2) {n : ℕ} (hn : 0 < n)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    0 < (explicitHarmonicCriticalBornShellScale
      chirality n pathPrefix).re := by
  let support := physicalCausalSuccessors n pathPrefix
  let amplitude :=
    (harmonicCriticalCausalSetGrowthLaw chirality).transition n pathPrefix
  have hMultiple : 1 < support.card :=
    physicalCausalSuccessors_card_gt_one_of_pos hn pathPrefix
  have hNonuniform : ∃ child ∈ support,
      amplitude child ≠ supportUniformAmplitude support :=
    harmonicCriticalNonuniformOnBranching chirality n pathPrefix hMultiple
  have hExcessPositive : 0 < supportBornExcess support amplitude :=
    supportBornExcess_pos_of_nonuniform support amplitude hNonuniform
  have hCardOne : (1 : ℝ) < support.card := by exact_mod_cast hMultiple
  have hNumeratorPositive :
      0 < 1 - (support.card : ℝ)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ hCardOne)
  have hRatioPositive :
      0 < (1 - (support.card : ℝ)⁻¹) /
        supportBornExcess support amplitude :=
    div_pos hNumeratorPositive hExcessPositive
  simp only [explicitHarmonicCriticalBornShellScale, support,
    if_neg (ne_of_gt hMultiple), supportBornShellScale, Complex.ofReal_re]
  exact Real.sqrt_pos.2 hRatioPositive

/-- The support-relative radial map rescales the imaginary part by the real
radial scale.  The uniform component is real, so it cannot cancel a nonzero
imaginary component. -/
theorem finiteSupportBornShellCorrection_im_of_real_scale
    {Branch : Type*} [Fintype Branch]
    (support : Finset Branch) (scale : ℂ) (amplitude : Branch → ℂ)
    (branch : Branch) (hBranch : branch ∈ support)
    (hScale : star scale = scale) :
    (finiteSupportBornShellCorrection support scale amplitude branch).im =
      scale.re * (amplitude branch).im := by
  have hScaleIm : scale.im = 0 := by
    exact Complex.conj_eq_iff_im.mp hScale
  simp [finiteSupportBornShellCorrection, hBranch,
    supportCenteredAmplitude, supportUniformAmplitude,
    Complex.mul_im, hScaleIm]

/-- Exact imaginary-part preservation formula for the canonical harmonic
Born-shell law on a physical transition. -/
theorem canonicalHarmonicBornShellTransition_im_of_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hPhysical : IsPhysicalCausalGrowthStep n pathPrefix child) :
    ((canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
        n pathPrefix child).im =
      (explicitHarmonicCriticalBornShellScale chirality n pathPrefix).re *
        ((harmonicCriticalCausalSetGrowthLaw chirality).transition
          n pathPrefix child).im := by
  change (finiteSupportBornShellCorrection
      (physicalCausalSuccessors n pathPrefix)
      (explicitHarmonicCriticalBornShellScale chirality n pathPrefix)
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition n pathPrefix)
      child).im = _
  apply finiteSupportBornShellCorrection_im_of_real_scale
  · simpa [physicalCausalSuccessors] using hPhysical
  · exact star_explicitHarmonicCriticalBornShellScale
      chirality n pathPrefix

/-- At positive rank, every raw transition with nonzero imaginary part
survives the canonical positive-radial Born correction. -/
theorem canonicalHarmonicBornShellTransition_ne_zero_of_raw_im_ne_zero
    (chirality : Fin 2) {n : ℕ} (hn : 0 < n)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hPhysical : IsPhysicalCausalGrowthStep n pathPrefix child)
    (hRawImaginary :
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition
        n pathPrefix child).im ≠ 0) :
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
        n pathPrefix child ≠ 0 := by
  intro hZero
  have hImaginary := congrArg Complex.im hZero
  rw [canonicalHarmonicBornShellTransition_im_of_physical
    chirality n pathPrefix child hPhysical] at hImaginary
  exact (mul_ne_zero
    (ne_of_gt (explicitHarmonicCriticalBornShellScale_re_pos_of_pos
      chirality hn pathPrefix)) hRawImaginary) hImaginary

/-- The one remaining finite target for realizing the displayed CSpec atlas
with the *Born-shell-corrected* selected law.  Zero leakage proves only the
reverse implication; this target says the 140 physical atlas edges retain
nonzero amplitude after radial correction. -/
def HarmonicBornShellAtlasTransitionNonzero (chirality : Fin 2) : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition n
      (atlasStepPrefix n hnext) (atlasStepChild n hnext) ≠ 0

/-- Reflection conjugacy transports the complete finite atlas certificate to
the opposite chirality.  Thus the positive-radial noncancellation audit only
has to be performed in one chiral sector. -/
theorem harmonicBornShellAtlasTransitionNonzero_reflected
    (chirality : Fin 2)
    (hNonzero : HarmonicBornShellAtlasTransitionNonzero chirality) :
    HarmonicBornShellAtlasTransitionNonzero
      (reflectedMicroscopicChirality chirality) := by
  intro n hnext
  rw [← star_canonicalHarmonicCriticalBornShellTransition chirality]
  simpa using hNonzero n hnext

theorem harmonicBornShellAtlasTransitionNonzero_one_of_zero
    (hNonzero : HarmonicBornShellAtlasTransitionNonzero (0 : Fin 2)) :
    HarmonicBornShellAtlasTransitionNonzero (1 : Fin 2) := by
  simpa [reflectedMicroscopicChirality] using
    harmonicBornShellAtlasTransitionNonzero_reflected (0 : Fin 2) hNonzero

/-- Rank zero has a unique child, so coherent normalization alone forces its
Born-shell transition to be exactly one. -/
theorem canonicalHarmonicBornShellTransition_rankZero_eq_one
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 0)
    (child : CausalSetGrowthBranch 0) :
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
        0 pathPrefix child = 1 := by
  classical
  have hNormalized :=
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).normalized
      0 pathPrefix
  calc
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
        0 pathPrefix child =
      ∑ other : CausalSetGrowthBranch 0,
        (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
          0 pathPrefix other := by
            symm
            apply Fintype.sum_eq_single child
            intro other hDifferent
            exact (hDifferent
              ((unlabeledCardinalCausalOrder_one_unique other).trans
                (unlabeledCardinalCausalOrder_one_unique child).symm)).elim
    _ = 1 := hNormalized

/-- Smaller sufficient finite target: only positive-rank atlas transitions
whose *raw* harmonic amplitude is purely real remain capable of radial
cancellation. -/
def HarmonicAtlasRawImaginaryNonzeroOnPositiveRank
    (chirality : Fin 2) : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140), 0 < n →
    ((harmonicCriticalCausalSetGrowthLaw chirality).transition n
      (atlasStepPrefix n hnext) (atlasStepChild n hnext)).im ≠ 0

theorem harmonicBornShellAtlasTransitionNonzero_of_rawImaginary
    (chirality : Fin 2)
    (hRawImaginary :
      HarmonicAtlasRawImaginaryNonzeroOnPositiveRank chirality) :
    HarmonicBornShellAtlasTransitionNonzero chirality := by
  intro n hnext
  by_cases hn : n = 0
  · subst n
    rw [canonicalHarmonicBornShellTransition_rankZero_eq_one]
    norm_num
  · exact canonicalHarmonicBornShellTransition_ne_zero_of_raw_im_ne_zero
      chirality (Nat.pos_of_ne_zero hn)
      (atlasStepPrefix n hnext) (atlasStepChild n hnext)
      (atlasStep_isPhysical n hnext)
      (hRawImaginary n hnext (Nat.pos_of_ne_zero hn))

/-- Unfolded positive-radial formula on a physical edge.  This is the exact
scalar equation that must be checked when the raw edge is purely real. -/
theorem canonicalHarmonicBornShellTransition_eq_radialFormula
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hPhysical : IsPhysicalCausalGrowthStep n pathPrefix child) :
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
        n pathPrefix child =
      supportUniformAmplitude (physicalCausalSuccessors n pathPrefix) +
        explicitHarmonicCriticalBornShellScale chirality n pathPrefix *
          ((harmonicCriticalCausalSetGrowthLaw chirality).transition
              n pathPrefix child -
            supportUniformAmplitude
              (physicalCausalSuccessors n pathPrefix)) := by
  change finiteSupportBornShellCorrection
      (physicalCausalSuccessors n pathPrefix)
      (explicitHarmonicCriticalBornShellScale chirality n pathPrefix)
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition n pathPrefix)
      child = _
  simp [finiteSupportBornShellCorrection,
    show child ∈ physicalCausalSuccessors n pathPrefix by
      simpa [physicalCausalSuccessors] using hPhysical,
    supportCenteredAmplitude]

/-- Exact reduced atlas target.  Non-real raw edges are already protected by
imaginary-part preservation; this predicate retains only the possible
purely-real cancellations `u + s(a-u) = 0`. -/
def HarmonicAtlasRealRadialCancellationFree (chirality : Fin 2) : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140), 0 < n →
    ((harmonicCriticalCausalSetGrowthLaw chirality).transition n
      (atlasStepPrefix n hnext) (atlasStepChild n hnext)).im = 0 →
    supportUniformAmplitude
          (physicalCausalSuccessors n (atlasStepPrefix n hnext)) +
        explicitHarmonicCriticalBornShellScale chirality n
            (atlasStepPrefix n hnext) *
          ((harmonicCriticalCausalSetGrowthLaw chirality).transition n
              (atlasStepPrefix n hnext) (atlasStepChild n hnext) -
            supportUniformAmplitude
              (physicalCausalSuccessors n (atlasStepPrefix n hnext))) ≠ 0

/-- The original 140-transition target is equivalent to the reduced real
radial equation.  Thus there is no hidden complex cancellation problem left:
only an exact equality among real algebraic/radical quantities can fail. -/
theorem harmonicBornShellAtlasTransitionNonzero_iff_realRadialCancellationFree
    (chirality : Fin 2) :
    HarmonicBornShellAtlasTransitionNonzero chirality ↔
      HarmonicAtlasRealRadialCancellationFree chirality := by
  constructor
  · intro hAll n hnext hn hReal
    rw [← canonicalHarmonicBornShellTransition_eq_radialFormula
      chirality n (atlasStepPrefix n hnext) (atlasStepChild n hnext)
      (atlasStep_isPhysical n hnext)]
    exact hAll n hnext
  · intro hReal n hnext
    by_cases hn : n = 0
    · subst n
      rw [canonicalHarmonicBornShellTransition_rankZero_eq_one]
      norm_num
    · have hnPositive : 0 < n := Nat.pos_of_ne_zero hn
      by_cases hRawReal :
          ((harmonicCriticalCausalSetGrowthLaw chirality).transition n
            (atlasStepPrefix n hnext) (atlasStepChild n hnext)).im = 0
      · rw [canonicalHarmonicBornShellTransition_eq_radialFormula
          chirality n (atlasStepPrefix n hnext) (atlasStepChild n hnext)
          (atlasStep_isPhysical n hnext)]
        exact hReal n hnext hnPositive hRawReal
      · exact canonicalHarmonicBornShellTransition_ne_zero_of_raw_im_ne_zero
          chirality hnPositive (atlasStepPrefix n hnext)
          (atlasStepChild n hnext) (atlasStep_isPhysical n hnext) hRawReal

theorem harmonicBornShellAtlasPathAmplitude_ne_zero_of_transition_nonzero
    (chirality : Fin 2)
    (hNonzero : HarmonicBornShellAtlasTransitionNonzero chirality) :
    ∀ (n : ℕ) (h : n ≤ 140),
      finiteRankedPathAmplitude
          (canonicalHarmonicCriticalBornShellGrowthLaw chirality) n
          (globalAtlasPhysicalGrowthPath n h) ≠ 0
  | 0, _ => by simp [finiteRankedPathAmplitude]
  | n + 1, h => by
      change
        finiteRankedPathAmplitude
            (canonicalHarmonicCriticalBornShellGrowthLaw chirality) n
            (atlasStepPrefix n h) *
          (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
            n (atlasStepPrefix n h) (atlasStepChild n h) ≠ 0
      exact mul_ne_zero
        (harmonicBornShellAtlasPathAmplitude_ne_zero_of_transition_nonzero
          chirality hNonzero n (Nat.le_trans (Nat.le_succ n) h))
        (hNonzero n h)

/-- Full alternative Gate 1 realization record.  Its only additional field
beyond the unconditional selected-law certificate is the explicitly named
140-transition Born-shell noncancellation target. -/
structure Gate1HarmonicBornShellAtlasRealizationClosed
    (chirality : Fin 2) : Prop where
  lawClosed : Gate1HarmonicBornShellLawClosed chirality
  atlasTransitionNonzero : HarmonicBornShellAtlasTransitionNonzero chirality
  atlasPathPhysical : IsPhysicalCausalGrowthPath 140
    (globalAtlasPhysicalGrowthPath 140 le_rfl)
  atlasPathAmplitudeNonzero :
    finiteRankedPathAmplitude
        (canonicalHarmonicCriticalBornShellGrowthLaw chirality) 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
  endpointOrder : Nonempty
    (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
      GlobalAtlasEvent)
  booleanCubeSeed :
    ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
  determinantOrientation : cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
  weakVertex : IsNontrivialPurelyRightHanded
    (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory)

theorem gate1HarmonicBornShellAtlasRealization_closed_of_transition_nonzero
    (chirality : Fin 2)
    (hNonzero : HarmonicBornShellAtlasTransitionNonzero chirality) :
    Gate1HarmonicBornShellAtlasRealizationClosed chirality := by
  exact
    ⟨gate1HarmonicBornShellLaw_closed chirality,
      hNonzero,
      globalAtlasPhysicalGrowthPath_isPhysical 140 le_rfl,
      harmonicBornShellAtlasPathAmplitude_ne_zero_of_transition_nonzero
        chirality hNonzero 140 le_rfl,
      ⟨globalAtlasPhysicalEndpointOrderIso⟩,
      globalAtlasPhysicalEndpoint_containsBooleanCubeSeed,
      cSpecOddLoopHistory_orientation,
      cSpecOddLoop_derives_rightWeakMirror⟩

/-- Exact frontier: full atlas realization by the selected Born-shell law is
equivalent to its 140 finite transition noncancellation checks.  Everything
else in the alternative Gate 1 record is unconditional. -/
theorem gate1HarmonicBornShellAtlasRealization_closed_iff
    (chirality : Fin 2) :
    Gate1HarmonicBornShellAtlasRealizationClosed chirality ↔
      HarmonicBornShellAtlasTransitionNonzero chirality := by
  constructor
  · exact fun h => h.atlasTransitionNonzero
  · exact gate1HarmonicBornShellAtlasRealization_closed_of_transition_nonzero
      chirality

#print axioms harmonicCriticalTransition_ne_zero_iff_physical
#print axioms harmonicCritical_atlasTransition_ne_zero
#print axioms intrinsicVacuumHarmonicPairSelection_closed
#print axioms gate1HarmonicBornShellLaw_closed
#print axioms intrinsicRankTwoSelection_not_fixedCanonicalSelection
#print axioms harmonicBornShellAtlasTransitionNonzero_reflected
#print axioms harmonicBornShellAtlasPathAmplitude_ne_zero_of_transition_nonzero
#print axioms gate1HarmonicBornShellAtlasRealization_closed_iff

end

end UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection
