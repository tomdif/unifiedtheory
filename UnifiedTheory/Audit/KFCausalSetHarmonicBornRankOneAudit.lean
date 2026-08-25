/-
  Audit/KFCausalSetHarmonicBornRankOneAudit.lean

  EXACT FIRST BRANCH OF THE ACTION-SELECTED HARMONIC BORN LAW

  The root birth (coordinate zero) is necessarily deterministic.  The first
  genuinely causal choice, at rank one, is not: the two physical children
  have conjugate amplitudes and exact Born probability `1/2` each.  In
  particular, a variance repair shifted past the root only needs to begin at
  causal stage one; this audit finds no rank-one obstruction forcing a second
  shift.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
import UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
import UnifiedTheory.Audit.KFCausalTransitionFiberSignature

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalTransitionFiberSignature

/-! ## 1. Exactly two nonzero raw branches -/

theorem harmonic_unlabeledAggregate_ne_zero_of_physical
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

theorem harmonicTransition_ne_zero_iff_physical
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
      (harmonic_unlabeledAggregate_ne_zero_of_physical
        chirality (currentUnlabeledCausalOrder n pathPrefix) child hPhysical)
      (harmonicCritical_unlabeled_partition_ne_zero chirality
        (currentUnlabeledCausalOrder n pathPrefix))

/-- A rank-one child other than the gregarious antichain and timid chain has
empty labeled transition fiber, hence zero interacting aggregate. -/
theorem interacting_rankOne_aggregate_eq_zero_of_ne
    (lambda : ℝ) (chirality : Fin 2)
    (child : UnlabeledCardinalCausalOrder 2)
    (hGregarious : child ≠ rankOneGregariousChild)
    (hTimid : child ≠ rankOneTimidChild) :
    labeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude lambda chirality)
        (cardinalCausalAntichain 1) child = 0 := by
  classical
  unfold labeledAggregatedCausalEdgeAmplitude
  apply Finset.sum_eq_zero
  intro transition _hTransition
  rcases rankOneCausalPast_cases transition.val with hEmpty | hFull
  · exact False.elim (hGregarious (by
      rw [rankOneGregariousChild, ← transition.property, hEmpty]))
  · exact False.elim (hTimid (by
      rw [rankOneTimidChild, ← transition.property, hFull]))

theorem harmonicCritical_rankOne_transition_eq_zero_of_ne
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (child : CausalSetGrowthBranch 1)
    (hGregarious : child ≠ rankOneGregariousChild)
    (hTimid : child ≠ rankOneTimidChild) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix child = 0 := by
  change harmonicCriticalTransition chirality
      (currentUnlabeledCausalOrder 1 pathPrefix) child = 0
  rw [unlabeledCardinalCausalOrder_one_unique
    (currentUnlabeledCausalOrder 1 pathPrefix)]
  unfold harmonicCriticalTransition
  rw [unlabeledAggregatedCausalEdgeAmplitude_mk,
    interacting_rankOne_aggregate_eq_zero_of_ne
      (harmonicCriticalPairCoupling 1) chirality child
        hGregarious hTimid]
  simp

theorem harmonicCritical_rankOne_gregarious_closed
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneGregariousChild =
      (1 - chiralMaximalEventPhase chirality) / 2 := by
  rw [harmonicCritical_rankOne_transition_eq_chiral,
    chiral_rankOne_gregarious_transition,
    chiral_normalized_gregarious_amplitude]

theorem harmonicCritical_rankOne_timid_closed
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneTimidChild =
      (1 + chiralMaximalEventPhase chirality) / 2 := by
  rw [harmonicCritical_rankOne_transition_eq_chiral,
    chiral_rankOne_timid_transition,
    chiral_normalized_timid_amplitude]

theorem harmonicCritical_rankOne_gregarious_normSq
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    Complex.normSq
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneGregariousChild) = 1 / 2 := by
  rw [harmonicCritical_rankOne_gregarious_closed]
  fin_cases chirality <;>
    norm_num [chiralMaximalEventPhase, Complex.normSq_apply]

theorem harmonicCritical_rankOne_timid_normSq
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    Complex.normSq
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneTimidChild) = 1 / 2 := by
  rw [harmonicCritical_rankOne_timid_closed]
  fin_cases chirality <;>
    norm_num [chiralMaximalEventPhase, Complex.normSq_apply]

/-- The physical successor support at the first genuine causal choice is
exactly the antichain/chain pair. -/
theorem physicalCausalSuccessors_rankOne
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    physicalCausalSuccessors 1 pathPrefix =
      {rankOneGregariousChild, rankOneTimidChild} := by
  classical
  ext child
  simp only [physicalCausalSuccessors, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hPhysical
    have hNonzero :=
      (harmonicTransition_ne_zero_iff_physical
        chirality 1 pathPrefix child).2 hPhysical
    by_contra hCases
    push_neg at hCases
    exact hNonzero
      (harmonicCritical_rankOne_transition_eq_zero_of_ne
        chirality pathPrefix child hCases.1 hCases.2)
  · intro hCases
    rcases hCases with rfl | rfl
    · apply (harmonicTransition_ne_zero_iff_physical
        chirality 1 pathPrefix rankOneGregariousChild).1
      rw [harmonicCritical_rankOne_gregarious_closed]
      fin_cases chirality <;>
        norm_num [chiralMaximalEventPhase] <;>
        intro hZero <;>
        have hImag := congrArg Complex.im hZero <;>
        norm_num at hImag
    · apply (harmonicTransition_ne_zero_iff_physical
        chirality 1 pathPrefix rankOneTimidChild).1
      rw [harmonicCritical_rankOne_timid_closed]
      fin_cases chirality <;>
        norm_num [chiralMaximalEventPhase] <;>
        intro hZero <;>
        have hImag := congrArg Complex.im hZero <;>
        norm_num at hImag

theorem physicalCausalSuccessors_rankOne_card
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (physicalCausalSuccessors 1 pathPrefix).card = 2 := by
  rw [physicalCausalSuccessors_rankOne chirality pathPrefix]
  rw [Finset.card_insert_of_notMem]
  · simp
  · simpa using rankOne_children_ne

/-! ## 2. The canonical Born shell fixes this already-Born-normalized pair -/

theorem harmonicCritical_rankOne_supportBornExcess
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    supportBornExcess (physicalCausalSuccessors 1 pathPrefix)
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition
          1 pathPrefix) = 1 / 2 := by
  rw [physicalCausalSuccessors_rankOne chirality pathPrefix]
  unfold supportBornExcess
  have hNotMem : rankOneGregariousChild ∉
      ({rankOneTimidChild} : Finset (CausalSetGrowthBranch 1)) := by
    simpa using rankOne_children_ne
  rw [Finset.sum_insert hNotMem, Finset.sum_singleton]
  have hCard :
      ({rankOneGregariousChild, rankOneTimidChild} :
        Finset (CausalSetGrowthBranch 1)).card = 2 := by
    rw [Finset.card_insert_of_notMem hNotMem]
    simp
  unfold supportCenteredAmplitude supportUniformAmplitude
  rw [hCard]
  rw [harmonicCritical_rankOne_gregarious_closed,
    harmonicCritical_rankOne_timid_closed]
  fin_cases chirality <;>
    norm_num [chiralMaximalEventPhase, Complex.normSq_apply]

theorem explicitHarmonicCriticalBornShellScale_rankOne
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    explicitHarmonicCriticalBornShellScale chirality 1 pathPrefix = 1 := by
  simp only [explicitHarmonicCriticalBornShellScale,
    physicalCausalSuccessors_rankOne_card chirality pathPrefix,
    OfNat.ofNat, reduceCtorEq, ↓reduceIte,
    harmonicCritical_rankOne_supportBornExcess chirality pathPrefix,
    supportBornShellScale]
  norm_num

theorem canonicalHarmonicBorn_rankOne_transition_eq_raw
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (child : CausalSetGrowthBranch 1) :
    (canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
        1 pathPrefix child =
      (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix child := by
  change finiteSupportBornShellCorrection
      (physicalCausalSuccessors 1 pathPrefix)
      (explicitHarmonicCriticalBornShellScale chirality 1 pathPrefix)
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition 1 pathPrefix)
      child = _
  rw [explicitHarmonicCriticalBornShellScale_rankOne]
  by_cases hPhysical : child ∈ physicalCausalSuccessors 1 pathPrefix
  · simp [finiteSupportBornShellCorrection, hPhysical,
      supportCenteredAmplitude]
  · have hNotPhysical :
        ¬ IsPhysicalCausalGrowthStep 1 pathPrefix child := by
      simpa [physicalCausalSuccessors] using hPhysical
    have hRaw :
        (harmonicCriticalCausalSetGrowthLaw chirality).transition
            1 pathPrefix child = 0 :=
      harmonicCriticalTransition_eq_zero_of_not_physical
        chirality (currentUnlabeledCausalOrder 1 pathPrefix) child hNotPhysical
    rw [hRaw]
    simp [finiteSupportBornShellCorrection, hPhysical]

/-! ## 3. Exact rank-one PMF -/

theorem canonicalHarmonicBorn_rankOne_gregarious_probability
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    Complex.normSq
      ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
        1 pathPrefix rankOneGregariousChild) = 1 / 2 := by
  rw [canonicalHarmonicBorn_rankOne_transition_eq_raw,
    harmonicCritical_rankOne_gregarious_normSq]

theorem canonicalHarmonicBorn_rankOne_timid_probability
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    Complex.normSq
      ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
        1 pathPrefix rankOneTimidChild) = 1 / 2 := by
  rw [canonicalHarmonicBorn_rankOne_transition_eq_raw,
    harmonicCritical_rankOne_timid_normSq]

/-- Exact answer to the repair-horizon audit: coordinate zero is a Dirac
birth, while causal stage one has two distinct positive weights, both `1/2`.
No extra shift to stage two is forced by degeneracy. -/
theorem canonicalHarmonicBorn_rankOne_exact_PMF
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    rankOneGregariousChild ≠ rankOneTimidChild
      ∧ Complex.normSq
          ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
            1 pathPrefix rankOneGregariousChild) = 1 / 2
      ∧ Complex.normSq
          ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
            1 pathPrefix rankOneTimidChild) = 1 / 2 := by
  exact ⟨rankOne_children_ne,
    canonicalHarmonicBorn_rankOne_gregarious_probability chirality pathPrefix,
    canonicalHarmonicBorn_rankOne_timid_probability chirality pathPrefix⟩

#print axioms canonicalHarmonicBorn_rankOne_transition_eq_raw
#print axioms canonicalHarmonicBorn_rankOne_exact_PMF

end

end UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit
