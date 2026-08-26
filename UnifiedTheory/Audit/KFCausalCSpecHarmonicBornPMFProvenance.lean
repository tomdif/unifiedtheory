/-
  Audit/KFCausalCSpecHarmonicBornPMFProvenance.lean

  CONDITIONAL STAGE-PMF PROVENANCE FOR THE FINITE CAUSAL BORN STATE

  The Gate-5 local density was constructed from filtered harmonic Born
  transition weights.  This module identifies those weights directly with
  the pushforward of the already normalized causal-growth stage PMF and then
  with the expectation of the corresponding local computational effect.

  The result is deliberately conditional on the selected finite parent
  `parentSchedule n`.  It is not an unconditional marginal of the infinite
  trajectory measure; that stronger statement would require summing over all
  parent histories or proving concentration on the selected schedule.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet
import UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornPMFProvenance

noncomputable section

open scoped BigOperators ENNReal
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalBornObservedWeight
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet
open UnifiedTheory.LayerC.SMHilbertInstantiation

universe u

/-! ## 1. Generic fixed-parent pushforward -/

/-- Pushing the normalized one-step Born PMF through a finite observation map
gives exactly the existing filtered observed Born weight.  This is a
fixed-parent conditional identity at rank `n`. -/
theorem causalBornStagePMF_map_observe_apply
    {ι : Type u} [Fintype ι]
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (n : ℕ) (i : ι) :
    (causalBornStagePMF law n (parentSchedule n)).map (observe n) i =
      ENNReal.ofReal
        (observedBornWeight law parentSchedule observe n i) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  unfold observedBornWeight
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro child _
    by_cases h : observe n child = i
    · simp [h]
    · simp [h, Ne.symm h]
  · intro child _
    split
    · exact Complex.normSq_nonneg _
    · exact le_rfl

/-! ## 2. Action-selected harmonic specialization -/

/-- At a recovered site, the supplied readout pushes the action-selected
harmonic stage PMF to the exact real weight used to build the local state. -/
theorem harmonicCausalBornStagePMF_map_readout_apply
    {site : Type u}
    (chirality : Fin 2)
    (R : HarmonicSingleGenerationReadout site)
    (i : site) (k : Fin singleGenDim) :
    (causalBornStagePMF (canonicalHarmonicBornLaw chirality)
        (R.rankAt i) (R.parentSchedule (R.rankAt i))).map
        (R.observe (R.rankAt i)) k =
      ENNReal.ofReal (harmonicReadoutWeight chirality R i k) := by
  exact causalBornStagePMF_map_observe_apply
    (canonicalHarmonicBornLaw chirality) R.parentSchedule R.observe
      (R.rankAt i) k

/-- End-to-end finite provenance: the pushed-forward conditional harmonic
stage PMF equals the Born expectation of the localized computational effect
in the canonical Gate-5 state. -/
theorem harmonicCausalBornStagePMF_map_readout_eq_local_expectation
    {site : Type u} [Fintype site] [Nonempty site]
    (chirality : Fin 2)
    (R : HarmonicSingleGenerationReadout site)
    (i : site) (k : Fin singleGenDim) :
    (causalBornStagePMF (canonicalHarmonicBornLaw chirality)
        (R.rankAt i) (R.parentSchedule (R.rankAt i))).map
        (R.observe (R.rankAt i)) k =
      ENNReal.ofReal
        ((harmonicLocalStateFunctional chirality R i
          (computationalEffectAt i k)).re) := by
  rw [harmonicLocalStateFunctional_computationalEffect]
  exact harmonicCausalBornStagePMF_map_readout_apply chirality R i k

/-! ## 3. Compatibility with finite path weights -/

/-- Extending one finite history multiplies its Born weight by precisely the
conditional stage-PMF mass of the selected child. -/
theorem finiteBornPathWeight_succ_eq_prefix_mul_stagePMF
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    ENNReal.ofReal
        (finiteBornPathWeight law (n + 1) (pathPrefix, child)) =
      ENNReal.ofReal (finiteBornPathWeight law n pathPrefix) *
        causalBornStagePMF law n pathPrefix child := by
  rw [causalBornStagePMF_apply]
  rw [← ENNReal.ofReal_mul
    (finiteBornPathWeight_nonneg law n pathPrefix)]
  congr 1
  simp [finiteBornPathWeight, finiteBornPathAmplitude,
    Complex.normSq_mul]

/-! ## 4. Axiom audit -/

#print axioms causalBornStagePMF_map_observe_apply
#print axioms harmonicCausalBornStagePMF_map_readout_apply
#print axioms harmonicCausalBornStagePMF_map_readout_eq_local_expectation
#print axioms finiteBornPathWeight_succ_eq_prefix_mul_stagePMF

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornPMFProvenance
