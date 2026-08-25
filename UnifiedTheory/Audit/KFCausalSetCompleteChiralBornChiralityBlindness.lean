/-
  Audit/KFCausalSetCompleteChiralBornChiralityBlindness.lean

  CHIRALITY BLINDNESS OF THE COMPLETE-CHIRAL BORN TRAJECTORY LAW

  The two complete interacting chiral amplitude laws are exchanged by complex
  conjugation.  Passing to normalized squared moduli therefore erases this
  distinction at every finite history.  This module propagates that equality
  through the stage PMFs, the history-dependent kernels, and the full
  Ionescu--Tulcea trajectory measures.

  Thus chirality remains genuine phase/interference data, but it cannot be
  recovered from the classical causal-growth path distribution alone.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure
import UnifiedTheory.Audit.KFCausalSetMicroscopicResponseLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetCompleteChiralBornChiralityBlindness

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetMicroscopicResponseLaw

/-! ## 1. Conjugate amplitudes give identical Born weights -/

/-- Reflection of the chirality label complex-conjugates every transition of
the complete interacting law. -/
theorem completeChiralCausalSetGrowthLaw_transition_star
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    star ((completeChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child) =
      (completeChiralCausalSetGrowthLaw
        (reflectedMicroscopicChirality chirality)).transition
          n pathPrefix child := by
  unfold completeChiralCausalSetGrowthLaw canonicalInteractingChiralTransition
  simp only [div_eq_mul_inv, star_mul', star_inv₀]
  rw [interacting_unlabeledAggregatedCausalEdgeAmplitude_star,
    interacting_unlabeledCausalEdgeAmplitudePartition_star]

/-- The squared modulus of a transition cannot distinguish the two reflected
chirality sectors. -/
theorem completeChiralTransition_normSq_reflection
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    Complex.normSq
        ((completeChiralCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)).transition
            n pathPrefix child) =
      Complex.normSq
        ((completeChiralCausalSetGrowthLaw chirality).transition
          n pathPrefix child) := by
  rw [← completeChiralCausalSetGrowthLaw_transition_star]
  exact Complex.normSq_conj _

/-- The total stagewise Born normalizer is reflection invariant. -/
theorem completeChiralStageBornMass_reflection
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    completeChiralStageBornMass
        (reflectedMicroscopicChirality chirality) n pathPrefix =
      completeChiralStageBornMass chirality n pathPrefix := by
  classical
  unfold completeChiralStageBornMass
  apply Finset.sum_congr rfl
  intro child _
  exact completeChiralTransition_normSq_reflection
    chirality n pathPrefix child

/-- Every normalized stagewise Born weight is reflection invariant. -/
theorem completeChiralStageBornWeight_reflection
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    completeChiralStageBornWeight
        (reflectedMicroscopicChirality chirality) n pathPrefix child =
      completeChiralStageBornWeight chirality n pathPrefix child := by
  unfold completeChiralStageBornWeight
  rw [completeChiralTransition_normSq_reflection,
    completeChiralStageBornMass_reflection]

/-! ## 2. Equality of the complete classical stochastic laws -/

/-- The next-branch PMF is chirality blind at every finite history. -/
theorem completeChiralStageBornPMF_reflection
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    completeChiralStageBornPMF
        (reflectedMicroscopicChirality chirality) n pathPrefix =
      completeChiralStageBornPMF chirality n pathPrefix := by
  apply PMF.ext
  intro child
  simp only [completeChiralStageBornPMF_apply]
  rw [completeChiralStageBornWeight_reflection]

/-- The rank-zero probability measure is chirality blind. -/
theorem completeChiralInitialBornMeasure_reflection
    (chirality : Fin 2) :
    completeChiralInitialBornMeasure
        (reflectedMicroscopicChirality chirality) =
      completeChiralInitialBornMeasure chirality := by
  unfold completeChiralInitialBornMeasure
  rw [completeChiralStageBornPMF_reflection]

/-- Every full-history transition kernel is chirality blind. -/
theorem completeChiralBornKernel_reflection
    (chirality : Fin 2) (n : ℕ) :
    completeChiralBornKernel
        (reflectedMicroscopicChirality chirality) n =
      completeChiralBornKernel chirality n := by
  apply Kernel.ext
  intro history
  change
    (completeChiralStageBornPMF
      (reflectedMicroscopicChirality chirality) (n + 1)
      (rankedGrowthPathOfIic n history)).toMeasure =
    (completeChiralStageBornPMF chirality (n + 1)
      (rankedGrowthPathOfIic n history)).toMeasure
  rw [completeChiralStageBornPMF_reflection]

/-- Main result: after applying the Born rule, the complete probability law
on infinite causal-growth trajectories is identical in the two reflected
chirality sectors. -/
theorem completeChiralBornTrajectoryMeasure_reflection
    (chirality : Fin 2) :
    completeChiralBornTrajectoryMeasure
        (reflectedMicroscopicChirality chirality) =
      completeChiralBornTrajectoryMeasure chirality := by
  unfold completeChiralBornTrajectoryMeasure
  rw [completeChiralInitialBornMeasure_reflection]
  congr 1
  funext n
  exact completeChiralBornKernel_reflection chirality n

/-- In particular, the two concrete labels `0` and `1` induce exactly the
same probability measure on complete causal-growth histories. -/
theorem completeChiralBornTrajectoryMeasure_zero_eq_one :
    completeChiralBornTrajectoryMeasure (0 : Fin 2) =
      completeChiralBornTrajectoryMeasure (1 : Fin 2) := by
  have h := completeChiralBornTrajectoryMeasure_reflection (0 : Fin 2)
  norm_num [reflectedMicroscopicChirality] at h
  exact h.symm

#print axioms completeChiralCausalSetGrowthLaw_transition_star
#print axioms completeChiralStageBornWeight_reflection
#print axioms completeChiralBornTrajectoryMeasure_zero_eq_one

end

end UnifiedTheory.Audit.KFCausalSetCompleteChiralBornChiralityBlindness
