/-
  Audit/KFCausalSetSourceQuantumEnsemble.lean

  THE FIRST EXACT HARMONIC SOURCE ENSEMBLE

  The multiplicative refinement benchmark has retention factor `|2y|` for
  every balanced kernel.  This file combines that observable with the actual
  harmonic chiral edge law above the first parent having three distinct source
  sectors: the two-antichain.

  The result is intrinsically quantum.  The three coherent source-bin quantum
  measures do not sum to one; destructive interference between the empty and
  full precursor bins restores total-event normalization.  Consequently the
  cylinder quantum measure alone does not define a classical expectation of
  coherence.  An ordinary expected retention is calculated only after adding
  an explicitly named singleton-Born normalization prescription.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetSourceMagnitudeDecoherence
import UnifiedTheory.Audit.KFCausalSetCriticalMultiplicity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble

noncomputable section

open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetCriticalMultiplicity
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality
open UnifiedTheory.Audit.KFCausalSetConjugationCompleteness
open UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
open UnifiedTheory.Audit.KFCausalSetSourceMagnitudeDecoherence

/-! ## 1. Source sectors of an antichain birth -/

/-- Every selected element of an antichain precursor is maximal inside that
precursor. -/
theorem antichainPast_maximalCount_eq_ancestorCount {n : ℕ}
    (past : CausalPastSet (cardinalCausalAntichain n)) :
    past.maximalCount = past.ancestorCount := by
  unfold CausalPastSet.maximalCount CausalPastSet.ancestorCount
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl (Fin n)) (by
    intro i
    constructor
    · exact fun h => h.1
    · intro hMem
      exact ⟨hMem, by
        intro j _hJ hRel
        have hij : i = j := by
          simpa [cardinalCausalAntichain] using hRel
        exact hij.symm⟩)

/-- Incidence-counting precursor population is exactly the Rideout--Sorkin
ancestor count. -/
theorem precursorPopulationQ_eq_ancestorCount {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    precursorPopulationQ past = (past.ancestorCount : ℚ) := by
  unfold precursorPopulationQ CausalPastSet.ancestorCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- Coherent raw amplitude of the `omega`-ancestor sector of an antichain.
The binomial factor is the proved number of actual precursor slots. -/
def antichainCoherentSourceSectorAmplitude
    (lambda : ℝ) (chirality : Fin 2) (total omega : ℕ) : ℂ :=
  (Nat.choose total omega : ℂ) *
    interactingChiralSignatureWeight lambda chirality omega omega

/-- The sector formula is literally the coherent sum of the microscopic raw
amplitudes over all precursor slots in that source sector. -/
theorem antichainCoherentSourceSectorAmplitude_eq_sum
    (lambda : ℝ) (chirality : Fin 2) (total omega : ℕ) :
    (∑ past : AntichainPrecursorSector total omega,
      (interactingChiralCausalEdgeAmplitude lambda chirality).amplitude
        (cardinalCausalAntichain total) past.val) =
      antichainCoherentSourceSectorAmplitude
        lambda chirality total omega := by
  have hEach : ∀ past : AntichainPrecursorSector total omega,
      (interactingChiralCausalEdgeAmplitude lambda chirality).amplitude
          (cardinalCausalAntichain total) past.val =
        interactingChiralSignatureWeight lambda chirality omega omega := by
    intro past
    change interactingChiralSignatureWeight lambda chirality
      past.val.ancestorCount past.val.maximalCount = _
    rw [antichainPast_maximalCount_eq_ancestorCount past.val, past.property]
  simp_rw [hEach]
  simp [antichainCoherentSourceSectorAmplitude,
    antichainPrecursorSector_card]

/-- Geometric source assigned to ancestor-count bin `0`, `1`, or `2` above
the two-antichain. -/
def antichainTwoSourceBinParameter (bin : Fin 3) : ℝ :=
  (bin.val : ℝ) / (2 * (3 + bin.val : ℕ))

/-- Every actual precursor in a source bin has the displayed geometric
parameter. -/
theorem antichainTwoSourceBinParameter_eq_birthSource
    (bin : Fin 3) (past : AntichainPrecursorSector 2 bin.val) :
    ((maximalBirthOrientationSourceQ
        (cardinalCausalAntichain 2) past.val : ℚ) : ℝ) =
      antichainTwoSourceBinParameter bin := by
  rw [maximalBirthOrientationSourceQ_formula,
    precursorExtension_totalCausalPastVolumeQ,
    precursorPopulationQ_eq_ancestorCount, past.property]
  have hParent :
      totalCausalPastVolumeQ (cardinalCausalAntichain 2) = 2 := by
    unfold totalCausalPastVolumeQ
    simp_rw [causalPastVolumeQ_antichain]
    norm_num
  rw [hParent]
  fin_cases bin <;> norm_num [antichainTwoSourceBinParameter]

/-- Exact retention factor attached to a source bin. -/
def antichainTwoSourceBinRetention (bin : Fin 3) : ℝ :=
  |2 * antichainTwoSourceBinParameter bin|

theorem antichainTwoSourceBinParameter_exact :
    antichainTwoSourceBinParameter 0 = 0
      ∧ antichainTwoSourceBinParameter 1 = 1 / 8
      ∧ antichainTwoSourceBinParameter 2 = 1 / 5 := by
  norm_num [antichainTwoSourceBinParameter]

theorem antichainTwoSourceBinRetention_exact :
    antichainTwoSourceBinRetention 0 = 0
      ∧ antichainTwoSourceBinRetention 1 = 1 / 4
      ∧ antichainTwoSourceBinRetention 2 = 2 / 5 := by
  norm_num [antichainTwoSourceBinRetention,
    antichainTwoSourceBinParameter]

/-! ## 2. Exact harmonic quantum-measure profile -/

/-- Coherent raw amplitude in each of the three source bins at the harmonic
rank-two coupling. -/
def harmonicAntichainTwoSourceBinAmplitude
    (chirality : Fin 2) (bin : Fin 3) : ℂ :=
  antichainCoherentSourceSectorAmplitude
    (harmonicCriticalPairCoupling 2) chirality 2 bin.val

theorem harmonicAntichainTwoSourceBinAmplitude_zero
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinAmplitude chirality 0 = 1 := by
  simp [harmonicAntichainTwoSourceBinAmplitude,
    antichainCoherentSourceSectorAmplitude,
    harmonicCriticalPairCoupling, harmonicCriticalPairCouplingQ,
    interactingChiralSignatureWeight, ancestorPairExponent,
    chiralGaussianPower_eq_phase_pow]

theorem harmonicAntichainTwoSourceBinAmplitude_one
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinAmplitude chirality 1 =
      2 * chiralMaximalEventPhase chirality := by
  simp [harmonicAntichainTwoSourceBinAmplitude,
    antichainCoherentSourceSectorAmplitude,
    harmonicCriticalPairCoupling, harmonicCriticalPairCouplingQ,
    interactingChiralSignatureWeight, ancestorPairExponent,
    chiralGaussianPower_eq_phase_pow]

theorem harmonicAntichainTwoSourceBinAmplitude_two
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinAmplitude chirality 2 =
      -(49 / 16 : ℂ) := by
  fin_cases chirality <;>
    norm_num [harmonicAntichainTwoSourceBinAmplitude,
      antichainCoherentSourceSectorAmplitude,
      harmonicCriticalPairCoupling, harmonicCriticalPairCouplingQ,
      harmonic, Finset.sum_range_succ, interactingChiralSignatureWeight,
      ancestorPairExponent, chiralGaussianPower_eq_phase_pow,
      chiralMaximalEventPhase]

/-- Raw local partition amplitude after coherent source-bin aggregation. -/
def harmonicAntichainTwoSourcePartition (chirality : Fin 2) : ℂ :=
  ∑ bin, harmonicAntichainTwoSourceBinAmplitude chirality bin

theorem harmonicAntichainTwoSourcePartition_exact (chirality : Fin 2) :
    harmonicAntichainTwoSourcePartition chirality =
      -(33 / 16 : ℂ) + 2 * chiralMaximalEventPhase chirality := by
  rw [harmonicAntichainTwoSourcePartition, Fin.sum_univ_three,
    harmonicAntichainTwoSourceBinAmplitude_zero,
    harmonicAntichainTwoSourceBinAmplitude_one,
    harmonicAntichainTwoSourceBinAmplitude_two]
  ring

theorem harmonicAntichainTwoSourcePartition_normSq (chirality : Fin 2) :
    Complex.normSq (harmonicAntichainTwoSourcePartition chirality) =
      2113 / 256 := by
  rw [harmonicAntichainTwoSourcePartition_exact]
  fin_cases chirality <;>
    norm_num [Complex.normSq_apply, chiralMaximalEventPhase]

theorem harmonicAntichainTwoSourcePartition_ne_zero (chirality : Fin 2) :
    harmonicAntichainTwoSourcePartition chirality ≠ 0 := by
  intro hZero
  have hNorm := harmonicAntichainTwoSourcePartition_normSq chirality
  rw [hZero] at hNorm
  norm_num [Complex.normSq_apply] at hNorm

/-- Normalized coherent amplitude of one source bin. -/
def harmonicAntichainTwoNormalizedSourceBinAmplitude
    (chirality : Fin 2) (bin : Fin 3) : ℂ :=
  harmonicAntichainTwoSourceBinAmplitude chirality bin /
    harmonicAntichainTwoSourcePartition chirality

/-- Quantum measure of a single coherent source-bin event. -/
def harmonicAntichainTwoSourceBinQuantumMeasure
    (chirality : Fin 2) (bin : Fin 3) : ℝ :=
  Complex.normSq
    (harmonicAntichainTwoNormalizedSourceBinAmplitude chirality bin)

theorem harmonicAntichainTwoSourceBinQuantumMeasure_zero
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinQuantumMeasure chirality 0 =
      256 / 2113 := by
  rw [harmonicAntichainTwoSourceBinQuantumMeasure,
    harmonicAntichainTwoNormalizedSourceBinAmplitude, Complex.normSq_div,
    harmonicAntichainTwoSourcePartition_normSq,
    harmonicAntichainTwoSourceBinAmplitude_zero]
  norm_num

theorem harmonicAntichainTwoSourceBinQuantumMeasure_one
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinQuantumMeasure chirality 1 =
      1024 / 2113 := by
  rw [harmonicAntichainTwoSourceBinQuantumMeasure,
    harmonicAntichainTwoNormalizedSourceBinAmplitude, Complex.normSq_div,
    harmonicAntichainTwoSourcePartition_normSq,
    harmonicAntichainTwoSourceBinAmplitude_one]
  fin_cases chirality <;>
    norm_num [Complex.normSq_apply, chiralMaximalEventPhase]

theorem harmonicAntichainTwoSourceBinQuantumMeasure_two
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinQuantumMeasure chirality 2 =
      2401 / 2113 := by
  rw [harmonicAntichainTwoSourceBinQuantumMeasure,
    harmonicAntichainTwoNormalizedSourceBinAmplitude, Complex.normSq_div,
    harmonicAntichainTwoSourcePartition_normSq,
    harmonicAntichainTwoSourceBinAmplitude_two]
  norm_num

/-- The three source-bin quantum measures are not a probability vector. -/
theorem harmonicAntichainTwoSourceBinQuantumMeasure_sum
    (chirality : Fin 2) :
    ∑ bin, harmonicAntichainTwoSourceBinQuantumMeasure chirality bin =
      3681 / 2113 := by
  rw [Fin.sum_univ_three,
    harmonicAntichainTwoSourceBinQuantumMeasure_zero,
    harmonicAntichainTwoSourceBinQuantumMeasure_one,
    harmonicAntichainTwoSourceBinQuantumMeasure_two]
  norm_num

theorem harmonicAntichainTwoNormalizedSourceBinAmplitude_sum
    (chirality : Fin 2) :
    ∑ bin, harmonicAntichainTwoNormalizedSourceBinAmplitude chirality bin =
      1 := by
  unfold harmonicAntichainTwoNormalizedSourceBinAmplitude
  rw [← Finset.sum_div, harmonicAntichainTwoSourcePartition]
  exact div_self (harmonicAntichainTwoSourcePartition_ne_zero chirality)

/-- The total source event remains normalized even though the individual bin
measures do not add to it. -/
theorem harmonicAntichainTwo_totalSourceQuantumMeasure
    (chirality : Fin 2) :
    Complex.normSq
        (∑ bin, harmonicAntichainTwoNormalizedSourceBinAmplitude
          chirality bin) = 1 := by
  rw [harmonicAntichainTwoNormalizedSourceBinAmplitude_sum]
  norm_num

/-- Pairwise quantum interference between two source bins. -/
def harmonicAntichainTwoSourceBinInterference
    (chirality : Fin 2) (first second : Fin 3) : ℝ :=
  2 * (harmonicAntichainTwoNormalizedSourceBinAmplitude chirality first *
    star (harmonicAntichainTwoNormalizedSourceBinAmplitude
      chirality second)).re

theorem harmonicAntichainTwoSourceBinInterference_zero_one
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinInterference chirality 0 1 = 0 := by
  unfold harmonicAntichainTwoSourceBinInterference
    harmonicAntichainTwoNormalizedSourceBinAmplitude
  rw [harmonicAntichainTwoSourceBinAmplitude_zero,
    harmonicAntichainTwoSourceBinAmplitude_one,
    harmonicAntichainTwoSourcePartition_exact]
  fin_cases chirality <;>
    norm_num [chiralMaximalEventPhase, Complex.div_re, Complex.div_im,
      Complex.normSq_apply]

theorem harmonicAntichainTwoSourceBinInterference_one_two
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinInterference chirality 1 2 = 0 := by
  unfold harmonicAntichainTwoSourceBinInterference
    harmonicAntichainTwoNormalizedSourceBinAmplitude
  rw [harmonicAntichainTwoSourceBinAmplitude_one,
    harmonicAntichainTwoSourceBinAmplitude_two,
    harmonicAntichainTwoSourcePartition_exact]
  fin_cases chirality <;>
    norm_num [chiralMaximalEventPhase, Complex.div_re, Complex.div_im,
      Complex.normSq_apply]

/-- All nonadditivity in this first ensemble is the destructive interference
between the gregarious and fully linked source bins. -/
theorem harmonicAntichainTwoSourceBinInterference_zero_two
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinInterference chirality 0 2 =
      -(1568 / 2113) := by
  unfold harmonicAntichainTwoSourceBinInterference
    harmonicAntichainTwoNormalizedSourceBinAmplitude
  rw [harmonicAntichainTwoSourceBinAmplitude_zero,
    harmonicAntichainTwoSourceBinAmplitude_two,
    harmonicAntichainTwoSourcePartition_exact]
  fin_cases chirality <;>
    norm_num [chiralMaximalEventPhase, Complex.div_re, Complex.div_im,
      Complex.normSq_apply]

/-! ## 3. Why an expected coherence needs an extra sampling rule -/

/-- A nonnegative finite profile is an ordinary probability profile when its
entries add to one. -/
def IsClassicalSourceProbabilityProfile (profile : Fin 3 → ℝ) : Prop :=
  (∀ bin, 0 ≤ profile bin) ∧ ∑ bin, profile bin = 1

/-- The harmonic quantum measure itself cannot be used as a classical source
distribution: its bin measures add to `3681/2113`, not one. -/
theorem harmonicSourceQuantumMeasure_not_classicalProbability
    (chirality : Fin 2) :
    ¬IsClassicalSourceProbabilityProfile
      (harmonicAntichainTwoSourceBinQuantumMeasure chirality) := by
  intro hProbability
  have hSum := hProbability.2
  rw [harmonicAntichainTwoSourceBinQuantumMeasure_sum] at hSum
  norm_num at hSum

/-- Optional additive profile obtained by explicitly renormalizing the three
singleton source-bin Born weights.  This is a sampling prescription, not the
original quantum measure. -/
def singletonBornSourceSamplingProbability
    (chirality : Fin 2) (bin : Fin 3) : ℝ :=
  harmonicAntichainTwoSourceBinQuantumMeasure chirality bin /
    (∑ candidate,
      harmonicAntichainTwoSourceBinQuantumMeasure chirality candidate)

theorem singletonBornSourceSamplingProbability_exact
    (chirality : Fin 2) :
    singletonBornSourceSamplingProbability chirality 0 = 256 / 3681
      ∧ singletonBornSourceSamplingProbability chirality 1 = 1024 / 3681
      ∧ singletonBornSourceSamplingProbability chirality 2 = 2401 / 3681 := by
  rw [singletonBornSourceSamplingProbability,
    singletonBornSourceSamplingProbability,
    singletonBornSourceSamplingProbability,
    harmonicAntichainTwoSourceBinQuantumMeasure_sum,
    harmonicAntichainTwoSourceBinQuantumMeasure_zero,
    harmonicAntichainTwoSourceBinQuantumMeasure_one,
    harmonicAntichainTwoSourceBinQuantumMeasure_two]
  norm_num

theorem singletonBornSourceSamplingProbability_isClassical
    (chirality : Fin 2) :
    IsClassicalSourceProbabilityProfile
      (singletonBornSourceSamplingProbability chirality) := by
  constructor
  · intro bin
    unfold singletonBornSourceSamplingProbability
    apply div_nonneg
    · exact Complex.normSq_nonneg _
    · rw [harmonicAntichainTwoSourceBinQuantumMeasure_sum]
      norm_num
  · rw [Fin.sum_univ_three,
      (singletonBornSourceSamplingProbability_exact chirality).1,
      (singletonBornSourceSamplingProbability_exact chirality).2.1,
      (singletonBornSourceSamplingProbability_exact chirality).2.2]
    norm_num

/-- Conditional one-step expected coherence retention under the explicitly
added singleton-Born sampling prescription. -/
def singletonBornExpectedSourceRetention (chirality : Fin 2) : ℝ :=
  ∑ bin, singletonBornSourceSamplingProbability chirality bin *
    antichainTwoSourceBinRetention bin

theorem singletonBornExpectedSourceRetention_exact (chirality : Fin 2) :
    singletonBornExpectedSourceRetention chirality = 6082 / 18405 := by
  rw [singletonBornExpectedSourceRetention, Fin.sum_univ_three,
    (singletonBornSourceSamplingProbability_exact chirality).1,
    (singletonBornSourceSamplingProbability_exact chirality).2.1,
    (singletonBornSourceSamplingProbability_exact chirality).2.2]
  norm_num [antichainTwoSourceBinRetention,
    antichainTwoSourceBinParameter]

/-! ## 4. Ensemble capstone -/

/-- **First exact source ensemble.**  The harmonic law predicts a normalized
but nonadditive three-bin quantum profile.  Only after adding a classical
sampling prescription does an ordinary expected retention exist. -/
theorem harmonicAntichainTwoSourceEnsemble_complete (chirality : Fin 2) :
    antichainTwoSourceBinRetention 0 = 0
      ∧ antichainTwoSourceBinRetention 1 = 1 / 4
      ∧ antichainTwoSourceBinRetention 2 = 2 / 5
      ∧ harmonicAntichainTwoSourceBinQuantumMeasure chirality 0 = 256 / 2113
      ∧ harmonicAntichainTwoSourceBinQuantumMeasure chirality 1 = 1024 / 2113
      ∧ harmonicAntichainTwoSourceBinQuantumMeasure chirality 2 = 2401 / 2113
      ∧ (∑ bin, harmonicAntichainTwoSourceBinQuantumMeasure chirality bin) =
          3681 / 2113
      ∧ Complex.normSq
          (∑ bin, harmonicAntichainTwoNormalizedSourceBinAmplitude
            chirality bin) = 1
      ∧ harmonicAntichainTwoSourceBinInterference chirality 0 2 =
          -(1568 / 2113)
      ∧ ¬IsClassicalSourceProbabilityProfile
          (harmonicAntichainTwoSourceBinQuantumMeasure chirality)
      ∧ singletonBornExpectedSourceRetention chirality = 6082 / 18405 := by
  exact ⟨antichainTwoSourceBinRetention_exact.1,
    antichainTwoSourceBinRetention_exact.2.1,
    antichainTwoSourceBinRetention_exact.2.2,
    harmonicAntichainTwoSourceBinQuantumMeasure_zero chirality,
    harmonicAntichainTwoSourceBinQuantumMeasure_one chirality,
    harmonicAntichainTwoSourceBinQuantumMeasure_two chirality,
    harmonicAntichainTwoSourceBinQuantumMeasure_sum chirality,
    harmonicAntichainTwo_totalSourceQuantumMeasure chirality,
    harmonicAntichainTwoSourceBinInterference_zero_two chirality,
    harmonicSourceQuantumMeasure_not_classicalProbability chirality,
    singletonBornExpectedSourceRetention_exact chirality⟩

#print axioms antichainCoherentSourceSectorAmplitude_eq_sum
#print axioms antichainTwoSourceBinParameter_eq_birthSource
#print axioms harmonicAntichainTwoSourceBinQuantumMeasure_sum
#print axioms harmonicAntichainTwoSourceBinInterference_zero_two
#print axioms harmonicSourceQuantumMeasure_not_classicalProbability
#print axioms singletonBornExpectedSourceRetention_exact
#print axioms harmonicAntichainTwoSourceEnsemble_complete

end

end UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble
