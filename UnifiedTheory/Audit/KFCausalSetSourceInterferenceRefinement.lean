/-
  Audit/KFCausalSetSourceInterferenceRefinement.lean

  PROJECTIVE REFINEMENT DOES NOT DECOHERE CYLINDER EVENTS

  The source-mixing benchmark and projective causal-set refinement are
  different operations.  Independent multiplicative mixing contracts the
  rank-two orientation kernel.  By contrast, exhaustive cylinder refinement
  sums over every continuation, and normalized transition amplitudes make
  every decoherence-functional entry exactly projectively invariant.

  Therefore nonzero inter-bin interference cannot decay under projective
  refinement alone.  A genuine classicalizing mechanism must be an additional
  non-projective CP channel, environmental trace, record restriction, or other
  coarse graining.  Finer source bins do not evade the theorem: it holds for
  arbitrary finite cylinder events.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetSourceInterferenceRefinement

noncomputable section

open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetSourceMagnitudeDecoherence
open UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble

/-! ## 1. Arbitrary cylinder-bin refinement -/

/-- Decoherence entry between two bins after exhaustively continuing both
cylinder events through `steps` further ranks. -/
def refinedCylinderBinDecoherence {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) {depth : ℕ}
    (sector : Fin 3 → Finset (RankedGrowthPath Branch depth))
    (steps : ℕ) (first second : Fin 3) : ℂ :=
  growthEventDecoherence
    (finiteRankedDepthDecoherence law (depth + steps))
    (refineRankedGrowthEventBy (sector first) steps)
    (refineRankedGrowthEventBy (sector second) steps)

/-- Projective consistency is a conservation law for every diagonal and
off-diagonal bin entry. -/
theorem refinedCylinderBinDecoherence_eq_base
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) {depth : ℕ}
    (sector : Fin 3 → Finset (RankedGrowthPath Branch depth))
    (steps : ℕ) (first second : Fin 3) :
    refinedCylinderBinDecoherence law sector steps first second =
      growthEventDecoherence
        (finiteRankedDepthDecoherence law depth)
        (sector first) (sector second) := by
  exact finiteRankedDepthDecoherence_projective_by law depth
    (sector first) (sector second) steps

theorem refinedCylinderBinDecoherence_one_eq_base
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) {depth : ℕ}
    (sector : Fin 3 → Finset (RankedGrowthPath Branch depth))
    (first second : Fin 3) :
    refinedCylinderBinDecoherence law sector 1 first second =
      growthEventDecoherence
        (finiteRankedDepthDecoherence law depth)
        (sector first) (sector second) :=
  refinedCylinderBinDecoherence_eq_base law sector 1 first second

theorem refinedCylinderBinDecoherence_two_eq_base
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) {depth : ℕ}
    (sector : Fin 3 → Finset (RankedGrowthPath Branch depth))
    (first second : Fin 3) :
    refinedCylinderBinDecoherence law sector 2 first second =
      growthEventDecoherence
        (finiteRankedDepthDecoherence law depth)
        (sector first) (sector second) :=
  refinedCylinderBinDecoherence_eq_base law sector 2 first second

/-- Real pair-interference contribution after refinement. -/
def refinedCylinderBinInterference {Branch : ℕ → Type*}
    [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) {depth : ℕ}
    (sector : Fin 3 → Finset (RankedGrowthPath Branch depth))
    (steps : ℕ) (first second : Fin 3) : ℝ :=
  2 * (refinedCylinderBinDecoherence
    law sector steps first second).re

theorem refinedCylinderBinInterference_eq_base
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) {depth : ℕ}
    (sector : Fin 3 → Finset (RankedGrowthPath Branch depth))
    (steps : ℕ) (first second : Fin 3) :
    refinedCylinderBinInterference law sector steps first second =
      2 * (growthEventDecoherence
        (finiteRankedDepthDecoherence law depth)
        (sector first) (sector second)).re := by
  rw [refinedCylinderBinInterference,
    refinedCylinderBinDecoherence_eq_base]

/-- A nonzero off-diagonal cylinder entry remains nonzero at every exhaustive
refinement depth. -/
theorem projectiveRefinement_preserves_nonzero_offDiagonal
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) {depth : ℕ}
    (sector : Fin 3 → Finset (RankedGrowthPath Branch depth))
    {first second : Fin 3}
    (hNonzero : growthEventDecoherence
      (finiteRankedDepthDecoherence law depth)
      (sector first) (sector second) ≠ 0)
    (steps : ℕ) :
    refinedCylinderBinDecoherence law sector steps first second ≠ 0 := by
  rw [refinedCylinderBinDecoherence_eq_base]
  exact hNonzero

/-! ## 2. Exact conflict with multiplicative source damping -/

/-- The independent-mixing benchmark would erase the empty/full channel in
one stage because the gregarious retention factor is zero. -/
theorem emptyFull_multiplicativeRetentionProduct_zero :
    antichainTwoSourceBinRetention 0 *
      antichainTwoSourceBinRetention 2 = 0 := by
  rw [antichainTwoSourceBinRetention_exact.1,
    antichainTwoSourceBinRetention_exact.2.2]
  norm_num

/-- The actual local harmonic empty/full entry is nonzero, while multiplying
it by the two source-retention factors gives zero. -/
theorem localHarmonic_projective_and_multiplicative_predictions_differ
    (chirality : Fin 2) :
    harmonicAntichainTwoSourceBinDecoherence chirality 0 2 ≠ 0
      ∧ antichainTwoSourceBinRetention 0 *
          antichainTwoSourceBinRetention 2 *
          harmonicAntichainTwoSourceBinDecoherence chirality 0 2 = 0 := by
  exact ⟨harmonicAntichainTwoSourceBinDecoherence_zero_two_ne_zero chirality,
    by rw [antichainTwoSourceBinRetention_exact.1]
       norm_num⟩

/-! ## 3. Harmonic cylinder no-go -/

/-- On the concrete harmonic causal-set law, one and two exhaustive
refinement stages leave every chosen source-bin entry unchanged.  This theorem
is independent of how finely the source sectors are defined. -/
theorem harmonicCylinderSourceBins_one_two_invariant
    (chirality : Fin 2) {depth : ℕ}
    (sector : Fin 3 →
      Finset (RankedGrowthPath CausalSetGrowthBranch depth))
    (first second : Fin 3) :
    refinedCylinderBinDecoherence
        (harmonicCriticalCausalSetGrowthLaw chirality)
        sector 1 first second =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (harmonicCriticalCausalSetGrowthLaw chirality) depth)
        (sector first) (sector second)
      ∧ refinedCylinderBinDecoherence
        (harmonicCriticalCausalSetGrowthLaw chirality)
        sector 2 first second =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (harmonicCriticalCausalSetGrowthLaw chirality) depth)
        (sector first) (sector second) := by
  exact ⟨refinedCylinderBinDecoherence_one_eq_base _ _ _ _,
    refinedCylinderBinDecoherence_two_eq_base _ _ _ _⟩

/-- If a cylinder-sector realization has the exact local two-antichain
empty/full entry, exhaustive refinement preserves its value `-784/2113` at
every later depth.  The realization hypothesis makes the finite local-to-
cylinder bridge explicit rather than silently identifying the two objects. -/
theorem realizedHarmonicSourceBins_zero_two_allRefinements
    (chirality : Fin 2) {depth : ℕ}
    (sector : Fin 3 →
      Finset (RankedGrowthPath CausalSetGrowthBranch depth))
    (hRealizes :
      growthEventDecoherence
          (finiteRankedDepthDecoherence
            (harmonicCriticalCausalSetGrowthLaw chirality) depth)
          (sector 0) (sector 2) =
        harmonicAntichainTwoSourceBinDecoherence chirality 0 2)
    (steps : ℕ) :
    refinedCylinderBinDecoherence
        (harmonicCriticalCausalSetGrowthLaw chirality)
        sector steps 0 2 = ((-784 / 2113 : ℝ) : ℂ) := by
  rw [refinedCylinderBinDecoherence_eq_base, hRealizes,
    harmonicAntichainTwoSourceBinDecoherence_zero_two]

/-- Under the same explicit realization bridge, the real pair-interference
contribution remains exactly `-1568/2113` at every refinement depth. -/
theorem realizedHarmonicSourceBins_interference_allRefinements
    (chirality : Fin 2) {depth : ℕ}
    (sector : Fin 3 →
      Finset (RankedGrowthPath CausalSetGrowthBranch depth))
    (hRealizes :
      growthEventDecoherence
          (finiteRankedDepthDecoherence
            (harmonicCriticalCausalSetGrowthLaw chirality) depth)
          (sector 0) (sector 2) =
        harmonicAntichainTwoSourceBinDecoherence chirality 0 2)
    (steps : ℕ) :
    refinedCylinderBinInterference
        (harmonicCriticalCausalSetGrowthLaw chirality)
        sector steps 0 2 = -1568 / 2113 := by
  rw [refinedCylinderBinInterference_eq_base, hRealizes,
    harmonicAntichainTwoSourceBinDecoherence_zero_two]
  norm_num

/-- **Refinement no-go.**  Exhaustive projective refinement transports
interference; it cannot suppress any nonzero cylinder off-diagonal.  The
multiplicative orientation benchmark is therefore an additional coarse-
graining channel, not the refinement map of the harmonic growth law. -/
theorem projectiveRefinement_does_not_generate_decoherence :
    (∀ (chirality : Fin 2) {depth : ℕ}
        (sector : Fin 3 →
          Finset (RankedGrowthPath CausalSetGrowthBranch depth))
        (steps : ℕ) (first second : Fin 3),
      refinedCylinderBinDecoherence
          (harmonicCriticalCausalSetGrowthLaw chirality)
          sector steps first second =
        growthEventDecoherence
          (finiteRankedDepthDecoherence
            (harmonicCriticalCausalSetGrowthLaw chirality) depth)
          (sector first) (sector second))
      ∧ (∀ chirality : Fin 2,
        harmonicAntichainTwoSourceBinDecoherence chirality 0 2 ≠ 0)
      ∧ antichainTwoSourceBinRetention 0 *
          antichainTwoSourceBinRetention 2 = 0 := by
  exact ⟨fun chirality _ sector steps first second =>
      refinedCylinderBinDecoherence_eq_base
        (harmonicCriticalCausalSetGrowthLaw chirality)
        sector steps first second,
    harmonicAntichainTwoSourceBinDecoherence_zero_two_ne_zero,
    emptyFull_multiplicativeRetentionProduct_zero⟩

#print axioms refinedCylinderBinDecoherence_eq_base
#print axioms projectiveRefinement_preserves_nonzero_offDiagonal
#print axioms harmonicCylinderSourceBins_one_two_invariant
#print axioms realizedHarmonicSourceBins_interference_allRefinements
#print axioms projectiveRefinement_does_not_generate_decoherence

end

end UnifiedTheory.Audit.KFCausalSetSourceInterferenceRefinement
