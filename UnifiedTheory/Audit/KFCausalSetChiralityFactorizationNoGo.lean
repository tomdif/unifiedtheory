/-
  Audit/KFCausalSetChiralityFactorizationNoGo.lean

  SCALAR SEQUENTIAL GROWTH CANNOT DERIVE A NONTRIVIAL COMMON CHIRALITY RECORD

  The common-sector compounding law needs two chirality alternatives which
  are simultaneously nonzero and exactly decoherent.  This file proves that
  no scalar-amplitude sequential-growth law can provide them.

  At every finite depth the repository's canonical growth functional is the
  rank-one outer product of one scalar path-amplitude vector.  Consequently
  every two-event restriction has zero determinant:

      D(A,A) D(B,B) = D(A,B) D(B,A).

  If both diagonal weights are nonzero, both cross terms are therefore
  nonzero.  Exact decoherence of a binary record forces at least one cell to
  have zero weight.  The obstruction quantifies over every finite branching
  alphabet, so merely appending a conserved chirality label to histories does
  not evade it while the amplitudes remain scalar.  Projective refinement
  preserves the nonzero cross term exactly.

  In particular, no scalar growth law realizes the interior chirality record
  `diag(1/2-y,1/2+y)` for `|y|<1/2`, including the first linked-birth record
  `(1/3,2/3)`.  The existing higher-rank theorem supplies the sharp exit:
  latent rank two realizes every balanced interior kernel and rank one cannot.

  Thus the common-sector factorization is not derivable from the present
  scalar growth container.  It requires genuinely vector/operator-valued
  transition data (or an equivalent orthogonal environment/record algebra),
  not another scalar transition rule.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetChiralityRecordCompounding
import UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralityFactorizationNoGo

noncomputable section

open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetSpectatorRecordChannel
open UnifiedTheory.Audit.KFCausalSetChiralityRecordCompounding

universe u

/-! ## 1. The universal rank-one event identity -/

/-- Every two-event restriction of one scalar amplitude vector has zero
determinant.  No disjointness or exhaustivity assumption is needed. -/
theorem scalarAmplitude_eventDeterminant_zero
    {History : Type u}
    (amplitude : History → ℂ) (first second : Finset History) :
    growthEventDecoherence (amplitudeDecoherence amplitude) first first *
          growthEventDecoherence (amplitudeDecoherence amplitude) second second -
        growthEventDecoherence (amplitudeDecoherence amplitude) first second *
          growthEventDecoherence (amplitudeDecoherence amplitude) second first = 0 := by
  simp only [amplitude_growthEventDecoherence_eq]
  ring

/-- Two scalar-amplitude events with nonzero diagonal weights necessarily
interfere. -/
theorem scalarAmplitude_nonzeroCells_have_nonzeroInterference
    {History : Type u}
    (amplitude : History → ℂ) (first second : Finset History)
    (hFirst : growthEventDecoherence
      (amplitudeDecoherence amplitude) first first ≠ 0)
    (hSecond : growthEventDecoherence
      (amplitudeDecoherence amplitude) second second ≠ 0) :
    growthEventDecoherence
        (amplitudeDecoherence amplitude) first second ≠ 0 := by
  intro hCross
  have hDet := scalarAmplitude_eventDeterminant_zero amplitude first second
  rw [hCross, zero_mul, sub_zero] at hDet
  exact (mul_ne_zero hFirst hSecond) hDet

/-! ## 2. No nontrivial exact binary record in scalar sequential growth -/

/-- A nontrivial exact binary record has two nonzero diagonal cells and zero
cross-decoherence. -/
def HasNontrivialExactBinaryRecord
    {History : Type u} [Fintype History]
    (D : GrowthDecoherenceFunctional History)
    (first second : Finset History) : Prop :=
  growthEventDecoherence D first first ≠ 0 ∧
    growthEventDecoherence D second second ≠ 0 ∧
    growthEventDecoherence D first second = 0 ∧
    growthEventDecoherence D second first = 0

/-- Universal scalar-growth no-go.  This also covers any enlarged branch type
carrying a nominally conserved chirality label: as long as the growth law has
one scalar amplitude per extended history, its event kernel is rank one. -/
theorem scalarRankedGrowth_no_nontrivial_exact_binary_record
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (depth : ℕ)
    (first second : Finset (RankedGrowthPath Branch depth)) :
    ¬ HasNontrivialExactBinaryRecord
        (finiteRankedDepthDecoherence law depth) first second := by
  rintro ⟨hFirst, hSecond, hCross, _hReverse⟩
  exact (scalarAmplitude_nonzeroCells_have_nonzeroInterference
    (finiteRankedPathAmplitude law depth) first second hFirst hSecond) hCross

/-- Direct specialization to the repository's complete interacting chiral
causal-set law.  Choosing either global chirality character does not change
the scalar-rank obstruction. -/
theorem completeChiralGrowth_no_nontrivial_exact_binary_record
    (chirality : Fin 2) (depth : ℕ)
    (first second : Finset
      (RankedGrowthPath CausalSetGrowthBranch depth)) :
    ¬ HasNontrivialExactBinaryRecord
        (finiteRankedDepthDecoherence
          (completeChiralCausalSetGrowthLaw chirality) depth)
        first second :=
  scalarRankedGrowth_no_nontrivial_exact_binary_record
    (completeChiralCausalSetGrowthLaw chirality) depth first second

/-- If two scalar-growth cells are nonzero at one depth, their interference
survives every exhaustive projective refinement.  Refinement cannot generate
the missing record factorization. -/
theorem scalarRankedGrowth_binaryInterference_persists
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (depth : ℕ)
    (first second : Finset (RankedGrowthPath Branch depth))
    (hFirst : growthEventDecoherence
      (finiteRankedDepthDecoherence law depth) first first ≠ 0)
    (hSecond : growthEventDecoherence
      (finiteRankedDepthDecoherence law depth) second second ≠ 0) :
    ∀ steps : ℕ,
      growthEventDecoherence
          (finiteRankedDepthDecoherence law (depth + steps))
          (refineRankedGrowthEventBy first steps)
          (refineRankedGrowthEventBy second steps) ≠ 0 := by
  intro steps
  rw [finiteRankedDepthDecoherence_projective_by]
  exact scalarAmplitude_nonzeroCells_have_nonzeroInterference
    (finiteRankedPathAmplitude law depth) first second hFirst hSecond

/-! ## 3. The interior chirality record is impossible at scalar rank -/

/-- No scalar sequential-growth functional can realize the nontrivial
chirality record weights `1/2-y` and `1/2+y` as exactly decoherent cells when
`y` lies in the strict positivity interval. -/
theorem scalarRankedGrowth_cannot_realize_interior_chirality_record
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (depth : ℕ)
    (first second : Finset (RankedGrowthPath Branch depth))
    {y : ℝ} (hy : |y| < 1 / 2) :
    ¬ (growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) first first =
            (((1 / 2 - y : ℝ) : ℂ))
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) second second =
            (((1 / 2 + y : ℝ) : ℂ))
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) first second = 0
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) second first = 0) := by
  rintro ⟨hFirstValue, hSecondValue, hCross, hReverse⟩
  have hyBounds := abs_lt.mp hy
  have hFirstPositive : 0 < (1 / 2 - y : ℝ) := by linarith
  have hSecondPositive : 0 < (1 / 2 + y : ℝ) := by linarith
  have hFirstNonzero : growthEventDecoherence
      (finiteRankedDepthDecoherence law depth) first first ≠ 0 := by
    rw [hFirstValue]
    exact_mod_cast ne_of_gt hFirstPositive
  have hSecondNonzero : growthEventDecoherence
      (finiteRankedDepthDecoherence law depth) second second ≠ 0 := by
    rw [hSecondValue]
    exact_mod_cast ne_of_gt hSecondPositive
  exact scalarRankedGrowth_no_nontrivial_exact_binary_record
    law depth first second
    ⟨hFirstNonzero, hSecondNonzero, hCross, hReverse⟩

/-- The first linked-birth record `(1/3,2/3)` is already excluded at every
depth of every scalar sequential-growth law. -/
theorem scalarRankedGrowth_cannot_realize_firstLinkedBirth_record
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (depth : ℕ)
    (first second : Finset (RankedGrowthPath Branch depth)) :
    ¬ (growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) first first = 1 / 3
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) second second = 2 / 3
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) first second = 0
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) second first = 0) := by
  simpa only [show (((1 / 2 - (1 / 6 : ℝ) : ℝ) : ℂ)) = 1 / 3 by norm_num,
      show (((1 / 2 + (1 / 6 : ℝ) : ℝ) : ℂ)) = 2 / 3 by norm_num] using
    scalarRankedGrowth_cannot_realize_interior_chirality_record
      law depth first second (y := (1 / 6 : ℝ)) (by norm_num)

/-! ## 4. Sharp exit: higher-rank data are necessary and sufficient -/

/-- The factorization frontier in its sharp form.  Scalar sequential growth
cannot realize the interior record, while the already constructed latent
rank-two amplitude realizes the underlying balanced kernel.  The latter is
therefore the minimal algebraic enlargement on which the chirality-basis
pinching can produce the desired exact record.

This theorem proves the required rank, not a microscopic vector-valued growth
law; constructing that law is the newly isolated frontier. -/
theorem commonChiralityFactorization_scalar_noGo_rankTwo_exit
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (depth : ℕ)
    (first second : Finset (RankedGrowthPath Branch depth))
    {y : ℝ} (hy : |y| < 1 / 2) :
    (¬ (growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) first first =
            (((1 / 2 - y : ℝ) : ℂ))
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) second second =
            (((1 / 2 + y : ℝ) : ℂ))
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) first second = 0
      ∧ growthEventDecoherence
          (finiteRankedDepthDecoherence law depth) second first = 0))
      ∧ IsTwoComponentAmplitudeKernel (balancedHistoryKernel y)
      ∧ ¬ IsScalarAmplitudeKernel (balancedHistoryKernel y)
      ∧ chiralityRecordDecoherence y 0 1 = 0
      ∧ chiralityRecordDecoherence y 1 0 = 0 := by
  have hyClosed : |y| ≤ 1 / 2 := le_of_lt hy
  exact ⟨scalarRankedGrowth_cannot_realize_interior_chirality_record
      law depth first second hy,
    balancedHistoryKernel_isTwoComponent hyClosed,
    strictInterior_not_scalarAmplitudeKernel hy,
    (chiralityRecordDecoherence_offDiagonal y).1,
    (chiralityRecordDecoherence_offDiagonal y).2⟩

#print axioms scalarAmplitude_eventDeterminant_zero
#print axioms scalarAmplitude_nonzeroCells_have_nonzeroInterference
#print axioms scalarRankedGrowth_no_nontrivial_exact_binary_record
#print axioms completeChiralGrowth_no_nontrivial_exact_binary_record
#print axioms scalarRankedGrowth_binaryInterference_persists
#print axioms scalarRankedGrowth_cannot_realize_interior_chirality_record
#print axioms scalarRankedGrowth_cannot_realize_firstLinkedBirth_record
#print axioms commonChiralityFactorization_scalar_noGo_rankTwo_exit

end

end UnifiedTheory.Audit.KFCausalSetChiralityFactorizationNoGo
