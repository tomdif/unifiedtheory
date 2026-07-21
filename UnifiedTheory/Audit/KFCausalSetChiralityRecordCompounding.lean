/-
  Audit/KFCausalSetChiralityRecordCompounding.lean

  CHIRALITY RECORD BIAS AND THE TWO-BIRTH COMPOUNDING TRIPWIRE

  Pinching a balanced kernel in its chirality eigenbasis gives the classical
  record weights `1/2-y` and `1/2+y`.  This gives the geometric source
  magnitude a framework-internal operational role: it is half of the signed
  bias of the chirality record.  The rank-three chain, fork, and singleton
  antichain births therefore have exact record biases `1/3`, `2/5`, and `1/4`.

  This does not by itself reconcile the interior geometric record with the
  pure character selected by balanced birth dynamics.  They are distinct
  objects in the current theory:

  * the sign response selects a pure signature character deterministically;
  * measuring the geometric balanced kernel gives an interior biased record.

  Two-birth arithmetic makes the missing bridge precise.  An independent
  product of the first two linked-birth records has probabilities

      (00,01,10,11) = (1/9,2/9,2/9,4/9),

  and leaves each one-birth marginal at `(1/3,2/3)`.  Independence therefore
  does not amplify a transported handedness law.

  If one instead supplies a common-chirality/transport contract and conditions
  both births onto the same sector, the sector likelihoods multiply and are
  renormalized.  The induced parameter law is

      y boxplus z = (y+z)/(1+4yz),

  equivalently `r boxplus s = (r+s)/(1+rs)` for record biases `r=2y`.
  The first two linked chain births then amplify `(1/3,2/3)` to `(1/5,4/5)`.
  This is the hyperbolic-tangent/odds-addition law, not the previously studied
  coherence-multiplication channel `2yz`.

  The common-sector conditioning is an explicit bridge, not a consequence of
  projective consistency, sign transport, or the finite tensor extension.
  Thus the file proves both the amplification mechanism and the exact extra
  law that sequential growth would still have to derive.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetSpectatorRecordChannel
import UnifiedTheory.Audit.KFCausalSetSourceMagnitudeDecoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralityRecordCompounding

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
open UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality
open UnifiedTheory.Audit.KFCausalSetConjugationCompleteness
open UnifiedTheory.Audit.KFCausalSetMicroscopicResponseLaw
open UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble
open UnifiedTheory.Audit.KFCausalSetSourceMagnitudeDecoherence
open UnifiedTheory.Audit.KFCausalSetSpectatorRecordChannel

/-! ## 1. The geometric source is the chirality-record bias -/

/-- Probability of one chirality-valued record after eigenbasis pinching. -/
def chiralityRecordProbability (y : ℝ) (chirality : Fin 2) : ℝ :=
  (chiralityRecordDecoherence y chirality chirality).re

@[simp] theorem chiralityRecordProbability_zero (y : ℝ) :
    chiralityRecordProbability y 0 = 1 / 2 - y := by
  rw [chiralityRecordProbability,
    show chiralityRecordDecoherence y 0 0 =
      (fun first second => chiralityRecordDecoherence y first second) 0 0
      from rfl,
    chiralityRecordDecoherence_exact]
  norm_num

@[simp] theorem chiralityRecordProbability_one (y : ℝ) :
    chiralityRecordProbability y 1 = 1 / 2 + y := by
  rw [chiralityRecordProbability,
    show chiralityRecordDecoherence y 1 1 =
      (fun first second => chiralityRecordDecoherence y first second) 1 1
      from rfl,
    chiralityRecordDecoherence_exact]
  norm_num

theorem chiralityRecordProbability_sum (y : ℝ) :
    ∑ chirality, chiralityRecordProbability y chirality = 1 := by
  rw [Fin.sum_univ_two]
  norm_num

/-- Signed record bias toward sector `1`.  In the repository convention this
is the `-i`/negative-holonomy record favored by a positive source. -/
def chiralityRecordBias (y : ℝ) : ℝ :=
  chiralityRecordProbability y 1 - chiralityRecordProbability y 0

theorem chiralityRecordBias_exact (y : ℝ) :
    chiralityRecordBias y = 2 * y := by
  simp [chiralityRecordBias]
  ring

/-- The finite deterministic character selector and the geometric record are
not the same kernel.  Positive drive selects sector `1`, while every geometric
source in the sharp quarter band assigns it probability strictly below 3/4. -/
theorem deterministicSelector_statisticalRecord_separation
    {source : ℝ} (hSource : 0 < source) (hQuarter : source < 1 / 4) :
    driveSelectedChirality 1 source = 1
      ∧ chiralityRecordProbability source 1 < 3 / 4
      ∧ chiralityRecordProbability source 1 ≠ 1 := by
  have hDrive : 0 < (1 : ℝ) * source := by simpa using hSource
  constructor
  · simp [driveSelectedChirality, hSource]
  constructor
  · simp
    linarith
  · simp
    linarith

theorem chainThree_chiralityRecord_exact :
    chiralityRecordProbability chainThreeNewbornSourceR 0 = 1 / 3
      ∧ chiralityRecordProbability chainThreeNewbornSourceR 1 = 2 / 3
      ∧ chiralityRecordBias chainThreeNewbornSourceR = 1 / 3 := by
  rw [chainThreeNewbornSourceR_exact]
  norm_num [chiralityRecordBias]

theorem forkThree_chiralityRecord_exact :
    chiralityRecordProbability forkThreeNewbornSourceR 0 = 3 / 10
      ∧ chiralityRecordProbability forkThreeNewbornSourceR 1 = 7 / 10
      ∧ chiralityRecordBias forkThreeNewbornSourceR = 2 / 5 := by
  rw [forkThreeNewbornSourceR_exact]
  norm_num [chiralityRecordBias]

theorem antichainSingleton_chiralityRecord_exact :
    chiralityRecordProbability (antichainTwoSourceBinParameter 1) 0 = 3 / 8
      ∧ chiralityRecordProbability (antichainTwoSourceBinParameter 1) 1 = 5 / 8
      ∧ chiralityRecordBias (antichainTwoSourceBinParameter 1) = 1 / 4 := by
  rw [(antichainTwoSourceBinParameter_exact).2.1]
  norm_num [chiralityRecordBias]

/-! ## 2. The first two sequential linked births -/

/-- Real source of the first linked birth, before the next full-chain birth. -/
def firstLinkedBirthSourceR : ℝ :=
  ((maximalBirthOrientationSourceQ firstLinkedParent firstLinkedPast : ℚ) : ℝ)

theorem firstLinkedBirthSourceR_exact :
    firstLinkedBirthSourceR = 1 / 6 := by
  norm_num [firstLinkedBirthSourceR, firstLinkedBirth_source_exact]

/-- The next full-precursor birth on the two-chain has the same source as the
first linked birth. -/
theorem firstTwoLinkedChainBirths_same_source :
    firstLinkedBirthSourceR = chainThreeNewbornSourceR
      ∧ firstLinkedBirthSourceR = 1 / 6 := by
  rw [firstLinkedBirthSourceR_exact, chainThreeNewbornSourceR_exact]
  norm_num

/-! ## 3. Independent records do not amplify -/

/-- Classical product probability of two independently pinched chirality
records. -/
def independentTwoBirthRecordProbability
    (y z : ℝ) (outcome : Fin 2 × Fin 2) : ℝ :=
  chiralityRecordProbability y outcome.1 *
    chiralityRecordProbability z outcome.2

theorem independentTwoBirthRecordProbability_sum (y z : ℝ) :
    ∑ outcome, independentTwoBirthRecordProbability y z outcome = 1 := by
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [independentTwoBirthRecordProbability]
  ring

/-- Independence leaves the second record marginal unchanged; the analogous
first-marginal statement follows by symmetry. -/
theorem independentTwoBirth_secondMarginal
    (y z : ℝ) (second : Fin 2) :
    ∑ first, independentTwoBirthRecordProbability y z (first, second) =
      chiralityRecordProbability z second := by
  fin_cases second <;>
    norm_num [independentTwoBirthRecordProbability, Fin.sum_univ_two] <;>
    ring

theorem independentTwoBirth_firstMarginal
    (y z : ℝ) (first : Fin 2) :
    ∑ second, independentTwoBirthRecordProbability y z (first, second) =
      chiralityRecordProbability y first := by
  fin_cases first <;>
    norm_num [independentTwoBirthRecordProbability, Fin.sum_univ_two] <;>
    ring

/-- Exact independent-product verdict for the first two sequential linked
chain births.  Mixed outcomes carry total probability `4/9`, and neither
marginal is more predictive than the original `2/3` record. -/
theorem firstTwoLinkedChainBirths_independent_exact :
    independentTwoBirthRecordProbability
        firstLinkedBirthSourceR chainThreeNewbornSourceR (0, 0) = 1 / 9
      ∧ independentTwoBirthRecordProbability
        firstLinkedBirthSourceR chainThreeNewbornSourceR (0, 1) = 2 / 9
      ∧ independentTwoBirthRecordProbability
        firstLinkedBirthSourceR chainThreeNewbornSourceR (1, 0) = 2 / 9
      ∧ independentTwoBirthRecordProbability
        firstLinkedBirthSourceR chainThreeNewbornSourceR (1, 1) = 4 / 9
      ∧ (∑ first, independentTwoBirthRecordProbability
          firstLinkedBirthSourceR chainThreeNewbornSourceR (first, 1)) = 2 / 3 := by
  rw [firstLinkedBirthSourceR_exact, chainThreeNewbornSourceR_exact]
  norm_num [independentTwoBirthRecordProbability,
    Fin.sum_univ_two]

/-! ## 4. A common transported sector compounds evidence -/

/-- Total weight of the equal-sector alternatives before conditioning. -/
def commonChiralityNormalizer (y z : ℝ) : ℝ :=
  chiralityRecordProbability y 0 * chiralityRecordProbability z 0 +
    chiralityRecordProbability y 1 * chiralityRecordProbability z 1

theorem commonChiralityNormalizer_exact (y z : ℝ) :
    commonChiralityNormalizer y z = 1 / 2 + 2 * y * z := by
  simp [commonChiralityNormalizer]
  ring

/-- Conditional probability of a single transported chirality shared by both
births.  This removes the mixed sectors and renormalizes the two matching
sector likelihoods. -/
def commonChiralityRecordProbability
    (y z : ℝ) (chirality : Fin 2) : ℝ :=
  chiralityRecordProbability y chirality *
      chiralityRecordProbability z chirality /
    commonChiralityNormalizer y z

theorem commonChiralityRecordProbability_sum
    {y z : ℝ} (hNormalizer : commonChiralityNormalizer y z ≠ 0) :
    ∑ chirality, commonChiralityRecordProbability y z chirality = 1 := by
  rw [Fin.sum_univ_two]
  unfold commonChiralityRecordProbability
  rw [← add_div]
  change commonChiralityNormalizer y z /
      commonChiralityNormalizer y z = 1
  exact div_self hNormalizer

/-- Parameter of the normalized common-sector record.  In normalized-bias
coordinates `r=2y`, this is the addition law `(r+s)/(1+rs)`. -/
def commonChiralityCompose (y z : ℝ) : ℝ :=
  (y + z) / (1 + 4 * y * z)

/-- Conditioning onto a common transported sector adds record evidence by the
normalized hyperbolic law, rather than multiplying coherence. -/
theorem commonChiralityBias_compose
    (y z : ℝ) :
    commonChiralityRecordProbability y z 1 -
        commonChiralityRecordProbability y z 0 =
      2 * commonChiralityCompose y z := by
  unfold commonChiralityRecordProbability
  rw [← sub_div, commonChiralityNormalizer_exact]
  simp only [chiralityRecordProbability_zero,
    chiralityRecordProbability_one]
  have hNumerator :
      (1 / 2 + y) * (1 / 2 + z) -
          (1 / 2 - y) * (1 / 2 - z) = y + z := by ring
  rw [hNumerator]
  have hNormalizer :
      (1 / 2 + 2 * y * z : ℝ) = (1 + 4 * y * z) / 2 := by ring
  rw [hNormalizer, div_div_eq_mul_div]
  unfold commonChiralityCompose
  rw [mul_div]
  ring

theorem commonChiralityRecordProbability_exact
    {y z : ℝ} (hDenominator : 1 + 4 * y * z ≠ 0) :
    commonChiralityRecordProbability y z 0 =
        1 / 2 - commonChiralityCompose y z
      ∧ commonChiralityRecordProbability y z 1 =
        1 / 2 + commonChiralityCompose y z := by
  have hNormalizer : 1 / 2 + 2 * y * z ≠ 0 := by
    intro hZero
    apply hDenominator
    nlinarith
  have hNormalizer' : commonChiralityNormalizer y z ≠ 0 := by
    rw [commonChiralityNormalizer_exact]
    exact hNormalizer
  have hSum := commonChiralityRecordProbability_sum hNormalizer'
  rw [Fin.sum_univ_two] at hSum
  have hBias := commonChiralityBias_compose y z
  constructor <;> linarith

theorem commonChiralityCompose_bias_coordinates
    (r s : ℝ) :
    2 * commonChiralityCompose (r / 2) (s / 2) =
      (r + s) / (1 + r * s) := by
  unfold commonChiralityCompose
  have hDenominator :
      1 + 4 * (r / 2) * (s / 2) = 1 + r * s := by ring
  rw [hDenominator]
  ring

/-- Two positive interior records amplify the common-sector parameter.  This
strict inequality is unavailable for the independent-product marginals. -/
theorem commonChiralityCompose_strictly_amplifies_left
    {y z : ℝ} (hyNonneg : 0 ≤ y) (hyInterior : y < 1 / 2)
    (hzPositive : 0 < z) :
    y < commonChiralityCompose y z := by
  have hySq : y ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_nonneg hyNonneg] using hyInterior
  have hGap : 0 < 1 - 4 * y ^ 2 := by nlinarith
  have hPositive : 0 < z * (1 - 4 * y ^ 2) := mul_pos hzPositive hGap
  have hDenominator : 0 < 1 + 4 * y * z := by
    positivity
  rw [commonChiralityCompose, lt_div_iff₀ hDenominator]
  nlinarith

/-- Finite compounding of two physical interior records remains interior.  It
can approach a pure endpoint only through an unbounded evidence limit. -/
theorem commonChiralityCompose_lt_half
    {y z : ℝ} (hyNonneg : 0 ≤ y) (hzNonneg : 0 ≤ z)
    (hyInterior : y < 1 / 2) (hzInterior : z < 1 / 2) :
    commonChiralityCompose y z < 1 / 2 := by
  have hDenominator : 0 < 1 + 4 * y * z := by positivity
  have hGap : 0 < (1 / 2 - y) * (1 / 2 - z) :=
    mul_pos (by linarith) (by linarith)
  rw [commonChiralityCompose, div_lt_iff₀ hDenominator]
  nlinarith

/-- Explicit contract identifying a physical two-birth aggregate with the
conditioned common-sector law.  Neither projectivity nor sign transport proves
this contract in the current repository. -/
def RealizesCommonChiralityTransport
    (physicalRecord : ℝ → ℝ → Fin 2 → ℝ) : Prop :=
  ∀ y z chirality,
    physicalRecord y z chirality =
      commonChiralityRecordProbability y z chirality

/-- Under the common-sector contract, the first two linked chain births
amplify the selected `-i` record from probability `2/3` to `4/5`. -/
theorem firstTwoLinkedChainBirths_commonSector_exact :
    commonChiralityRecordProbability
        firstLinkedBirthSourceR chainThreeNewbornSourceR 0 = 1 / 5
      ∧ commonChiralityRecordProbability
        firstLinkedBirthSourceR chainThreeNewbornSourceR 1 = 4 / 5
      ∧ commonChiralityCompose
        firstLinkedBirthSourceR chainThreeNewbornSourceR = 3 / 10 := by
  rw [firstLinkedBirthSourceR_exact, chainThreeNewbornSourceR_exact]
  norm_num [commonChiralityRecordProbability,
    commonChiralityNormalizer, commonChiralityCompose]

theorem firstTwoLinkedChainBirths_physical_amplification
    (physicalRecord : ℝ → ℝ → Fin 2 → ℝ)
    (hTransport : RealizesCommonChiralityTransport physicalRecord) :
    physicalRecord firstLinkedBirthSourceR chainThreeNewbornSourceR 1 = 4 / 5 := by
  rw [hTransport]
  exact firstTwoLinkedChainBirths_commonSector_exact.2.1

theorem forkThree_commonSector_self_exact :
    commonChiralityRecordProbability
        forkThreeNewbornSourceR forkThreeNewbornSourceR 0 = 9 / 58
      ∧ commonChiralityRecordProbability
        forkThreeNewbornSourceR forkThreeNewbornSourceR 1 = 49 / 58
      ∧ commonChiralityCompose
        forkThreeNewbornSourceR forkThreeNewbornSourceR = 10 / 29 := by
  rw [forkThreeNewbornSourceR_exact]
  norm_num [commonChiralityRecordProbability,
    commonChiralityNormalizer, commonChiralityCompose]

/-! ## 5. Repeated common-sector evidence -/

/-- Selected-sector probability after `births` identical likelihood factors,
written in odds form.  This is the iteration of the common-sector evidence
model, not a projective-growth marginal. -/
def repeatedCommonSelectedProbability (births : ℕ) (y : ℝ) : ℝ :=
  1 / (1 + ((1 / 2 - y) / (1 / 2 + y)) ^ births)

theorem repeatedCommonSelectedProbability_one
    {y : ℝ} (hSelectedWeight : 1 / 2 + y ≠ 0) :
    repeatedCommonSelectedProbability 1 y = 1 / 2 + y := by
  unfold repeatedCommonSelectedProbability
  simp only [pow_one]
  have hDenominator :
      1 + (1 / 2 - y) / (1 / 2 + y) =
        1 / (1 / 2 + y) := by
    calc
      1 + (1 / 2 - y) / (1 / 2 + y) =
          (1 / 2 + y) / (1 / 2 + y) +
            (1 / 2 - y) / (1 / 2 + y) := by
              rw [div_self hSelectedWeight]
      _ = ((1 / 2 + y) + (1 / 2 - y)) / (1 / 2 + y) := by ring
      _ = 1 / (1 / 2 + y) := by ring
  rw [hDenominator]
  simp

theorem firstTwoLinkedChainBirths_repeated_common_exact :
    repeatedCommonSelectedProbability 1 firstLinkedBirthSourceR = 2 / 3
      ∧ repeatedCommonSelectedProbability 2 firstLinkedBirthSourceR = 4 / 5 := by
  rw [firstLinkedBirthSourceR_exact]
  norm_num [repeatedCommonSelectedProbability]

/-- Every finite number of identical positive interior records remains
strictly nondeterministic, despite the asymptotic certainty theorem below. -/
theorem repeatedCommonSelectedProbability_lt_one
    (births : ℕ) {y : ℝ} (hPositive : 0 < y) (hInterior : y < 1 / 2) :
    repeatedCommonSelectedProbability births y < 1 := by
  have hNumeratorPositive : 0 < (1 / 2 - y : ℝ) := by linarith
  have hDenominatorPositive : 0 < (1 / 2 + y : ℝ) := by linarith
  have hRatioPositive :
      0 < (1 / 2 - y) / (1 / 2 + y) :=
    div_pos hNumeratorPositive hDenominatorPositive
  have hPowerPositive :
      0 < ((1 / 2 - y) / (1 / 2 + y)) ^ births :=
    pow_pos hRatioPositive births
  unfold repeatedCommonSelectedProbability
  rw [div_lt_iff₀ (by positivity :
    0 < 1 + ((1 / 2 - y) / (1 / 2 + y)) ^ births)]
  linarith

/-- A fixed positive interior record bias converges to certainty under repeated
common-sector likelihood multiplication.  This does not cover a varying
source sequence; positivity alone supplies no uniform rate. -/
theorem repeatedCommonSelectedProbability_tendsto_one
    {y : ℝ} (hPositive : 0 < y) (hInterior : y < 1 / 2) :
    Filter.Tendsto
      (fun births : ℕ => repeatedCommonSelectedProbability births y)
      Filter.atTop (nhds 1) := by
  have hNumeratorNonneg : 0 ≤ (1 / 2 - y : ℝ) := by linarith
  have hDenominatorPositive : 0 < (1 / 2 + y : ℝ) := by linarith
  have hRatioNonneg :
      0 ≤ (1 / 2 - y) / (1 / 2 + y) :=
    div_nonneg hNumeratorNonneg (le_of_lt hDenominatorPositive)
  have hRatioLtOne :
      (1 / 2 - y) / (1 / 2 + y) < (1 : ℝ) := by
    rw [div_lt_one hDenominatorPositive]
    linarith
  have hRatioAbs :
      |(1 / 2 - y) / (1 / 2 + y)| < (1 : ℝ) := by
    rw [abs_of_nonneg hRatioNonneg]
    exact hRatioLtOne
  have hPower := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hRatioAbs
  have hDenominator : Filter.Tendsto
      (fun births : ℕ =>
        1 + ((1 / 2 - y) / (1 / 2 + y)) ^ births)
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hPower)
  have hInverse := hDenominator.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa [repeatedCommonSelectedProbability, one_div] using hInverse

/-! ## 6. Honest two-birth verdict -/

/-- The complete finite verdict.  Source magnitude is an exact record bias;
independent sequential records do not amplify it; common-sector conditioning
does amplify it, but only behind an explicit transport/factorization contract. -/
theorem chiralityRecordCompounding_firstVerdict :
    chiralityRecordBias chainThreeNewbornSourceR = 1 / 3
      ∧ chiralityRecordBias forkThreeNewbornSourceR = 2 / 5
      ∧ chiralityRecordBias (antichainTwoSourceBinParameter 1) = 1 / 4
      ∧ (∑ first, independentTwoBirthRecordProbability
          firstLinkedBirthSourceR chainThreeNewbornSourceR (first, 1)) = 2 / 3
      ∧ commonChiralityRecordProbability
          firstLinkedBirthSourceR chainThreeNewbornSourceR 1 = 4 / 5
      ∧ Filter.Tendsto
          (fun births : ℕ =>
            repeatedCommonSelectedProbability births (1 / 6))
          Filter.atTop (nhds 1) := by
  exact ⟨chainThree_chiralityRecord_exact.2.2,
    forkThree_chiralityRecord_exact.2.2,
    antichainSingleton_chiralityRecord_exact.2.2,
    firstTwoLinkedChainBirths_independent_exact.2.2.2.2,
    firstTwoLinkedChainBirths_commonSector_exact.2.1,
    repeatedCommonSelectedProbability_tendsto_one (by norm_num) (by norm_num)⟩

#print axioms chiralityRecordBias_exact
#print axioms deterministicSelector_statisticalRecord_separation
#print axioms chainThree_chiralityRecord_exact
#print axioms forkThree_chiralityRecord_exact
#print axioms antichainSingleton_chiralityRecord_exact
#print axioms independentTwoBirthRecordProbability_sum
#print axioms firstTwoLinkedChainBirths_independent_exact
#print axioms commonChiralityRecordProbability_exact
#print axioms commonChiralityCompose_bias_coordinates
#print axioms commonChiralityCompose_strictly_amplifies_left
#print axioms commonChiralityCompose_lt_half
#print axioms firstTwoLinkedChainBirths_commonSector_exact
#print axioms repeatedCommonSelectedProbability_lt_one
#print axioms repeatedCommonSelectedProbability_tendsto_one
#print axioms chiralityRecordCompounding_firstVerdict

end

end UnifiedTheory.Audit.KFCausalSetChiralityRecordCompounding
