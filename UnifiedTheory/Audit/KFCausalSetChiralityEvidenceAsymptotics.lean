/-
  Audit/KFCausalSetChiralityEvidenceAsymptotics.lean

  LOG-ODDS CHARGE AND THE ASYMPTOTIC CHIRALITY-RECORD CRITERION

  The common-sector record law is exactly Bayesian binary-evidence
  accumulation.  For record bias `r = 2y`, define the evidence charge

      q(y) = artanh(2y)
           = 1/2 log ((1/2+y)/(1/2-y)).

  The conditioned composition law becomes additive in this coordinate.  For a
  sequence of records, total odds are `exp (2 * sum q_n)`.  Hence the exact
  decisiveness criterion is divergence of the partial charge sums.

  The criterion is then tested on actual causal-set geometry.  Along the
  future-maximal full-chain growth path,

      y_n = n / ((n+1)(n+2)),

  and each charge is bounded below by `1/(n+2)`.  The accumulated evidence
  therefore dominates a shifted harmonic number and diverges.  The associated
  common-sector posterior converges to one, though it remains below one at
  every finite depth.

  Positivity alone is not enough: an explicit positive geometric-decay
  sequence has summable artanh charge.  Thus the chain theorem does not prove a
  typical-history statement for quantum growth.  The unresolved dynamical
  question is whether the source sequence selected by the growth law almost
  surely/quantum-measure-generically satisfies the charge-divergence criterion.

  The resemblance to rapidity addition is recorded only as an algebraic
  isomorphism.  No Lorentz kinematics is derived from generic binary Bayes
  arithmetic.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import UnifiedTheory.Audit.KFCausalSetChiralityRecordCompounding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralityEvidenceAsymptotics

noncomputable section

open scoped BigOperators
open Filter Set
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
open UnifiedTheory.Audit.KFCausalSetChiralityRecordCompounding

/-! ## 1. The additive log-odds coordinate -/

/-- Half log-likelihood ratio carried by one chirality record. -/
def chiralityEvidenceCharge (y : ℝ) : ℝ :=
  Real.artanh (2 * y)

/-- On the physical open interval, the artanh coordinate is exactly half the
log-odds of the eigenbasis record. -/
theorem chiralityEvidenceCharge_eq_half_logOdds
    {y : ℝ} (hy : |y| < 1 / 2) :
    chiralityEvidenceCharge y =
      1 / 2 * Real.log ((1 / 2 + y) / (1 / 2 - y)) := by
  have hTwoY : 2 * y ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := abs_lt.mp hy
    constructor <;> linarith
  rw [chiralityEvidenceCharge, Real.artanh_eq_half_log hTwoY]
  congr 2
  have hDenominator : (1 - 2 * y : ℝ) ≠ 0 := by
    have h := abs_lt.mp hy
    linarith
  field_simp [hDenominator]

/-- The charge is at least the signed bias for a nonnegative interior source.
This one-term Taylor lower bound is the bridge to harmonic comparison. -/
theorem bias_le_chiralityEvidenceCharge
    {y : ℝ} (hyNonneg : 0 ≤ y) (hyInterior : y < 1 / 2) :
    2 * y ≤ chiralityEvidenceCharge y := by
  have hSeries := Real.sum_range_le_log_div
    (x := 2 * y) (by linarith) (by linarith) 1
  have hTwoY : 2 * y ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  rw [chiralityEvidenceCharge, Real.artanh_eq_half_log hTwoY]
  simpa using hSeries

/-- The common-sector Bayesian composition is additive in evidence charge.
This is binary log-odds arithmetic, not a derivation of Lorentz kinematics. -/
theorem chiralityEvidenceCharge_commonCompose_add
    {y z : ℝ} (hyNonneg : 0 ≤ y) (hzNonneg : 0 ≤ z)
    (hyInterior : y < 1 / 2) (hzInterior : z < 1 / 2) :
    chiralityEvidenceCharge (commonChiralityCompose y z) =
      chiralityEvidenceCharge y + chiralityEvidenceCharge z := by
  have hComposeNonneg : 0 ≤ commonChiralityCompose y z := by
    unfold commonChiralityCompose
    positivity
  have hComposeInterior := commonChiralityCompose_lt_half
    hyNonneg hzNonneg hyInterior hzInterior
  have hyAbs : |y| < 1 / 2 := by
    rw [abs_of_nonneg hyNonneg]
    exact hyInterior
  have hzAbs : |z| < 1 / 2 := by
    rw [abs_of_nonneg hzNonneg]
    exact hzInterior
  have hComposeAbs : |commonChiralityCompose y z| < 1 / 2 := by
    rw [abs_of_nonneg hComposeNonneg]
    exact hComposeInterior
  rw [chiralityEvidenceCharge_eq_half_logOdds hComposeAbs,
    chiralityEvidenceCharge_eq_half_logOdds hyAbs,
    chiralityEvidenceCharge_eq_half_logOdds hzAbs]
  have hOddsYPos : 0 < (1 / 2 + y) / (1 / 2 - y) :=
    div_pos (by linarith) (by linarith)
  have hOddsZPos : 0 < (1 / 2 + z) / (1 / 2 - z) :=
    div_pos (by linarith) (by linarith)
  have hOdds :
      (1 / 2 + commonChiralityCompose y z) /
          (1 / 2 - commonChiralityCompose y z) =
        ((1 / 2 + y) / (1 / 2 - y)) *
          ((1 / 2 + z) / (1 / 2 - z)) := by
    unfold commonChiralityCompose
    have hDxy : 1 + 4 * y * z ≠ 0 := by positivity
    have hDy : 1 / 2 - y ≠ 0 := by linarith
    have hDz : 1 / 2 - z ≠ 0 := by linarith
    field_simp [hDxy, hDy, hDz]
    ring
  rw [hOdds, Real.log_mul hOddsYPos.ne' hOddsZPos.ne']
  ring

/-! ## 2. Exact finite-sequence decisiveness criterion -/

/-- Accumulated half-log-odds through the first `depth` records. -/
def accumulatedChiralityEvidence
    (source : ℕ → ℝ) (depth : ℕ) : ℝ :=
  ∑ n ∈ Finset.range depth, chiralityEvidenceCharge (source n)

/-- Odds for the selected common sector. -/
def accumulatedChiralityOdds
    (source : ℕ → ℝ) (depth : ℕ) : ℝ :=
  Real.exp (2 * accumulatedChiralityEvidence source depth)

/-- Bayesian selected-sector probability reconstructed from the odds. -/
def accumulatedChiralityProbability
    (source : ℕ → ℝ) (depth : ℕ) : ℝ :=
  accumulatedChiralityOdds source depth /
    (1 + accumulatedChiralityOdds source depth)

/-- **Exact criterion.**  The odds become decisive exactly when the partial
sum of artanh charges diverges. -/
theorem accumulatedChiralityOdds_tendsto_atTop_iff
    (source : ℕ → ℝ) :
    Tendsto (accumulatedChiralityOdds source) atTop atTop ↔
      Tendsto (accumulatedChiralityEvidence source) atTop atTop := by
  change Tendsto
      (fun depth => Real.exp
        (2 * accumulatedChiralityEvidence source depth)) atTop atTop ↔ _
  rw [Real.tendsto_exp_comp_atTop]
  exact tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)

/-- Divergent evidence makes the common-sector record probability tend to
one. -/
theorem accumulatedChiralityProbability_tendsto_one
    {source : ℕ → ℝ}
    (hEvidence : Tendsto
      (accumulatedChiralityEvidence source) atTop atTop) :
    Tendsto (accumulatedChiralityProbability source) atTop (nhds 1) := by
  have hOdds : Tendsto (accumulatedChiralityOdds source) atTop atTop :=
    (accumulatedChiralityOdds_tendsto_atTop_iff source).2 hEvidence
  have hDenominator' : Tendsto
      (fun depth => accumulatedChiralityOdds source depth + 1)
      atTop atTop := hOdds.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hDenominator : Tendsto
      (fun depth => 1 + accumulatedChiralityOdds source depth)
      atTop atTop := by
    apply hDenominator'.congr'
    filter_upwards [] with depth
    ring
  have hInv := hDenominator.inv_tendsto_atTop
  have hProbabilityIdentity :
      accumulatedChiralityProbability source =
        fun depth => 1 -
          (1 + accumulatedChiralityOdds source depth)⁻¹ := by
    funext depth
    unfold accumulatedChiralityProbability
    have hPositive : 0 < accumulatedChiralityOdds source depth := by
      exact Real.exp_pos _
    have hDenominatorPositive :
        0 < 1 + accumulatedChiralityOdds source depth := by linarith
    field_simp [hDenominatorPositive.ne']
    ring
  rw [hProbabilityIdentity]
  simpa using (tendsto_const_nhds.sub hInv)

/-! ## 3. Actual full-chain growth is harmonically decisive -/

/-- Geometric source of the future-maximal event in the `(n+1)`-chain. -/
def fullChainBirthSource (n : ℕ) : ℝ :=
  (n : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))

theorem fullChainBirthSource_eq_geometric (n : ℕ) :
    fullChainBirthSource n =
      ((causalOrientationDensityQ
        (cardinalCausalChain (n + 1)) (Fin.last n) : ℚ) : ℝ) := by
  rw [causalOrientationDensityQ_chain_last]
  push_cast
  unfold fullChainBirthSource
  push_cast
  ring_nf

theorem fullChainBirthSource_nonneg (n : ℕ) :
    0 ≤ fullChainBirthSource n := by
  unfold fullChainBirthSource
  positivity

theorem fullChainBirthSource_lt_half (n : ℕ) :
    fullChainBirthSource n < 1 / 2 := by
  unfold fullChainBirthSource
  have hDen :
      0 < ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) := by
    positivity
  rw [div_lt_iff₀ hDen]
  push_cast
  nlinarith [sq_nonneg (n : ℝ)]

/-- Every linked full-chain birth charge dominates a shifted harmonic term. -/
theorem fullChainBirth_charge_ge_harmonicTerm
    (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n + 2 : ℕ) : ℝ) ≤
      chiralityEvidenceCharge (fullChainBirthSource n) := by
  have hBias := bias_le_chiralityEvidenceCharge
    (fullChainBirthSource_nonneg n) (fullChainBirthSource_lt_half n)
  refine le_trans ?_ hBias
  unfold fullChainBirthSource
  have hNTwo : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hNOne : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hNTwo]
  field_simp [hNOne.ne']
  exact_mod_cast (show n + 1 ≤ 2 * n by omega)

/-- Evidence accumulated over the first `depth` linked full-chain births,
starting at `n=1`. -/
def accumulatedFullChainEvidence (depth : ℕ) : ℝ :=
  ∑ k ∈ Finset.range depth,
    chiralityEvidenceCharge (fullChainBirthSource (k + 1))

theorem shifted_harmonic_tail_sum (depth : ℕ) :
    (∑ k ∈ Finset.range depth, 1 / (((k + 3 : ℕ) : ℝ))) =
      (harmonic (depth + 2) : ℝ) - (harmonic 2 : ℝ) := by
  induction depth with
  | zero => norm_num
  | succ depth ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show depth + 1 + 2 = (depth + 2) + 1 by omega,
        harmonic_succ (depth + 2)]
      push_cast
      ring

theorem accumulatedFullChainEvidence_ge_harmonicTail (depth : ℕ) :
    (harmonic (depth + 2) : ℝ) - (harmonic 2 : ℝ) ≤
      accumulatedFullChainEvidence depth := by
  rw [← shifted_harmonic_tail_sum]
  unfold accumulatedFullChainEvidence
  apply Finset.sum_le_sum
  intro k hk
  exact fullChainBirth_charge_ge_harmonicTerm (k + 1) (by omega)

theorem harmonic_cast_tendsto_atTop :
    Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  have hLog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hAnomaly := Real.tendsto_harmonic_sub_log
  have hSum := hLog.atTop_add hAnomaly
  apply hSum.congr'
  filter_upwards [] with n
  ring

theorem shifted_harmonic_tail_tendsto_atTop :
    Tendsto
      (fun depth : ℕ =>
        (harmonic (depth + 2) : ℝ) - (harmonic 2 : ℝ))
      atTop atTop := by
  have hShift : Tendsto (fun depth : ℕ => depth + 2) atTop atTop :=
    tendsto_add_atTop_nat 2
  have hHarmonic := harmonic_cast_tendsto_atTop.comp hShift
  have hTail := hHarmonic.atTop_add
    (tendsto_const_nhds (x := -(harmonic 2 : ℝ)))
  simpa [Function.comp_def, sub_eq_add_neg, add_comm] using hTail

/-- **Actual-path theorem.**  Full-chain sequential births accumulate infinite
chirality evidence. -/
theorem accumulatedFullChainEvidence_tendsto_atTop :
    Tendsto accumulatedFullChainEvidence atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall accumulatedFullChainEvidence_ge_harmonicTail)
    shifted_harmonic_tail_tendsto_atTop

theorem fullChainCommonSectorProbability_tendsto_one :
    Tendsto
      (accumulatedChiralityProbability
        (fun k => fullChainBirthSource (k + 1)))
      atTop (nhds 1) := by
  apply accumulatedChiralityProbability_tendsto_one
  simpa [accumulatedChiralityEvidence,
    accumulatedFullChainEvidence]
    using accumulatedFullChainEvidence_tendsto_atTop

/-! ## 4. Positivity alone does not imply decisiveness -/

/-- Abstract positive interior source with geometrically decaying bias. -/
def summableEvidenceSource (n : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ (n + 1)) / 2

theorem summableEvidenceSource_pos (n : ℕ) :
    0 < summableEvidenceSource n := by
  unfold summableEvidenceSource
  positivity

theorem summableEvidenceSource_lt_half (n : ℕ) :
    summableEvidenceSource n < 1 / 2 := by
  unfold summableEvidenceSource
  have hPow : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  have hPowLt : (1 / 2 : ℝ) ^ (n + 1) < 1 := by
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  nlinarith

/-- On `0 ≤ r ≤ 1/2`, artanh is bounded above by `2r`. -/
theorem chiralityEvidenceCharge_le_twice_bias
    {r : ℝ} (hrNonneg : 0 ≤ r) (hrHalf : r ≤ 1 / 2) :
    Real.artanh r ≤ 2 * r := by
  have hrOne : r < 1 := lt_of_le_of_lt hrHalf (by norm_num)
  have hUpper := Real.log_div_le_sum_range_add hrNonneg hrOne 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add] at hUpper
  have hUpper' :
      1 / 2 * Real.log ((1 + r) / (1 - r)) ≤
        r / (1 - r ^ 2) := by
    norm_num at hUpper ⊢
    exact hUpper
  rw [Real.artanh_eq_half_log (by constructor <;> linarith)]
  refine le_trans hUpper' ?_
  have hDenPos : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
  rw [div_le_iff₀ hDenPos]
  have hFactor : 0 ≤ 1 - 2 * r ^ 2 := by nlinarith [sq_nonneg r]
  nlinarith [mul_nonneg hrNonneg hFactor]

/-- Explicit counterregime: all sources are positive, but their evidence charge
is summable.  Positivity/sign transport alone therefore cannot prove record
decisiveness. -/
theorem summable_chiralityEvidenceCharge_example :
    Summable (fun n => chiralityEvidenceCharge (summableEvidenceSource n)) := by
  have hGeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => (1 / 2 : ℝ) ^ n) ?_ ?_ hGeom
  · intro n
    apply Real.artanh_nonneg
    exact mul_nonneg (by norm_num) (le_of_lt (summableEvidenceSource_pos n))
  · intro n
    unfold chiralityEvidenceCharge summableEvidenceSource
    have hPowNonneg : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
    have hPowHalf : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
      calc
        (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n * (1 / 2) := by
          rw [pow_succ]
        _ ≤ 1 * (1 / 2) := mul_le_mul_of_nonneg_right
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
          (by norm_num)
        _ = 1 / 2 := by ring
    have hUpper := chiralityEvidenceCharge_le_twice_bias
      hPowNonneg hPowHalf
    rw [show 2 * ((1 / 2 : ℝ) ^ (n + 1) / 2) =
      (1 / 2 : ℝ) ^ (n + 1) by ring]
    calc
      Real.artanh ((1 / 2 : ℝ) ^ (n + 1))
          ≤ 2 * ((1 / 2 : ℝ) ^ (n + 1)) := hUpper
      _ = (1 / 2 : ℝ) ^ n := by rw [pow_succ]; ring

/-! ## 5. Verdict -/

theorem chiralityEvidenceAsymptotics_firstVerdict :
    Tendsto accumulatedFullChainEvidence atTop atTop
      ∧ Tendsto
        (accumulatedChiralityProbability
          (fun k => fullChainBirthSource (k + 1)))
        atTop (nhds 1)
      ∧ Summable
        (fun n => chiralityEvidenceCharge (summableEvidenceSource n)) := by
  exact ⟨accumulatedFullChainEvidence_tendsto_atTop,
    fullChainCommonSectorProbability_tendsto_one,
    summable_chiralityEvidenceCharge_example⟩

#print axioms chiralityEvidenceCharge_eq_half_logOdds
#print axioms bias_le_chiralityEvidenceCharge
#print axioms chiralityEvidenceCharge_commonCompose_add
#print axioms accumulatedChiralityOdds_tendsto_atTop_iff
#print axioms accumulatedChiralityProbability_tendsto_one
#print axioms fullChainBirth_charge_ge_harmonicTerm
#print axioms accumulatedFullChainEvidence_tendsto_atTop
#print axioms fullChainCommonSectorProbability_tendsto_one
#print axioms summable_chiralityEvidenceCharge_example
#print axioms chiralityEvidenceAsymptotics_firstVerdict

end

end UnifiedTheory.Audit.KFCausalSetChiralityEvidenceAsymptotics
