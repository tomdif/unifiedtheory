/-
  Audit/KFCausalSetChiralityEvidenceSharpRate.lean

  SHARP FULL-CHAIN CHIRALITY-EVIDENCE EXPONENT

  The earlier harmonic sandwich proves only that full-chain record confidence
  sharpens polynomially.  Here the leading exponent is fixed exactly.

  Write `r_n = 2 y_n` for the signed record bias and
  `q_n = artanh r_n` for its half-log-odds charge.  The bias sum telescopes:

      sum_{n=1}^N r_n = 2 H_{N+1} + 4/(N+2) - 4.

  The nonlinear excess `q_n-r_n` is nonnegative and bounded by a summable
  cubic tail.  It therefore contributes only a finite constant.  Consequently

      E_N / log(N+1) -> 2,
      log odds_N / log(N+1) -> 4,
      log error_N / log(N+1) -> -4.

  Thus the conditional common-sector posterior error has sharp logarithmic
  power `N^-4` (up to a sub-power factor).  This is a theorem about the named
  full-chain evidence model.  It does not supply the still-missing decoherent
  charge partition or a probability measure on the infinite tail event.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.PSeries
import UnifiedTheory.Audit.KFCausalSetChiralityChargePartitionNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralityEvidenceSharpRate

noncomputable section

open scoped BigOperators
open Filter Set
open UnifiedTheory.Audit.KFCausalSetChiralityEvidenceAsymptotics

/-! ## 1. Cubic control of the nonlinear artanh excess -/

/-- On the interval needed below, the nonlinear artanh correction is at most
twice the cubic term. -/
theorem artanh_sub_self_le_two_mul_cube
    {r : ℝ} (hrNonneg : 0 ≤ r) (hrHalf : r ≤ 1 / 2) :
    Real.artanh r - r ≤ 2 * r ^ 3 := by
  have hrOne : r < 1 := lt_of_le_of_lt hrHalf (by norm_num)
  have hUpper := Real.log_div_le_sum_range_add hrNonneg hrOne 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, mul_zero, pow_one, mul_one, one_div] at hUpper
  rw [Real.artanh_eq_half_log (by constructor <;> linarith)]
  have hDenPos : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
  have hRemainder : r ^ 3 / (1 - r ^ 2) ≤ 2 * r ^ 3 := by
    rw [div_le_iff₀ hDenPos]
    have hCube : 0 ≤ r ^ 3 := pow_nonneg hrNonneg 3
    have hFactor : 0 ≤ 1 - 2 * r ^ 2 := by
      nlinarith [sq_nonneg r]
    nlinarith [mul_nonneg hCube hFactor]
  linarith

/-- Bias rather than half-log-odds charge at one full-chain birth. -/
def fullChainBirthBias (n : ℕ) : ℝ :=
  2 * fullChainBirthSource n

/-- Nonlinear evidence beyond the linear bias. -/
def fullChainBirthChargeExcess (n : ℕ) : ℝ :=
  chiralityEvidenceCharge (fullChainBirthSource n) - fullChainBirthBias n

theorem fullChainBirthChargeExcess_nonneg (n : ℕ) :
    0 ≤ fullChainBirthChargeExcess n := by
  unfold fullChainBirthChargeExcess fullChainBirthBias
  exact sub_nonneg.mpr (bias_le_chiralityEvidenceCharge
    (fullChainBirthSource_nonneg n) (fullChainBirthSource_lt_half n))

theorem fullChainBirthBias_le_two_harmonicTerm (n : ℕ) :
    fullChainBirthBias n ≤ 2 / ((n + 2 : ℕ) : ℝ) := by
  unfold fullChainBirthBias
  have h := fullChainBirthSource_le_harmonicTerm n
  calc
    2 * fullChainBirthSource n ≤
        2 * (1 / ((n + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2 / ((n + 2 : ℕ) : ℝ) := by ring

theorem fullChainBirthChargeExcess_le_cubicTail (n : ℕ) :
    fullChainBirthChargeExcess n ≤
      16 / (((n + 2 : ℕ) : ℝ) ^ 3) := by
  let r := fullChainBirthBias n
  have hrNonneg : 0 ≤ r := by
    exact mul_nonneg (by norm_num) (fullChainBirthSource_nonneg n)
  have hrHalf : r ≤ 1 / 2 := by
    dsimp [r, fullChainBirthBias]
    nlinarith [fullChainBirthSource_le_quarter n]
  have hArtanh := artanh_sub_self_le_two_mul_cube hrNonneg hrHalf
  have hrTerm := fullChainBirthBias_le_two_harmonicTerm n
  have hTermNonneg : 0 ≤ 2 / (((n + 2 : ℕ) : ℝ)) := by positivity
  have hCube := pow_le_pow_left₀ hrNonneg hrTerm 3
  unfold fullChainBirthChargeExcess chiralityEvidenceCharge
  change Real.artanh r - r ≤ _
  refine le_trans hArtanh ?_
  calc
    2 * r ^ 3 ≤ 2 * (2 / (((n + 2 : ℕ) : ℝ))) ^ 3 :=
      mul_le_mul_of_nonneg_left hCube (by norm_num)
    _ = 16 / (((n + 2 : ℕ) : ℝ) ^ 3) := by ring

theorem summable_fullChainBirthChargeExcess :
    Summable (fun k => fullChainBirthChargeExcess (k + 1)) := by
  have hPSeries : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow (p := 3)).2 (by norm_num)
  have hShift : Summable
      (fun k : ℕ => 16 / ((((k + 1) + 2 : ℕ) : ℝ) ^ 3)) := by
    have hShiftBase : Summable
        (fun k : ℕ => 1 / ((((k + 3 : ℕ) : ℝ) ^ 3))) := by
      simpa [Nat.add_assoc] using (summable_nat_add_iff 3).2 hPSeries
    convert hShiftBase.mul_left (16 : ℝ) using 1
    ext k
    push_cast
    ring
  exact Summable.of_nonneg_of_le
    (fun k => fullChainBirthChargeExcess_nonneg (k + 1))
    (fun k => fullChainBirthChargeExcess_le_cubicTail (k + 1))
    hShift

/-! ## 2. Exact telescoping bias sum -/

def accumulatedFullChainBias (depth : ℕ) : ℝ :=
  ∑ k ∈ Finset.range depth, fullChainBirthBias (k + 1)

theorem accumulatedFullChainBias_exact (depth : ℕ) :
    accumulatedFullChainBias depth =
      2 * (harmonic (depth + 1) : ℝ) +
        4 / ((depth + 2 : ℕ) : ℝ) - 4 := by
  induction depth with
  | zero => norm_num [accumulatedFullChainBias]
  | succ depth ih =>
      rw [accumulatedFullChainBias, Finset.sum_range_succ]
      change accumulatedFullChainBias depth +
        fullChainBirthBias (depth + 1) = _
      rw [ih]
      rw [show depth + 1 + 1 = (depth + 1) + 1 by omega,
        harmonic_succ (depth + 1)]
      unfold fullChainBirthBias fullChainBirthSource
      push_cast
      field_simp
      ring

/-- Accumulated nonlinear excess. -/
def accumulatedFullChainChargeExcess (depth : ℕ) : ℝ :=
  ∑ k ∈ Finset.range depth, fullChainBirthChargeExcess (k + 1)

theorem accumulatedFullChainEvidence_eq_bias_add_excess (depth : ℕ) :
    accumulatedFullChainEvidence depth =
      accumulatedFullChainBias depth + accumulatedFullChainChargeExcess depth := by
  unfold accumulatedFullChainEvidence accumulatedFullChainBias
    accumulatedFullChainChargeExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold fullChainBirthChargeExcess fullChainBirthBias
  ring

theorem accumulatedFullChainChargeExcess_tendsto :
    Tendsto accumulatedFullChainChargeExcess atTop
      (nhds (∑' k, fullChainBirthChargeExcess (k + 1))) := by
  exact summable_fullChainBirthChargeExcess.tendsto_sum_tsum_nat

/-! ## 3. Sharp evidence and odds exponents -/

theorem log_nat_succ_tendsto_atTop :
    Tendsto (fun depth : ℕ => Real.log (((depth + 1 : ℕ) : ℝ)))
      atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

theorem accumulatedFullChainEvidence_sub_two_log_tendsto :
    Tendsto
      (fun depth => accumulatedFullChainEvidence depth -
        2 * Real.log (((depth + 1 : ℕ) : ℝ)))
      atTop
      (nhds
        (2 * Real.eulerMascheroniConstant - 4 +
          ∑' k, fullChainBirthChargeExcess (k + 1))) := by
  have hHarmonic := Real.tendsto_harmonic_sub_log.comp
    (tendsto_add_atTop_nat 1)
  have hTail : Tendsto
      (fun depth : ℕ => 4 / (((depth + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    have hCast : Tendsto (fun depth : ℕ => (((depth + 2 : ℕ) : ℝ)))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    simpa using (tendsto_const_nhds.div_atTop hCast :
      Tendsto (fun depth : ℕ => 4 / (((depth + 2 : ℕ) : ℝ)))
        atTop (nhds 0))
  have hExcess := accumulatedFullChainChargeExcess_tendsto
  have hCombined := ((hHarmonic.const_mul (2 : ℝ)).add hTail).sub_const 4
  have hAll := hCombined.add hExcess
  have hEq :
      (fun depth =>
        2 * ((fun n => (harmonic n : ℝ) - Real.log (n : ℝ)) ∘
          fun a => a + 1) depth +
          4 / (((depth + 2 : ℕ) : ℝ)) - 4 +
          accumulatedFullChainChargeExcess depth) =ᶠ[atTop]
      (fun depth => accumulatedFullChainEvidence depth -
        2 * Real.log (((depth + 1 : ℕ) : ℝ))) := by
    filter_upwards [] with depth
    rw [accumulatedFullChainEvidence_eq_bias_add_excess,
      accumulatedFullChainBias_exact]
    simp only [Function.comp_apply]
    ring
  simpa only [add_zero] using hAll.congr' hEq

/-- **Sharp charge exponent.**  Full-chain half-log-odds grow as
`2 log N` to leading order. -/
theorem accumulatedFullChainEvidence_div_log_tendsto_two :
    Tendsto
      (fun depth => accumulatedFullChainEvidence depth /
        Real.log (((depth + 1 : ℕ) : ℝ)))
      atTop (nhds 2) := by
  have hCentered := accumulatedFullChainEvidence_sub_two_log_tendsto
  have hCenteredDiv := hCentered.div_atTop log_nat_succ_tendsto_atTop
  have hMain : Tendsto
      (fun depth => (2 : ℝ) +
        (accumulatedFullChainEvidence depth -
          2 * Real.log (((depth + 1 : ℕ) : ℝ))) /
            Real.log (((depth + 1 : ℕ) : ℝ)))
      atTop (nhds ((2 : ℝ) + 0)) :=
    tendsto_const_nhds.add hCenteredDiv
  have hEq :
      (fun depth => (2 : ℝ) +
        (accumulatedFullChainEvidence depth -
          2 * Real.log (((depth + 1 : ℕ) : ℝ))) /
            Real.log (((depth + 1 : ℕ) : ℝ))) =ᶠ[atTop]
      (fun depth => accumulatedFullChainEvidence depth /
        Real.log (((depth + 1 : ℕ) : ℝ))) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun depth hdepth => hdepth⟩] with depth hdepth
    have hLogPos : 0 < Real.log (((depth + 1 : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < depth + 1 by omega)
    field_simp [hLogPos.ne']
    ring
  simpa using hMain.congr' hEq

/-- Log odds of the full-chain common-sector record. -/
def fullChainLogOdds (depth : ℕ) : ℝ :=
  Real.log (accumulatedChiralityOdds
    (fun k => fullChainBirthSource (k + 1)) depth)

theorem fullChainLogOdds_eq (depth : ℕ) :
    fullChainLogOdds depth = 2 * accumulatedFullChainEvidence depth := by
  unfold fullChainLogOdds accumulatedChiralityOdds
  rw [Real.log_exp]
  rfl

/-- **Sharp odds exponent.**  Total record odds grow with logarithmic power
four. -/
theorem fullChainLogOdds_div_log_tendsto_four :
    Tendsto
      (fun depth => fullChainLogOdds depth /
        Real.log (((depth + 1 : ℕ) : ℝ)))
      atTop (nhds 4) := by
  have h : Tendsto
      (fun depth => (2 : ℝ) *
        (accumulatedFullChainEvidence depth /
          Real.log (((depth + 1 : ℕ) : ℝ))))
      atTop (nhds ((2 : ℝ) * 2)) :=
    accumulatedFullChainEvidence_div_log_tendsto_two.const_mul (2 : ℝ)
  have hEq :
      (fun depth => (2 : ℝ) *
        (accumulatedFullChainEvidence depth /
          Real.log (((depth + 1 : ℕ) : ℝ)))) =ᶠ[atTop]
      (fun depth => fullChainLogOdds depth /
        Real.log (((depth + 1 : ℕ) : ℝ))) := by
    filter_upwards [] with depth
    rw [fullChainLogOdds_eq]
    ring
  norm_num at h
  have h' : Tendsto
      (fun depth => (2 : ℝ) *
        (accumulatedFullChainEvidence depth /
          Real.log (((depth + 1 : ℕ) : ℝ))))
      atTop (nhds 4) := by
    simpa only [Nat.cast_add, Nat.cast_one] using h
  exact h'.congr' hEq

/-! ## 4. Sharp posterior-error exponent -/

def fullChainPosteriorError (depth : ℕ) : ℝ :=
  1 - accumulatedChiralityProbability
    (fun k => fullChainBirthSource (k + 1)) depth

theorem fullChainPosteriorError_eq (depth : ℕ) :
    fullChainPosteriorError depth =
      Real.exp (-2 * accumulatedFullChainEvidence depth) /
        (1 + Real.exp (-2 * accumulatedFullChainEvidence depth)) := by
  unfold fullChainPosteriorError accumulatedChiralityProbability
    accumulatedChiralityOdds
  have hExpPos : 0 < Real.exp (2 * accumulatedFullChainEvidence depth) :=
    Real.exp_pos _
  have hExpNegPos : 0 < Real.exp (-2 * accumulatedFullChainEvidence depth) :=
    Real.exp_pos _
  change
    1 - Real.exp (2 * accumulatedFullChainEvidence depth) /
        (1 + Real.exp (2 * accumulatedFullChainEvidence depth)) =
      Real.exp (-2 * accumulatedFullChainEvidence depth) /
        (1 + Real.exp (-2 * accumulatedFullChainEvidence depth))
  rw [show -2 * accumulatedFullChainEvidence depth =
      -(2 * accumulatedFullChainEvidence depth) by ring,
    Real.exp_neg]
  field_simp [hExpPos.ne', hExpNegPos.ne']
  ring

theorem fullChainLogPosteriorError_eq (depth : ℕ) :
    Real.log (fullChainPosteriorError depth) =
      -2 * accumulatedFullChainEvidence depth -
        Real.log (1 + Real.exp
          (-2 * accumulatedFullChainEvidence depth)) := by
  rw [fullChainPosteriorError_eq,
    Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp]

theorem fullChainLogCorrection_tendsto_zero :
    Tendsto
      (fun depth => Real.log
        (1 + Real.exp (-2 * accumulatedFullChainEvidence depth)))
      atTop (nhds 0) := by
  have hNegEvidence : Tendsto
      (fun depth => -2 * accumulatedFullChainEvidence depth)
      atTop atBot :=
    accumulatedFullChainEvidence_tendsto_atTop.const_mul_atTop_of_neg
      (by norm_num)
  have hExp : Tendsto
      (fun depth => Real.exp
        (-2 * accumulatedFullChainEvidence depth))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hNegEvidence
  have hOnePlus : Tendsto
      (fun depth => 1 + Real.exp
        (-2 * accumulatedFullChainEvidence depth))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hExp : Tendsto
      (fun depth => (1 : ℝ) + Real.exp
        (-2 * accumulatedFullChainEvidence depth))
      atTop (nhds ((1 : ℝ) + 0)))
  simpa using (Real.continuousAt_log one_ne_zero).tendsto.comp hOnePlus

/-- **Sharp posterior-error law.**  The conditional common-sector record error
has logarithmic power `-4`; equivalently it is `N^{-4+o(1)}`. -/
theorem fullChainPosteriorError_logExponent_neg_four :
    Tendsto
      (fun depth => Real.log (fullChainPosteriorError depth) /
        Real.log (((depth + 1 : ℕ) : ℝ)))
      atTop (nhds (-4)) := by
  have hEvidence : Tendsto
      (fun depth => (-2 : ℝ) *
        (accumulatedFullChainEvidence depth /
          Real.log (((depth + 1 : ℕ) : ℝ))))
      atTop (nhds ((-2 : ℝ) * 2)) :=
    accumulatedFullChainEvidence_div_log_tendsto_two.const_mul (-2 : ℝ)
  have hCorrection :=
    fullChainLogCorrection_tendsto_zero.div_atTop log_nat_succ_tendsto_atTop
  have hCombined := hEvidence.sub hCorrection
  have hEq :
      (fun depth =>
        (-2 : ℝ) * (accumulatedFullChainEvidence depth /
          Real.log (((depth + 1 : ℕ) : ℝ))) -
        Real.log (1 + Real.exp (-2 * accumulatedFullChainEvidence depth)) /
          Real.log (((depth + 1 : ℕ) : ℝ))) =ᶠ[atTop]
      (fun depth => Real.log (fullChainPosteriorError depth) /
        Real.log (((depth + 1 : ℕ) : ℝ))) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun depth hdepth => hdepth⟩] with depth hdepth
    have hLogNe : Real.log (((depth + 1 : ℕ) : ℝ)) ≠ 0 := by
      have hLogPos : 0 < Real.log (((depth + 1 : ℕ) : ℝ)) := by
        apply Real.log_pos
        exact_mod_cast (show 1 < depth + 1 by omega)
      exact hLogPos.ne'
    rw [fullChainLogPosteriorError_eq]
    field_simp [hLogNe]
  norm_num at hCombined
  have hCombined' : Tendsto
      (fun depth =>
        (-2 : ℝ) * (accumulatedFullChainEvidence depth /
          Real.log (((depth + 1 : ℕ) : ℝ))) -
        Real.log (1 + Real.exp (-2 * accumulatedFullChainEvidence depth)) /
          Real.log (((depth + 1 : ℕ) : ℝ)))
      atTop (nhds (-4)) := by
    simpa only [Nat.cast_add, Nat.cast_one, neg_mul] using hCombined
  exact hCombined'.congr' hEq

theorem fullChainEvidenceSharpRate_capstone :
    Tendsto
        (fun depth => accumulatedFullChainEvidence depth /
          Real.log (((depth + 1 : ℕ) : ℝ)))
        atTop (nhds 2)
      ∧ Tendsto
        (fun depth => fullChainLogOdds depth /
          Real.log (((depth + 1 : ℕ) : ℝ)))
        atTop (nhds 4)
      ∧ Tendsto
        (fun depth => Real.log (fullChainPosteriorError depth) /
          Real.log (((depth + 1 : ℕ) : ℝ)))
        atTop (nhds (-4)) := by
  exact ⟨accumulatedFullChainEvidence_div_log_tendsto_two,
    fullChainLogOdds_div_log_tendsto_four,
    fullChainPosteriorError_logExponent_neg_four⟩

#print axioms summable_fullChainBirthChargeExcess
#print axioms accumulatedFullChainBias_exact
#print axioms accumulatedFullChainEvidence_sub_two_log_tendsto
#print axioms accumulatedFullChainEvidence_div_log_tendsto_two
#print axioms fullChainLogOdds_div_log_tendsto_four
#print axioms fullChainPosteriorError_logExponent_neg_four
#print axioms fullChainEvidenceSharpRate_capstone

end

end UnifiedTheory.Audit.KFCausalSetChiralityEvidenceSharpRate
