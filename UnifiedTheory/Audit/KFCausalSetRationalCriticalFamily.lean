/-
  Audit/KFCausalSetRationalCriticalFamily.lean

  THE POSITIVE-RATIONAL CRITICAL FAMILY

  The elementary schedule lambda_n = (n+2)/(n+1) fixes the infrared scaling
  coefficient kappa=2 only because it chooses the simplest positive rational
  displacement.  Nothing in the zero-free theorem selects that value.

  For positive natural numbers a,b, define

      lambda_n(a,b) = 1 + (a/b)/(n+1)
                    = (b(n+1)+a)/(b(n+1)),
      g_n(a,b)      = lambda_n(a,b)^2.

  These schedules cover every positive rational displacement c=a/b.  They are
  all-parent zero-free, converge to the critical surface, and satisfy

      (n+1)(g_n(a,b)-1) -> 2a/b.

  Denominator clearing remains effective:

      ||Z_C(lambda_n(a,b))|| >= (b(n+1))^(-n(n-1)),

  with the corresponding condition-number bound

      condition(C,lambda_n(a,b))
        <= 2^n (b(n+1)+a)^(n(n-1)).

  Thus kappa is a positive-rational modulus of the kinematic construction.
  Choosing it is a genuinely additional microscopic problem.
-/

import UnifiedTheory.Audit.KFCausalSetRationalCriticalRunning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetRationalCriticalFamily

noncomputable section

open scoped BigOperators ComplexConjugate
open Filter Polynomial Topology
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralDynamics
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetCriticalRunning
open UnifiedTheory.Audit.KFCausalSetRationalCriticalRunning

/-! ## 1. Positive-rational critical schedules -/

def rationalCriticalFamilyPairCouplingQ (a b n : ℕ) : ℚ :=
  ((b * (n + 1) + a : ℕ) : ℚ) / ((b * (n + 1) : ℕ) : ℚ)

def rationalCriticalFamilyPairCoupling (a b n : ℕ) : ℝ :=
  ((b * (n + 1) + a : ℕ) : ℝ) / ((b * (n + 1) : ℕ) : ℝ)

def rationalCriticalFamilyEffectiveCoupling (a b n : ℕ) : ℝ :=
  effectivePairCoupling (rationalCriticalFamilyPairCoupling a b n)

theorem rationalCriticalFamilyPairCoupling_cast (a b n : ℕ) :
    ((rationalCriticalFamilyPairCouplingQ a b n : ℚ) : ℝ) =
      rationalCriticalFamilyPairCoupling a b n := by
  norm_num [rationalCriticalFamilyPairCouplingQ,
    rationalCriticalFamilyPairCoupling]

theorem rationalCriticalFamilyPairCoupling_eq_one_add
    (a b n : ℕ) (hb : 0 < b) :
    rationalCriticalFamilyPairCoupling a b n =
      1 + ((a : ℝ) / (b : ℝ)) / ((n : ℝ) + 1) := by
  unfold rationalCriticalFamilyPairCoupling
  have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hnReal : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

theorem rationalCriticalFamilyPairCouplingQ_gt_one
    (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    1 < rationalCriticalFamilyPairCouplingQ a b n := by
  unfold rationalCriticalFamilyPairCouplingQ
  rw [one_lt_div]
  · norm_num
    omega
  · positivity

theorem rationalCriticalFamilyPairCoupling_gt_one
    (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    1 < rationalCriticalFamilyPairCoupling a b n := by
  rw [← rationalCriticalFamilyPairCoupling_cast]
  exact_mod_cast rationalCriticalFamilyPairCouplingQ_gt_one a b n ha hb

theorem rationalCriticalFamilyPairCoupling_tendsto_one
    (a b : ℕ) (hb : 0 < b) :
    Tendsto (rationalCriticalFamilyPairCoupling a b) atTop (nhds 1) := by
  have hTail := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hScaled :
      Tendsto
        (fun n : ℕ => ((a : ℝ) / (b : ℝ)) *
          (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hTail)
  have hLimit := (tendsto_const_nhds (x := (1 : ℝ))).add hScaled
  have hLimit' :
      Tendsto
        (fun n : ℕ => 1 + ((a : ℝ) / (b : ℝ)) *
          (1 / ((n : ℝ) + 1))) atTop (nhds 1) := by
    simpa using hLimit
  apply hLimit'.congr'
  filter_upwards [] with n
  rw [rationalCriticalFamilyPairCoupling_eq_one_add a b n hb]
  ring

theorem rationalCriticalFamilyEffectiveCoupling_tendsto_one
    (a b : ℕ) (hb : 0 < b) :
    Tendsto (rationalCriticalFamilyEffectiveCoupling a b)
      atTop (nhds 1) := by
  change Tendsto
    (fun n : ℕ => rationalCriticalFamilyPairCoupling a b n ^ 2)
      atTop (nhds 1)
  have hPair := rationalCriticalFamilyPairCoupling_tendsto_one a b hb
  simpa [pow_two] using hPair.mul hPair

theorem rationalCriticalFamilyEffectiveCoupling_scaled_displacement
    (a b n : ℕ) (hb : 0 < b) :
    ((n : ℝ) + 1) *
        (rationalCriticalFamilyEffectiveCoupling a b n - 1) =
      2 * ((a : ℝ) / (b : ℝ)) +
        ((a : ℝ) / (b : ℝ)) ^ 2 / ((n : ℝ) + 1) := by
  unfold rationalCriticalFamilyEffectiveCoupling effectivePairCoupling
  rw [rationalCriticalFamilyPairCoupling_eq_one_add a b n hb]
  have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hnReal : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem rationalCriticalFamilyEffectiveCoupling_scaled_tendsto
    (a b : ℕ) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ => ((n : ℝ) + 1) *
        (rationalCriticalFamilyEffectiveCoupling a b n - 1))
      atTop (nhds (2 * ((a : ℝ) / (b : ℝ)))) := by
  have hTail := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hQuadraticTail :
      Tendsto
        (fun n : ℕ => ((a : ℝ) / (b : ℝ)) ^ 2 *
          (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hTail)
  have hLimit :=
    (tendsto_const_nhds (x := 2 * ((a : ℝ) / (b : ℝ)))).add
      hQuadraticTail
  have hLimit' :
      Tendsto
        (fun n : ℕ => 2 * ((a : ℝ) / (b : ℝ)) +
          ((a : ℝ) / (b : ℝ)) ^ 2 * (1 / ((n : ℝ) + 1)))
        atTop (nhds (2 * ((a : ℝ) / (b : ℝ)))) := by
    simpa using hLimit
  apply hLimit'.congr'
  filter_upwards [] with n
  rw [rationalCriticalFamilyEffectiveCoupling_scaled_displacement a b n hb]
  ring

/-! ## 2. Uniform zero-freeness and effective arithmetic bounds -/

theorem rationalCriticalFamily_parentPolynomial_eval_ne_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (interactingChiralRealPartitionPolynomial parent).eval₂
      (Int.castRingHom ℝ)
        (rationalCriticalFamilyPairCoupling a b n) ≠ 0 := by
  simpa [rationalCriticalFamilyPairCoupling_cast] using
    (rational_parentPolynomial_eval_ne_zero_of_one_lt
      (rationalCriticalFamilyPairCouplingQ_gt_one a b n ha hb) parent)

theorem rationalCriticalFamily_parentPolynomial_denominator_bound
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (1 : ℝ) ≤
      ((b : ℝ) * ((n : ℝ) + 1)) ^
          (interactingChiralRealPartitionPolynomial parent).natDegree *
        |(interactingChiralRealPartitionPolynomial parent).eval₂
          (Int.castRingHom ℝ)
            (rationalCriticalFamilyPairCoupling a b n)| := by
  let p := interactingChiralRealPartitionPolynomial parent
  let numerator : ℤ := (b * (n + 1) + a : ℕ)
  let denominator : ℤ := (b * (n + 1) : ℕ)
  have hDenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hEval :
      Polynomial.eval
          ((numerator : ℝ) / (denominator : ℝ))
          (p.map (algebraMap ℤ ℝ)) ≠ 0 := by
    simpa [p, numerator, denominator, Polynomial.eval₂_eq_eval_map,
      rationalCriticalFamilyPairCoupling] using
      rationalCriticalFamily_parentPolynomial_eval_ne_zero
        a b ha hb parent
  have hBound := one_le_pow_mul_abs_eval_div
    (K := ℝ) (f := p) (a := numerator) (b := denominator)
      hDenominator hEval
  simpa [p, numerator, denominator, Polynomial.eval₂_eq_eval_map,
    rationalCriticalFamilyPairCoupling] using hBound

theorem rationalCriticalFamily_parentPartition_norm_lower_bound
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2)
    {n : ℕ} (parent : CardinalCausalOrder n) :
    1 / (((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n) ≤
      ‖causalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude
          (rationalCriticalFamilyPairCoupling a b n) chirality) parent‖ := by
  have hDegree :=
    interactingChiralRealPartitionPolynomial_natDegree_le parent
  have hBase : (1 : ℝ) ≤ (b : ℝ) * ((n : ℝ) + 1) := by
    have hbOne : 1 ≤ b := hb
    have hbReal : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbOne
    calc
      (1 : ℝ) ≤ (b : ℝ) := hbReal
      _ ≤ (b : ℝ) * ((n : ℝ) + 1) := by
        have hbNonnegative : (0 : ℝ) ≤ (b : ℝ) := by positivity
        have hnNonnegative : (0 : ℝ) ≤ (n : ℝ) := by positivity
        nlinarith [mul_nonneg hbNonnegative hnNonnegative]
  have hPower :
      ((b : ℝ) * ((n : ℝ) + 1)) ^
          (interactingChiralRealPartitionPolynomial parent).natDegree ≤
        ((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n :=
    pow_le_pow_right₀ hBase hDegree
  have hRaw := rationalCriticalFamily_parentPolynomial_denominator_bound
    a b ha hb parent
  have hExpanded :
      (1 : ℝ) ≤
        ((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n *
          |(interactingChiralRealPartitionPolynomial parent).eval₂
            (Int.castRingHom ℝ)
              (rationalCriticalFamilyPairCoupling a b n)| :=
    hRaw.trans (mul_le_mul_of_nonneg_right hPower (abs_nonneg _))
  have hRealLower :
      1 / (((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n) ≤
        |(causalEdgeAmplitudePartition
          (interactingChiralCausalEdgeAmplitude
            (rationalCriticalFamilyPairCoupling a b n) chirality) parent).re| := by
    rw [interactingChiral_partition_re_eq_polynomial_eval]
    rw [div_le_iff₀ (pow_pos (mul_pos (by positivity) (by positivity)) _)]
    simpa [mul_comm] using hExpanded
  exact hRealLower.trans (Complex.abs_re_le_norm _)

/-! ## 3. Explicit condition control across the family -/

def rationalCriticalFamilyParentAbsoluteMass
    (a b : ℕ) (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) : ℝ :=
  ∑ past : CausalPastSet parent,
    ‖(interactingChiralCausalEdgeAmplitude
      (rationalCriticalFamilyPairCoupling a b n) chirality).amplitude
        parent past‖

def rationalCriticalFamilyParentConditionNumber
    (a b : ℕ) (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) : ℝ :=
  rationalCriticalFamilyParentAbsoluteMass a b chirality parent /
    ‖causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalFamilyPairCoupling a b n) chirality) parent‖

theorem rationalCriticalFamily_edgeAmplitude_norm_le
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2)
    {n : ℕ} {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) :
    ‖(interactingChiralCausalEdgeAmplitude
      (rationalCriticalFamilyPairCoupling a b n) chirality).amplitude
        parent past‖ ≤
      rationalCriticalFamilyPairCoupling a b n ^ ancestorPairExponent n := by
  change ‖interactingChiralSignatureWeight
    (rationalCriticalFamilyPairCoupling a b n) chirality
      past.ancestorCount past.maximalCount‖ ≤ _
  rw [interactingChiralSignatureWeight]
  simp only [norm_mul, norm_pow, Complex.norm_real,
    chiralGaussianPower_eq_phase_pow]
  have hLambdaPos : 0 < rationalCriticalFamilyPairCoupling a b n :=
    lt_trans zero_lt_one
      (rationalCriticalFamilyPairCoupling_gt_one a b n ha hb)
  rw [Real.norm_eq_abs, abs_of_pos hLambdaPos]
  have hPhaseNorm : ‖chiralMaximalEventPhase chirality‖ = 1 := by
    fin_cases chirality <;> norm_num [chiralMaximalEventPhase]
  rw [hPhaseNorm, one_pow, mul_one]
  exact pow_le_pow_right₀
    (le_of_lt (rationalCriticalFamilyPairCoupling_gt_one a b n ha hb))
    (ancestorPairExponent_mono (CausalPastSet.ancestorCount_le_rank past))

theorem rationalCriticalFamily_parentAbsoluteMass_upper_bound
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2)
    {n : ℕ} (parent : CardinalCausalOrder n) :
    rationalCriticalFamilyParentAbsoluteMass a b chirality parent ≤
      (2 ^ n : ℝ) *
        rationalCriticalFamilyPairCoupling a b n ^ ancestorPairExponent n := by
  classical
  unfold rationalCriticalFamilyParentAbsoluteMass
  calc
    (∑ past : CausalPastSet parent,
        ‖(interactingChiralCausalEdgeAmplitude
          (rationalCriticalFamilyPairCoupling a b n) chirality).amplitude
            parent past‖) ≤
        ∑ _past : CausalPastSet parent,
          rationalCriticalFamilyPairCoupling a b n ^
            ancestorPairExponent n := by
      apply Finset.sum_le_sum
      intro past _hPast
      exact rationalCriticalFamily_edgeAmplitude_norm_le
        a b ha hb chirality past
    _ = Fintype.card (CausalPastSet parent) *
          rationalCriticalFamilyPairCoupling a b n ^
            ancestorPairExponent n := by simp
    _ ≤ (2 ^ n : ℝ) *
          rationalCriticalFamilyPairCoupling a b n ^
            ancestorPairExponent n := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast causalPastSet_card_le_two_pow parent
      · exact pow_nonneg
          (lt_trans zero_lt_one
            (rationalCriticalFamilyPairCoupling_gt_one a b n ha hb)).le _

theorem rationalCriticalFamily_interactingChiral_partition_ne_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2)
    {n : ℕ} (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalFamilyPairCoupling a b n) chirality) parent ≠ 0 := by
  intro hZero
  have hNormZero := congrArg norm hZero
  have hLower := rationalCriticalFamily_parentPartition_norm_lower_bound
    a b ha hb chirality parent
  rw [norm_zero] at hNormZero
  rw [hNormZero] at hLower
  have hPositive :
      0 < 1 / (((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n) := by
    positivity
  linarith

theorem rationalCriticalFamily_parentConditionNumber_upper_bound
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2)
    {n : ℕ} (parent : CardinalCausalOrder n) :
    rationalCriticalFamilyParentConditionNumber a b chirality parent ≤
      ((2 ^ n : ℝ) *
        rationalCriticalFamilyPairCoupling a b n ^ ancestorPairExponent n) *
          ((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n := by
  let partition := causalEdgeAmplitudePartition
    (interactingChiralCausalEdgeAmplitude
      (rationalCriticalFamilyPairCoupling a b n) chirality) parent
  let massBound := (2 ^ n : ℝ) *
    rationalCriticalFamilyPairCoupling a b n ^ ancestorPairExponent n
  let denominatorPower :=
    ((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n
  have hPartitionNe : partition ≠ 0 :=
    rationalCriticalFamily_interactingChiral_partition_ne_zero
      a b ha hb chirality parent
  have hPartitionNormPos : 0 < ‖partition‖ := norm_pos_iff.mpr hPartitionNe
  have hLower : 1 / denominatorPower ≤ ‖partition‖ := by
    simpa [partition, denominatorPower] using
      rationalCriticalFamily_parentPartition_norm_lower_bound
        a b ha hb chirality parent
  have hMass :
      rationalCriticalFamilyParentAbsoluteMass a b chirality parent ≤
        massBound := by
    simpa [massBound] using
      rationalCriticalFamily_parentAbsoluteMass_upper_bound
        a b ha hb chirality parent
  have hMassBoundNonnegative : 0 ≤ massBound := by
    dsimp [massBound]
    exact mul_nonneg (by positivity)
      (pow_nonneg
        (lt_trans zero_lt_one
          (rationalCriticalFamilyPairCoupling_gt_one a b n ha hb)).le _)
  have hDenominatorPowerPos : 0 < denominatorPower := by
    dsimp [denominatorPower]
    positivity
  unfold rationalCriticalFamilyParentConditionNumber
  change rationalCriticalFamilyParentAbsoluteMass a b chirality parent /
      ‖partition‖ ≤ massBound * denominatorPower
  rw [div_le_iff₀ hPartitionNormPos]
  calc
    rationalCriticalFamilyParentAbsoluteMass a b chirality parent ≤
        massBound := hMass
    _ = (massBound * denominatorPower) * (1 / denominatorPower) := by
      field_simp
    _ ≤ (massBound * denominatorPower) * ‖partition‖ := by
      exact mul_le_mul_of_nonneg_left hLower
        (mul_nonneg hMassBoundNonnegative hDenominatorPowerPos.le)

theorem rationalCriticalFamily_parentConditionNumber_rank_bound
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2)
    {n : ℕ} (parent : CardinalCausalOrder n) :
    rationalCriticalFamilyParentConditionNumber a b chirality parent ≤
      (2 ^ n : ℝ) *
        ((b * (n + 1) + a : ℕ) : ℝ) ^ ancestorPairExponent n := by
  have hFactor :
      rationalCriticalFamilyPairCoupling a b n ^ ancestorPairExponent n *
          ((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n =
        ((b * (n + 1) + a : ℕ) : ℝ) ^ ancestorPairExponent n := by
    rw [← mul_pow]
    congr 1
    unfold rationalCriticalFamilyPairCoupling
    have hDenominator :
        (((b * (n + 1) : ℕ) : ℝ)) ≠ 0 := by positivity
    push_cast
    field_simp
  calc
    rationalCriticalFamilyParentConditionNumber a b chirality parent ≤
        ((2 ^ n : ℝ) *
          rationalCriticalFamilyPairCoupling a b n ^ ancestorPairExponent n) *
            ((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n :=
      rationalCriticalFamily_parentConditionNumber_upper_bound
        a b ha hb chirality parent
    _ = (2 ^ n : ℝ) *
          ((b * (n + 1) + a : ℕ) : ℝ) ^ ancestorPairExponent n := by
      rw [mul_assoc, hFactor]

/-! ## 4. A projective growth law for every positive rational modulus -/

theorem rationalCriticalFamily_unlabeled_partition_ne_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2)
    {n : ℕ} (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalFamilyPairCoupling a b n) chirality) parent ≠ 0 := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact rationalCriticalFamily_interactingChiral_partition_ne_zero
    a b ha hb chirality parentRepresentative

def rationalCriticalFamilyTransition
    (a b : ℕ) (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  unlabeledAggregatedCausalEdgeAmplitude
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalFamilyPairCoupling a b n) chirality) parent child /
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalFamilyPairCoupling a b n) chirality) parent

theorem rationalCriticalFamilyTransition_sum_one
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2)
    {n : ℕ} (parent : UnlabeledCardinalCausalOrder n) :
    ∑ child : UnlabeledCardinalCausalOrder (n + 1),
      rationalCriticalFamilyTransition a b chirality parent child = 1 := by
  classical
  simp only [rationalCriticalFamilyTransition, ← Finset.sum_div]
  rw [sum_unlabeledAggregatedCausalEdgeAmplitude,
    div_self (rationalCriticalFamily_unlabeled_partition_ne_zero
      a b ha hb chirality parent)]

def rationalCriticalFamilyCausalSetGrowthLaw
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := fun n pathPrefix child =>
    rationalCriticalFamilyTransition a b chirality
      (currentUnlabeledCausalOrder n pathPrefix) child
  normalized := fun _n pathPrefix =>
    rationalCriticalFamilyTransition_sum_one a b ha hb chirality
      (currentUnlabeledCausalOrder _ pathPrefix)

theorem rationalCriticalFamilyGrowth_projective_stronglyPositive
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (rationalCriticalFamilyCausalSetGrowthLaw a b ha hb chirality) n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          growthEventDecoherence
              (finiteRankedDepthDecoherence
                (rationalCriticalFamilyCausalSetGrowthLaw
                  a b ha hb chirality) (n + 1))
              (refineRankedGrowthEvent event₁)
              (refineRankedGrowthEvent event₂) =
            growthEventDecoherence
              (finiteRankedDepthDecoherence
                (rationalCriticalFamilyCausalSetGrowthLaw
                  a b ha hb chirality) n)
              event₁ event₂)
      ∧ IsHermitianGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (rationalCriticalFamilyCausalSetGrowthLaw a b ha hb chirality))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (rationalCriticalFamilyCausalSetGrowthLaw a b ha hb chirality))
      ∧ infiniteRankedCylinderDecoherence
          (rationalCriticalFamilyCausalSetGrowthLaw a b ha hb chirality)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1 :=
  normalized_stronglyPositive_infiniteRankedCylinder_family
    (rationalCriticalFamilyCausalSetGrowthLaw a b ha hb chirality)

/-- Capstone: kinematics admits every positive-rational critical scaling
coefficient.  Consequently the value of kappa cannot be inferred from
zero-freeness, projectivity, or strong positivity alone. -/
theorem positiveRationalCriticalFamily_capstone
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (chirality : Fin 2) :
    (∀ n : ℕ, ∀ parent : CardinalCausalOrder n,
      1 / (((b : ℝ) * ((n : ℝ) + 1)) ^ ancestorPairExponent n) ≤
        ‖causalEdgeAmplitudePartition
          (interactingChiralCausalEdgeAmplitude
            (rationalCriticalFamilyPairCoupling a b n) chirality) parent‖)
      ∧ (∀ n : ℕ, ∀ parent : CardinalCausalOrder n,
        rationalCriticalFamilyParentConditionNumber a b chirality parent ≤
          (2 ^ n : ℝ) *
            ((b * (n + 1) + a : ℕ) : ℝ) ^ ancestorPairExponent n)
      ∧ Tendsto (rationalCriticalFamilyEffectiveCoupling a b)
          atTop (nhds 1)
      ∧ Tendsto
          (fun n : ℕ => ((n : ℝ) + 1) *
            (rationalCriticalFamilyEffectiveCoupling a b n - 1))
          atTop (nhds (2 * ((a : ℝ) / (b : ℝ))))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (rationalCriticalFamilyCausalSetGrowthLaw
              a b ha hb chirality)) := by
  exact ⟨fun _n parent =>
      rationalCriticalFamily_parentPartition_norm_lower_bound
        a b ha hb chirality parent,
    fun _n parent =>
      rationalCriticalFamily_parentConditionNumber_rank_bound
        a b ha hb chirality parent,
    rationalCriticalFamilyEffectiveCoupling_tendsto_one a b hb,
    rationalCriticalFamilyEffectiveCoupling_scaled_tendsto a b hb,
    (rationalCriticalFamilyGrowth_projective_stronglyPositive
      a b ha hb chirality).2.2.2.1⟩

#print axioms rationalCriticalFamily_parentPolynomial_eval_ne_zero
#print axioms rationalCriticalFamily_parentPartition_norm_lower_bound
#print axioms rationalCriticalFamily_parentConditionNumber_rank_bound
#print axioms rationalCriticalFamilyGrowth_projective_stronglyPositive
#print axioms positiveRationalCriticalFamily_capstone

end

end UnifiedTheory.Audit.KFCausalSetRationalCriticalFamily
