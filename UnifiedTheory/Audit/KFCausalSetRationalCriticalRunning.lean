/-
  Audit/KFCausalSetRationalCriticalRunning.lean

  RATIONAL CRITICAL RUNNING WITH AN EFFECTIVE PARTITION BOUND

  The transcendental critical trajectory proves qualitative zero-freeness but
  does not by itself quantify the distance from destructive cancellation.  The
  unit constant coefficient of every parent polynomial gives a stronger route.

  The rational-root theorem implies that a rational root of an integer
  polynomial with constant coefficient one has absolute value at most one.
  Hence every rational lambda > 1 is simultaneously zero-free for every finite
  causal parent.  This permits the elementary running schedule

      lambda_n = (n + 2)/(n + 1) = 1 + 1/(n + 1),
      g_n      = lambda_n^2.

  It approaches the same critical surface with

      (n + 1)(g_n - 1) -> 2,

  and, unlike a bare transcendence argument, denominator clearing supplies the
  explicit all-parent estimate

      1/(n + 1)^(n(n-1)) <= |Re Z_C(lambda_n)| <= ||Z_C(lambda_n)||.

  The bound is extremely small and is not yet a useful continuum stability
  estimate.  Its significance is logical: exact zero-freeness, critical
  running, one normalized rank-dependent unlabeled dynamics, and an effective
  finite-rank partition margin are now compatible without a transcendental
  coupling or a totalization fallback.
-/

import UnifiedTheory.Audit.KFCausalSetCriticalRunning
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.DenomsClearable
import Mathlib.Data.Int.Order.Units

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetRationalCriticalRunning

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

/-! ## 1. Unit constant term excludes rational roots outside [-1,1] -/

/-- Rational-root bound specialized to the structural fact used by the parent
partition polynomials. -/
theorem rationalRoot_abs_le_one_of_coeff_zero_eq_one
    {p : ℤ[X]} (hConstant : p.coeff 0 = 1) {q : ℚ}
    (hRoot : Polynomial.aeval q p = 0) : |q| ≤ 1 := by
  have hDivides : IsFractionRing.num ℤ q ∣ (1 : ℤ) := by
    simpa [hConstant] using (num_dvd_of_is_root hRoot)
  have hNumeratorUnit : IsUnit (IsFractionRing.num ℤ q) :=
    isUnit_iff_dvd_one.mpr hDivides
  have hNumeratorAbs : |IsFractionRing.num ℤ q| = 1 :=
    Int.isUnit_iff_abs_eq.mp hNumeratorUnit
  have hDenominatorNe : (IsFractionRing.den ℤ q : ℤ) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den ℤ q).property
  have hDenominatorAbs :
      (1 : ℤ) ≤ |(IsFractionRing.den ℤ q : ℤ)| :=
    Int.one_le_abs hDenominatorNe
  rw [← IsFractionRing.mk'_num_den' ℤ q, abs_div]
  change |((IsFractionRing.num ℤ q : ℤ) : ℚ)| /
      |(((IsFractionRing.den ℤ q : ℤ) : ℤ) : ℚ)| ≤ 1
  rw [← Int.cast_abs, hNumeratorAbs, Int.cast_one, ← Int.cast_abs]
  rw [div_le_one]
  · exact_mod_cast (abs_pos.mpr hDenominatorNe)
  · exact_mod_cast hDenominatorAbs

/-- Evaluation at a rational commutes with the embedding into the reals.  This
small bridge lets the rational-root theorem control the real partition. -/
theorem aeval_eq_zero_of_real_eval₂_eq_zero {p : ℤ[X]} {q : ℚ}
    (hReal : p.eval₂ (Int.castRingHom ℝ) (q : ℝ) = 0) :
    Polynomial.aeval q p = 0 := by
  rw [Polynomial.aeval_def]
  apply (Rat.castHom ℝ).injective
  rw [map_zero, Polynomial.hom_eval₂]
  simpa using hReal

/-! ## 2. The elementary rational critical trajectory -/

def rationalCriticalPairCouplingQ (n : ℕ) : ℚ :=
  ((n : ℚ) + 2) / ((n : ℚ) + 1)

def rationalCriticalPairCoupling (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) / ((n : ℝ) + 1)

def rationalCriticalEffectiveCoupling (n : ℕ) : ℝ :=
  effectivePairCoupling (rationalCriticalPairCoupling n)

theorem rationalCriticalPairCoupling_cast (n : ℕ) :
    ((rationalCriticalPairCouplingQ n : ℚ) : ℝ) =
      rationalCriticalPairCoupling n := by
  norm_num [rationalCriticalPairCouplingQ, rationalCriticalPairCoupling]

theorem rationalCriticalPairCouplingQ_gt_one (n : ℕ) :
    1 < rationalCriticalPairCouplingQ n := by
  unfold rationalCriticalPairCouplingQ
  rw [one_lt_div]
  · norm_num
  · positivity

theorem rationalCriticalPairCoupling_gt_one (n : ℕ) :
    1 < rationalCriticalPairCoupling n := by
  rw [← rationalCriticalPairCoupling_cast]
  exact_mod_cast rationalCriticalPairCouplingQ_gt_one n

theorem rationalCriticalPairCoupling_eq_one_add (n : ℕ) :
    rationalCriticalPairCoupling n = 1 + 1 / ((n : ℝ) + 1) := by
  unfold rationalCriticalPairCoupling
  have hDenominator : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem rationalCriticalPairCoupling_tendsto_one :
    Tendsto rationalCriticalPairCoupling atTop (nhds 1) := by
  have hTail := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hLimit := (tendsto_const_nhds (x := (1 : ℝ))).add hTail
  have hLimit' :
      Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1))
        atTop (nhds 1) := by
    simpa using hLimit
  apply hLimit'.congr'
  filter_upwards [] with n
  exact (rationalCriticalPairCoupling_eq_one_add n).symm

theorem rationalCriticalEffectiveCoupling_tendsto_one :
    Tendsto rationalCriticalEffectiveCoupling atTop (nhds 1) := by
  change Tendsto (fun n : ℕ => rationalCriticalPairCoupling n ^ 2)
    atTop (nhds 1)
  simpa [pow_two] using rationalCriticalPairCoupling_tendsto_one.mul
    rationalCriticalPairCoupling_tendsto_one

theorem rationalCriticalEffectiveCoupling_scaled_displacement (n : ℕ) :
    ((n : ℝ) + 1) * (rationalCriticalEffectiveCoupling n - 1) =
      2 + 1 / ((n : ℝ) + 1) := by
  unfold rationalCriticalEffectiveCoupling effectivePairCoupling
  rw [rationalCriticalPairCoupling_eq_one_add]
  have hDenominator : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem rationalCriticalEffectiveCoupling_scaled_tendsto_two :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) * (rationalCriticalEffectiveCoupling n - 1))
      atTop (nhds 2) := by
  have hTail := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hLimit :
      Tendsto (fun n : ℕ => 2 + 1 / ((n : ℝ) + 1))
        atTop (nhds 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add hTail
  apply hLimit.congr'
  filter_upwards [] with n
  exact (rationalCriticalEffectiveCoupling_scaled_displacement n).symm

/-! ## 3. Exact zero-freeness and an effective lower bound -/

theorem rationalCritical_parentPolynomial_eval_ne_zero {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (interactingChiralRealPartitionPolynomial parent).eval₂
      (Int.castRingHom ℝ) (rationalCriticalPairCoupling n) ≠ 0 := by
  intro hEvaluation
  have hRationalRoot :
      Polynomial.aeval (rationalCriticalPairCouplingQ n)
        (interactingChiralRealPartitionPolynomial parent) = 0 := by
    apply aeval_eq_zero_of_real_eval₂_eq_zero
    simpa [rationalCriticalPairCoupling_cast] using hEvaluation
  have hAbs := rationalRoot_abs_le_one_of_coeff_zero_eq_one
    (interactingChiralRealPartitionPolynomial_coeff_zero parent) hRationalRoot
  rw [abs_of_pos
    (lt_trans zero_lt_one (rationalCriticalPairCouplingQ_gt_one n))] at hAbs
  exact (not_le_of_gt (rationalCriticalPairCouplingQ_gt_one n)) hAbs

/-- Denominator clearing turns qualitative nonvanishing into a finite-rank
integer-separation estimate. -/
theorem rationalCritical_parentPolynomial_denominator_bound {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (1 : ℝ) ≤
      ((n : ℝ) + 1) ^
          (interactingChiralRealPartitionPolynomial parent).natDegree *
        |(interactingChiralRealPartitionPolynomial parent).eval₂
          (Int.castRingHom ℝ) (rationalCriticalPairCoupling n)| := by
  let p := interactingChiralRealPartitionPolynomial parent
  have hEval :
      Polynomial.eval
          (((n : ℤ) + 2 : ℤ) / (((n : ℤ) + 1 : ℤ) : ℝ))
          (p.map (algebraMap ℤ ℝ)) ≠ 0 := by
    simpa [p, Polynomial.eval₂_eq_eval_map,
      rationalCriticalPairCoupling] using
      rationalCritical_parentPolynomial_eval_ne_zero parent
  have hBound := one_le_pow_mul_abs_eval_div
    (K := ℝ) (f := p) (a := ((n : ℤ) + 2))
    (b := ((n : ℤ) + 1)) (by omega) hEval
  simpa [p, Polynomial.eval₂_eq_eval_map,
    rationalCriticalPairCoupling] using hBound

/-- Rank-only lower bound for the real part of every parent partition. -/
theorem rationalCritical_parentPartition_re_abs_lower_bound
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    1 / (((n : ℝ) + 1) ^ ancestorPairExponent n) ≤
      |(causalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude
          (rationalCriticalPairCoupling n) chirality) parent).re| := by
  have hDegree :=
    interactingChiralRealPartitionPolynomial_natDegree_le parent
  have hBase : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
  have hPower :
      ((n : ℝ) + 1) ^
          (interactingChiralRealPartitionPolynomial parent).natDegree ≤
        ((n : ℝ) + 1) ^ ancestorPairExponent n :=
    pow_le_pow_right₀ hBase hDegree
  have hRaw := rationalCritical_parentPolynomial_denominator_bound parent
  have hExpanded :
      (1 : ℝ) ≤
        ((n : ℝ) + 1) ^ ancestorPairExponent n *
          |(interactingChiralRealPartitionPolynomial parent).eval₂
            (Int.castRingHom ℝ) (rationalCriticalPairCoupling n)| :=
    hRaw.trans (mul_le_mul_of_nonneg_right hPower (abs_nonneg _))
  rw [interactingChiral_partition_re_eq_polynomial_eval]
  rw [div_le_iff₀ (pow_pos (by positivity) _)]
  simpa [mul_comm] using hExpanded

/-- The complex partition norm inherits the same explicit lower bound. -/
theorem rationalCritical_parentPartition_norm_lower_bound
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    1 / (((n : ℝ) + 1) ^ ancestorPairExponent n) ≤
      ‖causalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude
          (rationalCriticalPairCoupling n) chirality) parent‖ :=
  (rationalCritical_parentPartition_re_abs_lower_bound chirality parent).trans
    (Complex.abs_re_le_norm _)

/-- Sum of raw transition-amplitude magnitudes before coherent
normalization. -/
def rationalCriticalParentAbsoluteMass (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) : ℝ :=
  ∑ past : CausalPastSet parent,
    ‖(interactingChiralCausalEdgeAmplitude
      (rationalCriticalPairCoupling n) chirality).amplitude parent past‖

/-- Numerical cancellation sensitivity of one parent: incoherent raw mass
divided by the norm of its coherent partition. -/
def rationalCriticalParentConditionNumber (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) : ℝ :=
  rationalCriticalParentAbsoluteMass chirality parent /
    ‖causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalPairCoupling n) chirality) parent‖

theorem rationalCritical_edgeAmplitude_norm_le {n : ℕ}
    (chirality : Fin 2) {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) :
    ‖(interactingChiralCausalEdgeAmplitude
      (rationalCriticalPairCoupling n) chirality).amplitude parent past‖ ≤
      rationalCriticalPairCoupling n ^ ancestorPairExponent n := by
  change ‖interactingChiralSignatureWeight
    (rationalCriticalPairCoupling n) chirality
      past.ancestorCount past.maximalCount‖ ≤ _
  rw [interactingChiralSignatureWeight]
  simp only [norm_mul, norm_pow, Complex.norm_real,
    chiralGaussianPower_eq_phase_pow]
  have hLambdaPos : 0 < rationalCriticalPairCoupling n :=
    lt_trans zero_lt_one (rationalCriticalPairCoupling_gt_one n)
  rw [Real.norm_eq_abs, abs_of_pos hLambdaPos]
  have hPhaseNorm : ‖chiralMaximalEventPhase chirality‖ = 1 := by
    fin_cases chirality <;> norm_num [chiralMaximalEventPhase]
  rw [hPhaseNorm, one_pow, mul_one]
  exact pow_le_pow_right₀ (le_of_lt (rationalCriticalPairCoupling_gt_one n))
    (ancestorPairExponent_mono (CausalPastSet.ancestorCount_le_rank past))

/-- The incoherent numerator grows at most exponentially times the maximal
pair weight. -/
theorem rationalCritical_parentAbsoluteMass_upper_bound
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    rationalCriticalParentAbsoluteMass chirality parent ≤
      (2 ^ n : ℝ) *
        rationalCriticalPairCoupling n ^ ancestorPairExponent n := by
  classical
  unfold rationalCriticalParentAbsoluteMass
  calc
    (∑ past : CausalPastSet parent,
        ‖(interactingChiralCausalEdgeAmplitude
          (rationalCriticalPairCoupling n) chirality).amplitude parent past‖) ≤
        ∑ _past : CausalPastSet parent,
          rationalCriticalPairCoupling n ^ ancestorPairExponent n := by
      apply Finset.sum_le_sum
      intro past _hPast
      exact rationalCritical_edgeAmplitude_norm_le chirality past
    _ = Fintype.card (CausalPastSet parent) *
          rationalCriticalPairCoupling n ^ ancestorPairExponent n := by simp
    _ ≤ (2 ^ n : ℝ) *
          rationalCriticalPairCoupling n ^ ancestorPairExponent n := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast causalPastSet_card_le_two_pow parent
      · exact pow_nonneg
          (lt_trans zero_lt_one
            (rationalCriticalPairCoupling_gt_one n)).le _

theorem rationalCritical_interactingChiral_partition_ne_zero
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalPairCoupling n) chirality) parent ≠ 0 := by
  intro hZero
  have hNormZero := congrArg norm hZero
  have hLower := rationalCritical_parentPartition_norm_lower_bound
    chirality parent
  rw [norm_zero] at hNormZero
  rw [hNormZero] at hLower
  have hPositive :
      0 < 1 / (((n : ℝ) + 1) ^ ancestorPairExponent n) := by positivity
  linarith

/-- Fully explicit, though deliberately conservative, condition-number bound.
It is finite at every rank but still superexponential, so it does not close the
continuum-stability problem. -/
theorem rationalCritical_parentConditionNumber_upper_bound
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    rationalCriticalParentConditionNumber chirality parent ≤
      ((2 ^ n : ℝ) *
        rationalCriticalPairCoupling n ^ ancestorPairExponent n) *
          ((n : ℝ) + 1) ^ ancestorPairExponent n := by
  let partition := causalEdgeAmplitudePartition
    (interactingChiralCausalEdgeAmplitude
      (rationalCriticalPairCoupling n) chirality) parent
  let massBound := (2 ^ n : ℝ) *
    rationalCriticalPairCoupling n ^ ancestorPairExponent n
  let denominatorPower := ((n : ℝ) + 1) ^ ancestorPairExponent n
  have hPartitionNe : partition ≠ 0 :=
    rationalCritical_interactingChiral_partition_ne_zero chirality parent
  have hPartitionNormPos : 0 < ‖partition‖ := norm_pos_iff.mpr hPartitionNe
  have hLower : 1 / denominatorPower ≤ ‖partition‖ := by
    simpa [partition, denominatorPower] using
      rationalCritical_parentPartition_norm_lower_bound chirality parent
  have hMass : rationalCriticalParentAbsoluteMass chirality parent ≤
      massBound := by
    simpa [massBound] using
      rationalCritical_parentAbsoluteMass_upper_bound chirality parent
  have hMassBoundNonnegative : 0 ≤ massBound := by
    dsimp [massBound]
    exact mul_nonneg (by positivity)
      (pow_nonneg
        (lt_trans zero_lt_one (rationalCriticalPairCoupling_gt_one n)).le _)
  have hDenominatorPowerPos : 0 < denominatorPower := by
    dsimp [denominatorPower]
    positivity
  unfold rationalCriticalParentConditionNumber
  change rationalCriticalParentAbsoluteMass chirality parent / ‖partition‖ ≤
    massBound * denominatorPower
  rw [div_le_iff₀ hPartitionNormPos]
  calc
    rationalCriticalParentAbsoluteMass chirality parent ≤ massBound := hMass
    _ = (massBound * denominatorPower) * (1 / denominatorPower) := by
      field_simp
    _ ≤ (massBound * denominatorPower) * ‖partition‖ := by
      exact mul_le_mul_of_nonneg_left hLower
        (mul_nonneg hMassBoundNonnegative hDenominatorPowerPos.le)

/-- Closed rank-only form of the condition-number estimate. -/
theorem rationalCritical_parentConditionNumber_rank_bound
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    rationalCriticalParentConditionNumber chirality parent ≤
      (2 ^ n : ℝ) * ((n : ℝ) + 2) ^ ancestorPairExponent n := by
  have hFactor :
      rationalCriticalPairCoupling n ^ ancestorPairExponent n *
          ((n : ℝ) + 1) ^ ancestorPairExponent n =
        ((n : ℝ) + 2) ^ ancestorPairExponent n := by
    rw [← mul_pow]
    congr 1
    unfold rationalCriticalPairCoupling
    have hDenominator : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  calc
    rationalCriticalParentConditionNumber chirality parent ≤
        ((2 ^ n : ℝ) *
          rationalCriticalPairCoupling n ^ ancestorPairExponent n) *
            ((n : ℝ) + 1) ^ ancestorPairExponent n :=
      rationalCritical_parentConditionNumber_upper_bound chirality parent
    _ = (2 ^ n : ℝ) * ((n : ℝ) + 2) ^ ancestorPairExponent n := by
      rw [mul_assoc, hFactor]

theorem rationalCritical_unlabeled_partition_ne_zero
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalPairCoupling n) chirality) parent ≠ 0 := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact rationalCritical_interactingChiral_partition_ne_zero
    chirality parentRepresentative

/-! ## 4. One genuinely rank-dependent normalized growth dynamics -/

def rationalCriticalTransition (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  unlabeledAggregatedCausalEdgeAmplitude
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalPairCoupling n) chirality) parent child /
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (rationalCriticalPairCoupling n) chirality) parent

theorem rationalCriticalTransition_sum_one (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    ∑ child : UnlabeledCardinalCausalOrder (n + 1),
      rationalCriticalTransition chirality parent child = 1 := by
  classical
  simp only [rationalCriticalTransition, ← Finset.sum_div]
  rw [sum_unlabeledAggregatedCausalEdgeAmplitude,
    div_self (rationalCritical_unlabeled_partition_ne_zero chirality parent)]

/-- A single growth law whose microscopic pair coupling runs with the current
causal-set rank. -/
def rationalCriticalCausalSetGrowthLaw (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := fun n pathPrefix child =>
    rationalCriticalTransition chirality
      (currentUnlabeledCausalOrder n pathPrefix) child
  normalized := fun _n pathPrefix =>
    rationalCriticalTransition_sum_one chirality
      (currentUnlabeledCausalOrder _ pathPrefix)

theorem rationalCriticalGrowth_projective_stronglyPositive
    (chirality : Fin 2) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (rationalCriticalCausalSetGrowthLaw chirality) n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          growthEventDecoherence
              (finiteRankedDepthDecoherence
                (rationalCriticalCausalSetGrowthLaw chirality) (n + 1))
              (refineRankedGrowthEvent event₁)
              (refineRankedGrowthEvent event₂) =
            growthEventDecoherence
              (finiteRankedDepthDecoherence
                (rationalCriticalCausalSetGrowthLaw chirality) n)
              event₁ event₂)
      ∧ IsHermitianGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (rationalCriticalCausalSetGrowthLaw chirality))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (rationalCriticalCausalSetGrowthLaw chirality))
      ∧ infiniteRankedCylinderDecoherence
          (rationalCriticalCausalSetGrowthLaw chirality)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1 :=
  normalized_stronglyPositive_infiniteRankedCylinder_family
    (rationalCriticalCausalSetGrowthLaw chirality)

/-- Capstone: the rational-root theorem upgrades the critical trajectory to an
effective, fallback-free, rank-dependent quantum sequential growth law. -/
theorem effective_rationalCritical_growth_capstone (chirality : Fin 2) :
    (∀ n : ℕ, ∀ parent : CardinalCausalOrder n,
      1 / (((n : ℝ) + 1) ^ ancestorPairExponent n) ≤
        ‖causalEdgeAmplitudePartition
          (interactingChiralCausalEdgeAmplitude
            (rationalCriticalPairCoupling n) chirality) parent‖)
      ∧ (∀ n : ℕ, ∀ parent : CardinalCausalOrder n,
        rationalCriticalParentConditionNumber chirality parent ≤
          (2 ^ n : ℝ) *
            ((n : ℝ) + 2) ^ ancestorPairExponent n)
      ∧ Tendsto rationalCriticalEffectiveCoupling atTop (nhds 1)
      ∧ Tendsto
          (fun n : ℕ =>
            ((n : ℝ) + 1) *
              (rationalCriticalEffectiveCoupling n - 1))
          atTop (nhds 2)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (rationalCriticalCausalSetGrowthLaw chirality)) := by
  exact ⟨fun _n parent =>
      rationalCritical_parentPartition_norm_lower_bound chirality parent,
    fun _n parent =>
      rationalCritical_parentConditionNumber_rank_bound chirality parent,
    rationalCriticalEffectiveCoupling_tendsto_one,
    rationalCriticalEffectiveCoupling_scaled_tendsto_two,
    (rationalCriticalGrowth_projective_stronglyPositive chirality).2.2.2.1⟩

#print axioms rationalRoot_abs_le_one_of_coeff_zero_eq_one
#print axioms rationalCritical_parentPartition_norm_lower_bound
#print axioms rationalCritical_parentConditionNumber_rank_bound
#print axioms rationalCritical_interactingChiral_partition_ne_zero
#print axioms rationalCriticalGrowth_projective_stronglyPositive
#print axioms effective_rationalCritical_growth_capstone

end

end UnifiedTheory.Audit.KFCausalSetRationalCriticalRunning
