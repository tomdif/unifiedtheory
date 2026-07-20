/-
  Audit/KFCausalSetMultiplicityCorrectedRunning.lean

  A ZERO-FREE, MULTIPLICITY-BALANCED CRITICAL LAW

  Edgewise finite-kappa schedules miss the binomial entropy of complete
  precursor sectors.  This module constructs a rational repair:

      lambda_0 = lambda_1 = 2,
      lambda_n = 1 + H_n / (2(n-1))  for n >= 2,

  where H_n is the rational harmonic number.  Every lambda_n is rational and
  strictly above one, so the all-parent rational-root theorem makes the law
  exactly zero-free at every finite rank.  At the same time lambda_n -> 1 and
  the coherently aggregated unlabeled one-missing/timid Born-mass ratio on
  (n+1)-antichains obeys

      (n+1)^2 / g_(n+1)^(2n) -> exp(-2 gamma).

  Thus arithmetic zero-freeness and multiplicity-corrected critical balance
  are compatible in one explicit normalized, projective, strongly-positive
  infinite-cylinder growth law.  This still does not derive the law from a
  microscopic action or select the reflection-odd chirality sign.
-/

import UnifiedTheory.Audit.KFCausalSetCriticalMultiplicity
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning

noncomputable section

open scoped BigOperators ComplexConjugate
open Filter Topology
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetCriticalRunning
open UnifiedTheory.Audit.KFCausalSetRationalCriticalRunning
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralDynamics
open UnifiedTheory.Audit.KFCausalSetCriticalMultiplicity

def harmonicCriticalPairCouplingQ (n : ℕ) : ℚ :=
  if n ≤ 1 then 2 else 1 + harmonic n / (2 * (n - 1))

def harmonicCriticalPairCoupling (n : ℕ) : ℝ := (harmonicCriticalPairCouplingQ n : ℝ)

def harmonicCriticalEffectiveCoupling (n : ℕ) : ℝ := harmonicCriticalPairCoupling n ^ 2

theorem harmonic_pos_of_pos {n : ℕ} (hn : 0 < n) : (0 : ℚ) < harmonic n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [harmonic_succ]
  have hnonneg : (0 : ℚ) ≤ harmonic k := by
    unfold harmonic
    positivity
  positivity

theorem harmonicCriticalPairCouplingQ_gt_one (n : ℕ) :
    1 < harmonicCriticalPairCouplingQ n := by
  by_cases hn : n ≤ 1
  · simp [harmonicCriticalPairCouplingQ, hn]
  · simp only [harmonicCriticalPairCouplingQ, hn, if_false]
    have hnpos : 0 < n := lt_trans Nat.zero_lt_one (lt_of_not_ge hn)
    have hH : (0 : ℚ) < harmonic n := harmonic_pos_of_pos hnpos
    have hnQ : (1 : ℚ) < n := by exact_mod_cast (lt_of_not_ge hn)
    have hden : (0 : ℚ) < (2 : ℚ) * (n - 1) :=
      mul_pos (by norm_num) (sub_pos.mpr hnQ)
    linarith [div_pos hH hden]

theorem harmonicCriticalPairCoupling_gt_one (n : ℕ) :
    1 < harmonicCriticalPairCoupling n := by
  change 1 < (harmonicCriticalPairCouplingQ n : ℝ)
  exact_mod_cast harmonicCriticalPairCouplingQ_gt_one n

theorem harmonicCritical_parentPolynomial_eval_ne_zero {n : ℕ} (parent : CardinalCausalOrder n) :
    (interactingChiralRealPartitionPolynomial parent).eval₂
      (Int.castRingHom ℝ) (harmonicCriticalPairCouplingQ n : ℝ) ≠ 0 :=
  rational_parentPolynomial_eval_ne_zero_of_one_lt
    (harmonicCriticalPairCouplingQ_gt_one n) parent

theorem harmonic_div_tendsto_zero : Tendsto
    (fun n : ℕ => (harmonic n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hDifference : Tendsto
      (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / (n : ℝ))
      atTop (nhds 0) :=
    Real.tendsto_harmonic_sub_log.div_atTop tendsto_natCast_atTop_atTop
  have hLog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have hEq :
      (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / (n : ℝ) +
        Real.log n / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (harmonic n : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
    ring
  simpa using (hDifference.add hLog).congr' hEq

theorem harmonic_div_sqrt_tendsto_zero : Tendsto
    (fun n : ℕ => (harmonic n : ℝ) / Real.sqrt n) atTop (nhds 0) := by
  have hDifference : Tendsto
      (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.sqrt n)
      atTop (nhds 0) :=
    Real.tendsto_harmonic_sub_log.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hLogReal : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x)
      atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hLog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.sqrt n)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using hLogReal.comp tendsto_natCast_atTop_atTop
  have hEq :
      (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.sqrt n +
        Real.log n / Real.sqrt n) =ᶠ[atTop]
      (fun n : ℕ => (harmonic n : ℝ) / Real.sqrt n) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  simpa using (hDifference.add hLog).congr' hEq

theorem harmonic_sq_div_tendsto_zero : Tendsto
    (fun n : ℕ => (harmonic n : ℝ) ^ 2 / (n : ℝ)) atTop (nhds 0) := by
  have hSq := harmonic_div_sqrt_tendsto_zero.pow 2
  have hEq :
      (fun n : ℕ => ((harmonic n : ℝ) / Real.sqrt n) ^ 2) =ᶠ[atTop]
      (fun n : ℕ => (harmonic n : ℝ) ^ 2 / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [div_pow]
    congr 1
    exact Real.sq_sqrt (by positivity)
  simpa using hSq.congr' hEq

theorem abs_log_one_add_sub_self_le (x : ℝ) (hx : 0 ≤ x) :
    |Real.log (1 + x) - x| ≤ x ^ 2 / 2 := by
  have hone : 0 < 1 + x := by linarith
  have hUpper : Real.log (1 + x) ≤ x := by
    simpa using Real.log_le_sub_one_of_pos hone
  rw [abs_of_nonpos (sub_nonpos.mpr hUpper)]
  have hLower := Real.le_log_one_add_of_nonneg hx
  calc
    -(Real.log (1 + x) - x) ≤ x - 2 * x / (x + 2) := by linarith
    _ = x ^ 2 / (x + 2) := by
      field_simp
      ring
    _ ≤ x ^ 2 / 2 :=
      div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) (by linarith)

theorem shifted_harmonic_sq_div_tendsto_zero : Tendsto
    (fun n : ℕ => (harmonic (n + 1) : ℝ) ^ 2 / (n : ℝ))
    atTop (nhds 0) := by
  have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_add_right n 1) tendsto_id
  have hSq := harmonic_sq_div_tendsto_zero.comp hShift
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hFactor : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    have hBase := (tendsto_const_nhds (x := (1 : ℝ))).add hInv
    have hEq :
        (fun n : ℕ => 1 + (1 : ℝ) / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      push_cast
      field_simp
    simpa using hBase.congr' hEq
  have hEq :
      (fun n : ℕ =>
        ((harmonic (n + 1) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ)) *
          (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => (harmonic (n + 1) : ℝ) ^ 2 / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    push_cast
    field_simp
  simpa [Function.comp_def] using (hSq.mul hFactor).congr' hEq

theorem harmonicCritical_scaledLogError_tendsto_zero : Tendsto
    (fun n : ℕ => 4 * (n : ℝ) *
      (Real.log (harmonicCriticalPairCoupling (n + 1)) -
        (harmonicCriticalPairCoupling (n + 1) - 1)))
    atTop (nhds 0) := by
  have hBound : Tendsto
      (fun n : ℕ => (harmonic (n + 1) : ℝ) ^ 2 / (2 * (n : ℝ)))
      atTop (nhds 0) := by
    have h := shifted_harmonic_sq_div_tendsto_zero.div_const 2
    have hEq :
        (fun n : ℕ => (harmonic (n + 1) : ℝ) ^ 2 / (n : ℝ) / 2) =ᶠ[atTop]
        (fun n : ℕ => (harmonic (n + 1) : ℝ) ^ 2 / (2 * (n : ℝ))) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp
    simpa using h.congr' hEq
  apply squeeze_zero_norm' _ hBound
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hbranch : ¬ n + 1 ≤ 1 := by omega
  have hH : (0 : ℝ) < (harmonic (n + 1) : ℝ) := by
    exact_mod_cast harmonic_pos_of_pos (Nat.succ_pos n)
  have hx : 0 ≤ (harmonic (n + 1) : ℝ) / (2 * (n : ℝ)) :=
    (div_nonneg hH.le (by positivity))
  have hTaylor := abs_log_one_add_sub_self_le
    ((harmonic (n + 1) : ℝ) / (2 * (n : ℝ))) hx
  have hLambda : harmonicCriticalPairCoupling (n + 1) =
      1 + (harmonic (n + 1) : ℝ) / (2 * (n : ℝ)) := by
    simp only [harmonicCriticalPairCoupling,
      harmonicCriticalPairCouplingQ, hbranch, if_false,
      Rat.cast_add, Rat.cast_one, Rat.cast_div]
    push_cast
    congr 2
    ring
  rw [hLambda]
  norm_num only [add_sub_cancel_left]
  rw [Real.norm_eq_abs, abs_mul]
  have hcoef : |4 * (n : ℝ)| = 4 * (n : ℝ) := abs_of_nonneg (by positivity)
  rw [hcoef]
  calc
    4 * (n : ℝ) *
        |Real.log (1 + (harmonic (n + 1) : ℝ) / (2 * (n : ℝ))) -
          (harmonic (n + 1) : ℝ) / (2 * (n : ℝ))| ≤
        4 * (n : ℝ) *
          (((harmonic (n + 1) : ℝ) / (2 * (n : ℝ))) ^ 2 / 2) := by
      gcongr
    _ = (harmonic (n + 1) : ℝ) ^ 2 / (2 * (n : ℝ)) := by
      field_simp
      ring

theorem harmonicCriticalPairCoupling_tendsto_one :
    Tendsto harmonicCriticalPairCoupling atTop (nhds 1) := by
  have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_add_right n 1) tendsto_id
  have hDiv := harmonic_div_tendsto_zero.comp hShift
  have hScaled : Tendsto
      (fun n : ℕ => (harmonic (n + 1) : ℝ) / (2 * (n : ℝ)))
      atTop (nhds 0) := by
    have hFactor : Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (2 * (n : ℝ)))
        atTop (nhds (1 / 2 : ℝ)) := by
      have hInv : Tendsto (fun n : ℕ => (1 / 2 : ℝ) / (n : ℝ))
          atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)
      have hBase := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add hInv
      have hEq :
          (fun n : ℕ => (1 / 2 : ℝ) + (1 / 2 : ℝ) / (n : ℝ)) =ᶠ[atTop]
          (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (2 * (n : ℝ))) := by
        filter_upwards [eventually_ne_atTop 0] with n hn
        push_cast
        field_simp
      simpa using hBase.congr' hEq
    have hEq :
        (fun n : ℕ =>
          ((harmonic (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
            (((n + 1 : ℕ) : ℝ) / (2 * (n : ℝ)))) =ᶠ[atTop]
        (fun n : ℕ => (harmonic (n + 1) : ℝ) / (2 * (n : ℝ))) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      push_cast
      field_simp
    simpa [Function.comp_def] using (hDiv.mul hFactor).congr' hEq
  apply (tendsto_add_atTop_iff_nat (f := harmonicCriticalPairCoupling) 1).mp
  have hEq :
      (fun n : ℕ => 1 + (harmonic (n + 1) : ℝ) / (2 * (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => harmonicCriticalPairCoupling (n + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hbranch : ¬ n + 1 ≤ 1 := by omega
    simp [harmonicCriticalPairCoupling, harmonicCriticalPairCouplingQ, hbranch]
  simpa using (tendsto_const_nhds.add hScaled).congr' hEq

theorem harmonicCritical_firstOrderCorrection_tendsto : Tendsto
    (fun n : ℕ => 2 * (n : ℝ) * (harmonicCriticalPairCoupling (n + 1) - 1) - Real.log (n + 1))
    atTop (nhds Real.eulerMascheroniConstant) := by
  have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_add_right n 1) tendsto_id
  apply (Real.tendsto_harmonic_sub_log.comp hShift).congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hbranch : ¬ n + 1 ≤ 1 := by omega
  simp [harmonicCriticalPairCoupling, harmonicCriticalPairCouplingQ, hbranch]
  field_simp

theorem harmonicCritical_logBornRatio_tendsto : Tendsto
    (fun n : ℕ => 2 * Real.log (n + 1) -
      4 * (n : ℝ) * Real.log (harmonicCriticalPairCoupling (n + 1)))
    atTop (nhds (-2 * Real.eulerMascheroniConstant)) := by
  have hFirstTwice := harmonicCritical_firstOrderCorrection_tendsto.const_mul 2
  have h := (hFirstTwice.add
    harmonicCritical_scaledLogError_tendsto_zero).neg
  have hEq :
      (fun n : ℕ => -(2 *
          (2 * (n : ℝ) * (harmonicCriticalPairCoupling (n + 1) - 1) -
            Real.log (n + 1)) +
        4 * (n : ℝ) *
          (Real.log (harmonicCriticalPairCoupling (n + 1)) -
            (harmonicCriticalPairCoupling (n + 1) - 1)))) =ᶠ[atTop]
      (fun n : ℕ => 2 * Real.log (n + 1) -
        4 * (n : ℝ) * Real.log (harmonicCriticalPairCoupling (n + 1))) := by
    filter_upwards [] with n
    ring
  simpa using h.congr' hEq

def harmonicCriticalBornRatio (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)) ^ 2 /
    (harmonicCriticalEffectiveCoupling (n + 1)) ^ (2 * n)

/-- The asymptotic observable is exactly the coherently aggregated unlabeled
antichain-sector ratio, not the incoherent precursor-slot ratio. -/
theorem harmonicCriticalBornRatio_eq_coherentSectorRatio (n : ℕ) :
    harmonicCriticalBornRatio n =
      antichainCoherentBornSectorMass (harmonicCriticalEffectiveCoupling (n + 1))
          (n + 1) n /
        antichainCoherentBornSectorMass (harmonicCriticalEffectiveCoupling (n + 1))
          (n + 1) (n + 1) := by
  have hg : harmonicCriticalEffectiveCoupling (n + 1) ≠ 0 := by
    exact pow_ne_zero 2 (ne_of_gt (lt_trans zero_lt_one
      (harmonicCriticalPairCoupling_gt_one (n + 1))))
  exact (antichainCoherentOneMissingBornToTimidRatio
    (harmonicCriticalEffectiveCoupling (n + 1)) hg n).symm

theorem harmonicCriticalBornRatio_eq_exp (n : ℕ) :
    harmonicCriticalBornRatio n = Real.exp (2 * Real.log (n + 1) -
      4 * (n : ℝ) * Real.log (harmonicCriticalPairCoupling (n + 1))) := by
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hLambda : 0 < harmonicCriticalPairCoupling (n + 1) :=
    lt_trans zero_lt_one (harmonicCriticalPairCoupling_gt_one (n + 1))
  rw [Real.exp_sub]
  have hNumerator : Real.exp (2 * Real.log ((n : ℝ) + 1)) =
      (((n + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    push_cast
    rfl
  rw [hNumerator]
  have hExponent : 4 * (n : ℝ) * Real.log (harmonicCriticalPairCoupling (n + 1)) =
      (((4 * n : ℕ) : ℝ)) * Real.log (harmonicCriticalPairCoupling (n + 1)) := by
    push_cast
    ring
  rw [hExponent, Real.exp_nat_mul, Real.exp_log hLambda]
  simp only [harmonicCriticalBornRatio, harmonicCriticalEffectiveCoupling]
  push_cast
  congr 1
  rw [← pow_mul]
  congr 1
  omega

theorem harmonicCriticalBornRatio_tendsto : Tendsto harmonicCriticalBornRatio atTop
    (nhds (Real.exp (-2 * Real.eulerMascheroniConstant))) := by
  have hExp := Real.continuous_exp.continuousAt.tendsto.comp
    harmonicCritical_logBornRatio_tendsto
  apply hExp.congr'
  filter_upwards [] with n
  exact (harmonicCriticalBornRatio_eq_exp n).symm

/-! ## A normalized projective infinite-cylinder law -/

theorem harmonicCritical_interactingChiral_partition_ne_zero
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (harmonicCriticalPairCoupling n) chirality) parent ≠ 0 := by
  intro hZero
  have hRealZero := congrArg Complex.re hZero
  rw [interactingChiral_partition_re_eq_polynomial_eval] at hRealZero
  exact harmonicCritical_parentPolynomial_eval_ne_zero parent (by
    simpa [harmonicCriticalPairCoupling] using hRealZero)

theorem harmonicCritical_unlabeled_partition_ne_zero
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (harmonicCriticalPairCoupling n) chirality) parent ≠ 0 := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact harmonicCritical_interactingChiral_partition_ne_zero
    chirality parentRepresentative

def harmonicCriticalTransition
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  unlabeledAggregatedCausalEdgeAmplitude
      (interactingChiralCausalEdgeAmplitude
        (harmonicCriticalPairCoupling n) chirality) parent child /
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (harmonicCriticalPairCoupling n) chirality) parent

theorem harmonicCriticalTransition_sum_one
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    ∑ child : UnlabeledCardinalCausalOrder (n + 1),
      harmonicCriticalTransition chirality parent child = 1 := by
  classical
  simp only [harmonicCriticalTransition, ← Finset.sum_div]
  rw [sum_unlabeledAggregatedCausalEdgeAmplitude,
    div_self (harmonicCritical_unlabeled_partition_ne_zero chirality parent)]

def harmonicCriticalCausalSetGrowthLaw (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := fun n pathPrefix child =>
    harmonicCriticalTransition chirality
      (currentUnlabeledCausalOrder n pathPrefix) child
  normalized := fun _n pathPrefix =>
    harmonicCriticalTransition_sum_one chirality
      (currentUnlabeledCausalOrder _ pathPrefix)

theorem harmonicCriticalGrowth_projective_stronglyPositive
    (chirality : Fin 2) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (harmonicCriticalCausalSetGrowthLaw chirality) n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          growthEventDecoherence
              (finiteRankedDepthDecoherence
                (harmonicCriticalCausalSetGrowthLaw chirality) (n + 1))
              (refineRankedGrowthEvent event₁)
              (refineRankedGrowthEvent event₂) =
            growthEventDecoherence
              (finiteRankedDepthDecoherence
                (harmonicCriticalCausalSetGrowthLaw chirality) n)
              event₁ event₂)
      ∧ IsHermitianGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (harmonicCriticalCausalSetGrowthLaw chirality))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (harmonicCriticalCausalSetGrowthLaw chirality))
      ∧ infiniteRankedCylinderDecoherence
          (harmonicCriticalCausalSetGrowthLaw chirality)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1 :=
  normalized_stronglyPositive_infiniteRankedCylinder_family
    (harmonicCriticalCausalSetGrowthLaw chirality)

/-- Capstone: one explicit rational law simultaneously avoids every finite
partition zero and preserves nonzero coherently aggregated unlabeled antichain
competition in the large-rank limit. -/
theorem multiplicityCorrectedCriticalGrowth_capstone (chirality : Fin 2) :
    (∀ n : ℕ, ∀ parent : CardinalCausalOrder n,
      causalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude
          (harmonicCriticalPairCoupling n) chirality) parent ≠ 0)
      ∧ Tendsto harmonicCriticalPairCoupling atTop (nhds 1)
      ∧ Tendsto harmonicCriticalBornRatio atTop
          (nhds (Real.exp (-2 * Real.eulerMascheroniConstant)))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (harmonicCriticalCausalSetGrowthLaw chirality)) := by
  exact ⟨fun _n parent =>
      harmonicCritical_interactingChiral_partition_ne_zero chirality parent,
    harmonicCriticalPairCoupling_tendsto_one,
    harmonicCriticalBornRatio_tendsto,
    (harmonicCriticalGrowth_projective_stronglyPositive chirality).2.2.2.1⟩

#print axioms UnifiedTheory.Audit.KFCausalSetCriticalMultiplicity.antichainPrecursorSector_card
#print axioms harmonicCritical_parentPolynomial_eval_ne_zero
#print axioms harmonicCriticalBornRatio_eq_coherentSectorRatio
#print axioms harmonicCriticalBornRatio_tendsto
#print axioms harmonicCriticalGrowth_projective_stronglyPositive
#print axioms multiplicityCorrectedCriticalGrowth_capstone

end

end UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
