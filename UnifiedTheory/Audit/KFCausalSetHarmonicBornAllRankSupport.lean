/-
  All-rank exact support for the canonical positive-radial harmonic Born law.

  The imaginary partition's constant coefficient counts singleton precursors,
  hence is at most the parent rank. The harmonic coupling's reduced numerator
  exceeds that rank by the classical 2-adic valuation of harmonic numbers.
  Rational-root divisibility therefore excludes imaginary cancellation at
  every rank, without an enumerated rank cutoff or a new phase convention.
-/

import UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit
import UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
import Mathlib.NumberTheory.Harmonic.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetHarmonicBornAllRankSupport

noncomputable section

open scoped BigOperators
open Polynomial
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetChiralDynamics
open UnifiedTheory.Audit.KFCausalSetCriticalRunning
open UnifiedTheory.Audit.KFCausalSetRationalCriticalRunning
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetActionNeutralExtension
open UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
open UnifiedTheory.Audit.KFCausalTransitionFiberSignature
open UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection
open UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit

/-- The harmonic coupling has a denominator divisible by a power of two
strictly larger than the parent rank. -/
theorem harmonicCriticalPairCouplingQ_den_gt_rank
    {n : ℕ} (hn : 1 < n) : n < (harmonicCriticalPairCouplingQ n).den := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnQ : (1 : ℚ) < n := by exact_mod_cast hn
  have hH : harmonic n ≠ 0 := ne_of_gt (harmonic_pos (by omega))
  have hN : (n : ℚ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hnQ)
  have hD : (2 : ℚ) * (n - 1) ≠ 0 := mul_ne_zero (by norm_num) hN
  have hTwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have hCast : (n : ℚ) - 1 = ((n - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hV : padicValRat 2 (harmonic n / (2 * (n - 1))) =
      -(Nat.log 2 n : ℤ) - (1 + (padicValNat 2 (n - 1) : ℤ)) := by
    rw [padicValRat.div hH hD, padicValRat_two_harmonic,
      padicValRat.mul (by norm_num) hN, hCast, padicValRat.of_nat]
    rw [hTwo]
  have hVneg : padicValRat 2 (harmonic n / (2 * (n - 1))) < 0 := by
    rw [hV]
    omega
  have hQ : harmonicCriticalPairCouplingQ n ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one (harmonicCriticalPairCouplingQ_gt_one n))
  have hCouplingV : padicValRat 2 (harmonicCriticalPairCouplingQ n) =
      -(Nat.log 2 n : ℤ) - (1 + (padicValNat 2 (n - 1) : ℤ)) := by
    unfold harmonicCriticalPairCouplingQ at hQ ⊢
    rw [if_neg (by omega : ¬ n ≤ 1)] at hQ ⊢
    rw [padicValRat.add_eq_min hQ (by norm_num) (div_ne_zero hH hD)
      (by simpa using ne_of_gt hVneg), padicValRat.one,
      min_eq_right (le_of_lt hVneg), hV]
  have hDenVal : Nat.log 2 n + 1 ≤
      padicValNat 2 (harmonicCriticalPairCouplingQ n).den := by
    rw [padicValRat] at hCouplingV
    unfold padicValInt at hCouplingV
    omega
  have hPow : 2 ^ (Nat.log 2 n + 1) ≤
      (harmonicCriticalPairCouplingQ n).den := by
    exact Nat.le_of_dvd (harmonicCriticalPairCouplingQ n).den_pos
      ((pow_dvd_pow 2 hDenVal).trans pow_padicValNat_dvd)
  exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).trans_le hPow

/-- The reduced numerator beats the sharp constant-coefficient bound at
every rank, replacing the previous finite `2^n` computation. -/
theorem harmonicCriticalPairCouplingQ_num_natAbs_gt_rank
    {n : ℕ} (hn : 1 < n) : n < (harmonicCriticalPairCouplingQ n).num.natAbs := by
  let q := harmonicCriticalPairCouplingQ n
  have hOne : (1 : ℚ) < q := harmonicCriticalPairCouplingQ_gt_one n
  have hDenPos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hNum : (q.den : ℚ) < q.num := by
    have := (lt_div_iff₀ hDenPos).mp (q.num_div_den.symm ▸ hOne)
    simpa using this
  have hNumInt : (q.den : ℤ) < q.num := by exact_mod_cast hNum
  have hAbs : q.den < q.num.natAbs := by
    have hNonneg : 0 ≤ q.num := le_trans (by positivity : (0 : ℤ) ≤ q.den) hNumInt.le
    exact_mod_cast (show (q.den : ℤ) < (q.num.natAbs : ℤ) by
      simpa [Int.natAbs_of_nonneg hNonneg] using hNumInt)
  exact (harmonicCriticalPairCouplingQ_den_gt_rank hn).trans hAbs

/-- Only singleton precursors contribute to the imaginary constant term. -/
theorem imagPrecursorMonomial_coeff_zero_eq_indicator
    {n : ℕ} {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    (C (gaussianIPow past.maximalCount).2 *
      X ^ ancestorPairExponent past.ancestorCount : ℤ[X]).coeff 0 =
        if past.ancestorCount = 1 then 1 else 0 := by
  classical
  by_cases hOne : past.ancestorCount = 1
  · simp [hOne, maximalCount_eq_one_of_ancestorCount_eq_one past hOne,
      ancestorPairExponent, gaussianIPow, gaussianMulI]
  · rw [if_neg hOne, coeff_C_mul_X_pow]
    split_ifs with hExp
    · have hZero : past.ancestorCount = 0 := by
        unfold ancestorPairExponent at hExp
        rcases Nat.mul_eq_zero.mp hExp.symm with h | h
        · exact h
        · omega
      have hPast := (ancestorCount_eq_zero_iff_empty past).mp hZero
      subst past
      simp [gaussianIPow]
    · rfl

/-- A one-ancestor precursor is determined by its unique member. -/
theorem singletonCausalPastSet_card_le_rank
    {n : ℕ} (parent : CardinalCausalOrder n) :
    Fintype.card {past : CausalPastSet parent // past.ancestorCount = 1} ≤ n := by
  classical
  let S := {past : CausalPastSet parent // past.ancestorCount = 1}
  have hUnique (s : S) : ∃ x : {i : Fin n // s.val.mem i = true},
      ∀ y, y = x := Nat.card_eq_one_iff_exists.mp s.property
  let representative (s : S) : Fin n := (Classical.choose (hUnique s)).val
  have hMem (s : S) (i : Fin n) : s.val.mem i = true ↔ i = representative s := by
    constructor
    · intro hi
      exact congrArg Subtype.val (Classical.choose_spec (hUnique s) ⟨i, hi⟩)
    · rintro rfl
      exact (Classical.choose (hUnique s)).property
  have hInjective : Function.Injective representative := by
    intro a b hab
    apply Subtype.ext
    apply CausalPastSet.ext
    funext i
    have hIff : a.val.mem i = true ↔ b.val.mem i = true := by
      rw [hMem a i, hMem b i, hab]
    cases ha : a.val.mem i <;> cases hb : b.val.mem i <;> simp_all
  simpa [S] using Fintype.card_le_of_injective representative hInjective

/-- The sharp constant-coefficient bound is linear in rank, rather than
the exponential bound needed for arbitrary polynomial coefficients. -/
theorem interactingChiralImagPartitionPolynomial_coeff_zero_le_rank
    {n : ℕ} (parent : CardinalCausalOrder n) :
    (interactingChiralImagPartitionPolynomial parent).coeff 0 ≤ (n : ℤ) := by
  classical
  have hCount : (interactingChiralImagPartitionPolynomial parent).coeff 0 =
      (Fintype.card {past : CausalPastSet parent // past.ancestorCount = 1} : ℤ) := by
    unfold interactingChiralImagPartitionPolynomial
    rw [finset_sum_coeff]
    simp_rw [imagPrecursorMonomial_coeff_zero_eq_indicator]
    simp [Fintype.card_subtype]
  rw [hCount]
  exact_mod_cast singletonCausalPastSet_card_le_rank parent

/-- At every nontrivial rank, rational-root divisibility would force the
coupling numerator to divide a positive integer no larger than the rank. -/
theorem harmonicCritical_parentImagPolynomial_eval_ne_zero
    {n : ℕ} (hn : 1 < n) (parent : CardinalCausalOrder n) :
    (interactingChiralImagPartitionPolynomial parent).eval₂
      (Int.castRingHom ℝ) (harmonicCriticalPairCouplingQ n : ℝ) ≠ 0 := by
  intro hEvaluation
  have hRoot : Polynomial.aeval (harmonicCriticalPairCouplingQ n)
      (interactingChiralImagPartitionPolynomial parent) = 0 :=
    aeval_eq_zero_of_real_eval₂_eq_zero hEvaluation
  have hDivides : IsFractionRing.num ℤ (harmonicCriticalPairCouplingQ n) ∣
      (interactingChiralImagPartitionPolynomial parent).coeff 0 :=
    num_dvd_of_is_root hRoot
  have hPositive := interactingChiralImagPartitionPolynomial_coeff_zero_pos
    (by omega : 0 < n) parent
  have hBound := Int.natAbs_le_of_dvd_ne_zero hDivides (ne_of_gt hPositive)
  rw [harmonicCriticalPairCouplingQ_isFractionRing_num_natAbs] at hBound
  have hCoefficientBound :
      ((interactingChiralImagPartitionPolynomial parent).coeff 0).natAbs ≤ n := by
    exact_mod_cast (show
        ((((interactingChiralImagPartitionPolynomial parent).coeff 0).natAbs : ℕ) : ℤ) ≤
          (n : ℤ) by
      rw [Int.natAbs_of_nonneg hPositive.le]
      exact interactingChiralImagPartitionPolynomial_coeff_zero_le_rank parent)
  exact (not_lt_of_ge (hBound.trans hCoefficientBound))
    (harmonicCriticalPairCouplingQ_num_natAbs_gt_rank hn)

/-- Both coordinates of the partition are nonzero, while every physical
transition numerator lies on a coordinate axis. Division makes its imaginary
coordinate nonzero, protecting it against the real radial correction. -/
theorem harmonicCriticalTransition_im_ne_zero_of_physical
    {n : ℕ} (hn : 1 < n)
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (hPhysical : IsUnlabeledOneElementExtension parent child) :
    (harmonicCriticalTransition (0 : Fin 2) parent child).im ≠ 0 := by
  refine Quotient.inductionOn parent ?_ hPhysical
  intro parentRep hPhysicalRep
  have hMultiplicity :
      0 < labeledCausalTransitionMultiplicity parentRep child :=
    (labeledCausalTransitionMultiplicity_pos_iff parentRep child).2 hPhysicalRep
  obtain ⟨base⟩ := Fintype.card_pos_iff.mp hMultiplicity
  let numerator := labeledAggregatedCausalEdgeAmplitude
    (interactingChiralCausalEdgeAmplitude
      (harmonicCriticalPairCoupling n) (0 : Fin 2)) parentRep child
  let denominator := causalEdgeAmplitudePartition
    (interactingChiralCausalEdgeAmplitude
      (harmonicCriticalPairCoupling n) (0 : Fin 2)) parentRep
  change (numerator / denominator).im ≠ 0
  apply complex_div_im_ne_zero_of_axis numerator denominator
  · dsimp [numerator]
    simpa [← base.property] using
      labeledAggregatedInteractingChiralAmplitude_at_target_ne_zero
        (ne_of_gt (lt_trans zero_lt_one (harmonicCriticalPairCoupling_gt_one n)))
        (0 : Fin 2) parentRep base.val
  · dsimp [denominator]
    rw [interactingChiral_partition_re_eq_polynomial_eval]
    exact harmonicCritical_parentPolynomial_eval_ne_zero parentRep
  · dsimp [denominator]
    rw [interactingChiral_partition_im_eq_imagPolynomial_eval_zeroChirality]
    exact harmonicCritical_parentImagPolynomial_eval_ne_zero hn parentRep
  · dsimp [numerator]
    simpa [← base.property] using
      labeledAggregatedHarmonicAmplitude_at_target_axis parentRep base.val

/-- All-rank exact physical support for the existing canonical positive-radial
representative, in both chiralities. No alternate phase selector is required. -/
theorem canonicalHarmonicBornShellTransition_ne_zero_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
          n pathPrefix child ≠ 0 ↔
      IsPhysicalCausalGrowthStep n pathPrefix child := by
  have hPositive :
      IsPhysicalCausalGrowthStep n pathPrefix child →
        (canonicalHarmonicCriticalBornShellGrowthLaw (0 : Fin 2)).transition
            n pathPrefix child ≠ 0 := by
    intro hPhysical
    by_cases hnZero : n = 0
    · subst n
      rw [canonicalHarmonicBornShellTransition_rankZero_eq_one]
      norm_num
    · by_cases hnOne : n = 1
      · subst n
        exact canonicalHarmonicBornShellTransition_rankOne_ne_zero_of_physical
          pathPrefix child hPhysical
      · apply canonicalHarmonicBornShellTransition_ne_zero_of_raw_im_ne_zero
          (0 : Fin 2) (by omega) pathPrefix child hPhysical
        exact harmonicCriticalTransition_im_ne_zero_of_physical (by omega)
          (currentUnlabeledCausalOrder n pathPrefix) child hPhysical
  constructor
  · intro hNonzero
    by_contra hNotPhysical
    exact hNonzero
      ((gate1HarmonicBornShellLaw_closed chirality).physicalSupport
        n pathPrefix child hNotPhysical)
  · intro hPhysical
    fin_cases chirality
    · exact hPositive hPhysical
    · have hStar :
          star
              ((canonicalHarmonicCriticalBornShellGrowthLaw (0 : Fin 2)).transition
                n pathPrefix child) ≠ 0 := by
        simpa using hPositive hPhysical
      rw [star_canonicalHarmonicCriticalBornShellTransition (0 : Fin 2)] at hStar
      simpa [reflectedMicroscopicChirality] using hStar

open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure

/-- Every allowed next child has strictly positive probability in the
canonical harmonic Born transition law. -/
theorem harmonicBornStagePMF_pos_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    0 < causalBornStagePMF (canonicalHarmonicBornNormalizedGrowthLaw chirality)
        n pathPrefix child ↔ IsPhysicalCausalGrowthStep n pathPrefix child := by
  rw [causalBornStagePMF_apply, ENNReal.ofReal_pos, Complex.normSq_pos]
  exact canonicalHarmonicBornShellTransition_ne_zero_iff_physical
    chirality n pathPrefix child

theorem harmonicFiniteBornPathAmplitude_ne_zero_iff_physical
    (chirality : Fin 2) :
    ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      finiteBornPathAmplitude (canonicalHarmonicBornNormalizedGrowthLaw chirality)
          n path ≠ 0 ↔ IsPhysicalCausalGrowthPath n path
  | 0, _ => by simp [finiteBornPathAmplitude, IsPhysicalCausalGrowthPath]
  | n + 1, path => by
      change (_ * _ ≠ 0) ↔
        (IsPhysicalCausalGrowthPath n path.1 ∧
          IsPhysicalCausalGrowthStep n path.1 path.2)
      rw [mul_ne_zero_iff,
        harmonicFiniteBornPathAmplitude_ne_zero_iff_physical chirality n path.1]
      exact and_congr_right fun _ =>
        canonicalHarmonicBornShellTransition_ne_zero_iff_physical
          chirality n path.1 path.2

/-- Full support persists along every finite physical history. -/
theorem harmonicFiniteBornPathWeight_pos_iff_physical
    (chirality : Fin 2) (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n) :
    0 < finiteBornPathWeight (canonicalHarmonicBornNormalizedGrowthLaw chirality)
        n path ↔ IsPhysicalCausalGrowthPath n path := by
  rw [finiteBornPathWeight, Complex.normSq_pos]
  exact harmonicFiniteBornPathAmplitude_ne_zero_iff_physical chirality n path

/-- The existing infinite trajectory measure assigns positive mass exactly
to finite cylinders specified by physical histories. This does not assert
positive mass for singleton infinite histories. -/
theorem harmonicBornTrajectoryMeasure_finiteCylinder_pos_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i) :
    0 < (harmonicBornTrajectoryMeasure chirality).map (Preorder.frestrictLe n) {history} ↔
      IsPhysicalCausalGrowthPath (n + 1) (rankedGrowthPathOfIic n history) := by
  rw [harmonicBornTrajectoryMeasure_finiteCylinder_singleton, ENNReal.ofReal_pos]
  exact harmonicFiniteBornPathWeight_pos_iff_physical chirality (n + 1)
    (rankedGrowthPathOfIic n history)

#print axioms harmonicCriticalPairCouplingQ_num_natAbs_gt_rank
#print axioms interactingChiralImagPartitionPolynomial_coeff_zero_le_rank
#print axioms canonicalHarmonicBornShellTransition_ne_zero_iff_physical
#print axioms harmonicBornTrajectoryMeasure_finiteCylinder_pos_iff_physical

end

end UnifiedTheory.Audit.KFCausalSetHarmonicBornAllRankSupport
