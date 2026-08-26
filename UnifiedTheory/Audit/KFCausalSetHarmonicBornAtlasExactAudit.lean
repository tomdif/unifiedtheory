/-
  Audit/KFCausalSetHarmonicBornAtlasExactAudit.lean

  Exact arithmetic audit for the positive-radial harmonic Born shell.

  The finite rank-2-through-139 rational-numerator inequality is discharged
  by `native_decide`.  Consequently its proof footprint includes
  `Lean.ofReduceBool` / `Lean.trustCompiler`; the mathematical reduction around
  that finite computation is kernel checked and no custom axiom is added.
-/

import UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection
import UnifiedTheory.Audit.KFCausalSetActionNeutralExtension
import UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit

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

/-! ## 1. The missing imaginary parent polynomial -/

/-- Integer polynomial whose evaluation is the imaginary coordinate of the
positive-chirality parent partition. -/
def interactingChiralImagPartitionPolynomial {n : ℕ}
    (parent : CardinalCausalOrder n) : ℤ[X] :=
  ∑ past : CausalPastSet parent,
    C (gaussianIPow past.maximalCount).2 *
      X ^ ancestorPairExponent past.ancestorCount

/-- Exact evaluation formula for the positive-chirality imaginary parent
partition. -/
theorem interactingChiral_partition_im_eq_imagPolynomial_eval_zeroChirality
    {n : ℕ} (lambda : ℝ) (parent : CardinalCausalOrder n) :
    (causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude lambda (0 : Fin 2)) parent).im =
      (interactingChiralImagPartitionPolynomial parent).eval₂
        (Int.castRingHom ℝ) lambda := by
  classical
  unfold causalEdgeAmplitudePartition
  change Complex.imAddGroupHom
      (∑ past : CausalPastSet parent,
        (interactingChiralCausalEdgeAmplitude lambda (0 : Fin 2)).amplitude
          parent past) = _
  rw [map_sum]
  change (∑ past : CausalPastSet parent,
    ((interactingChiralCausalEdgeAmplitude lambda (0 : Fin 2)).amplitude
      parent past).im) = _
  simp only [interactingChiralCausalEdgeAmplitude,
    rideoutSorkinSignatureAmplitude, interactingChiralSignatureWeight,
    chiralGaussianPower, if_true]
  unfold interactingChiralImagPartitionPolynomial
  change (∑ past : CausalPastSet parent,
      (((lambda : ℂ) ^ ancestorPairExponent past.ancestorCount *
        gaussianToComplex (gaussianIPow past.maximalCount)).im)) =
    (Polynomial.eval₂RingHom (Int.castRingHom ℝ) lambda)
      (∑ past : CausalPastSet parent,
        C (gaussianIPow past.maximalCount).2 *
          X ^ ancestorPairExponent past.ancestorCount)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro past _hPast
  simp only [map_mul]
  have hRealPow : ((lambda : ℂ) ^
      ancestorPairExponent past.ancestorCount).re =
      lambda ^ ancestorPairExponent past.ancestorCount := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hImagPow : ((lambda : ℂ) ^
      ancestorPairExponent past.ancestorCount).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hGaussianRe :
      (gaussianToComplex (gaussianIPow past.maximalCount)).re =
        ((gaussianIPow past.maximalCount).1 : ℝ) := by
    simp [gaussianToComplex, Complex.mul_re]
  have hGaussianIm :
      (gaussianToComplex (gaussianIPow past.maximalCount)).im =
        ((gaussianIPow past.maximalCount).2 : ℝ) := by
    simp [gaussianToComplex, Complex.mul_im]
  have hCoefficient :
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) lambda)
          (C (gaussianIPow past.maximalCount).2) =
        ((gaussianIPow past.maximalCount).2 : ℝ) := by
    change Polynomial.eval₂ (Int.castRingHom ℝ) lambda
      (C (gaussianIPow past.maximalCount).2) = _
    rw [eval₂_C]
    rfl
  have hPower :
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) lambda)
          (X ^ ancestorPairExponent past.ancestorCount) =
        lambda ^ ancestorPairExponent past.ancestorCount := by
    change Polynomial.eval₂ (Int.castRingHom ℝ) lambda
      (X ^ ancestorPairExponent past.ancestorCount) = _
    simp
  rw [hCoefficient, hPower]
  rw [Complex.mul_im, hRealPow, hImagPow, hGaussianRe, hGaussianIm]
  ring

/-- A singleton supported on a minimal event is a causal past set. -/
def minimalSingletonCausalPastSet {n : ℕ}
    (parent : CardinalCausalOrder n) (x : Fin n)
    (hx : IsMinimalIn parent x) : CausalPastSet parent where
  mem := fun y => decide (y = x)
  downwardClosed := by
    intro y z hy hz
    rw [decide_eq_true_eq] at hy ⊢
    subst y
    exact hx z hz

@[simp]
theorem minimalSingletonCausalPastSet_ancestorCount {n : ℕ}
    (parent : CardinalCausalOrder n) (x : Fin n)
    (hx : IsMinimalIn parent x) :
    (minimalSingletonCausalPastSet parent x hx).ancestorCount = 1 := by
  unfold CausalPastSet.ancestorCount
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro first second
    apply Subtype.ext
    have hFirst : first.val = x := by
      simpa [minimalSingletonCausalPastSet] using first.property
    have hSecond : second.val = x := by
      simpa [minimalSingletonCausalPastSet] using second.property
    exact hFirst.trans hSecond.symm
  · exact ⟨⟨x, by simp [minimalSingletonCausalPastSet]⟩⟩

/-- Every precursor contributes a nonnegative constant coefficient to the
imaginary parent polynomial.  It contributes one exactly at one ancestor. -/
theorem imagPrecursorMonomial_coeff_zero_nonneg {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    0 ≤ (C (gaussianIPow past.maximalCount).2 *
      X ^ ancestorPairExponent past.ancestorCount : ℤ[X]).coeff 0 := by
  rw [coeff_C_mul_X_pow]
  split_ifs with hExponent
  · have hCount : past.ancestorCount = 0 ∨ past.ancestorCount = 1 := by
      unfold ancestorPairExponent at hExponent
      rcases Nat.mul_eq_zero.mp hExponent.symm with hZero | hPredZero
      · exact Or.inl hZero
      · have hCountLeOne : past.ancestorCount ≤ 1 :=
          Nat.sub_eq_zero_iff_le.mp hPredZero
        by_cases hZero : past.ancestorCount = 0
        · exact Or.inl hZero
        · exact Or.inr (by omega)
    rcases hCount with hZero | hOne
    · have hPast : past = emptyCausalPastSet parent :=
        (ancestorCount_eq_zero_iff_empty past).mp hZero
      subst past
      simp [gaussianIPow]
    · rw [maximalCount_eq_one_of_ancestorCount_eq_one past hOne]
      simp [gaussianIPow, gaussianMulI]
  · simp

/-- Every nonempty causal parent has strictly positive constant coefficient
in its imaginary partition polynomial. -/
theorem interactingChiralImagPartitionPolynomial_coeff_zero_pos
    {n : ℕ} (hn : 0 < n) (parent : CardinalCausalOrder n) :
    0 < (interactingChiralImagPartitionPolynomial parent).coeff 0 := by
  classical
  cases n with
  | zero => omega
  | succ k =>
      obtain ⟨x, hx⟩ := exists_minimal parent
      unfold interactingChiralImagPartitionPolynomial
      rw [finset_sum_coeff]
      apply Finset.sum_pos'
      · intro past _hPast
        exact imagPrecursorMonomial_coeff_zero_nonneg past
      · refine ⟨minimalSingletonCausalPastSet parent x hx,
          Finset.mem_univ _, ?_⟩
        rw [coeff_C_mul_X_pow]
        have hAncestor :
            (minimalSingletonCausalPastSet parent x hx).ancestorCount = 1 :=
          minimalSingletonCausalPastSet_ancestorCount parent x hx
        have hMaximal :
            (minimalSingletonCausalPastSet parent x hx).maximalCount = 1 :=
          maximalCount_eq_one_of_ancestorCount_eq_one
            (minimalSingletonCausalPastSet parent x hx) hAncestor
        simp [hAncestor, hMaximal, ancestorPairExponent, gaussianIPow,
          gaussianMulI]

/-- One imaginary precursor monomial has coefficient height at most one. -/
theorem imagPrecursorMonomial_coeff_natAbs_le_one {n k : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    Int.natAbs
        ((C (gaussianIPow past.maximalCount).2 *
          X ^ ancestorPairExponent past.ancestorCount : ℤ[X]).coeff k) ≤ 1 := by
  rw [coeff_C_mul_X_pow]
  split_ifs
  · exact (gaussianIPow_coordinates_natAbs_le_one past.maximalCount).2
  · simp

set_option maxHeartbeats 800000 in
-- The finite-sum coefficient estimate needs a larger elaboration budget.
theorem interactingChiralImagPartitionPolynomial_coeff_natAbs_le_two_pow
    {n k : ℕ} (parent : CardinalCausalOrder n) :
    Int.natAbs
        ((interactingChiralImagPartitionPolynomial parent).coeff k) ≤
      2 ^ n := by
  classical
  unfold interactingChiralImagPartitionPolynomial
  rw [finset_sum_coeff]
  calc
    Int.natAbs
        (∑ past : CausalPastSet parent,
          (C (gaussianIPow past.maximalCount).2 *
            X ^ ancestorPairExponent past.ancestorCount : ℤ[X]).coeff k) ≤
        ∑ past : CausalPastSet parent,
          Int.natAbs
            ((C (gaussianIPow past.maximalCount).2 *
              X ^ ancestorPairExponent past.ancestorCount : ℤ[X]).coeff k) :=
      int_natAbs_finset_sum_le_sum_natAbs Finset.univ _
    _ ≤ ∑ _past : CausalPastSet parent, 1 := by
      apply Finset.sum_le_sum
      intro past _hPast
      exact imagPrecursorMonomial_coeff_natAbs_le_one past
    _ = Fintype.card (CausalPastSet parent) := by simp
    _ ≤ 2 ^ n := causalPastSet_card_le_two_pow parent

/-- At ranks 2 through 139, the reduced numerator of the harmonic coupling is
larger than the complete Boolean precursor carrier. -/
theorem harmonicCriticalPairCouplingQ_num_natAbs_gt_two_pow_below_140 :
    ∀ n : Fin 140, 1 < n.1 →
      2 ^ n.1 < (harmonicCriticalPairCouplingQ n.1).num.natAbs := by
  native_decide

/-- Mathlib's noncomputable fraction-ring numerator differs from the
computable canonical rational numerator by at most the integer unit sign. -/
theorem harmonicCriticalPairCouplingQ_isFractionRing_num_natAbs (n : ℕ) :
    Int.natAbs (IsFractionRing.num ℤ (harmonicCriticalPairCouplingQ n)) =
      (harmonicCriticalPairCouplingQ n).num.natAbs := by
  simpa [Int.associated_iff_natAbs] using
    (harmonicCriticalPairCouplingQ n).isFractionRingNum

/-- The imaginary parent partition cannot vanish at the harmonic coupling at
ranks 2 through 139.  The proof combines the rational-root divisor theorem
with the executable numerator bound above. -/
theorem harmonicCritical_parentImagPolynomial_eval_ne_zero_below_140
    {n : ℕ} (hn : 1 < n) (hRank : n < 140)
    (parent : CardinalCausalOrder n) :
    (interactingChiralImagPartitionPolynomial parent).eval₂
      (Int.castRingHom ℝ) (harmonicCriticalPairCouplingQ n : ℝ) ≠ 0 := by
  intro hEvaluation
  have hRoot : Polynomial.aeval (harmonicCriticalPairCouplingQ n)
      (interactingChiralImagPartitionPolynomial parent) = 0 :=
    aeval_eq_zero_of_real_eval₂_eq_zero hEvaluation
  have hDivides : IsFractionRing.num ℤ (harmonicCriticalPairCouplingQ n) ∣
      (interactingChiralImagPartitionPolynomial parent).coeff 0 :=
    num_dvd_of_is_root hRoot
  have hConstantNe :
      (interactingChiralImagPartitionPolynomial parent).coeff 0 ≠ 0 :=
    ne_of_gt (interactingChiralImagPartitionPolynomial_coeff_zero_pos
      (lt_trans Nat.zero_lt_one hn) parent)
  have hDivisorBound := Int.natAbs_le_of_dvd_ne_zero hDivides hConstantNe
  have hCoefficientBound :=
    interactingChiralImagPartitionPolynomial_coeff_natAbs_le_two_pow
      (k := 0) parent
  have hNumeratorBound :
      2 ^ n < Int.natAbs
        (IsFractionRing.num ℤ (harmonicCriticalPairCouplingQ n)) := by
    rw [harmonicCriticalPairCouplingQ_isFractionRing_num_natAbs]
    exact harmonicCriticalPairCouplingQ_num_natAbs_gt_two_pow_below_140
      ⟨n, hRank⟩ hn
  exact (not_lt_of_ge (hDivisorBound.trans hCoefficientBound))
    hNumeratorBound

/-! ## 2. Both parent coordinates protect every raw edge -/

/-- Every Gaussian power lies on one of the two coordinate axes. -/
theorem gaussianIPow_first_eq_zero_or_second_eq_zero (m : ℕ) :
    (gaussianIPow m).1 = 0 ∨ (gaussianIPow m).2 = 0 := by
  induction m with
  | zero => exact Or.inr rfl
  | succ m ih =>
      rcases ih with hFirst | hSecond
      · right
        simpa [gaussianIPow, gaussianMulI] using hFirst
      · left
        simp [gaussianIPow, gaussianMulI, hSecond]

/-- A positive-chirality microscopic signature amplitude is purely real or
purely imaginary. -/
theorem interactingChiralSignatureWeight_zeroChirality_axis
    (lambda : ℝ) (omega maximal : ℕ) :
    (interactingChiralSignatureWeight lambda (0 : Fin 2)
        omega maximal).re = 0 ∨
      (interactingChiralSignatureWeight lambda (0 : Fin 2)
        omega maximal).im = 0 := by
  have hRealPow : ((lambda : ℂ) ^ ancestorPairExponent omega).re =
      lambda ^ ancestorPairExponent omega := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hImagPow : ((lambda : ℂ) ^ ancestorPairExponent omega).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hGaussianRe :
      (gaussianToComplex (gaussianIPow maximal)).re =
        ((gaussianIPow maximal).1 : ℝ) := by
    simp [gaussianToComplex, Complex.mul_re]
  have hGaussianIm :
      (gaussianToComplex (gaussianIPow maximal)).im =
        ((gaussianIPow maximal).2 : ℝ) := by
    simp [gaussianToComplex, Complex.mul_im]
  rcases gaussianIPow_first_eq_zero_or_second_eq_zero maximal with
      hFirst | hSecond
  · left
    simp only [interactingChiralSignatureWeight]
    rw [show chiralGaussianPower (0 : Fin 2) maximal =
        gaussianToComplex (gaussianIPow maximal) by
      simp [chiralGaussianPower]]
    rw [Complex.mul_re, hRealPow, hImagPow, hGaussianRe, hGaussianIm,
      hFirst]
    ring
  · right
    simp only [interactingChiralSignatureWeight]
    rw [show chiralGaussianPower (0 : Fin 2) maximal =
        gaussianToComplex (gaussianIPow maximal) by
      simp [chiralGaussianPower]]
    rw [Complex.mul_im, hRealPow, hImagPow, hGaussianRe, hGaussianIm,
      hSecond]
    ring

/-- Signature rigidity makes every represented coherent transition numerator
axis-aligned as well. -/
theorem labeledAggregatedHarmonicAmplitude_at_target_axis {n : ℕ}
    (parent : CardinalCausalOrder n) (base : CausalPastSet parent) :
    (labeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude
          (harmonicCriticalPairCoupling n) (0 : Fin 2))
        parent (causalTransitionTarget parent base)).re = 0 ∨
      (labeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude
          (harmonicCriticalPairCoupling n) (0 : Fin 2))
        parent (causalTransitionTarget parent base)).im = 0 := by
  rw [labeledAggregatedInteractingChiralAmplitude_at_target]
  rcases interactingChiralSignatureWeight_zeroChirality_axis
      (harmonicCriticalPairCoupling n) base.ancestorCount base.maximalCount with
      hReal | hImag
  · left
    simp [Complex.mul_re, hReal]
  · right
    simp [Complex.mul_im, hImag]

/-- Dividing a nonzero axis-aligned numerator by a denominator with two
nonzero coordinates necessarily creates a nonzero imaginary coordinate. -/
theorem complex_div_im_ne_zero_of_axis
    (numerator denominator : ℂ)
    (hNumerator : numerator ≠ 0)
    (hDenominatorRe : denominator.re ≠ 0)
    (hDenominatorIm : denominator.im ≠ 0)
    (hAxis : numerator.re = 0 ∨ numerator.im = 0) :
    (numerator / denominator).im ≠ 0 := by
  have hDenominator : denominator ≠ 0 := by
    intro hZero
    apply hDenominatorRe
    rw [hZero]
    rfl
  have hNormSq : Complex.normSq denominator ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp hDenominator
  rw [Complex.div_im]
  rcases hAxis with hReal | hImag
  · have hNumeratorIm : numerator.im ≠ 0 := by
      intro hZero
      apply hNumerator
      apply Complex.ext <;> assumption
    rw [hReal, zero_mul, zero_div, sub_zero]
    exact div_ne_zero (mul_ne_zero hNumeratorIm hDenominatorRe) hNormSq
  · have hNumeratorRe : numerator.re ≠ 0 := by
      intro hZero
      apply hNumerator
      apply Complex.ext <;> assumption
    rw [hImag, zero_mul, zero_div, zero_sub]
    exact neg_ne_zero.mpr
      (div_ne_zero (mul_ne_zero hNumeratorRe hDenominatorIm) hNormSq)

/-- Every physical raw harmonic transition at ranks 2 through 139 has nonzero
imaginary coordinate.  This is stronger than the atlas-only target. -/
theorem harmonicCriticalTransition_im_ne_zero_of_physical_below_140
    {n : ℕ} (hn : 1 < n) (hRank : n < 140)
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (hPhysical : IsUnlabeledOneElementExtension parent child) :
    (harmonicCriticalTransition (0 : Fin 2) parent child).im ≠ 0 := by
  refine Quotient.inductionOn parent ?_ hPhysical
  intro parentRep hPhysicalRep
  have hMultiplicity :
      0 < labeledCausalTransitionMultiplicity parentRep child :=
    (labeledCausalTransitionMultiplicity_pos_iff parentRep child).2
      hPhysicalRep
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
        (ne_of_gt (lt_trans zero_lt_one
          (harmonicCriticalPairCoupling_gt_one n)))
        (0 : Fin 2) parentRep base.val
  · dsimp [denominator]
    rw [interactingChiral_partition_re_eq_polynomial_eval]
    exact harmonicCritical_parentPolynomial_eval_ne_zero parentRep
  · dsimp [denominator]
    rw [interactingChiral_partition_im_eq_imagPolynomial_eval_zeroChirality]
    simpa [harmonicCriticalPairCoupling] using
      harmonicCritical_parentImagPolynomial_eval_ne_zero_below_140
        hn hRank parentRep
  · dsimp [numerator]
    simpa [← base.property] using
      labeledAggregatedHarmonicAmplitude_at_target_axis parentRep base.val

/-! ## 3. Close the canonical positive-radial atlas target -/

/-- At rank one the canonical radial correction is the identity, so both
physical branches retain the raw law's exact support. -/
theorem canonicalHarmonicBornShellTransition_rankOne_ne_zero_of_physical
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (child : CausalSetGrowthBranch 1)
    (hPhysical : IsPhysicalCausalGrowthStep 1 pathPrefix child) :
    (canonicalHarmonicCriticalBornShellGrowthLaw (0 : Fin 2)).transition
        1 pathPrefix child ≠ 0 := by
  change (canonicalHarmonicBornNormalizedGrowthLaw (0 : Fin 2)).transition
    1 pathPrefix child ≠ 0
  rw [canonicalHarmonicBorn_rankOne_transition_eq_raw]
  exact (harmonicTransition_ne_zero_iff_physical
    (0 : Fin 2) 1 pathPrefix child).2 hPhysical

/-- The canonical radial Born correction preserves every physical transition
at ranks 2 through 139. -/
theorem canonicalHarmonicBornShellTransition_ne_zero_of_physical_below_140
    {n : ℕ} (hn : 1 < n) (hRank : n < 140)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hPhysical : IsPhysicalCausalGrowthStep n pathPrefix child) :
    (canonicalHarmonicCriticalBornShellGrowthLaw (0 : Fin 2)).transition
        n pathPrefix child ≠ 0 := by
  apply canonicalHarmonicBornShellTransition_ne_zero_of_raw_im_ne_zero
      (0 : Fin 2) (lt_trans Nat.zero_lt_one hn) pathPrefix child hPhysical
  change (harmonicCriticalTransition (0 : Fin 2)
    (currentUnlabeledCausalOrder n pathPrefix) child).im ≠ 0
  exact harmonicCriticalTransition_im_ne_zero_of_physical_below_140
    hn hRank (currentUnlabeledCausalOrder n pathPrefix) child hPhysical

/-- Exact discharge of the formerly open 140-edge positive-radial atlas
certificate in the positive chiral sector. -/
theorem harmonicBornShellAtlasTransitionNonzero_zero :
    HarmonicBornShellAtlasTransitionNonzero (0 : Fin 2) := by
  intro n hnext
  by_cases hn : n = 0
  · subst n
    rw [canonicalHarmonicBornShellTransition_rankZero_eq_one]
    norm_num
  · by_cases hnOne : n = 1
    · subst n
      exact canonicalHarmonicBornShellTransition_rankOne_ne_zero_of_physical
        (atlasStepPrefix 1 hnext) (atlasStepChild 1 hnext)
        (atlasStep_isPhysical 1 hnext)
    · exact canonicalHarmonicBornShellTransition_ne_zero_of_physical_below_140
        (by omega) (by omega)
        (atlasStepPrefix n hnext) (atlasStepChild n hnext)
        (atlasStep_isPhysical n hnext)

/-- Reflection closes the opposite chiral sector without a second audit. -/
theorem harmonicBornShellAtlasTransitionNonzero_one :
    HarmonicBornShellAtlasTransitionNonzero (1 : Fin 2) :=
  harmonicBornShellAtlasTransitionNonzero_one_of_zero
    harmonicBornShellAtlasTransitionNonzero_zero

/-- The canonical positive-radial harmonic Born shell now realizes the full
displayed CSpec atlas in either chiral sector. -/
theorem gate1HarmonicBornShellAtlasRealization_closed
    (chirality : Fin 2) :
    Gate1HarmonicBornShellAtlasRealizationClosed chirality := by
  fin_cases chirality
  · exact gate1HarmonicBornShellAtlasRealization_closed_of_transition_nonzero
      0 harmonicBornShellAtlasTransitionNonzero_zero
  · exact gate1HarmonicBornShellAtlasRealization_closed_of_transition_nonzero
      1 harmonicBornShellAtlasTransitionNonzero_one

end

end UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit
