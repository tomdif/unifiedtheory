/-
  Audit/KFCausalSetCriticalRunning.lean

  GENERIC ZERO-FREENESS AND A CRITICAL RUNNING TRAJECTORY

  The complete chiral law proves qualitative all-parent zero-freeness at a
  fixed transcendental square-root coupling.  This file sharpens the result
  in the two directions needed by the large-rank audit.

  First, it records effective size data for every n-event parent polynomial:

      degree P_C <= n (n - 1),
      |coeff_k P_C| <= #Past(C) <= 2^n.

  It then reverses the zero-free implication.  Any exact parent cancellation
  forces the real coupling to be algebraic.  Consequently the exceptional
  set, even after taking every finite rank and every parent, is countable.
  The precise genericity statement is therefore that exact cancellation is
  confined to a countable subset of the algebraic reals; algebraic couplings
  are not all asserted to cancel.

  Second, a fixed transcendental coupling does not address the critical
  scaling g_n -> 1 diagnosed computationally.  We construct the explicit
  Liouville-affine trajectory

      lambda_n = 1 + (L - 1)/(n + 1),   g_n = lambda_n^2,

  where L is the canonical base-two Liouville number.  Every lambda_n remains
  transcendental, hence every finite parent partition stays nonzero, while
  lambda_n -> 1, g_n -> 1, and

      (n + 1)(g_n - 1) -> 2(L - 1).

  This closes the qualitative tension between zero-freeness and critical
  running.  It deliberately does not claim a uniform lower bound on partition
  magnitude; that remaining problem is a causet-specific condition-number
  estimate, not a consequence of transcendence alone.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetCriticalRunning

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

/-! ## 1. Rank-controlled polynomial data -/

/-- A precursor cannot contain more elements than its n-event parent. -/
theorem CausalPastSet.ancestorCount_le_rank {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    past.ancestorCount ≤ n := by
  unfold CausalPastSet.ancestorCount
  simpa using
    (Finite.card_subtype_le (fun i : Fin n => past.mem i = true))

/-- The pair exponent is monotone in the ancestor count. -/
theorem ancestorPairExponent_mono {first second : ℕ}
    (h : first ≤ second) :
    ancestorPairExponent first ≤ ancestorPairExponent second := by
  rw [ancestorPairExponent_eq_twice_unordered,
    ancestorPairExponent_eq_twice_unordered]
  exact Nat.mul_le_mul_left 2 (Nat.choose_le_choose 2 h)

/-- The real partition polynomial of an n-event parent has degree at most
`n(n-1)`.  This is the exact worst-case exponent carried by the full past. -/
theorem interactingChiralRealPartitionPolynomial_natDegree_le {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (interactingChiralRealPartitionPolynomial parent).natDegree ≤
      ancestorPairExponent n := by
  classical
  unfold interactingChiralRealPartitionPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro past _hPast
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (ancestorPairExponent_mono (CausalPastSet.ancestorCount_le_rank past))

/-- Both integer coordinates of `i^m` have absolute value at most one. -/
theorem gaussianIPow_coordinates_natAbs_le_one (m : ℕ) :
    Int.natAbs (gaussianIPow m).1 ≤ 1 ∧
      Int.natAbs (gaussianIPow m).2 ≤ 1 := by
  induction m with
  | zero => simp [gaussianIPow]
  | succ m ih =>
      simp only [gaussianIPow, gaussianMulI]
      constructor
      · simpa using ih.2
      · simpa using ih.1

/-- Triangle inequality for a finite sum, stated in the natural-valued form
used by integer coefficient heights. -/
theorem int_natAbs_finset_sum_le_sum_natAbs {index : Type*}
    (s : Finset index) (f : index → ℤ) :
    Int.natAbs (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Int.natAbs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert item s hNotMem ih =>
      rw [Finset.sum_insert hNotMem, Finset.sum_insert hNotMem]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- A single precursor monomial contributes at most one in absolute value to
every coefficient. -/
theorem precursorMonomial_coeff_natAbs_le_one {n k : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    Int.natAbs
        ((C (gaussianIPow past.maximalCount).1 *
          X ^ ancestorPairExponent past.ancestorCount : ℤ[X]).coeff k) ≤ 1 := by
  rw [coeff_C_mul_X_pow]
  split_ifs
  · exact (gaussianIPow_coordinates_natAbs_le_one past.maximalCount).1
  · simp

/-- Forget the downward-closure proof and retain only the Boolean membership
code of a precursor. -/
def causalPastMembershipCode {n : ℕ} {parent : CardinalCausalOrder n} :
    CausalPastSet parent → (Fin n → Bool) :=
  fun past => past.mem

theorem causalPastMembershipCode_injective {n : ℕ}
    {parent : CardinalCausalOrder n} :
    Function.Injective (causalPastMembershipCode (parent := parent)) := by
  intro first second hCode
  apply CausalPastSet.ext
  exact hCode

/-- An n-event parent has at most `2^n` downward-closed precursor sets. -/
theorem causalPastSet_card_le_two_pow {n : ℕ}
    (parent : CardinalCausalOrder n) :
    Fintype.card (CausalPastSet parent) ≤ 2 ^ n := by
  classical
  calc
    Fintype.card (CausalPastSet parent) ≤
        Fintype.card (Fin n → Bool) :=
      Fintype.card_le_of_injective
        (causalPastMembershipCode (parent := parent))
        causalPastMembershipCode_injective
    _ = 2 ^ n := by simp

/-- Every coefficient has height at most the number of precursor sets. -/
theorem interactingChiralRealPartitionPolynomial_coeff_natAbs_le_card
    {n k : ℕ} (parent : CardinalCausalOrder n) :
    Int.natAbs
        ((interactingChiralRealPartitionPolynomial parent).coeff k) ≤
      Fintype.card (CausalPastSet parent) := by
  classical
  unfold interactingChiralRealPartitionPolynomial
  rw [finset_sum_coeff]
  calc
    Int.natAbs
        (∑ past : CausalPastSet parent,
          (C (gaussianIPow past.maximalCount).1 *
            X ^ ancestorPairExponent past.ancestorCount : ℤ[X]).coeff k) ≤
        ∑ past : CausalPastSet parent,
          Int.natAbs
            ((C (gaussianIPow past.maximalCount).1 *
              X ^ ancestorPairExponent past.ancestorCount : ℤ[X]).coeff k) :=
      int_natAbs_finset_sum_le_sum_natAbs Finset.univ _
    _ ≤ ∑ _past : CausalPastSet parent, 1 := by
      apply Finset.sum_le_sum
      intro past _hPast
      exact precursorMonomial_coeff_natAbs_le_one past
    _ = Fintype.card (CausalPastSet parent) := by simp

/-- Uniform elementary coefficient-height bound for every n-event parent. -/
theorem interactingChiralRealPartitionPolynomial_coeff_natAbs_le_two_pow
    {n k : ℕ} (parent : CardinalCausalOrder n) :
    Int.natAbs
        ((interactingChiralRealPartitionPolynomial parent).coeff k) ≤
      2 ^ n :=
  (interactingChiralRealPartitionPolynomial_coeff_natAbs_le_card parent).trans
    (causalPastSet_card_le_two_pow parent)

/-! ## 2. The exceptional locus is countable and algebraic -/

/-- Exact complex cancellation for one parent at one chirality. -/
def ParentCancellationSet {n : ℕ} (chirality : Fin 2)
    (parent : CardinalCausalOrder n) : Set ℝ :=
  {lambda | causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude lambda chirality) parent = 0}

/-- Every exact complex cancellation supplies a nonzero integer polynomial
witness, so its coupling is algebraic. -/
theorem isAlgebraic_of_mem_parentCancellationSet {n : ℕ}
    (chirality : Fin 2) (parent : CardinalCausalOrder n) {lambda : ℝ}
    (hCancellation : lambda ∈ ParentCancellationSet chirality parent) :
    IsAlgebraic ℤ lambda := by
  refine ⟨interactingChiralRealPartitionPolynomial parent,
    interactingChiralRealPartitionPolynomial_ne_zero parent, ?_⟩
  change causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude lambda chirality) parent = 0
    at hCancellation
  have hRealZero := congrArg Complex.re hCancellation
  rw [interactingChiral_partition_re_eq_polynomial_eval] at hRealZero
  simpa [Polynomial.aeval_def] using hRealZero

/-- Exceptional couplings after allowing every finite rank and parent. -/
def AllParentCancellationSet (chirality : Fin 2) : Set ℝ :=
  {lambda | ∃ n : ℕ, ∃ parent : CardinalCausalOrder n,
    lambda ∈ ParentCancellationSet chirality parent}

theorem allParentCancellationSet_subset_algebraic (chirality : Fin 2) :
    AllParentCancellationSet chirality ⊆ {lambda : ℝ | IsAlgebraic ℤ lambda} := by
  intro lambda hLambda
  rcases hLambda with ⟨n, parent, hCancellation⟩
  exact isAlgebraic_of_mem_parentCancellationSet chirality parent hCancellation

/-- The all-rank destructive-cancellation locus is countable.  This is the
formal genericity theorem: almost every real coupling is zero-free, and every
transcendental coupling is outside the exceptional set. -/
theorem allParentCancellationSet_countable (chirality : Fin 2) :
    (AllParentCancellationSet chirality).Countable :=
  (Algebraic.countable ℤ ℝ).mono
    (allParentCancellationSet_subset_algebraic chirality)

theorem transcendental_not_mem_allParentCancellationSet {lambda : ℝ}
    (hTranscendental : Transcendental ℤ lambda) (chirality : Fin 2) :
    lambda ∉ AllParentCancellationSet chirality := by
  intro hExceptional
  exact hTranscendental
    (allParentCancellationSet_subset_algebraic chirality hExceptional)

/-! ## 3. A zero-free trajectory running into the critical point -/

/-- Liouville-affine square-root coupling at rank `n`. -/
def criticalRunningPairCoupling (n : ℕ) : ℝ :=
  1 + (canonicalPairCoupling - 1) / ((n : ℝ) + 1)

/-- The physical unordered-pair coupling along the running trajectory. -/
def criticalRunningEffectiveCoupling (n : ℕ) : ℝ :=
  effectivePairCoupling (criticalRunningPairCoupling n)

theorem criticalRunningPairCoupling_gt_one (n : ℕ) :
    1 < criticalRunningPairCoupling n := by
  unfold criticalRunningPairCoupling
  have hNumerator : 0 < canonicalPairCoupling - 1 := by
    linarith [canonicalPairCoupling_gt_one]
  have hDenominator : 0 < (n : ℝ) + 1 := by positivity
  exact lt_add_of_pos_right 1 (div_pos hNumerator hDenominator)

/-- Exact 1/n displacement from the critical point. -/
theorem criticalRunningPairCoupling_scaled_displacement (n : ℕ) :
    ((n : ℝ) + 1) * (criticalRunningPairCoupling n - 1) =
      canonicalPairCoupling - 1 := by
  unfold criticalRunningPairCoupling
  have hDenominator : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Every point on the critical trajectory remains transcendental.  The
proof uses only closure of algebraic numbers under affine operations, so it
does not require a Lindemann--Weierstrass theorem. -/
theorem criticalRunningPairCoupling_transcendental (n : ℕ) :
    Transcendental ℤ (criticalRunningPairCoupling n) := by
  change ¬ IsAlgebraic ℤ (criticalRunningPairCoupling n)
  intro hRunningAlgebraic
  have hOne : IsAlgebraic ℤ (1 : ℝ) := isAlgebraic_one
  have hRank : IsAlgebraic ℤ (((n + 1 : ℕ) : ℝ)) :=
    isAlgebraic_nat (n + 1)
  have hReconstructed :
      IsAlgebraic ℤ
        (1 + ((n + 1 : ℕ) : ℝ) *
          (criticalRunningPairCoupling n - 1)) :=
    hOne.add (hRank.mul (hRunningAlgebraic.sub hOne))
  have hIdentity :
      1 + ((n + 1 : ℕ) : ℝ) *
          (criticalRunningPairCoupling n - 1) =
        canonicalPairCoupling := by
    calc
      1 + ((n + 1 : ℕ) : ℝ) *
            (criticalRunningPairCoupling n - 1) =
          1 + ((n : ℝ) + 1) *
            (criticalRunningPairCoupling n - 1) := by norm_num
      _ = 1 + (canonicalPairCoupling - 1) := by
        rw [criticalRunningPairCoupling_scaled_displacement]
      _ = canonicalPairCoupling := by ring
  rw [hIdentity] at hReconstructed
  exact canonicalPairCoupling_transcendental hReconstructed

/-- The square-root coupling approaches one. -/
theorem criticalRunningPairCoupling_tendsto_one :
    Tendsto criticalRunningPairCoupling atTop (nhds 1) := by
  have hTail :
      Tendsto
        (fun n : ℕ =>
          (canonicalPairCoupling - 1) / ((n : ℝ) + 1))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  simpa [criticalRunningPairCoupling] using tendsto_const_nhds.add hTail

theorem criticalRunningEffectiveCoupling_gt_one (n : ℕ) :
    1 < criticalRunningEffectiveCoupling n := by
  unfold criticalRunningEffectiveCoupling effectivePairCoupling
  nlinarith [criticalRunningPairCoupling_gt_one n]

theorem criticalRunningEffectiveCoupling_tendsto_one :
    Tendsto criticalRunningEffectiveCoupling atTop (nhds 1) := by
  change Tendsto
    (fun n : ℕ =>
      criticalRunningPairCoupling n ^ 2)
    atTop (nhds 1)
  simpa [pow_two] using
    criticalRunningPairCoupling_tendsto_one.mul
      criticalRunningPairCoupling_tendsto_one

/-- Exact finite-rank form of the critical scaling variable. -/
theorem criticalRunningEffectiveCoupling_scaled_displacement (n : ℕ) :
    ((n : ℝ) + 1) * (criticalRunningEffectiveCoupling n - 1) =
      2 * (canonicalPairCoupling - 1) +
        (canonicalPairCoupling - 1) ^ 2 / ((n : ℝ) + 1) := by
  unfold criticalRunningEffectiveCoupling effectivePairCoupling
  rw [show criticalRunningPairCoupling n =
      1 + (canonicalPairCoupling - 1) / ((n : ℝ) + 1) by rfl]
  have hDenominator : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The effective coupling follows the nontrivial `1/n` critical window. -/
theorem criticalRunningEffectiveCoupling_scaled_tendsto :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) * (criticalRunningEffectiveCoupling n - 1))
      atTop (nhds (2 * (canonicalPairCoupling - 1))) := by
  have hTail :
      Tendsto
        (fun n : ℕ =>
          (canonicalPairCoupling - 1) ^ 2 / ((n : ℝ) + 1))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hLimit :=
    (tendsto_const_nhds (x := 2 * (canonicalPairCoupling - 1))).add hTail
  have hLimit' :
      Tendsto
        (fun n : ℕ =>
          2 * (canonicalPairCoupling - 1) +
            (canonicalPairCoupling - 1) ^ 2 / ((n : ℝ) + 1))
        atTop (nhds (2 * (canonicalPairCoupling - 1))) := by
    simpa using hLimit
  apply hLimit'.congr'
  filter_upwards [] with n
  exact (criticalRunningEffectiveCoupling_scaled_displacement n).symm

/-- Every rank of the running trajectory is all-parent zero-free. -/
theorem criticalRunning_interactingChiral_partition_ne_zero
    (rank : ℕ) (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (criticalRunningPairCoupling rank) chirality) parent ≠ 0 :=
  interactingChiral_partition_ne_zero_of_transcendental
    (criticalRunningPairCoupling_transcendental rank) chirality parent

theorem criticalRunning_unlabeled_interactingChiral_partition_ne_zero
    (rank : ℕ) (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude
        (criticalRunningPairCoupling rank) chirality) parent ≠ 0 := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact criticalRunning_interactingChiral_partition_ne_zero
    rank chirality parentRepresentative

/-- The normalized unlabeled growth dynamics at one point of the running
trajectory.  The following theorem proves that its general totalization
constructor never reaches the exceptional fallback branch. -/
def criticalRunningChiralCausalSetGrowthLaw
    (rank : ℕ) (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  totalizedCausalEdgeGrowthLaw
    (interactingChiralCausalEdgeAmplitude
      (criticalRunningPairCoupling rank) chirality)

theorem criticalRunningChiralCausalSetGrowthLaw_transition_eq_direct
    (rank : ℕ) (chirality : Fin 2) {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    (criticalRunningChiralCausalSetGrowthLaw rank chirality).transition
        n pathPrefix child =
      unlabeledAggregatedCausalEdgeAmplitude
          (interactingChiralCausalEdgeAmplitude
            (criticalRunningPairCoupling rank) chirality)
          (currentUnlabeledCausalOrder n pathPrefix) child /
        unlabeledCausalEdgeAmplitudePartition
          (interactingChiralCausalEdgeAmplitude
            (criticalRunningPairCoupling rank) chirality)
          (currentUnlabeledCausalOrder n pathPrefix) := by
  simp [criticalRunningChiralCausalSetGrowthLaw,
    totalizedCausalEdgeGrowthLaw, totalizedNormalizedCausalEdgeAmplitude,
    criticalRunning_unlabeled_interactingChiral_partition_ne_zero]

theorem criticalRunningChiralCausalSetGrowthLaw_stronglyPositive
    (rank : ℕ) (chirality : Fin 2) :
    IsStronglyPositiveGrowthFunctional
      (infiniteRankedCylinderDecoherence
        (criticalRunningChiralCausalSetGrowthLaw rank chirality)) :=
  infiniteRankedCylinderDecoherence_stronglyPositive _

/-- Capstone: a full-support, zero-free chiral law exists at every point of
an explicit coupling trajectory that approaches the nontrivial critical
window at the required `1/n` rate. -/
theorem zeroFree_criticalRunningTrajectory (chirality : Fin 2) :
    (∀ rank : ℕ,
      HasFullRawSignatureSupport
        (interactingChiralSignatureWeight
          (criticalRunningPairCoupling rank) chirality))
      ∧ (∀ rank n : ℕ, ∀ parent : CardinalCausalOrder n,
        causalEdgeAmplitudePartition
          (interactingChiralCausalEdgeAmplitude
            (criticalRunningPairCoupling rank) chirality) parent ≠ 0)
      ∧ (∀ rank : ℕ,
        IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (criticalRunningChiralCausalSetGrowthLaw rank chirality)))
      ∧ Tendsto criticalRunningEffectiveCoupling atTop (nhds 1)
      ∧ Tendsto
          (fun n : ℕ =>
            ((n : ℝ) + 1) * (criticalRunningEffectiveCoupling n - 1))
          atTop (nhds (2 * (canonicalPairCoupling - 1))) := by
  refine ⟨?_, ?_, ?_, criticalRunningEffectiveCoupling_tendsto_one,
    criticalRunningEffectiveCoupling_scaled_tendsto⟩
  · intro rank
    rw [interactingChiralSignatureWeight_fullSupport_iff]
    exact ne_of_gt
      (lt_trans zero_lt_one (criticalRunningPairCoupling_gt_one rank))
  · exact fun rank _n parent =>
      criticalRunning_interactingChiral_partition_ne_zero
        rank chirality parent
  · exact fun rank =>
      criticalRunningChiralCausalSetGrowthLaw_stronglyPositive rank chirality

#print axioms interactingChiralRealPartitionPolynomial_natDegree_le
#print axioms interactingChiralRealPartitionPolynomial_coeff_natAbs_le_two_pow
#print axioms allParentCancellationSet_countable
#print axioms criticalRunningPairCoupling_transcendental
#print axioms zeroFree_criticalRunningTrajectory

end

end UnifiedTheory.Audit.KFCausalSetCriticalRunning
