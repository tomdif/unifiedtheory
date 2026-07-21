/-
  Audit/KFCausalSetChiralityEvidenceExtrema.lean

  EXACT RANKWISE EXTREMA OF NEWBORN CHIRALITY EVIDENCE

  For an `n`-event parent, write `V` for its inclusive causal-incidence
  volume and `k` for the precursor population of a maximal birth.  The exact
  source formula is

      y = k / (2 (V + 1 + k)).

  Antisymmetry gives the sharp incidence bounds

      n <= V <= n(n+1)/2.

  Consequently the rankwise source extrema are:

      all births:       0,
      linked births:    1 / (n(n+1)+4),
      maximal source:   n / (2(2n+1)).

  The linked minimum is attained by adjoining a newborn above only the bottom
  of an `n`-chain.  The maximum is attained by adjoining it above the full
  `n`-antichain (the one-top/star causet).  The full-chain timid birth has
  source `n/((n+1)(n+2))`; for `n>=2` it is strictly between those extrema,
  not the linked minimum.

  These are rankwise finite-combinatorial theorems.  The extremizers at each
  rank are not asserted to form one projectively compatible growth history.
  The evidence exponent four in the separate full-chain module is arithmetic:
  source bias contributes a factor two and converting half-log-odds to
  log-odds contributes the other factor two.  It is not spacetime dimension.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetChiralityEvidenceSharpRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralityEvidenceExtrema

noncomputable section

open scoped BigOperators
open Set
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
open UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality
open UnifiedTheory.Audit.KFCausalSetConjugationCompleteness
open UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble
open UnifiedTheory.Audit.KFCausalSetChiralityEvidenceAsymptotics

/-! ## 1. Sharp incidence-volume bounds -/

/-- Reflexivity supplies at least one incidence per event. -/
theorem rank_le_totalCausalPastVolumeQ {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (n : ℚ) ≤ totalCausalPastVolumeQ parent := by
  unfold totalCausalPastVolumeQ
  calc
    (n : ℚ) = ∑ _i : Fin n, (1 : ℚ) := by simp
    _ ≤ ∑ i : Fin n, causalPastVolumeQ parent i := by
      apply Finset.sum_le_sum
      intro i _hi
      exact causalPastVolumeQ_one_le parent i

/-- Antisymmetry allows at most one oriented incidence for each unordered
off-diagonal pair.  Summing the pairwise inequality over all ordered pairs
gives the sharp total-order upper bound. -/
theorem totalCausalPastVolumeQ_le_chain {n : ℕ}
    (parent : CardinalCausalOrder n) :
    totalCausalPastVolumeQ parent ≤ (n : ℚ) * (n + 1) / 2 := by
  let term : Fin n → Fin n → ℚ := fun i j =>
    if parent.rel i j = true then 1 else 0
  have hPair : ∀ i j : Fin n,
      term i j + term j i ≤ 1 + if i = j then 1 else 0 := by
    intro i j
    by_cases hij : parent.rel i j = true
    · by_cases hji : parent.rel j i = true
      · have hEq : i = j := parent.antisymm i j hij hji
        subst j
        simp [term, parent.refl]
      · dsimp [term]
        rw [if_pos hij, if_neg hji]
        split <;> norm_num
    · by_cases hji : parent.rel j i = true
      · dsimp [term]
        rw [if_neg hij, if_pos hji]
        split <;> norm_num
      · dsimp [term]
        rw [if_neg hij, if_neg hji]
        split <;> norm_num
  have hSum :
      (∑ i : Fin n, ∑ j : Fin n, (term i j + term j i)) ≤
        ∑ i : Fin n, ∑ j : Fin n,
          (1 + if i = j then (1 : ℚ) else 0) := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    exact hPair i j
  have hLeft :
      (∑ i : Fin n, ∑ j : Fin n, (term i j + term j i)) =
        2 * totalCausalPastVolumeQ parent := by
    unfold totalCausalPastVolumeQ causalPastVolumeQ term
    simp_rw [Finset.sum_add_distrib]
    rw [show (∑ x : Fin n, ∑ y : Fin n,
        if parent.rel x y = true then (1 : ℚ) else 0) =
      ∑ x : Fin n, ∑ y : Fin n,
        if parent.rel y x = true then (1 : ℚ) else 0 by
          rw [Finset.sum_comm]]
    ring
  have hRight :
      (∑ i : Fin n, ∑ j : Fin n,
        (1 + if i = j then (1 : ℚ) else 0)) =
        (n : ℚ) * n + n := by
    simp_rw [Finset.sum_add_distrib]
    simp
  rw [hLeft, hRight] at hSum
  nlinarith

/-! ## 2. Population bounds and abstract source extrema -/

theorem precursorPopulationQ_le_rank {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    precursorPopulationQ past ≤ n := by
  unfold precursorPopulationQ
  calc
    (∑ i : Fin n, if past.mem i = true then (1 : ℚ) else 0) ≤
        ∑ _i : Fin n, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro i _hi
      split <;> norm_num
    _ = n := by simp

theorem one_le_precursorPopulationQ_of_nonempty {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent)
    (hNonempty : past ≠ emptyCausalPastSet parent) :
    1 ≤ precursorPopulationQ past := by
  rw [precursorPopulationQ_eq_ancestorCount]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
    intro hZero
    apply hNonempty
    apply (precursorPopulationQ_eq_zero_iff_empty past).1
    rw [precursorPopulationQ_eq_ancestorCount, hZero]
    norm_num)

/-- The exact positive linked minimum at parent rank `n`. -/
theorem linkedBirthSource_rank_lower {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    (hNonempty : past ≠ emptyCausalPastSet parent) :
    1 / ((n : ℚ) * (n + 1) + 4) ≤
      maximalBirthOrientationSourceQ parent past := by
  rw [maximalBirthOrientationSourceQ_formula,
    precursorExtension_totalCausalPastVolumeQ]
  have hkOne := one_le_precursorPopulationQ_of_nonempty past hNonempty
  have hkRank := precursorPopulationQ_le_rank past
  have hVNonneg : 0 ≤ totalCausalPastVolumeQ parent :=
    le_trans (by positivity : (0 : ℚ) ≤ n)
      (rank_le_totalCausalPastVolumeQ parent)
  have hVUpper := totalCausalPastVolumeQ_le_chain parent
  have hDenPos :
      0 < 2 * (totalCausalPastVolumeQ parent + 1 +
        precursorPopulationQ past) := by
    have hnNonneg : (0 : ℚ) ≤ n := by positivity
    nlinarith
  have hRankDenPos : 0 < (n : ℚ) * (n + 1) + 4 := by positivity
  rw [div_le_div_iff₀ hRankDenPos hDenPos]
  nlinarith

/-- The one-top/star value is the sharp upper bound at parent rank `n`. -/
theorem maximalBirthSource_rank_upper {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    maximalBirthOrientationSourceQ parent past ≤
      (n : ℚ) / (2 * (2 * n + 1)) := by
  rw [maximalBirthOrientationSourceQ_formula,
    precursorExtension_totalCausalPastVolumeQ]
  have hkNonneg := precursorPopulationQ_nonneg past
  have hkRank := precursorPopulationQ_le_rank past
  have hVLower := rank_le_totalCausalPastVolumeQ parent
  have hDenPos :
      0 < 2 * (totalCausalPastVolumeQ parent + 1 +
        precursorPopulationQ past) := by
    have hnNonneg : (0 : ℚ) ≤ n := by positivity
    nlinarith
  by_cases hn : n = 0
  · subst n
    have hkZero : precursorPopulationQ past = 0 := by
      exact le_antisymm (by simpa using hkRank) hkNonneg
    simp [hkZero]
  · have hRankDenPos : (0 : ℚ) < 2 * (2 * n + 1) := by positivity
    rw [div_le_div_iff₀ hDenPos hRankDenPos]
    nlinarith

/-! ## 3. Exact extremizers -/

/-- The singleton bottom precursor of a nonempty chain. -/
def chainBottomPast (n : ℕ) :
    CausalPastSet (cardinalCausalChain (n + 1)) where
  mem := fun i => decide (i = 0)
  downwardClosed := by
    intro i j hi hij
    have hi0 : i = 0 := of_decide_eq_true hi
    subst i
    have hji : j ≤ 0 := by
      simpa [cardinalCausalChain] using hij
    have hj0 : j = 0 := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero hji
    exact decide_eq_true hj0

theorem chainBottomPast_population (n : ℕ) :
    precursorPopulationQ (chainBottomPast n) = 1 := by
  unfold precursorPopulationQ chainBottomPast
  simp

theorem chainBottomPast_source_exact (n : ℕ) :
    maximalBirthOrientationSourceQ (cardinalCausalChain (n + 1))
        (chainBottomPast n) =
      1 / (((n + 1 : ℕ) : ℚ) * (n + 2) + 4) := by
  rw [maximalBirthOrientationSourceQ_formula,
    precursorExtension_totalCausalPastVolumeQ,
    totalCausalPastVolumeQ_chain, chainBottomPast_population]
  push_cast
  field_simp
  ring

theorem antichainFullPast_population (n : ℕ) :
    precursorPopulationQ
        (fullCausalPastSet (cardinalCausalAntichain n)) = n := by
  simp [precursorPopulationQ, fullCausalPastSet]

theorem totalCausalPastVolumeQ_antichain (n : ℕ) :
    totalCausalPastVolumeQ (cardinalCausalAntichain n) = n := by
  unfold totalCausalPastVolumeQ
  simp_rw [causalPastVolumeQ_antichain]
  simp

theorem antichainFullBirth_source_exact (n : ℕ) :
    maximalBirthOrientationSourceQ (cardinalCausalAntichain n)
        (fullCausalPastSet (cardinalCausalAntichain n)) =
      (n : ℚ) / (2 * (2 * n + 1)) := by
  rw [maximalBirthOrientationSourceQ_formula,
    precursorExtension_totalCausalPastVolumeQ,
    totalCausalPastVolumeQ_antichain, antichainFullPast_population]
  ring

theorem chainFullBirth_source_exact (n : ℕ) :
    maximalBirthOrientationSourceQ (cardinalCausalChain n)
        (fullCausalPastSet (cardinalCausalChain n)) =
      (n : ℚ) / ((n + 1) * (n + 2)) := by
  rw [maximalBirthOrientationSourceQ_formula,
    precursorExtension_totalCausalPastVolumeQ,
    totalCausalPastVolumeQ_chain]
  have hPopulation : precursorPopulationQ
      (fullCausalPastSet (cardinalCausalChain n)) = n := by
    simp [precursorPopulationQ, fullCausalPastSet]
  rw [hPopulation]
  field_simp
  ring

/-- At every rank at least two, the timid full-chain birth is not the linked
minimum: a singleton-bottom birth in the same chain has strictly smaller
source. -/
theorem chainBottom_source_lt_chainFull_source (n : ℕ) (hn : 1 ≤ n) :
    maximalBirthOrientationSourceQ (cardinalCausalChain (n + 1))
        (chainBottomPast n) <
      maximalBirthOrientationSourceQ (cardinalCausalChain (n + 1))
        (fullCausalPastSet (cardinalCausalChain (n + 1))) := by
  rw [chainBottomPast_source_exact, chainFullBirth_source_exact]
  push_cast
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hLeftDen : (0 : ℚ) < (n + 1) * (n + 2) + 4 := by positivity
  have hRightDen : (0 : ℚ) < (n + 1 + 1) * (n + 1 + 2) := by positivity
  apply (div_lt_div_iff₀ hLeftDen hRightDen).2
  have hCubic : 0 ≤ (n + 2) ^ 2 * (n - 1 : ℚ) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

/-- For rank at least two, the timid full-chain source is also strictly below
the star maximum. -/
theorem chainFull_source_lt_antichainFull_source (n : ℕ) (hn : 2 ≤ n) :
    maximalBirthOrientationSourceQ (cardinalCausalChain n)
        (fullCausalPastSet (cardinalCausalChain n)) <
      maximalBirthOrientationSourceQ (cardinalCausalAntichain n)
        (fullCausalPastSet (cardinalCausalAntichain n)) := by
  rw [chainFullBirth_source_exact, antichainFullBirth_source_exact]
  have hnQ : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hLeftDen : (0 : ℚ) < (n + 1) * (n + 2) := by positivity
  have hRightDen : (0 : ℚ) < 2 * (2 * n + 1) := by positivity
  rw [div_lt_div_iff₀ hLeftDen hRightDen]
  have hnPos : (0 : ℚ) < n := by linarith
  have hGap : (0 : ℚ) < ((n : ℚ) + 1) * (n + 2) -
      2 * (2 * n + 1) := by
    nlinarith [mul_pos hnPos (by linarith : (0 : ℚ) < (n : ℚ) - 1)]
  nlinarith [mul_pos hnPos hGap]

/-! ## 4. Charge ordering and the corrected scope -/

def birthEvidenceChargeQ {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) : ℝ :=
  Real.artanh (2 * (maximalBirthOrientationSourceQ parent past : ℝ))

@[simp]
theorem gregariousBirthEvidenceCharge_eq_zero {n : ℕ}
    (parent : CardinalCausalOrder n) :
    birthEvidenceChargeQ parent (emptyCausalPastSet parent) = 0 := by
  simp [birthEvidenceChargeQ]

theorem chainBottomBirthEvidenceCharge_exact (n : ℕ) :
    birthEvidenceChargeQ (cardinalCausalChain (n + 1))
        (chainBottomPast n) =
      Real.artanh
        (2 / (((n + 1 : ℕ) : ℝ) * (n + 2) + 4)) := by
  unfold birthEvidenceChargeQ
  rw [chainBottomPast_source_exact]
  push_cast
  congr 1
  ring

theorem antichainFullBirthEvidenceCharge_exact (n : ℕ) :
    birthEvidenceChargeQ (cardinalCausalAntichain n)
        (fullCausalPastSet (cardinalCausalAntichain n)) =
      Real.artanh ((n : ℝ) / (2 * n + 1)) := by
  unfold birthEvidenceChargeQ
  rw [antichainFullBirth_source_exact]
  push_cast
  congr 1
  have hDen : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hDen]

theorem linkedBirthEvidenceCharge_rank_lower {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    (hNonempty : past ≠ emptyCausalPastSet parent) :
    Real.artanh (2 / (((n : ℝ) * (n + 1) + 4))) ≤
      birthEvidenceChargeQ parent past := by
  unfold birthEvidenceChargeQ
  apply Real.artanh_le_artanh
  · have hDen : (0 : ℝ) < (n : ℝ) * (n + 1) + 4 := by positivity
    have hNonneg : (0 : ℝ) ≤ 2 / ((n : ℝ) * (n + 1) + 4) := by positivity
    linarith
  · have hQuarter := maximalBirthSource_strictInterior parent past
    rw [abs_lt] at hQuarter
    have hQuarterCast :
        (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) <
          ((1 / 2 : ℚ) : ℝ) :=
      (Rat.cast_lt).2 hQuarter.2
    have hQuarterR :
        ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) < 1 / 2 := by
      norm_num at hQuarterCast ⊢
      exact hQuarterCast
    linarith
  · have hLower := linkedBirthSource_rank_lower parent past hNonempty
    have hLowerCast :
        ((1 / ((n : ℚ) * (n + 1) + 4) : ℚ) : ℝ) ≤
          ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) :=
      (Rat.cast_le).2 hLower
    push_cast at hLowerCast
    have hLowerR :
        1 / ((n : ℝ) * (n + 1) + 4) ≤
          ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hLowerCast
    calc
      2 / ((n : ℝ) * (n + 1) + 4) =
          2 * (1 / ((n : ℝ) * (n + 1) + 4)) := by ring
      _ ≤ 2 * ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hLowerR (by norm_num)

theorem birthEvidenceCharge_rank_upper {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    birthEvidenceChargeQ parent past ≤
      Real.artanh ((n : ℝ) / (2 * n + 1)) := by
  unfold birthEvidenceChargeQ
  apply Real.artanh_le_artanh
  · have hNonneg := maximalBirthOrientationSourceQ_nonneg parent past
    have hNonnegR : (0 : ℝ) ≤
        ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) := by
      exact_mod_cast hNonneg
    linarith
  · have hnNonneg : (0 : ℝ) ≤ n := by positivity
    have hDen : (0 : ℝ) < 2 * n + 1 := by positivity
    rw [div_lt_one hDen]
    linarith
  · have hUpper := maximalBirthSource_rank_upper parent past
    have hUpperCast :
        ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) ≤
          (((n : ℚ) / (2 * (2 * n + 1)) : ℚ) : ℝ) :=
      (Rat.cast_le).2 hUpper
    push_cast at hUpperCast
    have hUpperR :
        ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) ≤
          (n : ℝ) / (2 * (2 * n + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hUpperCast
    have hDen : (2 * n + 1 : ℝ) ≠ 0 := by positivity
    calc
      2 * ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) ≤
          2 * ((n : ℝ) / (2 * (2 * n + 1))) :=
        mul_le_mul_of_nonneg_left hUpperR (by norm_num)
      _ = (n : ℝ) / (2 * n + 1) := by field_simp [hDen]

/-- Rankwise source extremizers and the strict interior position of the timid
chain birth.  This deliberately makes no compatibility claim across ranks. -/
theorem rankwiseBirthEvidenceExtrema_capstone (n : ℕ) (hn : 1 ≤ n) :
    maximalBirthOrientationSourceQ (cardinalCausalChain (n + 1))
        (chainBottomPast n) =
        1 / (((n + 1 : ℕ) : ℚ) * (n + 2) + 4)
      ∧ maximalBirthOrientationSourceQ (cardinalCausalAntichain (n + 1))
          (fullCausalPastSet (cardinalCausalAntichain (n + 1))) =
        ((n + 1 : ℕ) : ℚ) / (2 * (2 * (n + 1) + 1))
      ∧ maximalBirthOrientationSourceQ (cardinalCausalChain (n + 1))
          (chainBottomPast n) <
        maximalBirthOrientationSourceQ (cardinalCausalChain (n + 1))
          (fullCausalPastSet (cardinalCausalChain (n + 1)))
      ∧ maximalBirthOrientationSourceQ (cardinalCausalChain (n + 1))
          (fullCausalPastSet (cardinalCausalChain (n + 1))) <
        maximalBirthOrientationSourceQ (cardinalCausalAntichain (n + 1))
          (fullCausalPastSet (cardinalCausalAntichain (n + 1))) := by
  refine ⟨chainBottomPast_source_exact n, ?_,
    chainBottom_source_lt_chainFull_source n hn,
    chainFull_source_lt_antichainFull_source (n + 1) (by omega)⟩
  simpa only [Nat.cast_add, Nat.cast_one] using
    antichainFullBirth_source_exact (n + 1)

#print axioms totalCausalPastVolumeQ_le_chain
#print axioms linkedBirthSource_rank_lower
#print axioms maximalBirthSource_rank_upper
#print axioms chainBottomPast_source_exact
#print axioms antichainFullBirth_source_exact
#print axioms chainBottom_source_lt_chainFull_source
#print axioms chainFull_source_lt_antichainFull_source
#print axioms gregariousBirthEvidenceCharge_eq_zero
#print axioms chainBottomBirthEvidenceCharge_exact
#print axioms antichainFullBirthEvidenceCharge_exact
#print axioms linkedBirthEvidenceCharge_rank_lower
#print axioms birthEvidenceCharge_rank_upper
#print axioms rankwiseBirthEvidenceExtrema_capstone

end

end UnifiedTheory.Audit.KFCausalSetChiralityEvidenceExtrema
