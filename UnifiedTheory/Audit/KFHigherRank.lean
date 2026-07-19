/-
  Audit/KFHigherRank.lean

  EXACT RANK-TWO K_F BENCHMARK

  This file evaluates the genuine determinant-defined operator at chamber
  rank two on the four preregistered finite orders.  It proves three facts:

  1. the normalized rank-two moment separates all four benchmark orders;
  2. rank two contains signed determinant interference and reverses the
     diamond/total-chain ordering seen at rank one;
  3. higher rank still cannot recover causal orientation, because the full
     symmetrized operator is order-dual invariant at every rank.

  The complementary skew determinant channel is then evaluated on rank-two
  diamond chambers and proved to distinguish the order from its dual.

  These are exact finite theorems, not continuum or ensemble claims.
-/

import UnifiedTheory.Audit.KFSpectralCoarseGraining

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFHigherRank

open UnifiedTheory.LayerB.KFFinitePoset
open UnifiedTheory.Audit.OrderSensitiveObservables
open UnifiedTheory.Audit.KFSpectralCoarseGraining

/-! ## 1. Exact enumeration of the six rank-two chambers on four events -/

/-- The six increasing event pairs `(01, 02, 03, 12, 13, 23)`. -/
def rankTwoPointFour : Fin 6 → Fin 2 → Fin 4 :=
  ![![0, 1], ![0, 2], ![0, 3], ![1, 2], ![1, 3], ![2, 3]]

theorem rankTwoPointFour_strict (k : Fin 6) :
    StrictMono (rankTwoPointFour k) := by
  fin_cases k <;> decide

def rankTwoChamberFour (k : Fin 6) : Chamber antichainFour 2 :=
  ⟨rankTwoPointFour k, rankTwoPointFour_strict k⟩

theorem rankTwoChamberFour_injective :
    Function.Injective rankTwoChamberFour := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [rankTwoChamberFour, rankTwoPointFour]

/-- The explicit list is exhaustive, not merely an injection. -/
noncomputable def rankTwoChamberFourEquiv :
    Fin 6 ≃ Chamber antichainFour 2 :=
  Equiv.ofBijective rankTwoChamberFour
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨rankTwoChamberFour_injective, rfl⟩)

/-! ## 2. The four exact rank-two matrices -/

def antichainFourKFRankTwo : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

def twoChainsFourKFRankTwo : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 0;
     0, 1, 1, 0, 1, 0;
     0, 1, 0, 1, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

def diamondFourKFRankTwo : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ 1, 0, 1, -1, 0,  1;
      0, 1, 1,  1, 1,  0;
      1, 1, 1,  0, 1,  1;
     -1, 1, 0,  1, 1, -1;
      0, 1, 1,  1, 1,  0;
      1, 0, 1, -1, 0,  1]

def chainFourKFRankTwo : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 1, 1, 0, 0, 0;
     1, 1, 1, 1, 1, 0;
     1, 1, 1, 0, 1, 1;
     0, 1, 0, 1, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 0, 1, 1]

theorem antichainFour_rankTwo_matrix :
    (fun i j => kFAtRank antichainFour 2
      (rankTwoChamberFour i) (rankTwoChamberFour j)) =
        antichainFourKFRankTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankTwoChamberFour, rankTwoPointFour, kFAtRank, zetaBlock,
      orderKernel, antichainFourKFRankTwo, Matrix.det_fin_two,
      antichainFour_rel_apply, Fin.ext_iff]

theorem twoChainsFour_rankTwo_matrix :
    (fun i j => kFAtRank twoChainsFour 2
      (rankTwoChamberFour i) (rankTwoChamberFour j)) =
        twoChainsFourKFRankTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankTwoChamberFour, rankTwoPointFour, kFAtRank, zetaBlock,
      orderKernel, twoChainsFourKFRankTwo, Matrix.det_fin_two,
      twoChainsFour_rel_apply, Fin.ext_iff]

theorem diamondFour_rankTwo_matrix :
    (fun i j => kFAtRank diamondFour 2
      (rankTwoChamberFour i) (rankTwoChamberFour j)) =
        diamondFourKFRankTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankTwoChamberFour, rankTwoPointFour, kFAtRank, zetaBlock,
      orderKernel, diamondFourKFRankTwo, Matrix.det_fin_two,
      diamondFour_rel_apply, Fin.ext_iff]

theorem chainFour_rankTwo_matrix :
    (fun i j => kFAtRank chainFour 2
      (rankTwoChamberFour i) (rankTwoChamberFour j)) =
        chainFourKFRankTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankTwoChamberFour, rankTwoPointFour, kFAtRank, zetaBlock,
      orderKernel, chainFourKFRankTwo, Matrix.det_fin_two,
      chainFour_rel_apply, Fin.ext_iff]

/-! ## 3. Exact normalized rank-two moments -/

private theorem normalizedRankTwo_of_matrix
    (P : UnifiedTheory.LayerB.NoBackgroundSpace.FinPoset)
    (e : Fin 6 ≃ Chamber P 2) (M : Matrix (Fin 6) (Fin 6) ℚ) (q : ℚ)
    (hnorm : chamberNormalization P 2 = 6)
    (hentry : ∀ i j, kFAtRank P 2 (e i) (e j) = M i j)
    (hmoment : (∑ i : Fin 6, ∑ j : Fin 6, M i j * M j i) / 36 = q) :
    normalizedKFSecondMomentAtRank P 2 = q := by
  unfold normalizedKFSecondMomentAtRank
  rw [hnorm, kFSecondMomentAtRank_reindex P 2 e]
  simp_rw [hentry]
  norm_num at hmoment ⊢
  exact hmoment

theorem antichainFour_normalizedKFRankTwo :
    normalizedKFSecondMomentAtRank antichainFour 2 = 1 / 6 := by
  refine normalizedRankTwo_of_matrix antichainFour rankTwoChamberFourEquiv
    antichainFourKFRankTwo (1 / 6) ?_ ?_ ?_
  · have hcount : chamberCount antichainFour 2 = 6 := rfl
    simp [chamberNormalization, hcount]
  · intro i j
    change kFAtRank antichainFour 2 (rankTwoChamberFour i)
      (rankTwoChamberFour j) = _
    exact congrFun (congrFun antichainFour_rankTwo_matrix i) j
  · simp_rw [Finset.sum_fin_eq_sum_range]
    norm_num [antichainFourKFRankTwo, Finset.sum_range_succ]

theorem twoChainsFour_normalizedKFRankTwo :
    normalizedKFSecondMomentAtRank twoChainsFour 2 = 4 / 9 := by
  refine normalizedRankTwo_of_matrix twoChainsFour rankTwoChamberFourEquiv
    twoChainsFourKFRankTwo (4 / 9) ?_ ?_ ?_
  · have hcount : chamberCount twoChainsFour 2 = 6 := rfl
    simp [chamberNormalization, hcount]
  · intro i j
    change kFAtRank twoChainsFour 2 (rankTwoChamberFour i)
      (rankTwoChamberFour j) = _
    exact congrFun (congrFun twoChainsFour_rankTwo_matrix i) j
  · simp_rw [Finset.sum_fin_eq_sum_range]
    norm_num [twoChainsFourKFRankTwo, Finset.sum_range_succ]

theorem diamondFour_normalizedKFRankTwo :
    normalizedKFSecondMomentAtRank diamondFour 2 = 13 / 18 := by
  refine normalizedRankTwo_of_matrix diamondFour rankTwoChamberFourEquiv
    diamondFourKFRankTwo (13 / 18) ?_ ?_ ?_
  · have hcount : chamberCount diamondFour 2 = 6 := rfl
    simp [chamberNormalization, hcount]
  · intro i j
    change kFAtRank diamondFour 2 (rankTwoChamberFour i)
      (rankTwoChamberFour j) = _
    exact congrFun (congrFun diamondFour_rankTwo_matrix i) j
  · simp_rw [Finset.sum_fin_eq_sum_range]
    norm_num [diamondFourKFRankTwo, Finset.sum_range_succ]

theorem chainFour_normalizedKFRankTwo :
    normalizedKFSecondMomentAtRank chainFour 2 = 2 / 3 := by
  refine normalizedRankTwo_of_matrix chainFour rankTwoChamberFourEquiv
    chainFourKFRankTwo (2 / 3) ?_ ?_ ?_
  · have hcount : chamberCount chainFour 2 = 6 := rfl
    simp [chamberNormalization, hcount]
  · intro i j
    change kFAtRank chainFour 2 (rankTwoChamberFour i)
      (rankTwoChamberFour j) = _
    exact congrFun (congrFun chainFour_rankTwo_matrix i) j
  · simp_rw [Finset.sum_fin_eq_sum_range]
    norm_num [chainFourKFRankTwo, Finset.sum_range_succ]

def NormalizedKFRankTwoSeparatesBenchmarks : Prop :=
    normalizedKFSecondMomentAtRank antichainFour 2 ≠
      normalizedKFSecondMomentAtRank twoChainsFour 2
    ∧ normalizedKFSecondMomentAtRank antichainFour 2 ≠
      normalizedKFSecondMomentAtRank diamondFour 2
    ∧ normalizedKFSecondMomentAtRank antichainFour 2 ≠
      normalizedKFSecondMomentAtRank chainFour 2
    ∧ normalizedKFSecondMomentAtRank twoChainsFour 2 ≠
      normalizedKFSecondMomentAtRank diamondFour 2
    ∧ normalizedKFSecondMomentAtRank twoChainsFour 2 ≠
      normalizedKFSecondMomentAtRank chainFour 2
    ∧ normalizedKFSecondMomentAtRank diamondFour 2 ≠
      normalizedKFSecondMomentAtRank chainFour 2

theorem normalizedKFRankTwo_separates_benchmarks :
    NormalizedKFRankTwoSeparatesBenchmarks := by
  unfold NormalizedKFRankTwoSeparatesBenchmarks
  rw [antichainFour_normalizedKFRankTwo,
    twoChainsFour_normalizedKFRankTwo,
    diamondFour_normalizedKFRankTwo,
    chainFour_normalizedKFRankTwo]
  norm_num

/-! ## 4. New information and the surviving obstruction -/

/-- Rank two contains signed determinant interference, unlike the rank-one
comparability matrix. -/
theorem diamond_rankTwo_has_negative_entry :
    kFAtRank diamondFour 2 (rankTwoChamberFour 0) (rankTwoChamberFour 3) = -1 := by
  have h := congrFun (congrFun diamondFour_rankTwo_matrix 0) 3
  norm_num [diamondFourKFRankTwo] at h ⊢
  exact h

/-- The diamond and total chain reverse spectral order between ranks one and
two.  Hence rank two is not merely a rescaled comparability-density count. -/
theorem diamond_chain_spectral_rank_inversion :
    normalizedKFSecondMoment diamondFour < normalizedKFSecondMoment chainFour
    ∧ normalizedKFSecondMomentAtRank chainFour 2 <
      normalizedKFSecondMomentAtRank diamondFour 2 := by
  rw [diamondFour_normalizedKF2, chainFour_normalizedKF2,
    chainFour_normalizedKFRankTwo, diamondFour_normalizedKFRankTwo]
  norm_num

/-- The complementary skew channel detects the orientation that symmetric
`K_F` loses, already on rank-two diamond chambers. -/
theorem diamond_rankTwo_orientation_channel_detects_dual :
    kFOrientationAtRank diamondFour 2
      (rankTwoChamberFour 0) (rankTwoChamberFour 2) = 1
    ∧ kFOrientationAtRank dualDiamondFour 2
      (rankTwoChamberFour 0) (rankTwoChamberFour 2) = -1 := by
  have hforward : kFOrientationAtRank diamondFour 2
      (rankTwoChamberFour 0) (rankTwoChamberFour 2) = 1 := by
    change (Matrix.det !![(1 : ℚ), 1; 0, 1] -
      Matrix.det !![(1 : ℚ), 1; 0, 0]) = 1
    norm_num [Matrix.det_fin_two]
  constructor
  · exact hforward
  · have hdual := congrFun (congrFun
      (kFOrientationAtRank_orderDual diamondFour 2)
      (rankTwoChamberFour 0)) (rankTwoChamberFour 2)
    calc
      kFOrientationAtRank dualDiamondFour 2
          (rankTwoChamberFour 0) (rankTwoChamberFour 2) =
          -(kFOrientationAtRank diamondFour 2
            (rankTwoChamberFour 0) (rankTwoChamberFour 2)) := by
        simpa [dualDiamondFour] using hdual
      _ = -1 := by rw [hforward]

/-- Higher rank adds shape information but cannot add time orientation for
the current forward/backward-symmetrized determinant operator. -/
theorem higher_rank_gain_and_limit :
    NormalizedKFRankTwoSeparatesBenchmarks
    ∧ normalizedKFSecondMoment diamondFour < normalizedKFSecondMoment chainFour
    ∧ normalizedKFSecondMomentAtRank chainFour 2 <
      normalizedKFSecondMomentAtRank diamondFour 2
    ∧ (∀ (P : UnifiedTheory.LayerB.NoBackgroundSpace.FinPoset) (r : ℕ),
      kFAtRank (orderDual P) r = kFAtRank P r)
    ∧ kFOrientationAtRank diamondFour 2
      (rankTwoChamberFour 0) (rankTwoChamberFour 2) = 1
    ∧ kFOrientationAtRank dualDiamondFour 2
      (rankTwoChamberFour 0) (rankTwoChamberFour 2) = -1 := by
  exact ⟨normalizedKFRankTwo_separates_benchmarks,
    diamond_chain_spectral_rank_inversion.1,
    diamond_chain_spectral_rank_inversion.2,
    kFAtRank_orderDual,
    diamond_rankTwo_orientation_channel_detects_dual.1,
    diamond_rankTwo_orientation_channel_detects_dual.2⟩

/-! ## Trust regression -/

#print axioms antichainFour_rankTwo_matrix
#print axioms diamondFour_rankTwo_matrix
#print axioms normalizedKFRankTwo_separates_benchmarks
#print axioms diamond_chain_spectral_rank_inversion
#print axioms diamond_rankTwo_orientation_channel_detects_dual
#print axioms higher_rank_gain_and_limit

end UnifiedTheory.Audit.KFHigherRank
