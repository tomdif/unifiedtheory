/-
  Audit/KFMultirankCoarseGraining.lean

  JOINT MULTIRANK + ORIENTATION COARSE-GRAINING

  This file tracks two complementary kinds of information through the exact
  diamond-to-three-chain quotient:

  * the symmetric normalized K_F profile at chamber ranks one and two;
  * the full skew orientation matrix at chamber rank two.

  The symmetric profile changes from `(7/8, 13/18)` to `(1, 7/9)` and is
  eventually constant at the coarse value.  Its components run by different
  amounts, so no single multiplicative coupling carries both ranks.  On the
  orientation side, the
  fine chamber map has nonuniform surviving fiber sizes `(2,1,2)`.
  Summing the fine skew channel over those fibers does not close on the original
  coarse ansatz: besides twice the recomputed coarse channel, it generates
  an exact long-range skew residual.  This is the finite operator-generation
  effect that a genuine multiscale flow must retain.

  This is an exact one-step finite blocking theorem.  It is not yet an
  iterated RG flow, a sprinkling ensemble, or a continuum result.
-/

import UnifiedTheory.Audit.KFHigherRank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFMultirankCoarseGraining

open Filter Topology
open UnifiedTheory.LayerB.KFFinitePoset
open UnifiedTheory.Audit.OrderSensitiveObservables
open UnifiedTheory.Audit.KFSpectralCoarseGraining
open UnifiedTheory.Audit.KFHigherRank

/-! ## 1. Coarse rank-two chamber carrier -/

/-- The three increasing pairs `(01, 02, 12)` on the coarse chain. -/
def rankTwoPointThree : Fin 3 → Fin 2 → Fin 3 :=
  ![![0, 1], ![0, 2], ![1, 2]]

theorem rankTwoPointThree_strict (k : Fin 3) :
    StrictMono (rankTwoPointThree k) := by
  fin_cases k <;> decide

def rankTwoChamberThree (k : Fin 3) : Chamber chainThree 2 :=
  ⟨rankTwoPointThree k, rankTwoPointThree_strict k⟩

theorem rankTwoChamberThree_injective :
    Function.Injective rankTwoChamberThree := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [rankTwoChamberThree, rankTwoPointThree]

noncomputable def rankTwoChamberThreeEquiv :
    Fin 3 ≃ Chamber chainThree 2 :=
  Equiv.ofBijective rankTwoChamberThree
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨rankTwoChamberThree_injective, rfl⟩)

def chainThreeKFRankTwo : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 0;
     1, 1, 1;
     0, 1, 1]

theorem chainThree_rankTwo_matrix :
    (fun i j => kFAtRank chainThree 2
      (rankTwoChamberThree i) (rankTwoChamberThree j)) =
        chainThreeKFRankTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankTwoChamberThree, rankTwoPointThree, kFAtRank, zetaBlock,
      orderKernel, chainThreeKFRankTwo, Matrix.det_fin_two,
      chainThree_rel_apply, Fin.ext_iff]

theorem chainThree_normalizedKFRankTwo :
    normalizedKFSecondMomentAtRank chainThree 2 = 7 / 9 := by
  unfold normalizedKFSecondMomentAtRank
  have hcount : chamberCount chainThree 2 = 3 := rfl
  have hnorm : chamberNormalization chainThree 2 = 3 := by
    simp [chamberNormalization, hcount]
  rw [hnorm, kFSecondMomentAtRank_reindex chainThree 2
    rankTwoChamberThreeEquiv]
  have hentry : ∀ i j : Fin 3,
      kFAtRank chainThree 2 (rankTwoChamberThreeEquiv i)
        (rankTwoChamberThreeEquiv j) = chainThreeKFRankTwo i j := by
    intro i j
    change kFAtRank chainThree 2 (rankTwoChamberThree i)
      (rankTwoChamberThree j) = _
    exact congrFun (congrFun chainThree_rankTwo_matrix i) j
  simp_rw [hentry, Finset.sum_fin_eq_sum_range]
  norm_num [chainThreeKFRankTwo, Finset.sum_range_succ]

/-! ## 2. Symmetric multirank profile flow -/

/-- The first two normalized symmetric spectral coordinates, promoted to
real values so the profile has an ordinary product topology. -/
def symmetricProfile12 (P : UnifiedTheory.LayerB.NoBackgroundSpace.FinPoset) :
    Fin 2 → ℝ :=
  ![(normalizedKFSecondMoment P : ℝ),
    (normalizedKFSecondMomentAtRank P 2 : ℝ)]

/-- The two-rank profile along one exact quotient: fine at scale zero and
coarse at every positive scale. -/
def symmetricProfileAtScale (step : OrderCoarseGraining) (scale : ℕ) :
    Fin 2 → ℝ :=
  if scale = 0 then symmetricProfile12 step.fine
  else symmetricProfile12 step.coarse

theorem symmetricProfileAtScale_converges (step : OrderCoarseGraining) :
    Tendsto (symmetricProfileAtScale step) atTop
      (𝓝 (symmetricProfile12 step.coarse)) := by
  apply tendsto_const_nhds.congr'
  refine Filter.eventually_atTop.2 ⟨1, ?_⟩
  intro scale hscale
  have hne : scale ≠ 0 := by omega
  simp [symmetricProfileAtScale, hne]

theorem diamond_symmetricProfile12 :
    symmetricProfile12 diamondFour = ![(7 / 8 : ℝ), 13 / 18] := by
  ext i
  fin_cases i <;>
    norm_num [symmetricProfile12, diamondFour_normalizedKF2,
      diamondFour_normalizedKFRankTwo]

theorem chainThree_symmetricProfile12 :
    symmetricProfile12 chainThree = ![(1 : ℝ), 7 / 9] := by
  ext i
  fin_cases i <;>
    norm_num [symmetricProfile12, chainThree_normalizedKF2,
      chainThree_normalizedKFRankTwo]

theorem diamond_multirank_profile_changes_under_blocking :
    symmetricProfileAtScale diamondToChainThree 0 = ![(7 / 8 : ℝ), 13 / 18]
    ∧ symmetricProfileAtScale diamondToChainThree 1 = ![(1 : ℝ), 7 / 9]
    ∧ symmetricProfileAtScale diamondToChainThree 0 ≠
      symmetricProfileAtScale diamondToChainThree 1 := by
  constructor
  · simpa [symmetricProfileAtScale, diamondToChainThree] using
      diamond_symmetricProfile12
  constructor
  · simpa [symmetricProfileAtScale, diamondToChainThree] using
      chainThree_symmetricProfile12
  · intro h
    have h0 := congrFun h 0
    norm_num [symmetricProfileAtScale, diamondToChainThree,
      symmetricProfile12, diamondFour_normalizedKF2,
      chainThree_normalizedKF2] at h0

/-- The two symmetric ranks run by different exact amounts.  Coarse graining
therefore changes the shape of the profile, not just its overall scale. -/
theorem diamond_multirank_profile_increment :
    (fun r => symmetricProfileAtScale diamondToChainThree 1 r -
      symmetricProfileAtScale diamondToChainThree 0 r) =
        ![(1 / 8 : ℝ), 1 / 18] := by
  ext r
  fin_cases r <;>
    norm_num [symmetricProfileAtScale, diamondToChainThree,
      symmetricProfile12, diamondFour_normalizedKF2,
      diamondFour_normalizedKFRankTwo, chainThree_normalizedKF2,
      chainThree_normalizedKFRankTwo]

/-- No single multiplicative coupling renormalizes both symmetric ranks:
rank one would require `8/7`, whereas rank two would require `14/13`. -/
theorem diamond_multirank_profile_not_uniformly_rescaled :
    ¬ ∃ Z : ℝ, ∀ r,
      symmetricProfileAtScale diamondToChainThree 1 r =
        Z * symmetricProfileAtScale diamondToChainThree 0 r := by
  rintro ⟨Z, hZ⟩
  have h0 := hZ 0
  have h1 := hZ 1
  norm_num [symmetricProfileAtScale, diamondToChainThree,
    symmetricProfile12, diamondFour_normalizedKF2,
    diamondFour_normalizedKFRankTwo, chainThree_normalizedKF2,
    chainThree_normalizedKFRankTwo] at h0 h1
  linarith

/-! ## 3. Full skew-channel pushforward -/

/-- Sum a fine matrix over the fibers of a partial fine-to-coarse index map.
`none` represents a fine chamber that collapses under blocking. -/
def pushForwardMatrix {m n : Type*} [Fintype m] [DecidableEq n]
    (block : m → Option n) (M : Matrix m m ℚ) : Matrix n n ℚ :=
  fun a b => ∑ i : m, ∑ j : m,
    if block i = some a ∧ block j = some b then M i j else 0

/-- Under the diamond quotient, chambers `01` and `02` both map to coarse
`01`; `03` maps to `02`; `12` collapses; and `13`, `23` map to `12`. -/
def diamondRankTwoBlock : Fin 6 → Option (Fin 3) :=
  ![some 0, some 0, some 1, none, some 2, some 2]

/-- Every declared surviving chamber image agrees pointwise with the event
block map used by `diamondToChainThree`. -/
theorem diamondRankTwoBlock_sound (i : Fin 6) (c : Fin 3)
    (h : diamondRankTwoBlock i = some c) :
    ∀ k : Fin 2,
      diamondBlock ((rankTwoChamberFour i).1 k) =
        (rankTwoChamberThree c).1 k := by
  intro k
  fin_cases i <;> fin_cases c <;> simp [diamondRankTwoBlock] at h
  all_goals
    fin_cases k <;> rfl

theorem diamond_collapsed_chamber_identified :
    diamondRankTwoBlock 3 = none
    ∧ diamondBlock ((rankTwoChamberFour 3).1 0) =
      diamondBlock ((rankTwoChamberFour 3).1 1) := by
  constructor <;> rfl

def diamondOrientationRankTwo : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ 0,  0,  1, -1,  0,  1;
      0,  0,  1,  1,  1,  0;
     -1, -1,  0,  0,  1,  1;
      1, -1,  0,  0,  1, -1;
      0, -1, -1, -1,  0,  0;
     -1,  0, -1,  1,  0,  0]

def chainThreeOrientationRankTwo : Matrix (Fin 3) (Fin 3) ℚ :=
  !![ 0,  1,  0;
     -1,  0,  1;
      0, -1,  0]

def diamondOrientationOperatorRankTwo : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => kFOrientationAtRank diamondFour 2
    (rankTwoChamberFour i) (rankTwoChamberFour j)

def chainThreeOrientationOperatorRankTwo : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => kFOrientationAtRank chainThree 2
    (rankTwoChamberThree i) (rankTwoChamberThree j)

theorem diamond_rankTwo_orientation_matrix :
    diamondOrientationOperatorRankTwo = diamondOrientationRankTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kFOrientationAtRank_two_apply, orderKernel,
      diamondOrientationOperatorRankTwo,
      rankTwoChamberFour, rankTwoPointFour, diamondOrientationRankTwo,
      diamondFour_rel_apply, Fin.ext_iff]

theorem chainThree_rankTwo_orientation_matrix :
    chainThreeOrientationOperatorRankTwo = chainThreeOrientationRankTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kFOrientationAtRank_two_apply, orderKernel,
      chainThreeOrientationOperatorRankTwo,
      rankTwoChamberThree, rankTwoPointThree, chainThreeOrientationRankTwo,
      chainThree_rel_apply, Fin.ext_iff]

/-- The new long-range skew operator generated by the quotient.  It couples
coarse chambers `01` and `12`, which have zero direct orientation entry in
the independently recomputed determinant channel. -/
def generatedLongRangeOrientation : Matrix (Fin 3) (Fin 3) ℚ :=
  !![ 0, 0,  2;
      0, 0,  0;
     -2, 0,  0]

/-- Fiber summation produces twice the independently recomputed coarse skew
matrix plus an exact long-range residual. -/
theorem diamond_orientation_pushforward_decomposition :
    pushForwardMatrix diamondRankTwoBlock diamondOrientationRankTwo =
      (2 : ℚ) • chainThreeOrientationRankTwo +
        generatedLongRangeOrientation := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp_rw [pushForwardMatrix, Finset.sum_fin_eq_sum_range]
  all_goals
    norm_num [diamondRankTwoBlock, diamondOrientationRankTwo,
      chainThreeOrientationRankTwo, generatedLongRangeOrientation,
      Finset.sum_range_succ, Fin.ext_iff] <;> simp <;> norm_num

/-- Normalizing by the factor that matches the adjacent coarse entries leaves
a unit long-range correction; the original one-operator orientation ansatz is
not closed under blocking. -/
theorem diamond_orientation_normalized_pushforward :
    (1 / 2 : ℚ) •
      pushForwardMatrix diamondRankTwoBlock diamondOrientationRankTwo =
        chainThreeOrientationRankTwo +
          (1 / 2 : ℚ) • generatedLongRangeOrientation := by
  rw [diamond_orientation_pushforward_decomposition]
  simp [smul_add, smul_smul]

theorem generatedLongRangeOrientation_nonzero :
    generatedLongRangeOrientation ≠ 0 := by
  intro h
  have h02 := congrFun (congrFun h 0) 2
  change (2 : ℚ) = 0 at h02
  norm_num at h02

theorem naive_orientation_ansatz_not_closed :
    pushForwardMatrix diamondRankTwoBlock diamondOrientationRankTwo ≠
      (2 : ℚ) • chainThreeOrientationRankTwo := by
  rw [diamond_orientation_pushforward_decomposition]
  exact add_ne_left.mpr generatedLongRangeOrientation_nonzero

/-- The same transport theorem stated directly for the generic orientation
operator rather than the displayed matrices. -/
theorem diamond_orientation_operator_tracks_through_blocking :
    (1 / 2 : ℚ) • pushForwardMatrix diamondRankTwoBlock
      diamondOrientationOperatorRankTwo =
        chainThreeOrientationOperatorRankTwo +
          (1 / 2 : ℚ) • generatedLongRangeOrientation := by
  rw [diamond_rankTwo_orientation_matrix,
    chainThree_rankTwo_orientation_matrix]
  exact diamond_orientation_normalized_pushforward

/-! ## 4. Joint finite coarse-graining theorem -/

theorem joint_multirank_orientation_coarse_graining :
    Tendsto (symmetricProfileAtScale diamondToChainThree) atTop
      (𝓝 (symmetricProfile12 chainThree))
    ∧ symmetricProfileAtScale diamondToChainThree 0 =
      ![(7 / 8 : ℝ), 13 / 18]
    ∧ symmetricProfileAtScale diamondToChainThree 1 =
      ![(1 : ℝ), 7 / 9]
    ∧ symmetricProfileAtScale diamondToChainThree 0 ≠
      symmetricProfileAtScale diamondToChainThree 1
    ∧ (fun r => symmetricProfileAtScale diamondToChainThree 1 r -
      symmetricProfileAtScale diamondToChainThree 0 r) =
        ![(1 / 8 : ℝ), 1 / 18]
    ∧ (¬ ∃ Z : ℝ, ∀ r,
      symmetricProfileAtScale diamondToChainThree 1 r =
        Z * symmetricProfileAtScale diamondToChainThree 0 r)
    ∧ (1 / 2 : ℚ) • pushForwardMatrix diamondRankTwoBlock
      diamondOrientationOperatorRankTwo =
        chainThreeOrientationOperatorRankTwo +
          (1 / 2 : ℚ) • generatedLongRangeOrientation
    ∧ generatedLongRangeOrientation ≠ 0 := by
  exact ⟨symmetricProfileAtScale_converges diamondToChainThree,
    diamond_multirank_profile_changes_under_blocking.1,
    diamond_multirank_profile_changes_under_blocking.2.1,
    diamond_multirank_profile_changes_under_blocking.2.2,
    diamond_multirank_profile_increment,
    diamond_multirank_profile_not_uniformly_rescaled,
    diamond_orientation_operator_tracks_through_blocking,
    generatedLongRangeOrientation_nonzero⟩

/-! ## Trust regression -/

#print axioms chainThree_normalizedKFRankTwo
#print axioms diamond_multirank_profile_changes_under_blocking
#print axioms diamond_multirank_profile_not_uniformly_rescaled
#print axioms diamondRankTwoBlock_sound
#print axioms diamond_orientation_operator_tracks_through_blocking
#print axioms naive_orientation_ansatz_not_closed
#print axioms joint_multirank_orientation_coarse_graining

end UnifiedTheory.Audit.KFMultirankCoarseGraining
