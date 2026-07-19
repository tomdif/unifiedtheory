/-
  Audit/KFOrientationCouplingFlow.lean

  EXACT ORIENTATION COUPLING RECURRENCE

  This file contrasts two certified quotients from a six-chain to a
  three-chain.  Uniform fibers `(2,2,2)` preserve the one-coupling orientation
  ansatz after normalization and compose with a second block exactly.  The
  nonuniform fibers `(1,2,3)` generate three incompatible pair couplings and
  cannot close for any scalar normalization.
-/

import UnifiedTheory.Audit.KFOrientationCountertermRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationCouplingFlow

open UnifiedTheory.LayerB.NoBackgroundSpace
open UnifiedTheory.Audit.OrderSensitiveObservables
open UnifiedTheory.Audit.KFSpectralCoarseGraining
open UnifiedTheory.Audit.KFMultirankCoarseGraining
open UnifiedTheory.Audit.KFOrientationDefect
open UnifiedTheory.Audit.KFOrientationPathObstruction

/-! ## 1. Uniform and nonuniform certified blocks -/

def chainSix : FinPoset where
  n := 6
  hn := by decide
  rel := fun i j => decide (i.val ≤ j.val)
  refl := by decide
  antisymm := by decide
  trans := by decide

@[simp]
theorem chainSix_rel_apply (i j : Fin 6) :
    chainSix.rel i j = decide (i.val ≤ j.val) := rfl

/-- Three equal fibers of size two. -/
def chainSixUniformBlock : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

/-- Fibers of sizes one, two, and three. -/
def chainSixNonuniformBlock : Fin 6 → Fin 3 := ![0, 1, 1, 2, 2, 2]

def chainSixUniformToChainThree : OrderCoarseGraining where
  fine := chainSix
  coarse := chainThree
  block := chainSixUniformBlock
  block_surjective := by decide
  relation_iff := by decide

def chainSixNonuniformToChainThree : OrderCoarseGraining where
  fine := chainSix
  coarse := chainThree
  block := chainSixNonuniformBlock
  block_surjective := by decide
  relation_iff := by decide

def chainSixUniformPartial : Fin 6 → Option (Fin 3) :=
  totalPartialBlock chainSixUniformBlock

def chainSixNonuniformPartial : Fin 6 → Option (Fin 3) :=
  totalPartialBlock chainSixNonuniformBlock

def chainThreeToTwoPartial : Fin 3 → Option (Fin 2) :=
  totalPartialBlock chainThreeBlock12

def chainSixUniformToTwoPath : Fin 6 → Option (Fin 2) :=
  composePartialBlock chainSixUniformPartial chainThreeToTwoPartial

theorem chainSixUniformPartial_apply :
    chainSixUniformPartial =
      ![some 0, some 0, some 1, some 1, some 2, some 2] := by
  funext i
  fin_cases i <;> rfl

theorem chainSixNonuniformPartial_apply :
    chainSixNonuniformPartial =
      ![some 0, some 1, some 1, some 2, some 2, some 2] := by
  funext i
  fin_cases i <;> rfl

theorem chainThreeToTwoPartial_apply :
    chainThreeToTwoPartial = ![some 0, some 1, some 1] := by
  funext i
  fin_cases i <;> rfl

/-! ## 2. Exact rank-one orientation matrices -/

def chainSixOrientationRankOne : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ 0,  1,  1,  1,  1,  1;
     -1,  0,  1,  1,  1,  1;
     -1, -1,  0,  1,  1,  1;
     -1, -1, -1,  0,  1,  1;
     -1, -1, -1, -1,  0,  1;
     -1, -1, -1, -1, -1,  0]

def chainThreeOrientationRankOne : Matrix (Fin 3) (Fin 3) ℚ :=
  !![ 0,  1,  1;
     -1,  0,  1;
     -1, -1,  0]

def chainSixNonuniformPushedOrientation : Matrix (Fin 3) (Fin 3) ℚ :=
  !![ 0,  2,  3;
     -2,  0,  6;
     -3, -6,  0]

theorem chainSix_orientationRankOne_matrix :
    orientationRankOne chainSix = chainSixOrientationRankOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orientationRankOne_apply,
      UnifiedTheory.LayerB.KFFinitePoset.orderKernel,
      chainSix_rel_apply, chainSixOrientationRankOne, Fin.ext_iff]

theorem chainThree_orientationRankOne_matrix :
    orientationRankOne chainThree = chainThreeOrientationRankOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orientationRankOne_apply,
      UnifiedTheory.LayerB.KFFinitePoset.orderKernel,
      chainThree_rel_apply, chainThreeOrientationRankOne, Fin.ext_iff]

/-! ## 3. Uniform closure and recurrence -/

theorem chainSixUniform_pushforward :
    pushForwardMatrix chainSixUniformPartial chainSixOrientationRankOne =
      (4 : ℚ) • chainThreeOrientationRankOne := by
  rw [chainSixUniformPartial_apply]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp_rw [pushForwardMatrix, Finset.sum_fin_eq_sum_range]
  all_goals
    norm_num [chainSixOrientationRankOne, chainThreeOrientationRankOne,
      Finset.sum_range_succ, Fin.ext_iff]

theorem chainThreeToTwo_pushforward :
    pushForwardMatrix chainThreeToTwoPartial chainThreeOrientationRankOne =
      (2 : ℚ) • chainTwoOrientationRankOne := by
  rw [chainThreeToTwoPartial_apply]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp_rw [pushForwardMatrix, Finset.sum_fin_eq_sum_range]
  all_goals
    norm_num [chainThreeOrientationRankOne, chainTwoOrientationRankOne,
      Finset.sum_range_succ, Fin.ext_iff]

theorem chainSixUniform_composite_pushforward :
    pushForwardMatrix chainSixUniformToTwoPath chainSixOrientationRankOne =
      (8 : ℚ) • chainTwoOrientationRankOne := by
  rw [chainSixUniformToTwoPath, pushForwardMatrix_compose,
    chainSixUniform_pushforward, pushForwardMatrix_smul,
    chainThreeToTwo_pushforward]
  module

theorem chainSixUniform_first_step_closed :
    orientationDefect chainSixUniformPartial (1 / 4 : ℚ)
      (orientationRankOne chainSix) (orientationRankOne chainThree) = 0 := by
  apply (orientationDefect_eq_zero_iff_closed _ _ _ _).2
  rw [chainSix_orientationRankOne_matrix,
    chainThree_orientationRankOne_matrix,
    chainSixUniform_pushforward]
  module

theorem chainThreeToTwo_second_step_closed :
    orientationDefect chainThreeToTwoPartial (1 / 2 : ℚ)
      (orientationRankOne chainThree) (orientationRankOne chainTwo) = 0 := by
  apply (orientationDefect_eq_zero_iff_closed _ _ _ _).2
  rw [chainThree_orientationRankOne_matrix,
    chainTwo_orientationRankOne_matrix,
    chainThreeToTwo_pushforward]
  module

theorem chainSixUniform_composite_closed :
    orientationDefect chainSixUniformToTwoPath (1 / 8 : ℚ)
      (orientationRankOne chainSix) (orientationRankOne chainTwo) = 0 := by
  apply (orientationDefect_eq_zero_iff_closed _ _ _ _).2
  rw [chainSix_orientationRankOne_matrix,
    chainTwo_orientationRankOne_matrix,
    chainSixUniform_composite_pushforward]
  module

/-! ## 4. Nonuniform fibers force multiple couplings -/

theorem chainSixNonuniform_pushforward :
    pushForwardMatrix chainSixNonuniformPartial chainSixOrientationRankOne =
      chainSixNonuniformPushedOrientation := by
  rw [chainSixNonuniformPartial_apply]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp_rw [pushForwardMatrix, Finset.sum_fin_eq_sum_range]
  all_goals
    norm_num [chainSixOrientationRankOne,
      chainSixNonuniformPushedOrientation,
      Finset.sum_range_succ, Fin.ext_iff]

/-- The three coarse pair couplings are `2`, `3`, and `6`; no common scalar
can turn all of them into the native unit orientation coupling. -/
theorem chainSixNonuniform_no_scalar_closure :
    ¬ ∃ weight : ℚ,
      weight • pushForwardMatrix chainSixNonuniformPartial
        chainSixOrientationRankOne = chainThreeOrientationRankOne := by
  rw [chainSixNonuniform_pushforward]
  rintro ⟨weight, h⟩
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  change weight * 2 = 1 at h01
  change weight * 3 = 1 at h02
  linarith

theorem chainSixNonuniform_defect_ne_zero (weight : ℚ) :
    orientationDefect chainSixNonuniformPartial weight
      (orientationRankOne chainSix) (orientationRankOne chainThree) ≠ 0 := by
  intro hZero
  have hClosed :=
    (orientationDefect_eq_zero_iff_closed _ _ _ _).1 hZero
  apply chainSixNonuniform_no_scalar_closure
  refine ⟨weight, ?_⟩
  simpa [chainSix_orientationRankOne_matrix,
    chainThree_orientationRankOne_matrix] using hClosed

/-! ## 5. Master coupling-flow theorem -/

theorem orientation_coupling_flow_uniformity_criterion :
    pushForwardMatrix chainSixUniformPartial chainSixOrientationRankOne =
      (4 : ℚ) • chainThreeOrientationRankOne
    ∧ pushForwardMatrix chainThreeToTwoPartial chainThreeOrientationRankOne =
      (2 : ℚ) • chainTwoOrientationRankOne
    ∧ pushForwardMatrix chainSixUniformToTwoPath chainSixOrientationRankOne =
      (8 : ℚ) • chainTwoOrientationRankOne
    ∧ orientationDefect chainSixUniformPartial (1 / 4 : ℚ)
      (orientationRankOne chainSix) (orientationRankOne chainThree) = 0
    ∧ orientationDefect chainThreeToTwoPartial (1 / 2 : ℚ)
      (orientationRankOne chainThree) (orientationRankOne chainTwo) = 0
    ∧ orientationDefect chainSixUniformToTwoPath (1 / 8 : ℚ)
      (orientationRankOne chainSix) (orientationRankOne chainTwo) = 0
    ∧ (∀ weight : ℚ,
      orientationDefect chainSixNonuniformPartial weight
        (orientationRankOne chainSix) (orientationRankOne chainThree) ≠ 0) := by
  exact ⟨chainSixUniform_pushforward,
    chainThreeToTwo_pushforward,
    chainSixUniform_composite_pushforward,
    chainSixUniform_first_step_closed,
    chainThreeToTwo_second_step_closed,
    chainSixUniform_composite_closed,
    chainSixNonuniform_defect_ne_zero⟩

/-! ## Trust regression -/

#print axioms chainSixUniform_pushforward
#print axioms chainSixUniform_composite_pushforward
#print axioms chainSixUniform_composite_closed
#print axioms chainSixNonuniform_pushforward
#print axioms chainSixNonuniform_no_scalar_closure
#print axioms chainSixNonuniform_defect_ne_zero
#print axioms orientation_coupling_flow_uniformity_criterion

end UnifiedTheory.Audit.KFOrientationCouplingFlow
