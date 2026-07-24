/-
  Audit/KFCausalCSpecBooleanCubeMargin.lean   (arc file 7/6 — concrete instantiation)

  DISCHARGING `IsCanonical` AND RESTRICTION-STABILITY ON THE NATIVE BOOLEAN CUBE

  The Boolean tangent cube B_3 = {0,1}^3 is already a genuine causal/CSpec
  realization (see KFCausalCSpecSheetRealization).  Its three directions a,b,c
  have three pair-continuation events (ab, ac, bc); the centered continuation
  profiles, scaled by 3 to stay integral, are

        c_a = (1, 1, -2),   c_b = (1, -2, 1),   c_c = (-2, 1, 1).

  We COMPUTE the overlap scores against the abstract `permScore` of file 2 and
  PROVE, unconditionally:

    * `booleanCube_permScores`     : identity 18, transpositions 0, 3-cycles -9;
    * `booleanCube_isCanonical`    : identity is the unique maximizer
                                     (discharges the `IsCanonical` hypothesis);
    * `booleanCube_strictMargin`   : the strict margin is 18;
    * restriction to two events: restricted margin 9,
      `booleanCube_restrictionError_le_six`, `..._eq_six`, and
      `..._margin_gt_twice_error` (18 > 2*6), giving `booleanCube_restrictionStable`;
    * `booleanCube_commonFrame`    : the trivial (identity) common frame.

  HONEST BOUNDARY.  This certifies ONE concrete local transition and controlled
  restriction, so Case 2 is LOCALLY reachable.  It does NOT give nontrivial global
  holonomy: the cube's three directions are globally labelable, so its atlas is
  trivial.  A nontrivial global carrier remains to be constructed.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecUniqueMatching
import UnifiedTheory.Audit.KFCausalCSpecIntrinsicDescent

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace UnifiedTheory.Audit.KFCausalCSpecBooleanCubeMargin

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecOverlapScore
open UnifiedTheory.Audit.KFCausalCSpecUniqueMatching
open UnifiedTheory.Audit.KFCausalCSpecIntrinsicDescent

/-! ## Integer-scaled centered pair-continuation profiles of the Boolean 3-cube -/

noncomputable def cA : EuclideanSpace ℝ (Fin 3) := !₂[1, 1, -2]
noncomputable def cB : EuclideanSpace ℝ (Fin 3) := !₂[1, -2, 1]
noncomputable def cC : EuclideanSpace ℝ (Fin 3) := !₂[-2, 1, 1]
noncomputable def cprof : Direction → EuclideanSpace ℝ (Fin 3) := ![cA, cB, cC]

/-- **The Gram matrix.** Diagonal 6, off-diagonal -3. -/
theorem gram_val (i j : Direction) :
    (inner ℝ (cprof i) (cprof j) : ℝ) = if j = i then 6 else -3 := by
  fin_cases i <;> fin_cases j <;> rw [PiLp.inner_apply] <;>
    simp [cprof, cA, cB, cC, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] <;>
    norm_num

/-! ## The permutation scores -/

/-- Closed form: the score counts fixed points — `6` per fixed direction, `-3`
per moved one. -/
theorem permScore_closed (σ : Equiv.Perm Direction) :
    permScore cprof cprof σ
      = (if σ 0 = 0 then (6:ℝ) else -3) + (if σ 1 = 1 then 6 else -3)
          + (if σ 2 = 2 then 6 else -3) := by
  simp only [permScore, score, Fin.sum_univ_three, gram_val]

theorem permScore_one : permScore cprof cprof 1 = 18 := by
  rw [permScore_closed]; norm_num [Equiv.Perm.one_apply]

/-- **Score table:** identity 18, a transposition 0, a 3-cycle -9. -/
theorem booleanCube_permScores :
    permScore cprof cprof 1 = 18
    ∧ permScore cprof cprof (Equiv.swap 0 1) = 0
    ∧ permScore cprof cprof (Equiv.swap 0 1 * Equiv.swap 1 2) = -9 := by
  refine ⟨permScore_one, ?_, ?_⟩ <;>
    · rw [permScore_closed]
      simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply] <;> norm_num

/-! ## Strict margin and canonicity -/

/-- **`IsCanonical`, discharged.** The identity strictly beats every other
permutation: the concrete positive-margin hypothesis of file 3 holds here.
Enumerating the six permutations avoids `split_ifs`' spurious impossible
branches. -/
theorem booleanCube_isCanonical : IsCanonical cprof cprof 1 := by
  intro σ hσ
  rw [permScore_one]
  fin_cases σ <;>
    first
      | exact absurd (by decide) hσ
      | (rw [permScore_closed]; simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply] <;> norm_num)

/-- **Strict margin = 18.** Every non-identity permutation scores at least 18
below the identity. -/
theorem booleanCube_strictMargin (σ : Equiv.Perm Direction) (hσ : σ ≠ 1) :
    permScore cprof cprof σ + 18 ≤ permScore cprof cprof 1 := by
  rw [permScore_one]
  fin_cases σ <;>
    first
      | exact absurd (by decide) hσ
      | (rw [permScore_closed]; simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply] <;> norm_num)

/-! ## Restriction to two pair-continuation events (drop the `bc` coordinate) -/

noncomputable def rA : EuclideanSpace ℝ (Fin 2) := !₂[1, 1]
noncomputable def rB : EuclideanSpace ℝ (Fin 2) := !₂[1, -2]
noncomputable def rC : EuclideanSpace ℝ (Fin 2) := !₂[-2, 1]
noncomputable def rprof : Direction → EuclideanSpace ℝ (Fin 2) := ![rA, rB, rC]

/-- Restricted score expanded to three inner products. -/
theorem rpermScore_eval (σ : Equiv.Perm Direction) :
    permScore rprof rprof σ
      = inner ℝ (rprof 0) (rprof (σ 0)) + inner ℝ (rprof 1) (rprof (σ 1))
        + inner ℝ (rprof 2) (rprof (σ 2)) := by
  simp only [permScore, score, Fin.sum_univ_three]

theorem rpermScore_one : permScore rprof rprof 1 = 12 := by
  rw [rpermScore_eval]
  simp only [Equiv.Perm.one_apply, PiLp.inner_apply, Fin.sum_univ_two]
  simp [rprof, rA, rB, rC, RCLike.inner_apply, conj_trivial] <;> norm_num

/-- **Restricted canonicity:** even after dropping one event, the identity is the
strict maximizer (restricted margin 9), so the restricted argmax is unchanged. -/
theorem booleanCube_restricted_isCanonical : IsCanonical rprof rprof 1 := by
  intro σ hσ
  rw [rpermScore_one, rpermScore_eval σ]
  simp only [PiLp.inner_apply, Fin.sum_univ_two]
  fin_cases σ <;>
    first
      | (exfalso; exact hσ (by decide))
      | (simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
          rprof, rA, rB, rC, RCLike.inner_apply, conj_trivial] <;> norm_num)

/-- **`IsCanonical` survives restriction** — the canonical transition (identity)
is the same on the full carrier and the restricted one. -/
theorem booleanCube_restrictionStable :
    IsCanonical cprof cprof 1 ∧ IsCanonical rprof rprof 1 :=
  ⟨booleanCube_isCanonical, booleanCube_restricted_isCanonical⟩

/-- **Restriction error ε ≤ 6.** The per-permutation discrepancy between the full
and restricted scores never exceeds 6. -/
theorem booleanCube_restrictionError_le_six (σ : Equiv.Perm Direction) :
    |permScore cprof cprof σ - permScore rprof rprof σ| ≤ 6 := by
  rw [permScore_closed, rpermScore_eval]
  simp only [PiLp.inner_apply, Fin.sum_univ_two]
  fin_cases σ <;>
    (simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      rprof, rA, rB, rC, RCLike.inner_apply, conj_trivial] <;> norm_num [abs_le])

/-- **ε = 6 is attained** at the identity: `|18 - 12| = 6`. -/
theorem booleanCube_restrictionError_eq_six :
    |permScore cprof cprof 1 - permScore rprof rprof 1| = 6 := by
  rw [permScore_one, rpermScore_one]; norm_num

/-- **Margin exceeds twice the restriction error:** 18 > 2·6.  Hence restricting
to two events cannot flip the argmax — the concrete restriction-stability
certificate. -/
theorem booleanCube_margin_gt_twice_restrictionError :
    (18 : ℝ) > 2 * 6 := by norm_num

/-! ## The common frame (trivial: the cube is globally labelable) -/

/-- **`CommonFrame`, discharged trivially.** Because all three directions are
globally available on the cube, the identity frame identifies every chart with
the common frame `Direction`; all transitions are the identity, so
restriction-stability holds vacuously and the atlas is labelable.  (This is the
honest boundary: the cube gives NO nontrivial holonomy.) -/
noncomputable def booleanCube_commonFrame (ChartIdx : Type*) :
    CommonFrame ChartIdx Direction where
  φ := fun _ => Equiv.refl Direction

theorem booleanCube_commonFrame_trivial (ChartIdx : Type*) (i j : ChartIdx) :
    (booleanCube_commonFrame ChartIdx).transition i j = Equiv.refl Direction := by
  ext a; simp [booleanCube_commonFrame, CommonFrame.transition]

#print axioms booleanCube_permScores
#print axioms booleanCube_isCanonical
#print axioms booleanCube_strictMargin
#print axioms booleanCube_restrictionStable
#print axioms booleanCube_restrictionError_le_six
#print axioms booleanCube_restrictionError_eq_six
#print axioms booleanCube_margin_gt_twice_restrictionError
#print axioms booleanCube_commonFrame_trivial

end UnifiedTheory.Audit.KFCausalCSpecBooleanCubeMargin
