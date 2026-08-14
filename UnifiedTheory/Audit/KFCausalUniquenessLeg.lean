/-
  Audit/KFCausalUniquenessLeg.lean

  THE UNIQUENESS LEG: MACHINE-CHECKED CORNERS OF "WHY COMPLEX
  QUADRATIC QUANTUM GROWTH" (companion to UNIQUENESS_LEG.md)

  1. `real_binary_bi_normalized_deterministic` - REAL amplitudes with
     both conservation laws at a binary branching are deterministic:
     a + b = 1 and a^2 + b^2 = 1 force (a,b) in {(1,0),(0,1)}.
     Nontrivial binary branching therefore REQUIRES complex phases
     (the quadrature circle of the pi/4 theorem).
  2. `l1_mixing_impossible` - the p = 1 instance of the Lamperti
     obstruction: no 2x2 real matrix with all entries nonzero
     preserves the l^1 norm on the four vectors e1, e2, (1,1),
     (1,-1).  (Linear lossless dynamics at p = 1 cannot mix; the
     general-p analytic proof is in the companion note; p = 2 is the
     unique mixing-compatible exponent.)
  3. `phase_order_matters_in_quaternions` - noncommuting unit phases
     break path-order independence: the covariance axiom (phase
     telescoping) forces an abelian phase group, excluding
     quaternionic amplitudes.  Witness: i * j = -(j * i) != j * i in
     the quaternions.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUniquenessLeg

/-! ## 1. Real branching is deterministic -/

/-- Real amplitudes under double conservation at a binary branching
are deterministic: the intersection of the plane `a + b = 1` with the
circle `a^2 + b^2 = 1` in the REAL plane is the two classical points.
Complex phases are necessary for nontrivial binary branching. -/
theorem real_binary_bi_normalized_deterministic (a b : ℝ)
    (h1 : a + b = 1) (h2 : a ^ 2 + b ^ 2 = 1) :
    (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  have hab : a * b = 0 := by nlinarith
  rcases mul_eq_zero.mp hab with ha | hb
  · right
    constructor
    · exact ha
    · linarith
  · left
    constructor
    · linarith
    · exact hb

/-! ## 2. The p = 1 Lamperti instance -/

/-- No 2x2 real matrix with all entries nonzero preserves the l^1
norm on e1, e2, (1,1) and (1,-1): equality in the triangle
inequality on (1,1) forces same-sign columns entrywise, on (1,-1)
opposite signs - contradiction.  Linear lossless dynamics with the
l^1 measure cannot mix branches. -/
theorem l1_mixing_impossible (a b c d : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he1 : |a| + |c| = 1) (he2 : |b| + |d| = 1)
    (hplus : |a + b| + |c + d| = 2)
    (hminus : |a - b| + |c - d| = 2) : False := by
  have t1 : |a + b| ≤ |a| + |b| := by
    cases abs_cases (a + b) <;> cases abs_cases a <;>
      cases abs_cases b <;> linarith
  have t2 : |c + d| ≤ |c| + |d| := by
    cases abs_cases (c + d) <;> cases abs_cases c <;>
      cases abs_cases d <;> linarith
  have t3 : |a - b| ≤ |a| + |b| := by
    cases abs_cases (a - b) <;> cases abs_cases a <;>
      cases abs_cases b <;> linarith
  have t4 : |c - d| ≤ |c| + |d| := by
    cases abs_cases (c - d) <;> cases abs_cases c <;>
      cases abs_cases d <;> linarith
  have s1 : |a + b| = |a| + |b| := by linarith
  have s2 : |a - b| = |a| + |b| := by linarith
  -- squaring the equalities: |a+b| = |a|+|b| gives ab = |a||b| >= 0,
  -- |a-b| = |a|+|b| gives -ab = |a||b| >= 0; both force ab = 0.
  have q1 : (a + b) ^ 2 = (|a| + |b|) ^ 2 := by rw [← s1, sq_abs]
  have q2 : (a - b) ^ 2 = (|a| + |b|) ^ 2 := by rw [← s2, sq_abs]
  have habs : a * b = |a| * |b| := by
    have : a ^ 2 + 2 * (a * b) + b ^ 2 =
        |a| ^ 2 + 2 * (|a| * |b|) + |b| ^ 2 := by
      have := q1
      ring_nf at this ⊢
      nlinarith [this]
    have h2a : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    have h2b : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
    nlinarith [this]
  have habs' : -(a * b) = |a| * |b| := by
    have : a ^ 2 - 2 * (a * b) + b ^ 2 =
        |a| ^ 2 + 2 * (|a| * |b|) + |b| ^ 2 := by
      have := q2
      ring_nf at this ⊢
      nlinarith [this]
    have h2a : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    have h2b : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
    nlinarith [this]
  have hzero : a * b = 0 := by linarith
  rcases mul_eq_zero.mp hzero with h | h
  · exact ha h
  · exact hb h

/-! ## 3. Noncommuting phases break covariance -/

open Quaternion in
/-- Quaternionic unit phases are path-order dependent: for the unit
quaternions i and j, the two path products differ.  Covariance
(path-order independence of class amplitudes, the phase-telescoping
axiom) therefore forces an abelian phase group: complex, not
quaternionic. -/
theorem phase_order_matters_in_quaternions :
    ∃ u v : ℍ[ℝ], u * v ≠ v * u := by
  refine ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ?_⟩
  intro h
  have hk := congrArg (fun q : ℍ[ℝ] => q.imK) h
  simp [Quaternion.imK_mul] at hk
  norm_num at hk

#print axioms real_binary_bi_normalized_deterministic
#print axioms l1_mixing_impossible
#print axioms phase_order_matters_in_quaternions

end UnifiedTheory.Audit.KFCausalUniquenessLeg
