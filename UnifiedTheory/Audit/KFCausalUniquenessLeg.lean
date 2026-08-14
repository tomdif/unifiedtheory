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
  4. `lamperti_two_by_two_gt_two` - the p > 2 Lamperti obstruction
     at 2x2 (four probes e1, e2, (1,1), (1,-1); parallelogram +
     Minkowski + strict superadditivity of x^(p/2)).
  5. `lamperti_columns_ne_two` - THE COMPLETE LAMPERTI OBSTRUCTION:
     every real p with 0 < p, p != 2, every dimension n, two columns
     sharing one support coordinate.  Above p = 2: midpoint
     convexity vs strict superadditivity of x^(p/2).  Below p = 2
     everything mirrors: midpoint concavity vs strict subadditivity.
     Same four probes decide the whole line.  Abstract cores:
     `quadrature_probes_gt_one_impossible` / `_lt_one_impossible`.
  6. `p_two_probes_force_unitary` - the p = 2 escape is EXACTLY
     unitarity: probes e1, e2, (1,1), (1,i) force
     conj a * b + conj c * d = 0.  The interference sector allowed
     at p = 2 is precisely the unitary group.
  7. `mixing_lossless_forces_p_eq_two` - NO-HYBRID THEOREM: a
     lossless linear step that superposes two basis directions
     anywhere forces p = 2 for the WHOLE space.  No lossless world
     mixes a quantum sector with any other measure exponent.
  8. `lossless_ne_two_is_weighted_permutation` - the POSITIVE
     Lamperti theorem: for p != 2 a lossless step IS a weighted
     permutation (each column one unit-modulus entry, locations a
     permutation).  Classical dynamics is all that exists off p = 2.
  9. `l2_lossless_columns_orthogonal` - general-n unitarity: an
     l^2-lossless step has orthonormal columns.  p = 2 = U(n).
  10. `lossless_dichotomy` + `frozen_measure_ne_two` - THE GRAND
     DICHOTOMY: every lossless dynamics is a weighted permutation or
     unitary, nothing else; and for p != 2 the action on MEASURES is
     a fixed permutation independent of phases - probabilities can
     be relabeled but never continuously transported.  Continuous
     evolution of the observable world is uniquely quantum.
  11. `change_and_divisibility_force_born` - THE DIVISIBLE-TIME
     THEOREM: a lossless dynamics whose step has a lossless m-th
     root for every m (time has no smallest step), and under which
     anything at all changes, is forced onto p = 2 - hence unitary
     quantum mechanics.  Eliminates the nonclassicality axiom A5:
     no axiom mentions superposition.  Mechanism: off p = 2 every
     root is a weighted permutation (structure theorem), measure
     actions iterate as powers of its permutation
     (`frozen_measure_pow`), and at m = |Perm(Fin n)| Lagrange
     gives sigma^m = 1 (`root_at_symmetric_order_forces_static`):
     the dynamics is measure-static, nothing ever happens
     (`divisible_time_forces_static`).
  12. `root_at_group_exponent_forces_static` - the consumed root
     order sharpened from n! to the group EXPONENT of S_n
     (= lcm(1,...,n)): one lossless root at that order suffices.
  13. `antiunitary_has_no_half_step` - the square of any semilinear
     map is complex-linear, so a nonzero conjugate-linear
     (antiunitary-type) step has NO square root among semilinear
     maps: divisibility at m = 2 eliminates antiunitary evolution.
     Purely algebraic - no norm needed.
  14. `lossless_bijection_is_real_linear` - LINEARITY IS DERIVED
     (Mazur-Ulam): for p >= 1, any surjective map preserving the
     state measure and pairwise distinguishability is real-linear.
     The linearity axiom A1 reduces to losslessness-of-information.
  15. `born_function_unique` - THE BORN FUNCTION FROM MONOTONE
     CAUCHY: a monotone measure additive over perpendicular
     decompositions is exactly f(x) = x^2 f(1).  No continuity
     assumed (monotone solutions of Cauchy's equation are linear:
     `monotone_additive_on_cone_is_linear`).  The half of A6 that
     classifies the measure GIVEN Pythagorean additivity is now a
     theorem; deriving that additivity from a mixing lossless step
     (Orlicz-Lamperti) is the registered open seam.
  16. `born_from_time_alone` - THE ZERO-STRUCTURE CAPSTONE: a bare
     SET-MAP of states (no linearity, no complex structure, no
     losslessness of F itself assumed) whose steps subdivide into
     surjective measure- and distinguishability-preserving
     sub-steps, and under which anything changes, is forced onto
     p = 2.  Chain: Mazur-Ulam makes each root real-linear; the
     REAL block-structure theorem `real_lossless_frozen_measure`
     (the Lamperti probes never needed complex-linearity - the
     within-block pair is exactly the one the probes cannot
     couple) freezes measures at p != 2; the group-exponent root +
     Lagrange makes F measure-static.  Remaining structure: the
     measure family itself, p >= 1, finite n.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Exponent
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Lp.PiLp

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


/-! ## 4. The general-p Lamperti obstruction, p > 2 (machine-checked)

For every real p > 2, NO 2x2 complex matrix whose first row has two
nonzero entries can satisfy the four isometry probes e1, e2, (1,1),
(1,-1) in the l^p norm.  Proof without calculus: parallelogram law
per coordinate + two-term Minkowski (Real.Lp_add_le) + STRICT
superadditivity of x ^ q for q = p/2 > 1, via the x ^ q < x trick on
(0,1).  Together with `l1_mixing_impossible` (p = 1, discrete probes)
and the analytic t-expansion for 1 < p < 2 (UNIQUENESS_LEG.md), this
is the Lamperti leg: only p = 2 admits mixing isometries. -/

/-- Strict superadditivity of `x ^ q` for `q > 1` on positives. -/
theorem rpow_superadd_strict {q A B : ℝ} (hq : 1 < q)
    (hA : 0 < A) (hB : 0 < B) : A ^ q + B ^ q < (A + B) ^ q := by
  have hAB : 0 < A + B := by linarith
  have hs : A / (A + B) < 1 := by
    rw [div_lt_one hAB]; linarith
  have ht : B / (A + B) < 1 := by
    rw [div_lt_one hAB]; linarith
  have hs0 : 0 < A / (A + B) := div_pos hA hAB
  have ht0 : 0 < B / (A + B) := div_pos hB hAB
  have key1 : (A / (A + B)) ^ q < A / (A + B) := by
    have h := Real.rpow_lt_rpow_of_exponent_gt hs0 hs hq
    rwa [Real.rpow_one] at h
  have key2 : (B / (A + B)) ^ q < B / (A + B) := by
    have h := Real.rpow_lt_rpow_of_exponent_gt ht0 ht hq
    rwa [Real.rpow_one] at h
  have hApos : (0:ℝ) < (A + B) ^ q := Real.rpow_pos_of_pos hAB q
  have eA : A = (A + B) * (A / (A + B)) := by field_simp
  have eB : B = (A + B) * (B / (A + B)) := by field_simp
  have hA' : A ^ q = (A + B) ^ q * (A / (A + B)) ^ q := by
    conv_lhs => rw [eA]
    rw [Real.mul_rpow hAB.le hs0.le]
  have hB' : B ^ q = (A + B) ^ q * (B / (A + B)) ^ q := by
    conv_lhs => rw [eB]
    rw [Real.mul_rpow hAB.le ht0.le]
  have hsum : A / (A + B) + B / (A + B) = 1 := by field_simp
  calc A ^ q + B ^ q
      = (A + B) ^ q * ((A / (A + B)) ^ q + (B / (A + B)) ^ q) := by
        rw [hA', hB']; ring
    _ < (A + B) ^ q * (A / (A + B) + B / (A + B)) :=
        mul_lt_mul_of_pos_left (add_lt_add key1 key2) hApos
    _ = (A + B) ^ q := by rw [hsum, mul_one]

/-- Nonstrict version (allows zero arguments). -/
theorem rpow_superadd {q A B : ℝ} (hq : 1 < q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : A ^ q + B ^ q ≤ (A + B) ^ q := by
  have hq0 : q ≠ 0 := ne_of_gt (by linarith)
  rcases eq_or_lt_of_le hA with h | h
  · rw [← h, Real.zero_rpow hq0]; simp
  rcases eq_or_lt_of_le hB with h2 | h2
  · rw [← h2, Real.zero_rpow hq0]; simp
  exact (rpow_superadd_strict hq h h2).le

/-- THE p > 2 LAMPERTI OBSTRUCTION, machine-checked: for any real
p > 2, no 2x2 complex matrix [[a,b],[c,d]] with a ≠ 0 and b ≠ 0 can
preserve the l^p norm of e₁, e₂, (1,1) and (1,-1) simultaneously.
Hence a p-isometric step (p > 2) cannot mix: its columns have
disjoint supports (weighted permutation), so nonclassical branching
(axiom A5) forces p ≤ 2. -/
theorem lamperti_two_by_two_gt_two {p : ℝ} (hp : 2 < p)
    (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (he1 : ‖a‖ ^ p + ‖c‖ ^ p = 1)
    (he2 : ‖b‖ ^ p + ‖d‖ ^ p = 1)
    (hplus : ‖a + b‖ ^ p + ‖c + d‖ ^ p = 2)
    (hminus : ‖a - b‖ ^ p + ‖c - d‖ ^ p = 2) : False := by
  set q : ℝ := p / 2 with hqdef
  have hq : 1 < q := by rw [hqdef]; linarith
  have hq0 : q ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < q)
  -- convert ‖z‖^p into (‖z‖*‖z‖)^q
  have conv : ∀ z : ℂ, ‖z‖ ^ p = (‖z‖ * ‖z‖) ^ q := by
    intro z
    have h2q : p = 2 * q := by rw [hqdef]; ring
    have hsq : ‖z‖ * ‖z‖ = ‖z‖ ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [h2q, hsq, ← Real.rpow_mul (norm_nonneg z)]
  set A1 := ‖a + b‖ * ‖a + b‖ with hA1
  set B1 := ‖a - b‖ * ‖a - b‖ with hB1
  set A2 := ‖c + d‖ * ‖c + d‖ with hA2
  set B2 := ‖c - d‖ * ‖c - d‖ with hB2
  set X := ‖a‖ * ‖a‖ with hX
  set Y := ‖b‖ * ‖b‖ with hY
  set Z := ‖c‖ * ‖c‖ with hZ
  set W := ‖d‖ * ‖d‖ with hW
  have hXpos : 0 < X := by
    rw [hX]; exact mul_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr ha)
  have hYpos : 0 < Y := by
    rw [hY]; exact mul_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hb)
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hA10 : 0 ≤ A1 := by rw [hA1]; positivity
  have hA20 : 0 ≤ A2 := by rw [hA2]; positivity
  have hB10 : 0 ≤ B1 := by rw [hB1]; positivity
  have hB20 : 0 ≤ B2 := by rw [hB2]; positivity
  -- the four probe conditions in q-variables
  have c1 : X ^ q + Z ^ q = 1 := by
    rw [hX, hZ, ← conv a, ← conv c]; exact he1
  have c2 : Y ^ q + W ^ q = 1 := by
    rw [hY, hW, ← conv b, ← conv d]; exact he2
  have c3 : A1 ^ q + A2 ^ q = 2 := by
    rw [hA1, hA2, ← conv (a + b), ← conv (c + d)]; exact hplus
  have c4 : B1 ^ q + B2 ^ q = 2 := by
    rw [hB1, hB2, ← conv (a - b), ← conv (c - d)]; exact hminus
  -- parallelogram law per coordinate
  have par1 : A1 + B1 = 2 * (X + Y) := by
    rw [hA1, hB1, hX, hY]; exact parallelogram_law_with_norm ℂ a b
  have par2 : A2 + B2 = 2 * (Z + W) := by
    rw [hA2, hB2, hZ, hW]; exact parallelogram_law_with_norm ℂ c d
  set S := (A1 + B1) ^ q + (A2 + B2) ^ q with hS
  -- LOWER bound: strict superadditivity through the parallelogram
  have low : 2 ^ q * 2 < S := by
    have l1 : (2 * X) ^ q + (2 * Y) ^ q < (A1 + B1) ^ q := by
      rw [par1, show (2:ℝ) * (X + Y) = 2 * X + 2 * Y by ring]
      exact rpow_superadd_strict hq (by linarith) (by linarith)
    have l2 : (2 * Z) ^ q + (2 * W) ^ q ≤ (A2 + B2) ^ q := by
      rw [par2, show (2:ℝ) * (Z + W) = 2 * Z + 2 * W by ring]
      exact rpow_superadd hq (by linarith) (by linarith)
    have e1 : (2 * X) ^ q = 2 ^ q * X ^ q :=
      Real.mul_rpow (by norm_num) hXpos.le
    have e2 : (2 * Y) ^ q = 2 ^ q * Y ^ q :=
      Real.mul_rpow (by norm_num) hYpos.le
    have e3 : (2 * Z) ^ q = 2 ^ q * Z ^ q :=
      Real.mul_rpow (by norm_num) hZ0
    have e4 : (2 * W) ^ q = 2 ^ q * W ^ q :=
      Real.mul_rpow (by norm_num) hW0
    have expand : 2 ^ q * X ^ q + 2 ^ q * Y ^ q +
        (2 ^ q * Z ^ q + 2 ^ q * W ^ q) = 2 ^ q * 2 := by
      have hgrp : 2 ^ q * X ^ q + 2 ^ q * Y ^ q +
          (2 ^ q * Z ^ q + 2 ^ q * W ^ q)
          = 2 ^ q * ((X ^ q + Z ^ q) + (Y ^ q + W ^ q)) := by ring
      rw [hgrp, c1, c2]; norm_num
    calc 2 ^ q * 2
        = 2 ^ q * X ^ q + 2 ^ q * Y ^ q +
          (2 ^ q * Z ^ q + 2 ^ q * W ^ q) := expand.symm
      _ = ((2 * X) ^ q + (2 * Y) ^ q) + ((2 * Z) ^ q + (2 * W) ^ q) := by
          rw [e1, e2, e3, e4]
      _ < (A1 + B1) ^ q + (A2 + B2) ^ q := add_lt_add_of_lt_of_le l1 l2
      _ = S := hS.symm
  -- UPPER bound: two-term Minkowski (Real.Lp_add_le)
  have mink := Real.Lp_add_le (Finset.univ : Finset (Fin 2))
    (![A1, A2]) (![B1, B2]) hq.le
  have sum1 : ∑ i : Fin 2, |(![A1, A2]) i| ^ q = 2 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [abs_of_nonneg hA10, abs_of_nonneg hA20]
    exact c3
  have sum2 : ∑ i : Fin 2, |(![B1, B2]) i| ^ q = 2 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [abs_of_nonneg hB10, abs_of_nonneg hB20]
    exact c4
  have sum3 : ∑ i : Fin 2, |(![A1, A2]) i + (![B1, B2]) i| ^ q = S := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [abs_of_nonneg (show (0:ℝ) ≤ A1 + B1 by linarith),
        abs_of_nonneg (show (0:ℝ) ≤ A2 + B2 by linarith), hS]
  rw [sum1, sum2, sum3] at mink
  -- mink : S ^ (1/q) ≤ 2 ^ (1/q) + 2 ^ (1/q)
  have hS0 : 0 ≤ S := by
    rw [hS]
    have h1 : (0:ℝ) ≤ (A1 + B1) ^ q := Real.rpow_nonneg (by linarith) q
    have h2 : (0:ℝ) ≤ (A2 + B2) ^ q := Real.rpow_nonneg (by linarith) q
    linarith
  have hexp : 1 / q * q = 1 := by field_simp
  have raise : S ≤ (2 ^ (1 / q) + 2 ^ (1 / q)) ^ q := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hS0 _) mink
      (by linarith : (0:ℝ) ≤ q)
    rwa [← Real.rpow_mul hS0, hexp, Real.rpow_one] at h
  have final : ((2:ℝ) ^ (1 / q) + 2 ^ (1 / q)) ^ q = 2 ^ q * 2 := by
    rw [show (2:ℝ) ^ (1 / q) + 2 ^ (1 / q) = 2 * 2 ^ (1 / q) by ring,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2)
          (Real.rpow_nonneg (by norm_num) _),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), hexp, Real.rpow_one]
  rw [final] at raise
  linarith



/-! ## 5. The COMPLETE Lamperti obstruction: every p ≠ 2, every arity

The 2x2 / p > 2 result above generalizes in two directions at once,
with NO new analytic input:

  (a) ARBITRARY ARITY: the proof never used dimension 2 - the
      parallelogram law holds per coordinate and midpoint convexity /
      superadditivity sum over any `Fin n`.
  (b) THE WHOLE RANGE 0 < p < 2 AS WELL: for q = p/2 < 1 every
      inequality REVERSES - x ^ q is midpoint-CONCAVE and strictly
      SUBadditive - so the same four probes yield the mirror-image
      contradiction.  (This corrects an earlier informal claim that
      the four probes were slack below p = 2: they are not.  The
      correct pairing is convexity-with-superadditivity above 2 and
      concavity-with-subadditivity below 2.)

Consequence: for EVERY real p with 0 < p, p ≠ 2, two columns of a
lossless step that overlap at even ONE coordinate are impossible -
column supports are pairwise disjoint and the dynamics is a weighted
permutation (relabeled classical determinism).  Superposition at any
branching of any arity forces p = 2 exactly. -/

/-- Midpoint convexity of `x ^ q` for `q ≥ 1`. -/
theorem rpow_midpoint_convex {q A B : ℝ} (hq : 1 ≤ q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + B) ^ q ≤ 2 ^ (q - 1) * (A ^ q + B ^ q) := by
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 2)), (0:ℝ) ≤ ![A, B] i := by
    intro i _
    fin_cases i
    · exact hA
    · exact hB
  have h := Real.rpow_arith_mean_le_arith_mean_rpow
    (Finset.univ : Finset (Fin 2)) (fun _ => (1:ℝ)/2) ![A, B]
    (fun i _ => by norm_num) (by rw [Fin.sum_univ_two]; norm_num) hz hq
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hmul : (A + B) ^ q = 2 ^ q * ((1:ℝ)/2 * A + 1/2 * B) ^ q := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2)
      (by linarith : (0:ℝ) ≤ 1/2 * A + 1/2 * B)]
    congr 1
    ring
  have h2q : (0:ℝ) < 2 ^ q := Real.rpow_pos_of_pos two_pos q
  calc (A + B) ^ q
      = 2 ^ q * ((1:ℝ)/2 * A + 1/2 * B) ^ q := hmul
    _ ≤ 2 ^ q * ((1:ℝ)/2 * A ^ q + 1/2 * B ^ q) :=
        mul_le_mul_of_nonneg_left h h2q.le
    _ = 2 ^ (q - 1) * (A ^ q + B ^ q) := by
        rw [Real.rpow_sub two_pos, Real.rpow_one]
        ring

/-- Midpoint concavity of `x ^ q` for `0 < q ≤ 1`: obtained by
applying midpoint convexity at exponent `1/q ≥ 1` to `A^q, B^q`. -/
theorem rpow_midpoint_concave {q A B : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    2 ^ (q - 1) * (A ^ q + B ^ q) ≤ (A + B) ^ q := by
  have hqinv : 1 ≤ 1 / q := by
    rw [le_div_iff₀ hq0]; linarith
  have h := rpow_midpoint_convex (q := 1 / q) (A := A ^ q) (B := B ^ q)
    hqinv (Real.rpow_nonneg hA q) (Real.rpow_nonneg hB q)
  have hAid : (A ^ q) ^ ((1:ℝ)/q) = A := by
    rw [← Real.rpow_mul hA, mul_one_div, div_self (ne_of_gt hq0),
      Real.rpow_one]
  have hBid : (B ^ q) ^ ((1:ℝ)/q) = B := by
    rw [← Real.rpow_mul hB, mul_one_div, div_self (ne_of_gt hq0),
      Real.rpow_one]
  rw [hAid, hBid] at h
  -- h : (A^q + B^q) ^ (1/q) ≤ 2 ^ (1/q - 1) * (A + B)
  have hsum0 : (0:ℝ) ≤ A ^ q + B ^ q := by
    have := Real.rpow_nonneg hA q
    have := Real.rpow_nonneg hB q
    linarith
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hsum0 _) h hq0.le
  rw [← Real.rpow_mul hsum0, show (1:ℝ)/q * q = 1 by field_simp,
    Real.rpow_one] at h2
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (by linarith),
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at h2
  have hexp : ((1:ℝ)/q - 1) * q = 1 - q := by
    field_simp
  rw [hexp] at h2
  -- h2 : A^q + B^q ≤ 2 ^ (1 - q) * (A + B) ^ q
  have hq1pos : (0:ℝ) < 2 ^ (q - 1) := Real.rpow_pos_of_pos two_pos _
  have hprod : (2:ℝ) ^ (q - 1) * 2 ^ ((1:ℝ) - q) = 1 := by
    rw [← Real.rpow_add two_pos]
    norm_num
  calc 2 ^ (q - 1) * (A ^ q + B ^ q)
      ≤ 2 ^ (q - 1) * (2 ^ ((1:ℝ) - q) * (A + B) ^ q) :=
        mul_le_mul_of_nonneg_left h2 hq1pos.le
    _ = (2 ^ (q - 1) * 2 ^ ((1:ℝ) - q)) * (A + B) ^ q := by ring
    _ = (A + B) ^ q := by rw [hprod, one_mul]

/-- Strict SUBadditivity of `x ^ q` for `0 < q < 1` on positives
(mirror of `rpow_superadd_strict`). -/
theorem rpow_subadd_strict {q A B : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hA : 0 < A) (hB : 0 < B) : (A + B) ^ q < A ^ q + B ^ q := by
  have hAB : 0 < A + B := by linarith
  have hs : A / (A + B) < 1 := by
    rw [div_lt_one hAB]; linarith
  have ht : B / (A + B) < 1 := by
    rw [div_lt_one hAB]; linarith
  have hs0 : 0 < A / (A + B) := div_pos hA hAB
  have ht0 : 0 < B / (A + B) := div_pos hB hAB
  have key1 : A / (A + B) < (A / (A + B)) ^ q := by
    have h := Real.rpow_lt_rpow_of_exponent_gt hs0 hs hq1
    rwa [Real.rpow_one] at h
  have key2 : B / (A + B) < (B / (A + B)) ^ q := by
    have h := Real.rpow_lt_rpow_of_exponent_gt ht0 ht hq1
    rwa [Real.rpow_one] at h
  have hApos : (0:ℝ) < (A + B) ^ q := Real.rpow_pos_of_pos hAB q
  have eA : A = (A + B) * (A / (A + B)) := by field_simp
  have eB : B = (A + B) * (B / (A + B)) := by field_simp
  have hA' : A ^ q = (A + B) ^ q * (A / (A + B)) ^ q := by
    conv_lhs => rw [eA]
    rw [Real.mul_rpow hAB.le hs0.le]
  have hB' : B ^ q = (A + B) ^ q * (B / (A + B)) ^ q := by
    conv_lhs => rw [eB]
    rw [Real.mul_rpow hAB.le ht0.le]
  have hsum : A / (A + B) + B / (A + B) = 1 := by field_simp
  calc (A + B) ^ q
      = (A + B) ^ q * (A / (A + B) + B / (A + B)) := by
        rw [hsum, mul_one]
    _ < (A + B) ^ q * ((A / (A + B)) ^ q + (B / (A + B)) ^ q) :=
        mul_lt_mul_of_pos_left (add_lt_add key1 key2) hApos
    _ = A ^ q + B ^ q := by rw [hA', hB']; ring

/-- Nonstrict subadditivity (allows zero arguments). -/
theorem rpow_subadd {q A B : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : (A + B) ^ q ≤ A ^ q + B ^ q := by
  rcases eq_or_lt_of_le hA with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hq0)]; simp
  rcases eq_or_lt_of_le hB with h2 | h2
  · rw [← h2, Real.zero_rpow (ne_of_gt hq0)]; simp
  exact (rpow_subadd_strict hq0 hq1 h h2).le

/-- Abstract quadrature rigidity, q > 1: nonnegative sequences
coupled by the parallelogram identity cannot satisfy the four probe
sums (1,1,2,2) if any coordinate has both parents strictly positive.
Upper bound by midpoint convexity, lower by strict superadditivity. -/
theorem quadrature_probes_gt_one_impossible {q : ℝ} (hq : 1 < q)
    {n : ℕ} (P Q A B : Fin n → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hpar : ∀ i, A i + B i = 2 * (P i + Q i))
    (k : Fin n) (hPk : 0 < P k) (hQk : 0 < Q k)
    (s1 : ∑ i, P i ^ q = 1) (s2 : ∑ i, Q i ^ q = 1)
    (s3 : ∑ i, A i ^ q = 2) (s4 : ∑ i, B i ^ q = 2) : False := by
  have h2q : (2:ℝ) ^ (q - 1) = 2 ^ q / 2 := by
    rw [Real.rpow_sub two_pos, Real.rpow_one]
  have upper : ∑ i, (A i + B i) ^ q ≤ 2 ^ q * 2 := by
    calc ∑ i, (A i + B i) ^ q
        ≤ ∑ i, 2 ^ (q - 1) * (A i ^ q + B i ^ q) :=
          Finset.sum_le_sum fun i _ =>
            rpow_midpoint_convex hq.le (hA i) (hB i)
      _ = 2 ^ (q - 1) * ((∑ i, A i ^ q) + (∑ i, B i ^ q)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = 2 ^ q * 2 := by rw [s3, s4, h2q]; ring
  have lower : 2 ^ q * 2 < ∑ i, (A i + B i) ^ q := by
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (2 * P i) ^ q + (2 * Q i) ^ q ≤ (A i + B i) ^ q := by
      intro i _
      rw [hpar i, show (2:ℝ) * (P i + Q i) = 2 * P i + 2 * Q i by ring]
      exact rpow_superadd hq (by have := hP i; linarith)
        (by have := hQ i; linarith)
    have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)),
        (2 * P i) ^ q + (2 * Q i) ^ q < (A i + B i) ^ q := by
      refine ⟨k, Finset.mem_univ k, ?_⟩
      rw [hpar k, show (2:ℝ) * (P k + Q k) = 2 * P k + 2 * Q k by ring]
      exact rpow_superadd_strict hq (by linarith) (by linarith)
    have hsum := Finset.sum_lt_sum hle hlt
    have heval : ∑ i, ((2 * P i) ^ q + (2 * Q i) ^ q) = 2 ^ q * 2 := by
      rw [Finset.sum_add_distrib]
      have e1 : ∑ i, (2 * P i) ^ q = 2 ^ q * ∑ i, P i ^ q := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Real.mul_rpow (by norm_num) (hP i)
      have e2 : ∑ i, (2 * Q i) ^ q = 2 ^ q * ∑ i, Q i ^ q := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Real.mul_rpow (by norm_num) (hQ i)
      rw [e1, e2, s1, s2]; ring
    rwa [heval] at hsum
  linarith

/-- Abstract quadrature rigidity, 0 < q < 1: the mirror image -
lower bound by midpoint concavity, upper by strict subadditivity. -/
theorem quadrature_probes_lt_one_impossible {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) {n : ℕ} (P Q A B : Fin n → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hpar : ∀ i, A i + B i = 2 * (P i + Q i))
    (k : Fin n) (hPk : 0 < P k) (hQk : 0 < Q k)
    (s1 : ∑ i, P i ^ q = 1) (s2 : ∑ i, Q i ^ q = 1)
    (s3 : ∑ i, A i ^ q = 2) (s4 : ∑ i, B i ^ q = 2) : False := by
  have h2q : (2:ℝ) ^ (q - 1) = 2 ^ q / 2 := by
    rw [Real.rpow_sub two_pos, Real.rpow_one]
  have lower : 2 ^ q * 2 ≤ ∑ i, (A i + B i) ^ q := by
    calc 2 ^ q * 2
        = 2 ^ (q - 1) * ((∑ i, A i ^ q) + (∑ i, B i ^ q)) := by
          rw [s3, s4, h2q]; ring
      _ = ∑ i, 2 ^ (q - 1) * (A i ^ q + B i ^ q) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ i, (A i + B i) ^ q :=
          Finset.sum_le_sum fun i _ =>
            rpow_midpoint_concave hq0 hq1.le (hA i) (hB i)
  have upper : ∑ i, (A i + B i) ^ q < 2 ^ q * 2 := by
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (A i + B i) ^ q ≤ (2 * P i) ^ q + (2 * Q i) ^ q := by
      intro i _
      rw [hpar i, show (2:ℝ) * (P i + Q i) = 2 * P i + 2 * Q i by ring]
      exact rpow_subadd hq0 hq1 (by have := hP i; linarith)
        (by have := hQ i; linarith)
    have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)),
        (A i + B i) ^ q < (2 * P i) ^ q + (2 * Q i) ^ q := by
      refine ⟨k, Finset.mem_univ k, ?_⟩
      rw [hpar k, show (2:ℝ) * (P k + Q k) = 2 * P k + 2 * Q k by ring]
      exact rpow_subadd_strict hq0 hq1 (by linarith) (by linarith)
    have hsum := Finset.sum_lt_sum hle hlt
    have heval : ∑ i, ((2 * P i) ^ q + (2 * Q i) ^ q) = 2 ^ q * 2 := by
      rw [Finset.sum_add_distrib]
      have e1 : ∑ i, (2 * P i) ^ q = 2 ^ q * ∑ i, P i ^ q := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Real.mul_rpow (by norm_num) (hP i)
      have e2 : ∑ i, (2 * Q i) ^ q = 2 ^ q * ∑ i, Q i ^ q := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Real.mul_rpow (by norm_num) (hQ i)
      rw [e1, e2, s1, s2]; ring
    rwa [heval] at hsum
  linarith

/-- THE COMPLETE LAMPERTI OBSTRUCTION, machine-checked: for every
real p with 0 < p and p ≠ 2, in every dimension n, two columns
u, v of a lossless step that satisfy the four l^p probes and share
even one support coordinate are impossible.  Column supports of a
p-isometric step are pairwise disjoint: the dynamics is a weighted
permutation, and superposition at ANY branching arity forces
p = 2 exactly. -/
theorem lamperti_columns_ne_two {p : ℝ} (hp0 : 0 < p) (hp2 : p ≠ 2)
    {n : ℕ} (u v : Fin n → ℂ) (k : Fin n)
    (hu : u k ≠ 0) (hv : v k ≠ 0)
    (he1 : ∑ i, ‖u i‖ ^ p = 1) (he2 : ∑ i, ‖v i‖ ^ p = 1)
    (hplus : ∑ i, ‖u i + v i‖ ^ p = 2)
    (hminus : ∑ i, ‖u i - v i‖ ^ p = 2) : False := by
  set q : ℝ := p / 2 with hqdef
  have hq0 : 0 < q := by rw [hqdef]; linarith
  have conv : ∀ z : ℂ, ‖z‖ ^ p = (‖z‖ * ‖z‖) ^ q := by
    intro z
    have h2q : p = 2 * q := by rw [hqdef]; ring
    have hsq : ‖z‖ * ‖z‖ = ‖z‖ ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [h2q, hsq, ← Real.rpow_mul (norm_nonneg z)]
  have c1 : ∑ i, (‖u i‖ * ‖u i‖) ^ q = 1 :=
    (Finset.sum_congr rfl fun i _ => (conv (u i)).symm).trans he1
  have c2 : ∑ i, (‖v i‖ * ‖v i‖) ^ q = 1 :=
    (Finset.sum_congr rfl fun i _ => (conv (v i)).symm).trans he2
  have c3 : ∑ i, (‖u i + v i‖ * ‖u i + v i‖) ^ q = 2 :=
    (Finset.sum_congr rfl fun i _ => (conv (u i + v i)).symm).trans hplus
  have c4 : ∑ i, (‖u i - v i‖ * ‖u i - v i‖) ^ q = 2 :=
    (Finset.sum_congr rfl fun i _ => (conv (u i - v i)).symm).trans hminus
  have hpar : ∀ i : Fin n,
      ‖u i + v i‖ * ‖u i + v i‖ + ‖u i - v i‖ * ‖u i - v i‖
      = 2 * (‖u i‖ * ‖u i‖ + ‖v i‖ * ‖v i‖) :=
    fun i => parallelogram_law_with_norm ℂ (u i) (v i)
  have hPk : 0 < ‖u k‖ * ‖u k‖ :=
    mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hu)
  have hQk : 0 < ‖v k‖ * ‖v k‖ :=
    mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hv)
  rcases lt_or_gt_of_ne hp2 with h | h
  · have hq1 : q < 1 := by rw [hqdef]; linarith
    exact quadrature_probes_lt_one_impossible hq0 hq1
      (fun i => ‖u i‖ * ‖u i‖) (fun i => ‖v i‖ * ‖v i‖)
      (fun i => ‖u i + v i‖ * ‖u i + v i‖)
      (fun i => ‖u i - v i‖ * ‖u i - v i‖)
      (fun i => by positivity) (fun i => by positivity)
      (fun i => by positivity) (fun i => by positivity)
      hpar k hPk hQk c1 c2 c3 c4
  · have hq1 : 1 < q := by rw [hqdef]; linarith
    exact quadrature_probes_gt_one_impossible hq1
      (fun i => ‖u i‖ * ‖u i‖) (fun i => ‖v i‖ * ‖v i‖)
      (fun i => ‖u i + v i‖ * ‖u i + v i‖)
      (fun i => ‖u i - v i‖ * ‖u i - v i‖)
      (fun i => by positivity) (fun i => by positivity)
      (fun i => by positivity) (fun i => by positivity)
      hpar k hPk hQk c1 c2 c3 c4

/-! ## 6. The p = 2 escape is EXACTLY unitarity -/

/-- At p = 2 the probes do not merely fail to forbid mixing - they
force column orthogonality.  Four probes (e₁, e₂, (1,1), (1,i))
pin the full complex inner product: conj a · b + conj c · d = 0.
With the normalization probes this says the matrix is unitary: the
interference sector allowed at p = 2 is exactly the unitary group. -/
theorem p_two_probes_force_unitary (a b c d : ℂ)
    (he1 : ‖a‖ * ‖a‖ + ‖c‖ * ‖c‖ = 1)
    (he2 : ‖b‖ * ‖b‖ + ‖d‖ * ‖d‖ = 1)
    (hplus : ‖a + b‖ * ‖a + b‖ + ‖c + d‖ * ‖c + d‖ = 2)
    (hplusI : ‖a + Complex.I * b‖ * ‖a + Complex.I * b‖
      + ‖c + Complex.I * d‖ * ‖c + Complex.I * d‖ = 2) :
    (starRingEnd ℂ) a * b + (starRingEnd ℂ) c * d = 0 := by
  have exp1 := norm_add_mul_self (𝕜 := ℂ) a b
  have exp2 := norm_add_mul_self (𝕜 := ℂ) c d
  have exp3 := norm_add_mul_self (𝕜 := ℂ) a (Complex.I * b)
  have exp4 := norm_add_mul_self (𝕜 := ℂ) c (Complex.I * d)
  rw [RCLike.inner_apply, RCLike.re_to_complex] at exp1 exp2 exp3 exp4
  have hIb : ‖Complex.I * b‖ * ‖Complex.I * b‖ = ‖b‖ * ‖b‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hId : ‖Complex.I * d‖ * ‖Complex.I * d‖ = ‖d‖ * ‖d‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [hIb] at exp3
  rw [hId] at exp4
  have hre : (b * (starRingEnd ℂ) a).re + (d * (starRingEnd ℂ) c).re
      = 0 := by
    have hp := hplus
    rw [exp1, exp2] at hp
    linarith
  have him : (b * (starRingEnd ℂ) a).im + (d * (starRingEnd ℂ) c).im
      = 0 := by
    have h3 : (Complex.I * b * (starRingEnd ℂ) a).re
        = -(b * (starRingEnd ℂ) a).im := by
      rw [mul_assoc, Complex.I_mul_re]
    have h4 : (Complex.I * d * (starRingEnd ℂ) c).re
        = -(d * (starRingEnd ℂ) c).im := by
      rw [mul_assoc, Complex.I_mul_re]
    have hp := hplusI
    rw [exp3, exp4, h3, h4] at hp
    linarith
  have hzero : b * (starRingEnd ℂ) a + d * (starRingEnd ℂ) c = 0 := by
    apply Complex.ext
    · rw [Complex.add_re, Complex.zero_re]; exact hre
    · rw [Complex.add_im, Complex.zero_im]; exact him
  calc (starRingEnd ℂ) a * b + (starRingEnd ℂ) c * d
      = b * (starRingEnd ℂ) a + d * (starRingEnd ℂ) c := by ring
    _ = 0 := hzero

/-! ## 7. No hybrid worlds: the measure exponent is GLOBAL -/

/-- NO-HYBRID THEOREM: a linear step that preserves the total
|·|^p measure on all states and superposes ANY two basis directions
anywhere (both columns nonzero at one common coordinate) forces
p = 2 - for the WHOLE space at once.  There is no lossless dynamics
in which a mixing (quantum) sector coexists with a sector governed
by any other measure exponent: one interference event anywhere
forces the Born exponent everywhere. -/
theorem mixing_lossless_forces_p_eq_two {p : ℝ} (hp0 : 0 < p)
    {n : ℕ} (T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, ‖T x i‖ ^ p = ∑ i, ‖x i‖ ^ p)
    (j₁ j₂ : Fin n) (hj : j₁ ≠ j₂) (k : Fin n)
    (h1 : T (Pi.single j₁ 1) k ≠ 0) (h2 : T (Pi.single j₂ 1) k ≠ 0) :
    p = 2 := by
  by_contra hp2
  have hp0' : p ≠ 0 := ne_of_gt hp0
  have single_sum : ∀ j : Fin n,
      ∑ i, ‖(Pi.single j 1 : Fin n → ℂ) i‖ ^ p = 1 := by
    intro j
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, norm_one, Real.one_rpow]
    · intro i _ hne
      rw [Pi.single_eq_of_ne hne, norm_zero, Real.zero_rpow hp0']
    · intro hmem
      exact absurd (Finset.mem_univ j) hmem
  have pair_add : ∑ i,
      ‖((Pi.single j₁ 1 + Pi.single j₂ 1 : Fin n → ℂ)) i‖ ^ p = 2 := by
    have hzero : ∀ i ∈ Finset.univ,
        i ∉ ({j₁, j₂} : Finset (Fin n)) →
        ‖((Pi.single j₁ 1 + Pi.single j₂ 1 : Fin n → ℂ)) i‖ ^ p = 0 := by
      intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [Pi.add_apply, Pi.single_eq_of_ne hi.1, Pi.single_eq_of_ne hi.2,
        add_zero, norm_zero, Real.zero_rpow hp0']
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero,
      Finset.sum_insert (by simpa using hj), Finset.sum_singleton]
    simp only [Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj.symm,
      add_zero, zero_add, norm_one, Real.one_rpow]
    norm_num
  have pair_sub : ∑ i,
      ‖((Pi.single j₁ 1 - Pi.single j₂ 1 : Fin n → ℂ)) i‖ ^ p = 2 := by
    have hzero : ∀ i ∈ Finset.univ,
        i ∉ ({j₁, j₂} : Finset (Fin n)) →
        ‖((Pi.single j₁ 1 - Pi.single j₂ 1 : Fin n → ℂ)) i‖ ^ p = 0 := by
      intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [Pi.sub_apply, Pi.single_eq_of_ne hi.1, Pi.single_eq_of_ne hi.2,
        sub_zero, norm_zero, Real.zero_rpow hp0']
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero,
      Finset.sum_insert (by simpa using hj), Finset.sum_singleton]
    simp only [Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj.symm,
      sub_zero, zero_sub, norm_neg, norm_one, Real.one_rpow]
    norm_num
  refine lamperti_columns_ne_two hp0 hp2
    (T (Pi.single j₁ 1)) (T (Pi.single j₂ 1)) k h1 h2 ?_ ?_ ?_ ?_
  · exact (hiso _).trans (single_sum j₁)
  · exact (hiso _).trans (single_sum j₂)
  · calc ∑ i, ‖T (Pi.single j₁ 1) i + T (Pi.single j₂ 1) i‖ ^ p
        = ∑ i, ‖T (Pi.single j₁ 1 + Pi.single j₂ 1) i‖ ^ p := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_add, Pi.add_apply]
      _ = 2 := (hiso _).trans pair_add
  · calc ∑ i, ‖T (Pi.single j₁ 1) i - T (Pi.single j₂ 1) i‖ ^ p
        = ∑ i, ‖T (Pi.single j₁ 1 - Pi.single j₂ 1) i‖ ^ p := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_sub, Pi.sub_apply]
      _ = 2 := (hiso _).trans pair_sub




/-! ## 8. The POSITIVE Lamperti theorem: p ≠ 2 lossless = weighted permutation

The obstruction (section 5) says overlapping columns are impossible.
Counting turns this into a classification: n columns with pairwise
disjoint nonempty supports inside n coordinates have exactly one
nonzero entry each, of unit modulus, at locations forming a
permutation.  For p ≠ 2 the lossless maps are EXACTLY the
generalized permutations: relabel the classical facts, attach
phases that never interfere. -/

/-- The l^p mass of a standard basis vector is 1. -/
theorem single_probe_sum {p : ℝ} (hp0' : p ≠ 0) {n : ℕ} (j : Fin n) :
    ∑ i, ‖(Pi.single j 1 : Fin n → ℂ) i‖ ^ p = 1 := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, norm_one, Real.one_rpow]
  · intro i _ hne
    rw [Pi.single_eq_of_ne hne, norm_zero, Real.zero_rpow hp0']
  · intro hmem
    exact absurd (Finset.mem_univ j) hmem

/-- `x ^ p = 1` with `x ≥ 0`, `p > 0` forces `x = 1`. -/
theorem norm_eq_one_of_rpow_eq_one {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p)
    (h : x ^ p = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hcon := Real.rpow_lt_rpow hx hlt hp
    rw [Real.one_rpow] at hcon
    linarith
  · exact heq
  · have hcon := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) hgt hp
    rw [Real.one_rpow] at hcon
    linarith

/-- STRUCTURE THEOREM: for 0 < p, p ≠ 2, a lossless linear step on
ℂ^n is a weighted permutation - every column is a single unit-modulus
entry, and the entry locations form a permutation of the coordinates.
Classical dynamics is the ONLY thing that exists away from p = 2. -/
theorem lossless_ne_two_is_weighted_permutation {p : ℝ}
    (hp0 : 0 < p) (hp2 : p ≠ 2) {n : ℕ}
    (T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, ‖T x i‖ ^ p = ∑ i, ‖x i‖ ^ p) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j : Fin n, ∃ c : ℂ,
      ‖c‖ = 1 ∧ T (Pi.single j 1) = Pi.single (σ j) c := by
  classical
  have hp0' : p ≠ 0 := ne_of_gt hp0
  have colsum : ∀ j : Fin n, ∑ i, ‖T (Pi.single j 1) i‖ ^ p = 1 :=
    fun j => (hiso _).trans (single_probe_sum hp0' j)
  set S : Fin n → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i => T (Pi.single j 1) i ≠ 0)
    with hS
  have hmemS : ∀ j i, i ∈ S j ↔ T (Pi.single j 1) i ≠ 0 := by
    intro j i
    rw [hS]
    simp [Finset.mem_filter]
  have hne : ∀ j, (S j).Nonempty := by
    intro j
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hzero : ∀ i, T (Pi.single j 1) i = 0 := by
      intro i
      by_contra hnz
      have hmem : i ∈ S j := (hmemS j i).mpr hnz
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty i)
    have hz : ∑ i, ‖T (Pi.single j 1) i‖ ^ p = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [hzero i, norm_zero, Real.zero_rpow hp0']
    rw [colsum j] at hz
    norm_num at hz
  have hdisj : ∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (S j₁) (S j₂) := by
    intro j₁ j₂ hj
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    exact hp2 (mixing_lossless_forces_p_eq_two hp0 T hiso j₁ j₂ hj k
      ((hmemS j₁ k).mp hk1) ((hmemS j₂ k).mp hk2))
  have hcard1 : ∀ j, (S j).card = 1 := by
    have hsumle : ∑ j, (S j).card ≤ n := by
      rw [← Finset.card_biUnion
        (fun j₁ _ j₂ _ hj => hdisj j₁ j₂ hj)]
      calc ((Finset.univ : Finset (Fin n)).biUnion S).card
          ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    have hge : ∀ j ∈ (Finset.univ : Finset (Fin n)), 1 ≤ (S j).card :=
      fun j _ => Finset.card_pos.mpr (hne j)
    have hone : ∑ _j : Fin n, (1:ℕ) = n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    have htot : ∑ _j : Fin n, (1:ℕ) ≤ ∑ j, (S j).card := by
      exact Finset.sum_le_sum hge
    have heq : ∑ _j : Fin n, (1:ℕ) = ∑ j, (S j).card := by
      omega
    intro j
    exact ((Finset.sum_eq_sum_iff_of_le hge).mp heq j
      (Finset.mem_univ j)).symm
  have hloc : ∀ j, ∃ k, S j = {k} :=
    fun j => Finset.card_eq_one.mp (hcard1 j)
  choose loc hlocS using hloc
  have hmem : ∀ j i, T (Pi.single j 1) i ≠ 0 ↔ i = loc j := by
    intro j i
    constructor
    · intro hnz
      have : i ∈ S j := (hmemS j i).mpr hnz
      rw [hlocS j] at this
      exact Finset.mem_singleton.mp this
    · intro h
      subst h
      have : loc j ∈ S j := by
        rw [hlocS j]
        exact Finset.mem_singleton_self _
      exact (hmemS j (loc j)).mp this
  have hinj : Function.Injective loc := by
    intro j₁ j₂ h
    by_contra hj
    exact hp2 (mixing_lossless_forces_p_eq_two hp0 T hiso j₁ j₂ hj
      (loc j₁) ((hmem j₁ (loc j₁)).mpr rfl) ((hmem j₂ (loc j₁)).mpr h))
  have hbij : Function.Bijective loc :=
    Finite.injective_iff_bijective.mp hinj
  refine ⟨Equiv.ofBijective loc hbij, ?_⟩
  intro j
  refine ⟨T (Pi.single j 1) (loc j), ?_, ?_⟩
  · have hsum1 : ∑ i, ‖T (Pi.single j 1) i‖ ^ p
        = ‖T (Pi.single j 1) (loc j)‖ ^ p := by
      rw [Finset.sum_eq_single (loc j)]
      · intro i _ hne'
        have hz : T (Pi.single j 1) i = 0 := by
          by_contra hnz
          exact hne' ((hmem j i).mp hnz)
        rw [hz, norm_zero, Real.zero_rpow hp0']
      · intro hmem'
        exact absurd (Finset.mem_univ _) hmem'
    rw [colsum j] at hsum1
    exact norm_eq_one_of_rpow_eq_one (norm_nonneg _) hp0 hsum1.symm
  · funext i
    simp only [Equiv.ofBijective_apply]
    by_cases h : i = loc j
    · subst h
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]
      by_contra hnz
      exact h ((hmem j i).mp hnz)

/-! ## 9. General-n unitarity at p = 2 -/

/-- The l^2 mass (mul-self form) of a scaled basis vector. -/
theorem single_probe_sum_sq {n : ℕ} (j : Fin n) (α : ℂ)
    (hα : ‖α‖ = 1) :
    ∑ i, ‖(Pi.single j α : Fin n → ℂ) i‖
      * ‖(Pi.single j α : Fin n → ℂ) i‖ = 1 := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, hα, mul_one]
  · intro i _ hne
    rw [Pi.single_eq_of_ne hne, norm_zero, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ j) hmem

/-- The l^2 mass of a two-site unit-modulus probe is 2. -/
theorem pair_probe_sum_sq {n : ℕ} {j₁ j₂ : Fin n} (hj : j₁ ≠ j₂)
    (α β : ℂ) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) :
    ∑ i, ‖(Pi.single j₁ α + Pi.single j₂ β : Fin n → ℂ) i‖
      * ‖(Pi.single j₁ α + Pi.single j₂ β : Fin n → ℂ) i‖ = 2 := by
  classical
  have hzero : ∀ i ∈ Finset.univ,
      i ∉ ({j₁, j₂} : Finset (Fin n)) →
      ‖(Pi.single j₁ α + Pi.single j₂ β : Fin n → ℂ) i‖
        * ‖(Pi.single j₁ α + Pi.single j₂ β : Fin n → ℂ) i‖ = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [Pi.add_apply, Pi.single_eq_of_ne hi.1, Pi.single_eq_of_ne hi.2,
      add_zero, norm_zero, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero,
    Finset.sum_insert (by simpa using hj), Finset.sum_singleton]
  simp only [Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj.symm,
    add_zero, zero_add, hα, hβ]
  norm_num

/-- GENERAL-n UNITARITY: an l^2-lossless linear step has orthogonal
columns - in every dimension, losslessness at the Born exponent
forces the full complex inner product of any two columns to vanish.
With `single_probe_sum_sq` (columns are unit vectors) this says T is
unitary: the p = 2 sector is exactly U(n). -/
theorem l2_lossless_columns_orthogonal {n : ℕ}
    (T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ,
      ∑ i, ‖T x i‖ * ‖T x i‖ = ∑ i, ‖x i‖ * ‖x i‖)
    (j₁ j₂ : Fin n) (hj : j₁ ≠ j₂) :
    ∑ i, (starRingEnd ℂ) (T (Pi.single j₁ 1) i)
      * T (Pi.single j₂ 1) i = 0 := by
  have n1 : ∑ i, ‖T (Pi.single j₁ 1) i‖ * ‖T (Pi.single j₁ 1) i‖
      = 1 := (hiso _).trans (single_probe_sum_sq j₁ 1 (by simp))
  have n2 : ∑ i, ‖T (Pi.single j₂ 1) i‖ * ‖T (Pi.single j₂ 1) i‖
      = 1 := (hiso _).trans (single_probe_sum_sq j₂ 1 (by simp))
  have probe : ∀ β : ℂ, ‖β‖ = 1 →
      ∑ i, ‖T (Pi.single j₁ 1) i + β * T (Pi.single j₂ 1) i‖
        * ‖T (Pi.single j₁ 1) i + β * T (Pi.single j₂ 1) i‖ = 2 := by
    intro β hβ
    have hxT : ∀ i : Fin n,
        T (Pi.single j₁ 1) i + β * T (Pi.single j₂ 1) i
        = T (Pi.single j₁ 1 + Pi.single j₂ β) i := by
      intro i
      have hsingle : (Pi.single j₂ β : Fin n → ℂ)
          = β • (Pi.single j₂ 1 : Fin n → ℂ) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [map_add, hsingle, map_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    have h2 : ∑ i, ‖T (Pi.single j₁ 1 + Pi.single j₂ β) i‖
        * ‖T (Pi.single j₁ 1 + Pi.single j₂ β) i‖ = 2 := by
      rw [hiso]
      exact pair_probe_sum_sq hj 1 β (by simp) hβ
    rw [Finset.sum_congr rfl fun i _ => by rw [hxT i]]
    exact h2
  have expand : ∀ β : ℂ, ‖β‖ = 1 →
      ∑ i, ((β * T (Pi.single j₂ 1) i)
        * (starRingEnd ℂ) (T (Pi.single j₁ 1) i)).re = 0 := by
    intro β hβ
    have hper : ∀ i : Fin n,
        ‖T (Pi.single j₁ 1) i + β * T (Pi.single j₂ 1) i‖
          * ‖T (Pi.single j₁ 1) i + β * T (Pi.single j₂ 1) i‖
        = ‖T (Pi.single j₁ 1) i‖ * ‖T (Pi.single j₁ 1) i‖
          + 2 * ((β * T (Pi.single j₂ 1) i)
              * (starRingEnd ℂ) (T (Pi.single j₁ 1) i)).re
          + ‖T (Pi.single j₂ 1) i‖ * ‖T (Pi.single j₂ 1) i‖ := by
      intro i
      have h := norm_add_mul_self (𝕜 := ℂ)
        (T (Pi.single j₁ 1) i) (β * T (Pi.single j₂ 1) i)
      rw [RCLike.inner_apply, RCLike.re_to_complex] at h
      rw [h, norm_mul, hβ, one_mul]
    have hsum := probe β hβ
    rw [Finset.sum_congr rfl fun i _ => hper i,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      n1, n2, ← Finset.mul_sum] at hsum
    linarith
  have hre := expand 1 (by simp)
  have him := expand Complex.I (by simp)
  apply Complex.ext
  · rw [Complex.re_sum, Complex.zero_re]
    have hconv : ∀ i : Fin n,
        ((starRingEnd ℂ) (T (Pi.single j₁ 1) i)
          * T (Pi.single j₂ 1) i).re
        = ((1 * T (Pi.single j₂ 1) i)
            * (starRingEnd ℂ) (T (Pi.single j₁ 1) i)).re := by
      intro i
      congr 1
      ring
    rw [Finset.sum_congr rfl fun i _ => hconv i]
    exact hre
  · rw [Complex.im_sum, Complex.zero_im]
    have hconv : ∀ i : Fin n,
        ((Complex.I * T (Pi.single j₂ 1) i)
          * (starRingEnd ℂ) (T (Pi.single j₁ 1) i)).re
        = -((starRingEnd ℂ) (T (Pi.single j₁ 1) i)
            * T (Pi.single j₂ 1) i).im := by
      intro i
      rw [mul_assoc, Complex.I_mul_re,
        mul_comm (T (Pi.single j₂ 1) i)
          ((starRingEnd ℂ) (T (Pi.single j₁ 1) i))]
    rw [Finset.sum_congr rfl fun i _ => hconv i,
      Finset.sum_neg_distrib] at him
    linarith

/-! ## 10. The grand dichotomy and the frozen world -/

/-- THE GRAND DICHOTOMY: every lossless linear dynamics on any
measure system |·|^p is EITHER a weighted permutation (classical
relabeling with inert phases) OR lives at p = 2 with orthogonal
columns (quantum unitarity).  There is no third kind of lossless
time evolution. -/
theorem lossless_dichotomy {p : ℝ} (hp0 : 0 < p) {n : ℕ}
    (T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, ‖T x i‖ ^ p = ∑ i, ‖x i‖ ^ p) :
    (∃ σ : Equiv.Perm (Fin n), ∀ j : Fin n, ∃ c : ℂ,
      ‖c‖ = 1 ∧ T (Pi.single j 1) = Pi.single (σ j) c)
    ∨ (p = 2 ∧ ∀ j₁ j₂ : Fin n, j₁ ≠ j₂ →
        ∑ i, (starRingEnd ℂ) (T (Pi.single j₁ 1) i)
          * T (Pi.single j₂ 1) i = 0) := by
  by_cases hp2 : p = 2
  · right
    refine ⟨hp2, ?_⟩
    intro j₁ j₂ hj
    have conv2 : ∀ z : ℂ, ‖z‖ ^ (2:ℝ) = ‖z‖ * ‖z‖ := by
      intro z
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      ring
    refine l2_lossless_columns_orthogonal T ?_ j₁ j₂ hj
    intro x
    have h := hiso x
    rw [hp2] at h
    calc ∑ i, ‖T x i‖ * ‖T x i‖
        = ∑ i, ‖T x i‖ ^ (2:ℝ) :=
          Finset.sum_congr rfl fun i _ => (conv2 _).symm
      _ = ∑ i, ‖x i‖ ^ (2:ℝ) := h
      _ = ∑ i, ‖x i‖ * ‖x i‖ :=
          Finset.sum_congr rfl fun i _ => conv2 _
  · left
    exact lossless_ne_two_is_weighted_permutation hp0 hp2 T hiso

/-- THE FROZEN WORLD (discrete core): for p ≠ 2, the induced action
on MEASURES is a fixed permutation, independent of the phase data -
‖(Tx)(σ j)‖ = ‖x j‖ for every state x.  Probabilities can only be
relabeled, never continuously transported: in any measure system
other than Born's, nothing can ever happen to the observable world.
Continuous evolution of probability is uniquely quantum. -/
theorem frozen_measure_ne_two {p : ℝ} (hp0 : 0 < p) (hp2 : p ≠ 2)
    {n : ℕ} (T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, ‖T x i‖ ^ p = ∑ i, ‖x i‖ ^ p) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (x : Fin n → ℂ) (j : Fin n),
      ‖T x (σ j)‖ = ‖x j‖ := by
  obtain ⟨σ, hσ⟩ :=
    lossless_ne_two_is_weighted_permutation hp0 hp2 T hiso
  refine ⟨σ, ?_⟩
  intro x j
  have hsingle : ∀ (j' : Fin n) (a : ℂ),
      (Pi.single j' a : Fin n → ℂ)
        = a • (Pi.single j' 1 : Fin n → ℂ) := by
    intro j' a
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hTx : T x (σ j) = x j * T (Pi.single j 1) (σ j) := by
    conv_lhs => rw [show x = ∑ j', Pi.single j' (x j') from
      (Finset.univ_sum_single x).symm]
    rw [map_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · rw [hsingle j (x j), map_smul, Pi.smul_apply, smul_eq_mul]
    · intro j' _ hne
      obtain ⟨c, _, hcol⟩ := hσ j'
      have hne2 : σ j ≠ σ j' := fun h => hne (σ.injective h.symm)
      rw [hsingle j' (x j'), map_smul, Pi.smul_apply, hcol,
        smul_eq_mul, Pi.single_eq_of_ne hne2, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  obtain ⟨c, hc1, hcol⟩ := hσ j
  rw [hTx, hcol, Pi.single_eq_same, norm_mul, hc1, mul_one]




/-! ## 11. THE DIVISIBLE-TIME THEOREM: quantum mechanics from time alone

The classification still uses the nonclassicality axiom A5 ("some
step mixes") - a quantumness assumption invoked to derive quantum
mechanics.  This section eliminates it.

Suppose the step T of a lossless dynamics can be SUBDIVIDED: for
every m there is a lossless S with S^m = T (time has no smallest
step).  If p ≠ 2, every such S is a weighted permutation (structure
theorem), its measure action is its permutation part σ (frozen-world
theorem), and permutation parts compose.  Taking m = |S_n|! - the
order of the full symmetric group - Lagrange's theorem gives
σ^m = 1 for EVERY σ.  So T's measure action is the identity:
pointwise, on every state, nothing ever happens.

Contrapositive: if time is infinitely divisible and anything at all
changes, then p = 2 - hence unitarity, hence complex quantum
mechanics.  The axioms are now: (1) losslessness, (2) time has no
smallest step, (3) something happens.  All three are statements
about TIME, none about superposition. -/

/-- Iterating the frozen-world theorem: the k-th power of a lossless
step moves measures by the k-th power of its permutation. -/
theorem frozen_measure_pow {p : ℝ} (hp0 : 0 < p) (hp2 : p ≠ 2)
    {n : ℕ} (S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hS : ∀ x : Fin n → ℂ, ∑ i, ‖S x i‖ ^ p = ∑ i, ‖x i‖ ^ p) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (k : ℕ) (x : Fin n → ℂ) (j : Fin n),
      ‖(S ^ k) x ((σ ^ k) j)‖ = ‖x j‖ := by
  obtain ⟨σ, hσ⟩ := frozen_measure_ne_two hp0 hp2 S hS
  refine ⟨σ, ?_⟩
  intro k
  induction k with
  | zero =>
    intro x j
    rw [pow_zero, pow_zero, Module.End.one_apply, Equiv.Perm.one_apply]
  | succ k ih =>
    intro x j
    rw [pow_succ, pow_succ, Module.End.mul_apply, Equiv.Perm.mul_apply,
      ih (S x) (σ j)]
    exact hσ x j

/-- A lossless step (p ≠ 2) raised to the order of the symmetric
group is measure-static: Lagrange kills the permutation part. -/
theorem root_at_symmetric_order_forces_static {p : ℝ} (hp0 : 0 < p)
    (hp2 : p ≠ 2) {n : ℕ}
    (S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hS : ∀ x : Fin n → ℂ, ∑ i, ‖S x i‖ ^ p = ∑ i, ‖x i‖ ^ p) :
    ∀ (x : Fin n → ℂ) (j : Fin n),
      ‖(S ^ Fintype.card (Equiv.Perm (Fin n))) x j‖ = ‖x j‖ := by
  obtain ⟨σ, hσ⟩ := frozen_measure_pow hp0 hp2 S hS
  intro x j
  have h := hσ (Fintype.card (Equiv.Perm (Fin n))) x j
  rw [show σ ^ Fintype.card (Equiv.Perm (Fin n)) = 1 from
    pow_card_eq_one, Equiv.Perm.one_apply] at h
  exact h

/-- THE DIVISIBLE-TIME THEOREM (static form): if the step T of a
lossless p ≠ 2 dynamics admits a lossless m-th root for every m
(time has no smallest step), then T is measure-static - pointwise,
on every state, ‖T x j‖ = ‖x j‖.  In a p ≠ 2 world with divisible
time, nothing ever happens. -/
theorem divisible_time_forces_static {p : ℝ} (hp0 : 0 < p)
    (hp2 : p ≠ 2) {n : ℕ}
    (T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hdiv : ∀ m : ℕ, 0 < m →
      ∃ S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ),
        (∀ x : Fin n → ℂ, ∑ i, ‖S x i‖ ^ p = ∑ i, ‖x i‖ ^ p)
        ∧ S ^ m = T) :
    ∀ (x : Fin n → ℂ) (j : Fin n), ‖T x j‖ = ‖x j‖ := by
  obtain ⟨S, hS, hpow⟩ := hdiv (Fintype.card (Equiv.Perm (Fin n)))
    (Fintype.card_pos_iff.mpr ⟨1⟩)
  intro x j
  rw [← hpow]
  exact root_at_symmetric_order_forces_static hp0 hp2 S hS x j

/-- THE DIVISIBLE-TIME THEOREM (headline form): a lossless dynamics
whose steps subdivide indefinitely, and under which ANYTHING at all
changes, is forced onto the Born exponent p = 2 - hence, by the
dichotomy, unitary quantum mechanics.  Losslessness + divisible time
+ something happens ⟹ quantum.  No axiom mentions superposition. -/
theorem change_and_divisibility_force_born {p : ℝ} (hp0 : 0 < p)
    {n : ℕ} (T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hdiv : ∀ m : ℕ, 0 < m →
      ∃ S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ),
        (∀ x : Fin n → ℂ, ∑ i, ‖S x i‖ ^ p = ∑ i, ‖x i‖ ^ p)
        ∧ S ^ m = T)
    (hchange : ∃ (x : Fin n → ℂ) (j : Fin n), ‖T x j‖ ≠ ‖x j‖) :
    p = 2 := by
  by_contra hp2
  obtain ⟨x, j, hx⟩ := hchange
  exact hx (divisible_time_forces_static hp0 hp2 T hdiv x j)


/-! ## 12. Sharpening the consumed root order: n! → exponent(Sₙ)

The divisible-time theorem consumed a root at m = n!.  Lagrange only
needs σ^m = 1 for every σ, i.e. m a multiple of the EXPONENT of the
symmetric group — which is lcm(1,…,n), far below n! (e.g. n = 10:
lcm = 2520 vs 10! = 3628800).  One lossless root at that single
order already forces staticity. -/

/-- Sharpened root order: a single lossless root at the exponent of
`Equiv.Perm (Fin n)` (= lcm(1,…,n)) forces measure-staticity at
p ≠ 2. -/
theorem root_at_group_exponent_forces_static {p : ℝ} (hp0 : 0 < p)
    (hp2 : p ≠ 2) {n : ℕ}
    (S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hS : ∀ x : Fin n → ℂ, ∑ i, ‖S x i‖ ^ p = ∑ i, ‖x i‖ ^ p) :
    ∀ (x : Fin n → ℂ) (j : Fin n),
      ‖(S ^ Monoid.exponent (Equiv.Perm (Fin n))) x j‖ = ‖x j‖ := by
  obtain ⟨σ, hσ⟩ := frozen_measure_pow hp0 hp2 S hS
  intro x j
  have h := hσ (Monoid.exponent (Equiv.Perm (Fin n))) x j
  rw [show σ ^ Monoid.exponent (Equiv.Perm (Fin n)) = 1 from
    Monoid.pow_exponent_eq_one σ, Equiv.Perm.one_apply] at h
  exact h

/-! ## 13. Antiunitaries have no half-step

Deriving only REAL-linearity (section 14) opens the Wigner gap: at
p = 2 the real-linear lossless group contains antiunitaries
(conjugate-linear isometries).  The divisibility axiom closes it at
m = 2 already: the square of ANY semilinear map — linear or
conjugate-linear — is complex-LINEAR, so a nonzero conjugate-linear
step has no semilinear square root at all.  Time evolution is
unitary rather than antiunitary because half-steps exist.  (That
every real-linear lossless map at p = 2 is unitary or antiunitary
is Wigner's classification, not formalized here; the semilinearity
hypothesis records that seam.)  Purely algebraic: no norm appears. -/

/-- The square of a semilinear map (complex-linear OR
conjugate-linear) is always complex-linear. -/
theorem square_of_semilinear_is_linear {n : ℕ}
    (S : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))
    (hS : (∀ (z : ℂ) (x : Fin n → ℂ), S (z • x) = z • S x) ∨
          (∀ (z : ℂ) (x : Fin n → ℂ),
            S (z • x) = (starRingEnd ℂ) z • S x)) :
    ∀ (z : ℂ) (x : Fin n → ℂ), (S * S) (z • x) = z • (S * S) x := by
  intro z x
  rcases hS with hlin | hconj
  · rw [Module.End.mul_apply, hlin, hlin, Module.End.mul_apply]
  · rw [Module.End.mul_apply, hconj, hconj, Complex.conj_conj,
      Module.End.mul_apply]

/-- A nonzero conjugate-linear (antiunitary-type) map has NO square
root among semilinear maps: divisibility eliminates antiunitary
evolution. -/
theorem antiunitary_has_no_half_step {n : ℕ}
    (T S : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))
    (hroot : S * S = T)
    (hS : (∀ (z : ℂ) (x : Fin n → ℂ), S (z • x) = z • S x) ∨
          (∀ (z : ℂ) (x : Fin n → ℂ),
            S (z • x) = (starRingEnd ℂ) z • S x))
    (hanti : ∀ (z : ℂ) (x : Fin n → ℂ),
      T (z • x) = (starRingEnd ℂ) z • T x)
    (hmove : ∃ x : Fin n → ℂ, T x ≠ 0) : False := by
  obtain ⟨x, hx⟩ := hmove
  have hlin := square_of_semilinear_is_linear S hS
  rw [hroot] at hlin
  have h1 := hlin Complex.I x
  have h2 := hanti Complex.I x
  rw [Complex.conj_I] at h2
  rw [h2] at h1
  have key : Complex.I • T x = -(Complex.I • T x) := by
    rw [← neg_smul]
    exact h1.symm
  have h2a : Complex.I • T x + Complex.I • T x = 0 :=
    add_eq_zero_iff_eq_neg.mpr key
  have h2b : (2 : ℂ) • (Complex.I • T x) = 0 := by
    rw [two_smul]
    exact h2a
  have h2c : Complex.I • T x = 0 := by
    rcases smul_eq_zero.mp h2b with h | h
    · norm_num at h
    · exact h
  rcases smul_eq_zero.mp h2c with h | h
  · exact Complex.I_ne_zero h
  · exact hx h

/-! ## 14. Linearity is DERIVED: Mazur–Ulam

The linearity axiom A1 reduces to losslessness.  Read losslessness
as preservation of DISTINGUISHABILITY — the measure-distance between
any two states, not merely the weight of each state.  Then for
p ≥ 1 the measure-distance is a genuine metric (the ℓᵖ metric), a
surjective distance-preserving map is affine by Mazur–Ulam, and the
state-measure pins the base point: real-linearity is forced.  No
linear structure is assumed of the dynamics — only that it is a
surjection of the state space preserving weight and distance.

Honest boundary: this yields REAL-linearity; complex-linearity vs
conjugate-linearity is the Wigner gap, addressed at p = 2 by
section 13.  For 0 < p < 1 the measure-distance is a quasi-metric
and Mazur–Ulam does not apply — that band keeps linearity as an
assumption. -/

/-- LINEARITY DERIVED (Mazur–Ulam): for p ≥ 1, a surjective map of
state space preserving the state measure and pairwise
distinguishability is real-linear. -/
theorem lossless_bijection_is_real_linear
    {p : ℝ} (hp : 1 ≤ p) {n : ℕ}
    (F : (Fin n → ℂ) → (Fin n → ℂ))
    (hsurj : Function.Surjective F)
    (hmeas : ∀ x : Fin n → ℂ, ∑ i, ‖F x i‖ ^ p = ∑ i, ‖x i‖ ^ p)
    (hdist : ∀ x y : Fin n → ℂ,
      ∑ i, ‖F x i - F y i‖ ^ p = ∑ i, ‖x i - y i‖ ^ p) :
    (∀ x y : Fin n → ℂ, F (x + y) = F x + F y) ∧
    (∀ (c : ℝ) (x : Fin n → ℂ), F (c • x) = c • F x) := by
  classical
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hzero : ∀ z : Fin n → ℂ, (∑ i, ‖z i‖ ^ p) = 0 → z = 0 := by
    intro z hz
    funext i
    by_contra hne
    have hpos : 0 < ‖z i‖ ^ p :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hne) p
    have hle : ‖z i‖ ^ p ≤ ∑ k, ‖z k‖ ^ p :=
      Finset.single_le_sum
        (fun k _ => Real.rpow_nonneg (norm_nonneg _) p)
        (Finset.mem_univ i)
    rw [hz] at hle
    linarith
  have hinj : Function.Injective F := by
    intro x y hxy
    have h := hdist x y
    rw [hxy] at h
    have h0 : (∑ i, ‖x i - y i‖ ^ p) = 0 := by
      rw [← h]
      simp [Real.zero_rpow (ne_of_gt hp0)]
    have := hzero _ h0
    funext i
    have := congrFun this i
    simpa [sub_eq_zero] using this
  have hF0 : F 0 = 0 := by
    apply hzero
    rw [hmeas]
    simp [Real.zero_rpow (ne_of_gt hp0)]
  set P : ENNReal := ENNReal.ofReal p with hP
  have hPtoReal : P.toReal = p := ENNReal.toReal_ofReal (le_of_lt hp0)
  have hPpos : 0 < P.toReal := by rw [hPtoReal]; exact hp0
  haveI : Fact (1 ≤ P) := ⟨by
    rw [hP]
    exact_mod_cast ENNReal.one_le_ofReal.mpr hp⟩
  let e0 : (Fin n → ℂ) ≃ (Fin n → ℂ) := Equiv.ofBijective F ⟨hinj, hsurj⟩
  let e : PiLp P (fun _ : Fin n => ℂ) ≃ PiLp P (fun _ : Fin n => ℂ) :=
    ((WithLp.equiv P _).trans e0).trans (WithLp.equiv P _).symm
  have he_apply : ∀ x : PiLp P (fun _ : Fin n => ℂ),
      e x = WithLp.toLp P (F (WithLp.ofLp x)) := fun _ => rfl
  have hisom : Isometry e := by
    apply Isometry.of_dist_eq
    intro a b
    rw [PiLp.dist_eq_sum hPpos, PiLp.dist_eq_sum hPpos]
    congr 1
    simp only [dist_eq_norm]
    rw [hPtoReal]
    exact hdist (WithLp.ofLp a) (WithLp.ofLp b)
  let isom : PiLp P (fun _ : Fin n => ℂ) ≃ᵢ PiLp P (fun _ : Fin n => ℂ) :=
    ⟨e, hisom⟩
  have h0 : isom 0 = 0 := by
    show e 0 = 0
    rw [he_apply]
    simp [hF0]
  let L := isom.toRealLinearIsometryEquivOfMapZero h0
  have hL : ∀ x : PiLp P (fun _ : Fin n => ℂ), L x = e x := by
    intro x
    show (isom.toRealLinearIsometryEquivOfMapZero h0) x = e x
    rw [IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero]
    rfl
  constructor
  · intro x y
    have h := L.map_add (WithLp.toLp P x) (WithLp.toLp P y)
    rw [hL, hL, hL] at h
    rw [he_apply, he_apply, he_apply] at h
    have h' := congrArg (WithLp.ofLp) h
    simpa using h'
  · intro c x
    have h := L.map_smul c (WithLp.toLp P x)
    rw [hL, hL] at h
    rw [he_apply, he_apply] at h
    have h' := congrArg (WithLp.ofLp) h
    simpa using h'

/-! ## 15. The Born FUNCTION from monotone Cauchy

The last analytic plank A6 assumed the measure is |·|^p for some p,
and the theorems above then picked p = 2.  This section removes the
power-family assumption for the classification half: a measure
additive over PERPENDICULAR decompositions and monotone in amplitude
is exactly f(x) = x² f(1) — the Born function itself, not just its
exponent.  No continuity is assumed anywhere: monotone solutions of
Cauchy's functional equation are already linear (rationals pin the
values, monotonicity squeezes the irrationals — Hamel-basis
pathologies are killed by order, not topology).

Registered open seam (the other half): deriving Pythagorean
additivity of the measure from the EXISTENCE of a mixing lossless
step — the Orlicz–Lamperti generalization of the structure theorem.
With that, A6 dissolves entirely. -/

/-- Monotone + additive on the nonnegative cone forces linearity.
No continuity assumed. -/
theorem monotone_additive_on_cone_is_linear (g : ℝ → ℝ)
    (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → g (a + b) = g a + g b)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b) :
    ∀ x : ℝ, 0 ≤ x → g x = x * g 1 := by
  have g0 : g 0 = 0 := by
    have h := hadd 0 0 le_rfl le_rfl
    norm_num at h
    linarith
  have hnat : ∀ (k : ℕ) (x : ℝ), 0 ≤ x → g (k * x) = k * g x := by
    intro k
    induction k with
    | zero => intro x _; simpa using g0
    | succ k ih =>
      intro x hx
      have hkx : (0 : ℝ) ≤ k * x := mul_nonneg (Nat.cast_nonneg k) hx
      have : ((k + 1 : ℕ) : ℝ) * x = k * x + x := by push_cast; ring
      rw [this, hadd _ _ hkx hx, ih x hx]
      push_cast
      ring
  have hratNN : ∀ (a b : ℕ), 0 < b → g (a / b) = (a / b) * g 1 := by
    intro a b hb
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hab : (0 : ℝ) ≤ a / b := div_nonneg (Nat.cast_nonneg a) (le_of_lt hbR)
    have h1 : g ((b : ℝ) * (a / b)) = b * g (a / b) := hnat b _ hab
    have h2 : (b : ℝ) * (a / b) = a := by field_simp
    have h3 : g (a : ℝ) = a * g 1 := by
      have := hnat a 1 zero_le_one
      simpa using this
    rw [h2, h3] at h1
    field_simp at h1 ⊢
    linarith
  have hrat : ∀ q : ℚ, 0 ≤ q → g (q : ℝ) = (q : ℝ) * g 1 := by
    intro q hq
    have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hcast : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum
    have hden : 0 < q.den := q.pos
    have hqR : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
      rw [hcast, Rat.cast_def]
    rw [hqR]
    exact hratNN q.num.toNat q.den hden
  have hg1 : 0 ≤ g 1 := by
    have := hmono 0 1 le_rfl zero_le_one
    linarith [g0]
  intro x hx
  rcases eq_or_lt_of_le hg1 with hg1e | hg1pos
  · obtain ⟨q, hq⟩ := exists_rat_gt x
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast le_of_lt (lt_of_le_of_lt hx hq)
    have hup : g x ≤ g q := hmono _ _ hx (le_of_lt hq)
    have hlo : g 0 ≤ g x := hmono _ _ le_rfl hx
    rw [hrat q hq0, ← hg1e] at hup
    rw [g0] at hlo
    have : g x = 0 := le_antisymm (by simpa using hup) hlo
    rw [this, ← hg1e]
    ring
  · apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hδ : 0 < ε / g 1 := div_pos hε hg1pos
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right x hδ)
      have hq0 : (0 : ℚ) ≤ q := by
        exact_mod_cast le_of_lt (lt_of_le_of_lt hx hq1)
      calc g x ≤ g q := hmono _ _ hx (le_of_lt hq1)
        _ = q * g 1 := hrat q hq0
        _ ≤ (x + ε / g 1) * g 1 :=
            mul_le_mul_of_nonneg_right (le_of_lt hq2) hg1
        _ = x * g 1 + ε := by field_simp
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hδ : 0 < ε / g 1 := div_pos hε hg1pos
      by_cases hxs : x ≤ ε / g 1
      · have h1 : x * g 1 ≤ ε := by
          have := mul_le_mul_of_nonneg_right hxs hg1
          calc x * g 1 ≤ (ε / g 1) * g 1 := this
            _ = ε := by field_simp
        have h2 : 0 ≤ g x := by
          have := hmono 0 x le_rfl hx
          linarith [g0]
        linarith
      · push_neg at hxs
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self x hδ)
        have hq0 : (0 : ℚ) ≤ q := by
          have : (0 : ℝ) < x - ε / g 1 := by linarith
          exact_mod_cast le_of_lt (lt_trans this hq1)
        calc x * g 1 = (x - ε / g 1) * g 1 + ε := by field_simp; ring
          _ ≤ q * g 1 + ε := by
              have := mul_le_mul_of_nonneg_right (le_of_lt hq1) hg1
              linarith
          _ = g q + ε := by rw [hrat q hq0]
          _ ≤ g x + ε := by
              have := hmono q x (by exact_mod_cast hq0) (le_of_lt hq2)
              linarith

/-- THE BORN FUNCTION IS UNIQUE: a monotone measure additive over
perpendicular decompositions is exactly f(x) = x² f(1).  No
continuity assumed. -/
theorem born_function_unique (f : ℝ → ℝ)
    (hpyth : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      f (Real.sqrt (s + t)) = f (Real.sqrt s) + f (Real.sqrt t))
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b) :
    ∀ x : ℝ, 0 ≤ x → f x = x ^ 2 * f 1 := by
  set g : ℝ → ℝ := fun t => f (Real.sqrt t) with hg
  have hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → g (a + b) = g a + g b := by
    intro a b ha hb
    exact hpyth a b ha hb
  have hmonog : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b := by
    intro a b ha hab
    exact hmono _ _ (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt hab)
  have hlin := monotone_additive_on_cone_is_linear g hadd hmonog
  intro x hx
  have h := hlin (x ^ 2) (sq_nonneg x)
  rw [hg] at h
  simp only [] at h
  rw [Real.sqrt_sq hx, Real.sqrt_one] at h
  exact h


/-! ## 16. THE ZERO-STRUCTURE CAPSTONE: the Born exponent from a
bare set-map of states

Everything assembled.  `born_from_time_alone` assumes NO algebraic
structure of the dynamics whatsoever — not linearity, not
additivity, not complex-linearity, not even that F itself is
lossless.  The hypotheses are:

  * a number p ≥ 1 specifying the measure Σ‖·‖^p;
  * for every m, a SET-MAP root G with G^[m] = F that is surjective
    and preserves the state measure and pairwise distinguishability
    (time has no smallest step, and each sub-step loses nothing);
  * some measure changes under F (something happens).

Conclusion: p = 2.  The chain, entirely internal: Mazur–Ulam turns
any root into a real-linear map (§14); the REAL block-structure
theorem below (`real_lossless_frozen_measure`) shows an ℝ-linear
lossless step at p ≠ 2 moves measures by a fixed permutation — the
ℂ-linearity of §8-§10 was never essential, because the Lamperti
probes are all real combinations of the 2n real basis directions
e_j, i·e_j, and pairs within one complex block are exactly the ones
the probes cannot couple (‖1+i‖^p ≠ 2), which is the block
structure; iterating and taking the root at the group exponent of
Sₙ (Lagrange) freezes every measure, contradicting change.

F's own losslessness is DERIVED (F is a composite of lossless
roots).  Honest scope: the measure family Σ‖·‖^p is the one
remaining structural assumption (§15 points at its dissolution via
monotone Cauchy — the Orlicz–Lamperti seam); p ≥ 1 for Mazur–Ulam;
the conclusion is the Born EXPONENT — upgrading "p = 2" to "unitary"
needs complex structure on the dynamics (an O(2n)-vs-U(n) gauge
seam: measure-losslessness alone at p = 2 allows all real-orthogonal
maps; unitarity additionally requires phase covariance or
transition-probability preservation à la Wigner). -/

/-- `x ^ p` is injective on nonnegatives for `p > 0`. -/
theorem rpow_left_inj_nonneg {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hp : 0 < p) (h : x ^ p = y ^ p) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have := Real.rpow_lt_rpow hx hlt hp
    linarith
  · exact heq
  · have := Real.rpow_lt_rpow hy hgt hp
    linarith

/-- Measure of a single-coordinate state. -/
theorem single_sum_eq {p : ℝ} (hp0' : p ≠ 0) {n : ℕ} (j : Fin n)
    (c : ℂ) :
    ∑ i, ‖(Pi.single j c : Fin n → ℂ) i‖ ^ p = ‖c‖ ^ p := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro i _ hne
    rw [Pi.single_eq_of_ne hne, norm_zero, Real.zero_rpow hp0']
  · intro hmem
    exact absurd (Finset.mem_univ j) hmem

/-- Measure of a unit single-coordinate state is 1. -/
theorem single_probe_sum_unit {p : ℝ} (hp0' : p ≠ 0) {n : ℕ}
    (j : Fin n) (c : ℂ) (hc : ‖c‖ = 1) :
    ∑ i, ‖(Pi.single j c : Fin n → ℂ) i‖ ^ p = 1 := by
  rw [single_sum_eq hp0' j c, hc, Real.one_rpow]

/-- Measure of a two-coordinate unit-pair state is 2. -/
theorem pair_probe_sum_unit {p : ℝ} (hp0' : p ≠ 0) {n : ℕ}
    {j₁ j₂ : Fin n} (hj : j₁ ≠ j₂) (c d : ℂ)
    (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    ∑ i, ‖(Pi.single j₁ c + Pi.single j₂ d : Fin n → ℂ) i‖ ^ p = 2 := by
  have hsplit : ∀ i : Fin n,
      ‖(Pi.single j₁ c + Pi.single j₂ d : Fin n → ℂ) i‖ ^ p
      = ‖(Pi.single j₁ c : Fin n → ℂ) i‖ ^ p
        + ‖(Pi.single j₂ d : Fin n → ℂ) i‖ ^ p := by
    intro i
    by_cases h1 : i = j₁
    · subst h1
      simp [Pi.single_eq_same, Pi.single_eq_of_ne hj,
        Real.zero_rpow hp0']
    · by_cases h2 : i = j₂
      · subst h2
        simp [Pi.single_eq_same, Pi.single_eq_of_ne h1,
          Real.zero_rpow hp0']
      · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2,
          Real.zero_rpow hp0']
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    single_sum_eq hp0' j₁ c, single_sum_eq hp0' j₂ d, hc, hd,
    Real.one_rpow]
  norm_num

/-- REAL block-structure / frozen measure: an ℝ-linear lossless step
at p ≠ 2 moves measures by a fixed permutation.  No complex-linearity
assumed: the probes are all real combinations of the 2n real basis
directions e_j, i·e_j, and pairs across different complex coordinates
are killed by the Lamperti obstruction; block counting pins one
complex coordinate per block. -/
theorem real_lossless_frozen_measure {p : ℝ} (hp0 : 0 < p)
    (hp2 : p ≠ 2) {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, ‖L x i‖ ^ p = ∑ i, ‖x i‖ ^ p) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (x : Fin n → ℂ) (j : Fin n),
      ‖L x (σ j)‖ = ‖x j‖ := by
  classical
  have hp0' : p ≠ 0 := ne_of_gt hp0
  have colu : ∀ j : Fin n, ∑ i, ‖L (Pi.single j 1) i‖ ^ p = 1 :=
    fun j => (hiso _).trans (single_probe_sum hp0' j)
  -- cross-block obstruction, uniform in the unit phases c, d
  have hpair_sub : ∀ {j₁ j₂ : Fin n}, j₁ ≠ j₂ → ∀ (c d : ℂ),
      ‖c‖ = 1 → ‖d‖ = 1 →
      ∑ i, ‖(Pi.single j₁ c - Pi.single j₂ d : Fin n → ℂ) i‖ ^ p = 2 := by
    intro j₁ j₂ hj c d hc hd
    have hrw : (Pi.single j₁ c - Pi.single j₂ d : Fin n → ℂ)
        = Pi.single j₁ c + Pi.single j₂ (-d) := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.single_apply]
      split_ifs <;> ring
    rw [hrw]
    exact pair_probe_sum_unit hp0' hj c (-d) hc (by rw [norm_neg]; exact hd)
  have hdisjcase : ∀ {j₁ j₂ : Fin n}, j₁ ≠ j₂ → ∀ (c d : ℂ),
      ‖c‖ = 1 → ‖d‖ = 1 → ∀ k : Fin n,
      L (Pi.single j₁ c) k ≠ 0 → L (Pi.single j₂ d) k ≠ 0 → False := by
    intro j₁ j₂ hj c d hc hd k h1 h2
    refine lamperti_columns_ne_two hp0 hp2
      (L (Pi.single j₁ c)) (L (Pi.single j₂ d)) k h1 h2
      ((hiso _).trans (single_probe_sum_unit hp0' j₁ c hc))
      ((hiso _).trans (single_probe_sum_unit hp0' j₂ d hd))
      ?_ ?_
    · have hLab : ∀ i : Fin n,
          L (Pi.single j₁ c) i + L (Pi.single j₂ d) i
          = L (Pi.single j₁ c + Pi.single j₂ d) i := by
        intro i
        rw [map_add]
        rfl
      rw [Finset.sum_congr rfl fun i _ => by rw [hLab i]]
      exact (hiso _).trans (pair_probe_sum_unit hp0' hj c d hc hd)
    · have hLab : ∀ i : Fin n,
          L (Pi.single j₁ c) i - L (Pi.single j₂ d) i
          = L (Pi.single j₁ c - Pi.single j₂ d) i := by
        intro i
        rw [map_sub]
        rfl
      rw [Finset.sum_congr rfl fun i _ => by rw [hLab i]]
      exact (hiso _).trans (hpair_sub hj c d hc hd)
  -- block supports
  set S : Fin n → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun i =>
      L (Pi.single j 1) i ≠ 0 ∨ L (Pi.single j Complex.I) i ≠ 0)
    with hSdef
  have hne : ∀ j, (S j).Nonempty := by
    intro j
    have hex : ∃ i, L (Pi.single j 1) i ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hz : ∑ i, ‖L (Pi.single j 1) i‖ ^ p = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [hall i, norm_zero, Real.zero_rpow hp0']
      rw [colu j] at hz
      norm_num at hz
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hi⟩⟩
  have hdisj : ∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (S j₁) (S j₂) := by
    intro j₁ j₂ hj
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    obtain ⟨-, h1⟩ := Finset.mem_filter.mp hk1
    obtain ⟨-, h2⟩ := Finset.mem_filter.mp hk2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hdisjcase hj 1 1 (by simp) (by simp) k h1 h2
    · exact hdisjcase hj 1 Complex.I (by simp) (by simp) k h1 h2
    · exact hdisjcase hj Complex.I 1 (by simp) (by simp) k h1 h2
    · exact hdisjcase hj Complex.I Complex.I (by simp) (by simp) k h1 h2
  -- counting: n disjoint nonempty supports are singletons
  have hcard1 : ∀ j, (S j).card = 1 := by
    have hsumle : ∑ j, (S j).card ≤ n := by
      rw [← Finset.card_biUnion (fun j₁ _ j₂ _ hj => hdisj j₁ j₂ hj)]
      calc ((Finset.univ : Finset (Fin n)).biUnion S).card
          ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    have hge : ∀ j ∈ (Finset.univ : Finset (Fin n)), 1 ≤ (S j).card :=
      fun j _ => Finset.card_pos.mpr (hne j)
    have hone : ∑ _j : Fin n, (1:ℕ) = n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    have htot : ∑ _j : Fin n, (1:ℕ) ≤ ∑ j, (S j).card :=
      Finset.sum_le_sum hge
    have heq : ∑ _j : Fin n, (1:ℕ) = ∑ j, (S j).card := by omega
    intro j
    exact ((Finset.sum_eq_sum_iff_of_le hge).mp heq j
      (Finset.mem_univ j)).symm
  have hloc : ∀ j, ∃ k, S j = {k} :=
    fun j => Finset.card_eq_one.mp (hcard1 j)
  choose loc hlocS using hloc
  have hoff : ∀ j i, i ≠ loc j →
      L (Pi.single j 1) i = 0 ∧ L (Pi.single j Complex.I) i = 0 := by
    intro j i hne'
    by_contra hcon
    have hmem : i ∈ S j :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_and_or.mp hcon⟩
    rw [hlocS j] at hmem
    exact hne' (Finset.mem_singleton.mp hmem)
  have hinj : Function.Injective loc := by
    intro j₁ j₂ h
    by_contra hj
    have h1 : loc j₁ ∈ S j₁ := by
      rw [hlocS j₁]; exact Finset.mem_singleton_self _
    have h2 : loc j₁ ∈ S j₂ := by
      rw [hlocS j₂, ← h]; exact Finset.mem_singleton_self _
    exact (Finset.disjoint_left.mp (hdisj j₁ j₂ hj)) h1 h2
  -- the block decomposition of a single-coordinate state
  have hblock : ∀ (j : Fin n) (z : ℂ),
      L (Pi.single j z) = Pi.single (loc j)
        (z.re • L (Pi.single j 1) (loc j)
          + z.im • L (Pi.single j Complex.I) (loc j)) := by
    intro j z
    have hdecomp : (Pi.single j z : Fin n → ℂ)
        = z.re • (Pi.single j 1 : Fin n → ℂ)
          + z.im • (Pi.single j Complex.I : Fin n → ℂ) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply]
      split_ifs
      · rw [Complex.real_smul, Complex.real_smul, mul_one]
        exact (Complex.re_add_im z).symm
      · simp
    rw [hdecomp, map_add, map_smul, map_smul]
    funext i
    by_cases h : i = loc j
    · subst h
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same]
    · obtain ⟨h1, h2⟩ := hoff j i h
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, h1, h2,
        Pi.single_eq_of_ne h, smul_zero, smul_zero, add_zero]
  -- block norm preservation
  have hbnorm : ∀ (j : Fin n) (z : ℂ),
      ‖z.re • L (Pi.single j 1) (loc j)
        + z.im • L (Pi.single j Complex.I) (loc j)‖ = ‖z‖ := by
    intro j z
    have hmz := hiso (Pi.single j z)
    rw [hblock j z, single_sum_eq hp0' (loc j) _,
      single_sum_eq hp0' j z] at hmz
    exact rpow_left_inj_nonneg (norm_nonneg _) (norm_nonneg _) hp0 hmz
  refine ⟨Equiv.ofBijective loc (Finite.injective_iff_bijective.mp hinj),
    ?_⟩
  intro x j
  simp only [Equiv.ofBijective_apply]
  have hTx : L x (loc j) = (x j).re • L (Pi.single j 1) (loc j)
      + (x j).im • L (Pi.single j Complex.I) (loc j) := by
    conv_lhs => rw [show x = ∑ j', Pi.single j' (x j') from
      (Finset.univ_sum_single x).symm]
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [hblock j (x j), Pi.single_eq_same]
    · intro j' _ hne'
      rw [hblock j' (x j')]
      exact Pi.single_eq_of_ne (fun h => hne' ((hinj h).symm)) _
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hTx]
  exact hbnorm j (x j)

/-- THE ZERO-STRUCTURE CAPSTONE: a bare set-map of states whose
steps subdivide into surjective measure- and distinguishability-
preserving sub-steps, and under which anything at all changes, is
forced onto the Born exponent p = 2.  No linearity, no complex
structure, no losslessness of F itself is assumed — all of it is
derived. -/
theorem born_from_time_alone {p : ℝ} (hp : 1 ≤ p) {n : ℕ}
    (F : (Fin n → ℂ) → (Fin n → ℂ))
    (hdiv : ∀ m : ℕ, 0 < m →
      ∃ G : (Fin n → ℂ) → (Fin n → ℂ),
        Function.Surjective G ∧
        (∀ x : Fin n → ℂ, ∑ i, ‖G x i‖ ^ p = ∑ i, ‖x i‖ ^ p) ∧
        (∀ x y : Fin n → ℂ,
          ∑ i, ‖G x i - G y i‖ ^ p = ∑ i, ‖x i - y i‖ ^ p) ∧
        G^[m] = F)
    (hchange : ∃ (x : Fin n → ℂ) (j : Fin n), ‖F x j‖ ≠ ‖x j‖) :
    p = 2 := by
  by_contra hp2
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hMpos : 0 < Monoid.exponent (Equiv.Perm (Fin n)) :=
    Monoid.exponent_pos.mpr Monoid.ExponentExists.of_finite
  obtain ⟨G, hsurj, hmeas, hdist, hpow⟩ :=
    hdiv (Monoid.exponent (Equiv.Perm (Fin n))) hMpos
  obtain ⟨hadd, hsmul⟩ :=
    lossless_bijection_is_real_linear hp G hsurj hmeas hdist
  let L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := G
      map_add' := hadd
      map_smul' := fun c x => hsmul c x }
  have hisoL : ∀ x : Fin n → ℂ, ∑ i, ‖L x i‖ ^ p = ∑ i, ‖x i‖ ^ p :=
    hmeas
  obtain ⟨σ, hσ⟩ := real_lossless_frozen_measure hp0 hp2 L hisoL
  have hσG : ∀ (x : Fin n → ℂ) (j : Fin n), ‖G x (σ j)‖ = ‖x j‖ :=
    fun x j => hσ x j
  have hiter : ∀ (k : ℕ) (x : Fin n → ℂ) (j : Fin n),
      ‖G^[k] x ((σ ^ k) j)‖ = ‖x j‖ := by
    intro k
    induction k with
    | zero =>
      intro x j
      rw [Function.iterate_zero_apply, pow_zero, Equiv.Perm.one_apply]
    | succ k ih =>
      intro x j
      rw [Function.iterate_succ_apply, pow_succ, Equiv.Perm.mul_apply,
        ih (G x) (σ j)]
      exact hσG x j
  obtain ⟨x, j, hx⟩ := hchange
  have h := hiter (Monoid.exponent (Equiv.Perm (Fin n))) x j
  rw [hpow, show σ ^ Monoid.exponent (Equiv.Perm (Fin n)) = 1 from
    Monoid.pow_exponent_eq_one σ, Equiv.Perm.one_apply] at h
  exact hx h

#print axioms real_binary_bi_normalized_deterministic
#print axioms l1_mixing_impossible
#print axioms phase_order_matters_in_quaternions
#print axioms rpow_superadd_strict
#print axioms lamperti_two_by_two_gt_two
#print axioms rpow_midpoint_convex
#print axioms rpow_midpoint_concave
#print axioms rpow_subadd_strict
#print axioms quadrature_probes_gt_one_impossible
#print axioms quadrature_probes_lt_one_impossible
#print axioms lamperti_columns_ne_two
#print axioms p_two_probes_force_unitary
#print axioms mixing_lossless_forces_p_eq_two
#print axioms lossless_ne_two_is_weighted_permutation
#print axioms l2_lossless_columns_orthogonal
#print axioms lossless_dichotomy
#print axioms frozen_measure_ne_two
#print axioms frozen_measure_pow
#print axioms root_at_symmetric_order_forces_static
#print axioms divisible_time_forces_static
#print axioms change_and_divisibility_force_born
#print axioms root_at_group_exponent_forces_static
#print axioms square_of_semilinear_is_linear
#print axioms antiunitary_has_no_half_step
#print axioms lossless_bijection_is_real_linear
#print axioms monotone_additive_on_cone_is_linear
#print axioms born_function_unique
#print axioms rpow_left_inj_nonneg
#print axioms single_sum_eq
#print axioms single_probe_sum_unit
#print axioms pair_probe_sum_unit
#print axioms real_lossless_frozen_measure
#print axioms born_from_time_alone

end UnifiedTheory.Audit.KFCausalUniquenessLeg
