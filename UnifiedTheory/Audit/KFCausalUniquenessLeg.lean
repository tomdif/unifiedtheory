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
  4. `lamperti_two_by_two_gt_two` - the GENERAL p > 2 Lamperti
     obstruction, for ALL real p > 2 at once: no 2x2 complex matrix
     with nonzero mixing entries preserves the l^p norm of the four
     probes e1, e2, (1,1), (1,-1).  Calculus-free proof:
     parallelogram law + two-term Minkowski + strict superadditivity
     of x^(p/2).  With p = 1 (item 2) machine-checked and 1 < p < 2
     by the analytic t-expansion (UNIQUENESS_LEG.md, registered
     debt), p = 2 is the unique mixing-compatible measure exponent.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Basic

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

#print axioms real_binary_bi_normalized_deterministic
#print axioms l1_mixing_impossible
#print axioms phase_order_matters_in_quaternions
#print axioms rpow_superadd_strict
#print axioms lamperti_two_by_two_gt_two

end UnifiedTheory.Audit.KFCausalUniquenessLeg
