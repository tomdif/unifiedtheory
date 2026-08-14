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

end UnifiedTheory.Audit.KFCausalUniquenessLeg
