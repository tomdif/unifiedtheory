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
  17. `quantum_mechanics_from_time_alone` - THE FULL PACKAGE:
     divisible lossless PHASE-COVARIANT set-map roots + change give
     p = 2 AND F complex-linear with orthonormal columns - unitary
     quantum mechanics, whole.  Gauge (the global phase is
     unobservable; only the quarter-turn is used) closes the
     O(2n)-vs-U(n) Wigner gap:
     `phase_covariant_real_linear_is_complex_linear`.
  18. `balanced_beam_splitter_forces_born` - FIRST BREACH OF THE
     ORLICZ-LAMPERTI WALL: a monotone measure Σ f(‖·‖) lossless
     across ONE balanced two-way interference step is exactly
     f(x) = x² f(1) - the Born function from the full monotone
     class, no continuity, no power family.  Via the halving law +
     the Jordan-von Neumann quadratic functional equation with
     monotone solutions (`monotone_quadratic_functional_eq`).
     Dynamical wrapper: `lossless_beam_splitter_step_forces_born`.
  19. `dense_splitting_forces_linear` + `splitter_family_forces_born`
     - DENSE SPLITTING RIGIDITY: splitters of a DENSE set of
     transmittances (what iterating ONE generic lossless rotation
     supplies) force the Born function over all monotone measures.
     The heart is `dense_splitting_no_jump`: continuity is DERIVED
     - a jump would be copied in full by every available ratio,
     and finitely many disjoint copies exceed the total variation.
     Order kills the jump; dense ratios then give exact Pythagorean
     additivity; monotone Cauchy finishes.  Generic interference,
     not fine-tuned interference, is enough for Born.
  20. `generic_rotation_forces_born` - THE DENSITY GLUE FORMALIZED:
     for θ/π irrational, {cos²(kθ)} is dense in (0,1)
     (`cos_sq_orbit_dense`, via AddSubgroup.dense_or_cyclic on
     ℤθ + ℤπ), and iterating one lossless rotation block realizes
     that dense splitter family (`rotation_block_iterate`).
     End-to-end, citation-free: ONE lossless irrational-angle
     rotation step forces f(x) = x² f(1) for every monotone
     measure.  Almost every interference device forces Born by
     itself.
  21. `mixing_block_forces_measure_continuity` - EXCHANGE
     TRANSPORT: subtracting the (s,t)/(s,-t) probes of ONE mixing
     block yields an exchange identity that copies any jump of the
     measure, in full, to κ²·w (κ = σ/c); for lopsided blocks
     (c² ≠ σ²) the copies descend a geometric ladder and finitely
     many exceed the total variation.  EVERY mixing block - any
     angle, rational or irrational, unnormalized - forces the
     monotone measure to be continuous.  No iteration of the
     dynamics is used.  Residue: continuous g under the finite
     per-scale constraints of a rational-angle block (registered
     Mellin attack in the section header).
  22. `approximate_beam_splitter_near_born` - STABILITY: if the
     balanced-splitter losslessness holds only to precision δ, the
     monotone measure is uniformly within (4/3)·δ of an exact Born
     function (`monotone_quadratic_stability`: Hyers' geometric
     sequence + §18 monotone rigidity classifying the limit).
     Finite-precision interference data quantitatively bounds
     Born-rule deviations - the reconstruction as an experimental
     inequality.
  23. `complex_mixing_block_forces_born` - THE WALL FALLS: probing
     one mixing block with a COMPLEX phase sweeps the output
     argument over a continuous interval at fixed input measure;
     overlapping intervals chain across each level
     (`phase_interval_additivity`, explicit finite ladder, no
     continuity/monotonicity/density) and force exact Pythagorean
     additivity.  ONE interference device plus a dialable phase
     forces the Born function on ALL monotone measures - any angle,
     unnormalized.  Supersedes the SS18-21 case analysis for the
     Born conclusion.
  24. `quantum_mechanics_from_a_beam_splitter` - THE TERMINAL
     THEOREM: monotone nontrivial measure + lossless surjective
     distinguishability-preserving gauge-covariant SET-MAP dynamics
     + one lossless beam-splitter event  ==>  f(x) = x^2 f(1) with
     f(1) > 0 AND the dynamics is complex-linear with orthonormal
     columns.  The Born rule and unitary quantum mechanics, with
     the measure function, linearity, complex structure, and
     unitarity all DERIVED.  (Born first via the phase continuum;
     the derived l^2 metric then powers Mazur-Ulam retroactively.)
  25. `master_chaining` - MEASURE HOMOGENIZATION: two functions
     g1, g2 tied by the interference exchange (P + Q = 1) are forced
     equal and jointly linear - a common Born function.  One
     interference event between two sectors forces them onto the
     SAME probability calculus (the same FUNCTION, not just the same
     exponent), from arbitrary monotone pairs.  Engine of the
     two-overlap Born-or-trivial result.
  26. THE WIDTH-PHASE METER (formal core of the quantum expansion
     law): `single_class_born` (degenerate-spectrum no-go),
     `halfplane_separation_infeasible` (octant-coverage necessity),
     `antipodal_pair_reaches_born` (one antipodal pair suffices,
     explicit quadratic root), `gap_splits_width` +
     `width_phase_octant` + `octant_period` (each unit of causal
     in-degree rotates the amplitude phase by one octant at pi/4;
     zeta^8 = 1 - width metered mod 8).  Born feasibility of a
     restricted growth family = octant coverage of its gap phases.

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
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecificLimits.Basic

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

/-! ## 17. Gauge closes the Wigner gap: unitarity, not just p = 2

The zero-structure capstone concluded the Born exponent but not
unitarity: measure-losslessness alone at p = 2 permits all of
O(2n).  ONE physically-forced covariance closes the gap: the global
phase is unobservable (gauge), so each sub-step commutes with it —
and commuting with the single quarter-turn x ↦ i·x already upgrades
Mazur–Ulam's real-linearity to complex-linearity
(`phase_covariant_real_linear_is_complex_linear`: z = re + im·i and
ℝ-linearity do the rest).  Then p = 2 (capstone) plus the general-n
unitarity theorem give orthonormal columns.

`quantum_mechanics_from_time_alone` — THE FULL PACKAGE.
Hypotheses: p ≥ 1; for every m a surjective set-map root of F
preserving measure, distinguishability, and the global phase; and
something happens.  Conclusion: p = 2 AND F is a complex-linear map
with orthonormal columns — unitary quantum mechanics, whole.  The
axioms name: time (divisible, lossless), gauge (phase is
unobservable), and change. -/

/-- A real-linear map commuting with the quarter-turn of global
phase is complex-linear. -/
theorem phase_covariant_real_linear_is_complex_linear {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))
    (hphase : ∀ x : Fin n → ℂ, L (Complex.I • x) = Complex.I • L x) :
    ∀ (z : ℂ) (x : Fin n → ℂ), L (z • x) = z • L x := by
  intro z x
  have hzdecomp : ∀ y : Fin n → ℂ,
      z • y = z.re • y + z.im • (Complex.I • y) := by
    intro y
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul,
      smul_eq_mul]
    have hz : (z.re : ℂ) + z.im * Complex.I = z := Complex.re_add_im z
    linear_combination (y i) * hz.symm
  rw [hzdecomp x, map_add, map_smul, map_smul, hphase, ← hzdecomp (L x)]

/-- THE FULL PACKAGE: complex quantum mechanics from time alone. -/
theorem quantum_mechanics_from_time_alone {p : ℝ} (hp : 1 ≤ p) {n : ℕ}
    (F : (Fin n → ℂ) → (Fin n → ℂ))
    (hdiv : ∀ m : ℕ, 0 < m →
      ∃ G : (Fin n → ℂ) → (Fin n → ℂ),
        Function.Surjective G ∧
        (∀ x : Fin n → ℂ, ∑ i, ‖G x i‖ ^ p = ∑ i, ‖x i‖ ^ p) ∧
        (∀ x y : Fin n → ℂ,
          ∑ i, ‖G x i - G y i‖ ^ p = ∑ i, ‖x i - y i‖ ^ p) ∧
        (∀ x : Fin n → ℂ, G (Complex.I • x) = Complex.I • G x) ∧
        G^[m] = F)
    (hchange : ∃ (x : Fin n → ℂ) (j : Fin n), ‖F x j‖ ≠ ‖x j‖) :
    p = 2 ∧
    ∃ U : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ),
      (∀ x : Fin n → ℂ, U x = F x) ∧
      ∀ j₁ j₂ : Fin n,
        ∑ i, (starRingEnd ℂ) (U (Pi.single j₁ 1) i)
          * U (Pi.single j₂ 1) i
        = if j₁ = j₂ then 1 else 0 := by
  have hp2 : p = 2 :=
    born_from_time_alone hp F
      (fun m hm => by
        obtain ⟨G, h1, h2, h3, _, h5⟩ := hdiv m hm
        exact ⟨G, h1, h2, h3, h5⟩)
      hchange
  refine ⟨hp2, ?_⟩
  -- F itself is a root at m = 1
  obtain ⟨G, hsurj, hmeas, hdist, hphase, hpow⟩ := hdiv 1 one_pos
  have hGF : G = F := by
    rw [← hpow]
    exact (Function.iterate_one G).symm
  subst hGF
  obtain ⟨hadd, hsmulR⟩ :=
    lossless_bijection_is_real_linear hp G hsurj hmeas hdist
  let L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := G
      map_add' := hadd
      map_smul' := fun c x => hsmulR c x }
  have hphaseL : ∀ x : Fin n → ℂ, L (Complex.I • x) = Complex.I • L x :=
    hphase
  have hsmulC := phase_covariant_real_linear_is_complex_linear L hphaseL
  let U : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := G
      map_add' := hadd
      map_smul' := fun z x => hsmulC z x }
  -- the p = 2 measure in mul-self form
  have hsq : ∀ z : ℂ, ‖z‖ ^ (2:ℝ) = ‖z‖ * ‖z‖ := by
    intro z
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hms : ∀ x : Fin n → ℂ,
      ∑ i, ‖U x i‖ * ‖U x i‖ = ∑ i, ‖x i‖ * ‖x i‖ := by
    intro x
    have h := hmeas x
    rw [hp2] at h
    calc ∑ i, ‖U x i‖ * ‖U x i‖
        = ∑ i, ‖G x i‖ ^ (2:ℝ) :=
          Finset.sum_congr rfl fun i _ => (hsq _).symm
      _ = ∑ i, ‖x i‖ ^ (2:ℝ) := h
      _ = ∑ i, ‖x i‖ * ‖x i‖ :=
          Finset.sum_congr rfl fun i _ => hsq _
  refine ⟨U, fun x => rfl, ?_⟩
  intro j₁ j₂
  by_cases hj : j₁ = j₂
  · subst hj
    rw [if_pos rfl]
    have hcol : ∑ i, ‖U (Pi.single j₁ 1) i‖ * ‖U (Pi.single j₁ 1) i‖
        = 1 := (hms _).trans (single_probe_sum_sq j₁ 1 (by simp))
    calc ∑ i, (starRingEnd ℂ) (U (Pi.single j₁ 1) i)
          * U (Pi.single j₁ 1) i
        = ∑ i, ((‖U (Pi.single j₁ 1) i‖ * ‖U (Pi.single j₁ 1) i‖ : ℝ)
            : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_comm ((starRingEnd ℂ) _), Complex.mul_conj]
          norm_cast
          rw [Complex.normSq_eq_norm_sq]
          ring
      _ = ((∑ i, ‖U (Pi.single j₁ 1) i‖ * ‖U (Pi.single j₁ 1) i‖ : ℝ)
            : ℂ) := by
          rw [Complex.ofReal_sum]
      _ = 1 := by rw [hcol]; norm_num
  · rw [if_neg hj]
    exact l2_lossless_columns_orthogonal U hms j₁ j₂ hj

/-! ## 18. A beam splitter forces the Born function: first breach of
the Orlicz–Lamperti wall

Section 15 left one seam in dissolving the measure family: deriving
Pythagorean additivity from the EXISTENCE of a mixing lossless step,
for an arbitrary monotone measure Σ f(‖·‖).  This section breaches
it at the physically canonical mixing step: if the measure is
lossless across ONE balanced two-way interference step (a 50/50
beam splitter — the columns (e₁±e₂)/√2), then f is EXACTLY the Born
function x² f(1).  Not the exponent within a power family — the
function itself, from the full class of monotone measures, with no
continuity assumed.

Mechanism: probing the splitter with (s, t) gives
f((s+t)/√2) + f(|s−t|/√2) = f(s) + f(t); the t = 0 probe gives the
halving law f(s/√2) = f(s)/2; together they yield the
Jordan–von Neumann quadratic functional equation
f(s+t) + f(s−t) = 2f(s) + 2f(t) on the cone, whose monotone
solutions are exactly x² f(1)
(`monotone_quadratic_functional_eq`: naturals by two-step
induction, rationals by scaling, irrationals by order squeeze —
Hamel pathologies again die by monotonicity, not topology).

Physics reading: interference and probability-additivity coexist
for exactly one measure calculus.  Any world with a monotone
measure, losslessness, and one balanced interference event is
already Born.  Remaining Orlicz–Lamperti generality (arbitrary
mixing matrices rather than the canonical one) stays open. -/

/-- Monotone solutions of the Jordan–von Neumann quadratic
functional equation on the cone are exactly x² f(1).  No continuity
assumed. -/
theorem monotone_quadratic_functional_eq (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (hquad : ∀ s t : ℝ, 0 ≤ t → t ≤ s →
      f (s + t) + f (s - t) = 2 * f s + 2 * f t) :
    ∀ x : ℝ, 0 ≤ x → f x = x ^ 2 * f 1 := by
  have hnat : ∀ (k : ℕ) (x : ℝ), 0 ≤ x → f (k * x) = (k:ℝ)^2 * f x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 => intro x _; simpa using hf0
      | 1 => intro x _; norm_num
      | (m+2) =>
        intro x hx
        have h1 := ih (m+1) (by omega) x hx
        have h0 := ih m (by omega) x hx
        have hle : x ≤ ((m+1 : ℕ) : ℝ) * x := by
          have : (1:ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
          nlinarith
        have hq := hquad (((m+1 : ℕ) : ℝ) * x) x hx hle
        have e1 : ((m+1 : ℕ) : ℝ) * x + x = ((m+2 : ℕ) : ℝ) * x := by
          push_cast; ring
        have e2 : ((m+1 : ℕ) : ℝ) * x - x = (m : ℝ) * x := by
          push_cast; ring
        rw [e1, e2, h1] at hq
        have h0' : f ((m : ℕ) * x) = ((m : ℕ) : ℝ)^2 * f x := h0
        push_cast at h0' hq ⊢
        nlinarith [hq, h0']
  have hratsq : ∀ (a b : ℕ), 0 < b → f ((a : ℝ) / b) = ((a:ℝ)/b)^2 * f 1 := by
    intro a b hb
    have hbR : (0:ℝ) < b := by exact_mod_cast hb
    have hab : (0:ℝ) ≤ (a:ℝ) / b := div_nonneg (Nat.cast_nonneg a) (le_of_lt hbR)
    have h1 : f ((b:ℝ) * ((a:ℝ)/b)) = ((b:ℝ))^2 * f ((a:ℝ)/b) := hnat b _ hab
    have h2 : (b:ℝ) * ((a:ℝ)/b) = a := by field_simp
    have h3 : f (a:ℝ) = ((a:ℝ))^2 * f 1 := by
      have := hnat a 1 zero_le_one
      simpa using this
    rw [h2, h3] at h1
    have hb2 : ((b:ℝ))^2 ≠ 0 := by positivity
    field_simp at h1 ⊢
    linarith
  have hrat : ∀ q : ℚ, 0 ≤ q → f (q : ℝ) = ((q:ℝ))^2 * f 1 := by
    intro q hq
    have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hcast : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum
    have hqR : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
      rw [hcast, Rat.cast_def]
    rw [hqR]
    exact hratsq q.num.toNat q.den q.pos
  have hf1 : 0 ≤ f 1 := by
    have := hmono 0 1 le_rfl zero_le_one
    linarith
  intro x hx
  rcases eq_or_lt_of_le hf1 with hf1e | hf1pos
  · obtain ⟨q, hq⟩ := exists_rat_gt x
    have hq0 : (0:ℚ) ≤ q := by exact_mod_cast le_of_lt (lt_of_le_of_lt hx hq)
    have hup : f x ≤ f q := hmono _ _ hx (le_of_lt hq)
    have hlo : f 0 ≤ f x := hmono _ _ le_rfl hx
    rw [hrat q hq0, ← hf1e] at hup
    rw [hf0] at hlo
    have : f x = 0 := le_antisymm (by simpa using hup) hlo
    rw [this, ← hf1e]
    ring
  · apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hden : 0 < (2 * x + 1) * f 1 := by nlinarith
      set δ : ℝ := min 1 (ε / ((2 * x + 1) * f 1)) with hδdef
      have hδpos : 0 < δ := lt_min one_pos (div_pos hε hden)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right x hδpos)
      have hq0 : (0:ℚ) ≤ q := by
        exact_mod_cast le_of_lt (lt_of_le_of_lt hx hq1)
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hδ2 : δ ≤ ε / ((2 * x + 1) * f 1) := min_le_right _ _
      have hkey : ((q:ℝ))^2 * f 1 ≤ x^2 * f 1 + ε := by
        have hqx : (q:ℝ) < x + δ := hq2
        have hq2' : ((q:ℝ))^2 < (x + δ)^2 := by
          have : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq0
          nlinarith
        have hexp : (x + δ)^2 ≤ x^2 + δ * (2*x + 1) := by nlinarith
        have hδε : δ * ((2*x+1) * f 1) ≤ ε := by
          calc δ * ((2*x+1) * f 1)
              ≤ (ε / ((2*x+1) * f 1)) * ((2*x+1) * f 1) := by
                exact mul_le_mul_of_nonneg_right hδ2 (le_of_lt hden)
            _ = ε := by field_simp
        nlinarith
      calc f x ≤ f q := hmono _ _ hx (le_of_lt hq1)
        _ = ((q:ℝ))^2 * f 1 := hrat q hq0
        _ ≤ x^2 * f 1 + ε := hkey
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hden : 0 < (2 * x + 1) * f 1 := by nlinarith
      set δ : ℝ := min 1 (ε / ((2 * x + 1) * f 1)) with hδdef
      have hδpos : 0 < δ := lt_min one_pos (div_pos hε hden)
      have hδ2 : δ ≤ ε / ((2 * x + 1) * f 1) := min_le_right _ _
      have hδε : δ * ((2*x+1) * f 1) ≤ ε := by
        calc δ * ((2*x+1) * f 1)
            ≤ (ε / ((2*x+1) * f 1)) * ((2*x+1) * f 1) := by
              exact mul_le_mul_of_nonneg_right hδ2 (le_of_lt hden)
          _ = ε := by field_simp
      by_cases hxs : x ≤ δ
      · have h1 : x^2 * f 1 ≤ ε := by
          have hδ1 : δ ≤ 1 := min_le_left _ _
          nlinarith
        have h2 : 0 ≤ f x := by
          have := hmono 0 x le_rfl hx
          linarith
        linarith
      · push_neg at hxs
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self x hδpos)
        have hq0 : (0:ℚ) ≤ q := by
          have : (0:ℝ) < x - δ := by linarith
          exact_mod_cast le_of_lt (lt_trans this hq1)
        have hkey : x^2 * f 1 ≤ ((q:ℝ))^2 * f 1 + ε := by
          have hqx : x - δ < (q:ℝ) := hq1
          have hq2' : (x - δ)^2 ≤ ((q:ℝ))^2 := by
            have h0q : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq0
            have hxδ : (0:ℝ) ≤ x - δ := by linarith
            nlinarith
          have hexp : x^2 - δ * (2*x+1) ≤ (x - δ)^2 := by nlinarith
          nlinarith
        calc x^2 * f 1 ≤ ((q:ℝ))^2 * f 1 + ε := hkey
          _ = f q + ε := by rw [hrat q hq0]
          _ ≤ f x + ε := by
              have := hmono q x (by exact_mod_cast hq0) (le_of_lt hq2)
              linarith

/-- A BALANCED BEAM SPLITTER FORCES THE BORN FUNCTION: if a monotone
measure is lossless across one balanced two-way interference step,
it is exactly f(x) = x² f(1).  No continuity, no power-family
assumption. -/
theorem balanced_beam_splitter_forces_born (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (hsplit : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      f ((s + t) / Real.sqrt 2) + f (|s - t| / Real.sqrt 2)
        = f s + f t) :
    ∀ x : ℝ, 0 ≤ x → f x = x ^ 2 * f 1 := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hhalf : ∀ s : ℝ, 0 ≤ s → f (s / Real.sqrt 2) = f s / 2 := by
    intro s hs
    have h := hsplit s 0 hs le_rfl
    rw [add_zero, sub_zero, abs_of_nonneg hs, hf0, add_zero] at h
    linarith
  apply monotone_quadratic_functional_eq f hf0 hmono
  intro s t ht hts
  have hs : 0 ≤ s := le_trans ht hts
  have h := hsplit s t hs ht
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)] at h
  rw [hhalf (s + t) (by linarith), hhalf (s - t) (by linarith)] at h
  linarith

/-- The dynamical wrapper: a real-linear step, lossless for the
measure Σ f(‖·‖), one of whose column pairs is a balanced beam
splitter, forces f(x) = x² f(1). -/
theorem lossless_beam_splitter_step_forces_born {n : ℕ}
    (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, f ‖B x i‖ = ∑ i, f ‖x i‖)
    {j₁ j₂ k₁ k₂ : Fin n} (hj : j₁ ≠ j₂) (hk : k₁ ≠ k₂)
    (hcol1 : B (Pi.single j₁ 1)
      = (Real.sqrt 2)⁻¹ • (Pi.single k₁ 1 + Pi.single k₂ 1))
    (hcol2 : B (Pi.single j₂ 1)
      = (Real.sqrt 2)⁻¹ • (Pi.single k₁ 1 - Pi.single k₂ 1)) :
    ∀ x : ℝ, 0 ≤ x → f x = x ^ 2 * f 1 := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- measure of a two-coordinate state
  have hpairf : ∀ {a b : Fin n}, a ≠ b → ∀ c d : ℂ,
      ∑ i, f ‖(Pi.single a c + Pi.single b d : Fin n → ℂ) i‖
        = f ‖c‖ + f ‖d‖ := by
    intro a b hab c d
    have hsplit' : ∀ i : Fin n,
        f ‖(Pi.single a c + Pi.single b d : Fin n → ℂ) i‖
        = f ‖(Pi.single a c : Fin n → ℂ) i‖
          + f ‖(Pi.single b d : Fin n → ℂ) i‖ := by
      intro i
      by_cases h1 : i = a
      · subst h1
        simp [Pi.single_eq_same, Pi.single_eq_of_ne hab, hf0]
      · by_cases h2 : i = b
        · subst h2
          simp [Pi.single_eq_same, Pi.single_eq_of_ne h1, hf0]
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, hf0]
    rw [Finset.sum_congr rfl fun i _ => hsplit' i, Finset.sum_add_distrib]
    have hsing : ∀ (e : Fin n) (z : ℂ),
        ∑ i, f ‖(Pi.single e z : Fin n → ℂ) i‖ = f ‖z‖ := by
      intro e z
      rw [Finset.sum_eq_single e]
      · rw [Pi.single_eq_same]
      · intro i _ hne
        rw [Pi.single_eq_of_ne hne, norm_zero, hf0]
      · intro hmem
        exact absurd (Finset.mem_univ e) hmem
    rw [hsing a c, hsing b d]
  apply balanced_beam_splitter_forces_born f hf0 hmono
  intro s t hs ht
  have hin : (s • (Pi.single j₁ 1 : Fin n → ℂ)
      + t • (Pi.single j₂ 1 : Fin n → ℂ))
      = Pi.single j₁ (s : ℂ) + Pi.single j₂ (t : ℂ) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply,
      Complex.real_smul]
    split_ifs <;> ring
  have hout : B (s • (Pi.single j₁ 1 : Fin n → ℂ)
      + t • (Pi.single j₂ 1 : Fin n → ℂ))
      = Pi.single k₁ (((s + t) / Real.sqrt 2 : ℝ) : ℂ)
        + Pi.single k₂ (((s - t) / Real.sqrt 2 : ℝ) : ℂ) := by
    rw [map_add, map_smul, map_smul, hcol1, hcol2]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Pi.single_apply, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_inv]
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hs2
    split_ifs <;> field_simp <;> ring
  have h := hiso (s • (Pi.single j₁ 1 : Fin n → ℂ)
    + t • (Pi.single j₂ 1 : Fin n → ℂ))
  rw [hout, hin] at h
  rw [hpairf hk _ _, hpairf hj _ _] at h
  rw [Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Complex.norm_real] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs] at h
  rw [abs_of_nonneg hs, abs_of_nonneg ht,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (s + t) / Real.sqrt 2),
    abs_div, abs_of_pos hs2] at h
  exact h

/-! ## 19. DENSE SPLITTING RIGIDITY: generic interference forces
Born over ALL monotone measures

Section 18 needed one fine-tuned 50/50 splitter.  This section
removes the fine-tuning: a monotone measure lossless across two-way
splitters of a DENSE set of transmittances λ ∈ (0,1) is exactly the
Born function.  Physically, a dense transmittance family is what a
single GENERIC interference device supplies: iterating one lossless
rotation of irrational angle θ/π produces splitters of transmittance
cos²(kθ), dense in (0,1) (orbit density of irrational rotations —
classical; its formalization via `AddSubgroup.dense_or_cyclic` is
the one remaining glue step, cited not formalized).  One generic
beam splitter, iterated, forces the Born rule.

The mathematical heart is `dense_splitting_no_jump`: CONTINUITY IS
DERIVED, NOT ASSUMED.  If the measure had a jump of size J at some
y, every available ratio λ would copy that jump in full onto the
pair {λy, (1−λ)y} (the split identity transports increments), and
N distinct ratios produce N disjoint copies below y — but a
monotone function has only g(2y) of total variation to spend, so N
copies of J exceed it for large N.  Order kills the jump.  With
continuity derived, dense ratios extend the split identity to
exact Pythagorean additivity, and monotone Cauchy (§15) finishes.
No topology is assumed anywhere in the chain; the only inputs are
order and losslessness. -/

/-- Increments of a monotone function over a sorted family of
disjoint intervals in `[0, B]` sum to at most `g B - g 0`. -/
theorem sum_sorted_increments_le (g : ℝ → ℝ)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b) :
    ∀ (N : ℕ) (a b : ℕ → ℝ) (B : ℝ),
      (∀ i, i < N → 0 ≤ a i) → (∀ i, i < N → a i ≤ b i) →
      (∀ i j, i < j → j < N → b i ≤ a j) →
      (∀ i, i < N → b i ≤ B) → 0 ≤ B →
      ∑ i ∈ Finset.range N, (g (b i) - g (a i)) ≤ g B - g 0 := by
  intro N
  induction N with
  | zero =>
    intro a b B _ _ _ _ hB0
    simpa using sub_nonneg.mpr (hmono 0 B le_rfl hB0)
  | succ N ih =>
    intro a b B h0 hab hsort hB hB0
    rw [Finset.sum_range_succ]
    have hprefix := ih a b (a N) (fun i hi => h0 i (by omega))
      (fun i hi => hab i (by omega))
      (fun i j hij hj => hsort i j hij (by omega))
      (fun i hi => hsort i N hi (by omega))
      (h0 N (by omega))
    have hmid : g (a N) ≤ g (b N) :=
      hmono _ _ (h0 N (by omega)) (hab N (by omega))
    have hlast : g (b N) ≤ g B :=
      hmono _ _ (le_trans (h0 N (by omega)) (hab N (by omega)))
        (hB N (by omega))
    linarith

set_option maxHeartbeats 1000000 in
/-- NO JUMPS: dense splitting forbids discontinuities.  A jump at y
would be copied in full below y by every available ratio, and
finitely many disjoint copies already exceed the total variation.
Continuity of the measure is DERIVED, not assumed. -/
theorem dense_splitting_no_jump (g : ℝ → ℝ)
    (hg0 : g 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b)
    (D : Set ℝ)
    (hD : ∀ u v : ℝ, 0 < u → u < v → v < 1 →
      ∃ lam, lam ∈ D ∧ u < lam ∧ lam < v)
    (hsplit : ∀ lam, lam ∈ D → 0 < lam → lam < 1 →
      ∀ x : ℝ, 0 ≤ x → g (lam * x) + g ((1 - lam) * x) = g x) :
    ∀ y : ℝ, 0 < y → ∀ ε : ℝ, 0 < ε →
      ∃ a' b' : ℝ, 0 ≤ a' ∧ a' < y ∧ y < b' ∧ g b' - g a' < ε := by
    intro y hy ε hε
    by_contra hcon
    push_neg at hcon
    -- hcon : ∀ a' b', 0 ≤ a' → a' < y → y < b' → ε ≤ g b' - g a'
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * g (2*y) / ε)
    set N : ℕ := N₀ + 1 with hNdef
    have hNgt : 2 * g (2*y) / ε < (N:ℝ) := by
      have : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_succ N₀
      linarith
    set W : ℝ := (N:ℝ) + 1 with hWdef
    have hWpos : (0:ℝ) < W := by positivity
    have hW1 : (1:ℝ) ≤ W := by
      have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      linarith
    set δ : ℝ := 1/(8*W) with hδdef
    set γ : ℝ := 1/(4*W) with hγdef
    have hδpos : 0 < δ := by positivity
    have hγpos : 0 < γ := by positivity
    have hγ1 : γ ≤ 1 := by
      rw [hγdef]
      rw [div_le_one (by positivity)]
      linarith
    -- the target midpoints, clamped so `choose` is unconditional
    have hcastN : ∀ i : ℕ, i < N → ((min i (N-1) : ℕ) : ℝ) = (i : ℝ) := by
      intro i hi
      congr 1
      omega
    have hμbounds : ∀ i : ℕ,
        (1:ℝ)/2 + 1/(2*W) ≤ 1/2 + ((min i (N-1) : ℕ) + 1 : ℝ)/(2*W) ∧
        1/2 + ((min i (N-1) : ℕ) + 1 : ℝ)/(2*W) ≤ 1/2 + (N:ℝ)/(2*W) := by
      intro i
      constructor
      · have h1 : (0:ℝ) ≤ ((min i (N-1) : ℕ) : ℝ) := Nat.cast_nonneg _
        have := div_le_div_of_nonneg_right (c := 2*W) (by linarith : (1:ℝ) ≤ ((min i (N-1) : ℕ) : ℝ) + 1) (by positivity)
        linarith [this]
      · have h1 : ((min i (N-1) : ℕ) : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.min_le_right i (N-1)
        have h2 : ((N-1 : ℕ) : ℝ) + 1 ≤ (N:ℝ) := by
          have : ((N-1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
            have : (1:ℕ) ≤ N := by omega
            push_cast [Nat.cast_sub this]
            ring
          linarith [this.le]
        have := div_le_div_of_nonneg_right (c := 2*W)
          (by linarith : ((min i (N-1) : ℕ) : ℝ) + 1 ≤ (N:ℝ)) (by positivity)
        linarith [this]
    have hpick : ∀ i : ℕ, ∃ lam, lam ∈ D ∧
        1/2 + ((min i (N-1) : ℕ) + 1 : ℝ)/(2*W) - δ < lam ∧
        lam < 1/2 + ((min i (N-1) : ℕ) + 1 : ℝ)/(2*W) + δ := by
      intro i
      obtain ⟨hlo, hhi⟩ := hμbounds i
      apply hD
      · -- 0 < μ - δ
        have : δ < 1/(2*W) := by
          rw [hδdef]
          apply div_lt_div_of_pos_left one_pos (by positivity)
          linarith
        linarith
      · linarith
      · -- μ + δ < 1
        have hN2W : (N:ℝ)/(2*W) = 1/2 - 1/(2*W) := by
          rw [hWdef]
          field_simp
          ring
        have : δ < 1/(2*W) := by
          rw [hδdef]
          apply div_lt_div_of_pos_left one_pos (by positivity)
          linarith
        rw [hN2W] at hhi
        linarith
    choose lam hlamD hlam1 hlam2 using hpick
    -- bounds and separation
    have hlam_half : ∀ i, i < N → 1/2 < lam i := by
      intro i hi
      have := (hμbounds i).1
      have hδlt : δ < 1/(2*W) := by
        rw [hδdef]
        apply div_lt_div_of_pos_left one_pos (by positivity)
        linarith
      linarith [hlam1 i]
    have hlam_lt1 : ∀ i, i < N → lam i < 1 := by
      intro i hi
      have := (hμbounds i).2
      have hN2W : (N:ℝ)/(2*W) = 1/2 - 1/(2*W) := by
        rw [hWdef]
        field_simp
        ring
      have hδlt : δ < 1/(2*W) := by
        rw [hδdef]
        apply div_lt_div_of_pos_left one_pos (by positivity)
        linarith
      rw [hN2W] at this
      linarith [hlam2 i]
    have hsep : ∀ i j, i < j → j < N → lam i + γ ≤ lam j := by
      intro i j hij hj
      have hi : i < N := lt_trans hij hj
      have hci := hcastN i hi
      have hcj := hcastN j hj
      have h1 := hlam2 i
      have h2 := hlam1 j
      rw [hci] at h1
      rw [hcj] at h2
      have hij' : (i:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast hij
      have hgap : ((i:ℝ)+1)/(2*W) + 1/(2*W) ≤ ((j:ℝ)+1)/(2*W) := by
        rw [div_add_div_same]
        apply div_le_div_of_nonneg_right (by linarith) (by positivity)
      have hδγ : 2*δ + γ ≤ 1/(2*W) := by
        rw [hδdef, hγdef]
        rw [show (8:ℝ)*W = 8*W from rfl]
        have : (1:ℝ)/(8*W) + 1/(8*W) + 1/(4*W) = 1/(2*W) := by
          field_simp
          ring
        linarith [this]
      linarith
    -- the bracket
    set η : ℝ := γ/8 with hηdef
    have hηpos : 0 < η := by positivity
    have hη1 : η < 1 := by
      rw [hηdef]
      linarith
    set a₀ : ℝ := y*(1-η) with ha₀def
    set b₀ : ℝ := y*(1+η) with hb₀def
    have ha₀0 : 0 ≤ a₀ := by
      rw [ha₀def]
      apply mul_nonneg (le_of_lt hy)
      linarith
    have ha₀y : a₀ < y := by
      rw [ha₀def]
      nlinarith
    have hyb₀ : y < b₀ := by
      rw [hb₀def]
      nlinarith
    have hb₀2y : b₀ ≤ 2*y := by
      rw [hb₀def]
      nlinarith
    have hb₀0 : 0 ≤ b₀ := le_trans ha₀0 (le_of_lt (lt_trans ha₀y hyb₀))
    -- each ratio copies the full jump
    have hrel : ∀ i, i < N →
        (g (lam i * b₀) - g (lam i * a₀))
        + (g ((1 - lam i) * b₀) - g ((1 - lam i) * a₀))
        = g b₀ - g a₀ := by
      intro i hi
      have hb := hsplit (lam i) (hlamD i) (by linarith [hlam_half i hi])
        (hlam_lt1 i hi) b₀ hb₀0
      have ha := hsplit (lam i) (hlamD i) (by linarith [hlam_half i hi])
        (hlam_lt1 i hi) a₀ ha₀0
      linarith
    have hjump : ε ≤ g b₀ - g a₀ := hcon a₀ b₀ ha₀0 ha₀y hyb₀
    have hsum_lo : (N:ℝ) * ε ≤
        ∑ i ∈ Finset.range N,
          ((g (lam i * b₀) - g (lam i * a₀))
            + (g ((1 - lam i) * b₀) - g ((1 - lam i) * a₀))) := by
      calc (N:ℝ) * ε = ∑ _i ∈ Finset.range N, ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            rw [hrel i (Finset.mem_range.mp hi)]
            exact hjump
    -- upper family
    have hupper : ∑ i ∈ Finset.range N,
        (g (lam i * b₀) - g (lam i * a₀)) ≤ g b₀ - g 0 := by
      apply sum_sorted_increments_le g hmono N _ _ b₀
      · intro i hi
        exact mul_nonneg (by linarith [hlam_half i hi]) ha₀0
      · intro i hi
        apply mul_le_mul_of_nonneg_left (by linarith) (by linarith [hlam_half i hi])
      · intro i j hij hj
        have hi : i < N := lt_trans hij hj
        have hs := hsep i j hij hj
        have hli := hlam_lt1 i hi
        have hlhi := hlam_half i hi
        have hlhj := hlam_half j hj
        rw [ha₀def, hb₀def]
        have key : lam i * (1+η) ≤ lam j * (1-η) := by
          have h1 : lam i * (1+η) ≤ lam i + η := by nlinarith
          have h2 : lam j - lam j * η ≥ lam j - η := by nlinarith [hlam_lt1 j hj]
          have h3 : lam i + η ≤ lam j - η := by
            have hηγ : 2*η ≤ γ := by rw [hηdef]; linarith
            linarith
          nlinarith [hlam_lt1 j hj]
        calc lam i * (y*(1+η)) = (lam i * (1+η)) * y := by ring
          _ ≤ (lam j * (1-η)) * y := by
              apply mul_le_mul_of_nonneg_right key (le_of_lt hy)
          _ = lam j * (y*(1-η)) := by ring
      · intro i hi
        calc lam i * b₀ ≤ 1 * b₀ := by
              apply mul_le_mul_of_nonneg_right
                (le_of_lt (hlam_lt1 i hi)) hb₀0
          _ = b₀ := one_mul _
      · exact hb₀0
    -- lower family (reflected index so it is increasing)
    have hlower : ∑ i ∈ Finset.range N,
        (g ((1 - lam i) * b₀) - g ((1 - lam i) * a₀)) ≤ g b₀ - g 0 := by
      rw [← Finset.sum_range_reflect]
      apply sum_sorted_increments_le g hmono N
        (fun i => (1 - lam (N - 1 - i)) * a₀)
        (fun i => (1 - lam (N - 1 - i)) * b₀) b₀
      · intro i hi
        exact mul_nonneg (by linarith [hlam_lt1 (N-1-i) (by omega)]) ha₀0
      · intro i hi
        apply mul_le_mul_of_nonneg_left (by linarith)
          (by linarith [hlam_lt1 (N-1-i) (by omega)])
      · intro i j hij hj
        have hp : N - 1 - j < N - 1 - i := by omega
        have hqN : N - 1 - i < N := by omega
        have hs := hsep (N-1-j) (N-1-i) hp hqN
        set p := N - 1 - j
        set q := N - 1 - i
        have hlq1 : lam q < 1 := hlam_lt1 q hqN
        have hlp_half : 1/2 < lam p := hlam_half p (by omega)
        have hlq_half : 1/2 < lam q := hlam_half q hqN
        rw [ha₀def, hb₀def]
        have key : (1 - lam q) * (1+η) ≤ (1 - lam p) * (1-η) := by
          have hq2 : 1 - lam q ≤ 1/2 := by linarith
          have hp2 : 1 - lam p ≤ 1/2 := by linarith
          have hlam_pq : 1 - lam q ≤ 1 - lam p - γ := by linarith
          have hηγ : 2*η ≤ γ := by rw [hηdef]; linarith
          nlinarith [hlam_lt1 p (by omega)]
        calc (1 - lam q) * (y*(1+η)) = ((1 - lam q) * (1+η)) * y := by ring
          _ ≤ ((1 - lam p) * (1-η)) * y := by
              apply mul_le_mul_of_nonneg_right key (le_of_lt hy)
          _ = (1 - lam p) * (y*(1-η)) := by ring
      · intro i hi
        have h1 : 1 - lam (N-1-i) ≤ 1 := by
          linarith [hlam_half (N-1-i) (by omega)]
        calc (1 - lam (N-1-i)) * b₀ ≤ 1 * b₀ := by
              apply mul_le_mul_of_nonneg_right h1 hb₀0
          _ = b₀ := one_mul _
      · exact hb₀0
    -- assemble the contradiction
    have hsum_split : ∑ i ∈ Finset.range N,
        ((g (lam i * b₀) - g (lam i * a₀))
          + (g ((1 - lam i) * b₀) - g ((1 - lam i) * a₀)))
        = (∑ i ∈ Finset.range N, (g (lam i * b₀) - g (lam i * a₀)))
          + ∑ i ∈ Finset.range N,
              (g ((1 - lam i) * b₀) - g ((1 - lam i) * a₀)) :=
      Finset.sum_add_distrib
    have hgb₀ : g b₀ ≤ g (2*y) := hmono _ _ hb₀0 hb₀2y
    have hfinal : (N:ℝ) * ε ≤ 2 * g (2*y) := by
      rw [hsum_split] at hsum_lo
      rw [hg0] at hupper hlower
      linarith
    have : 2 * g (2*y) < (N:ℝ) * ε := by
      rw [div_lt_iff₀ hε] at hNgt
      linarith
    linarith

set_option maxHeartbeats 1000000 in
/-- DENSE SPLITTING RIGIDITY: a monotone g with
g(λx) + g((1-λ)x) = g(x) for a dense set of ratios λ is linear.
No continuity assumed — it is derived (`dense_splitting_no_jump`),
then dense ratios extend the split to exact additivity, and
monotone Cauchy finishes. -/
theorem dense_splitting_forces_linear (g : ℝ → ℝ)
    (hg0 : g 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b)
    (D : Set ℝ)
    (hD : ∀ u v : ℝ, 0 < u → u < v → v < 1 →
      ∃ lam, lam ∈ D ∧ u < lam ∧ lam < v)
    (hsplit : ∀ lam, lam ∈ D → 0 < lam → lam < 1 →
      ∀ x : ℝ, 0 ≤ x → g (lam * x) + g ((1 - lam) * x) = g x) :
    ∀ x : ℝ, 0 ≤ x → g x = x * g 1 := by
  have hcont := dense_splitting_no_jump g hg0 hmono D hD hsplit
  -- additivity from derived continuity + dense ratios
  have hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → g (a + b) = g a + g b := by
    intro a b ha hb
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · rw [← ha0, hg0]
      ring_nf
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · rw [← hb0, hg0]
      ring_nf
    have hx : 0 < a + b := by linarith
    set x : ℝ := a + b with hxdef
    have key : ∀ ε : ℝ, 0 < ε → |g x - (g a + g b)| ≤ 2*ε := by
      intro ε hε
      obtain ⟨a₁, a₂, ha₁0, ha₁a, haa₂, haincr⟩ := hcont a hapos ε hε
      obtain ⟨b₁, b₂, hb₁0, hb₁b, hbb₂, hbincr⟩ := hcont b hbpos ε hε
      set u' : ℝ := max (max (a₁/x) ((x - b₂)/x)) (a/(2*x)) with hu'def
      set v' : ℝ := min (min (a₂/x) ((x - b₁)/x)) ((a/x + 1)/2) with hv'def
      have hu'pos : 0 < u' := lt_max_of_lt_right (by positivity)
      have hu'lt : u' < a/x := by
        apply max_lt (max_lt ?_ ?_) ?_
        · exact div_lt_div_of_pos_right ha₁a hx
        · rw [div_lt_div_iff_of_pos_right hx]
          linarith
        · exact div_lt_div_of_pos_left hapos hx (by linarith)
      have hv'gt : a/x < v' := by
        apply lt_min (lt_min ?_ ?_) ?_
        · exact div_lt_div_of_pos_right haa₂ hx
        · rw [div_lt_div_iff_of_pos_right hx]
          linarith
        · have hax1 : a/x < 1 := by
            rw [div_lt_one hx]
            linarith
          linarith
      have hv'lt1 : v' < 1 := by
        apply min_lt_of_right_lt
        have hax1 : a/x < 1 := by
          rw [div_lt_one hx]
          linarith
        linarith
      obtain ⟨lam, hlamD, hlamu, hlamv⟩ := hD u' v' hu'pos
        (lt_trans hu'lt hv'gt) hv'lt1
      have hlam0 : 0 < lam := lt_trans hu'pos hlamu
      have hlam1 : lam < 1 := lt_trans hlamv hv'lt1
      have hs := hsplit lam hlamD hlam0 hlam1 x (le_of_lt hx)
      -- λx ∈ (a₁, a₂)
      have hlxa₁ : a₁ < lam * x := by
        have h1 : a₁/x < lam := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hlamu
        rw [div_lt_iff₀ hx] at h1
        linarith
      have hlxa₂ : lam * x < a₂ := by
        have h1 : lam < a₂/x := lt_of_lt_of_le hlamv (le_trans (min_le_left _ _) (min_le_left _ _))
        rw [lt_div_iff₀ hx] at h1
        linarith
      -- (1-λ)x ∈ (b₁, b₂)
      have hlxb₁ : b₁ < (1 - lam) * x := by
        have h1 : lam < (x - b₁)/x := lt_of_lt_of_le hlamv (le_trans (min_le_left _ _) (min_le_right _ _))
        rw [lt_div_iff₀ hx] at h1
        nlinarith
      have hlxb₂ : (1 - lam) * x < b₂ := by
        have h1 : (x - b₂)/x < lam := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hlamu
        rw [div_lt_iff₀ hx] at h1
        nlinarith
      -- estimate the two displacements
      have hga : |g (lam * x) - g a| ≤ g a₂ - g a₁ := by
        rw [abs_sub_le_iff]
        constructor
        · have h1 : g (lam*x) ≤ g a₂ :=
            hmono _ _ (mul_nonneg (le_of_lt hlam0) (le_of_lt hx)) (le_of_lt hlxa₂)
          have h2 : g a₁ ≤ g a := hmono _ _ ha₁0 (le_of_lt ha₁a)
          linarith
        · have h1 : g a ≤ g a₂ := hmono _ _ (le_of_lt hapos) (le_of_lt haa₂)
          have h2 : g a₁ ≤ g (lam*x) := hmono _ _ ha₁0 (le_of_lt hlxa₁)
          linarith
      have hgb : |g ((1 - lam) * x) - g b| ≤ g b₂ - g b₁ := by
        rw [abs_sub_le_iff]
        constructor
        · have h1 : g ((1-lam)*x) ≤ g b₂ :=
            hmono _ _ (mul_nonneg (by linarith) (le_of_lt hx)) (le_of_lt hlxb₂)
          have h2 : g b₁ ≤ g b := hmono _ _ hb₁0 (le_of_lt hb₁b)
          linarith
        · have h1 : g b ≤ g b₂ := hmono _ _ (le_of_lt hbpos) (le_of_lt hbb₂)
          have h2 : g b₁ ≤ g ((1-lam)*x) := hmono _ _ hb₁0 (le_of_lt hlxb₁)
          linarith
      calc |g x - (g a + g b)|
          = |(g (lam*x) - g a) + (g ((1-lam)*x) - g b)| := by
            rw [← hs]
            ring_nf
        _ ≤ |g (lam*x) - g a| + |g ((1-lam)*x) - g b| := abs_add_le _ _
        _ ≤ (g a₂ - g a₁) + (g b₂ - g b₁) := add_le_add hga hgb
        _ ≤ 2*ε := by linarith
    have hzero : g x - (g a + g b) = 0 := by
      by_contra hne
      have habs : 0 < |g x - (g a + g b)| := abs_pos.mpr hne
      have h4 := key (|g x - (g a + g b)|/4) (by positivity)
      linarith
    linarith
  exact monotone_additive_on_cone_is_linear g hadd hmono

/-- A DENSE FAMILY OF SPLITTERS FORCES THE BORN FUNCTION: a monotone
measure lossless across two-way splitters of a dense set of
transmittances is exactly f(x) = x² f(1). -/
theorem splitter_family_forces_born (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (D : Set ℝ)
    (hD : ∀ u v : ℝ, 0 < u → u < v → v < 1 →
      ∃ lam, lam ∈ D ∧ u < lam ∧ lam < v)
    (hsplit : ∀ lam, lam ∈ D → 0 < lam → lam < 1 → ∀ s : ℝ, 0 ≤ s →
      f (Real.sqrt lam * s) + f (Real.sqrt (1 - lam) * s) = f s) :
    ∀ x : ℝ, 0 ≤ x → f x = x ^ 2 * f 1 := by
  set g : ℝ → ℝ := fun t => f (Real.sqrt t) with hgdef
  have hg0 : g 0 = 0 := by
    rw [hgdef]
    simp [Real.sqrt_zero, hf0]
  have hmonog : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b := by
    intro a b _ hab
    exact hmono _ _ (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt hab)
  have hsplitg : ∀ lam, lam ∈ D → 0 < lam → lam < 1 →
      ∀ x : ℝ, 0 ≤ x → g (lam * x) + g ((1 - lam) * x) = g x := by
    intro lam hlamD hlam0 hlam1 x hx
    rw [hgdef]
    simp only []
    rw [Real.sqrt_mul (le_of_lt hlam0) x, Real.sqrt_mul (by linarith) x]
    exact hsplit lam hlamD hlam0 hlam1 (Real.sqrt x) (Real.sqrt_nonneg x)
  have hlin := dense_splitting_forces_linear g hg0 hmonog D hD hsplitg
  intro x hx
  have h := hlin (x ^ 2) (sq_nonneg x)
  rw [hgdef] at h
  simp only [] at h
  rw [Real.sqrt_sq hx, Real.sqrt_one] at h
  exact h

/-- Dynamical wrapper: lossless real-linear steps realizing a dense
family of splitter transmittances force the Born function.  Only ONE
column per step is consumed. -/
theorem lossless_splitter_family_forces_born (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (D : Set ℝ)
    (hD : ∀ u v : ℝ, 0 < u → u < v → v < 1 →
      ∃ lam, lam ∈ D ∧ u < lam ∧ lam < v)
    (hstep : ∀ lam, lam ∈ D → 0 < lam → lam < 1 →
      ∃ (n : ℕ) (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))
        (j k₁ k₂ : Fin n), k₁ ≠ k₂ ∧
        (∀ x : Fin n → ℂ, ∑ i, f ‖B x i‖ = ∑ i, f ‖x i‖) ∧
        B (Pi.single j 1)
          = Pi.single k₁ ((Real.sqrt lam : ℝ) : ℂ)
            + Pi.single k₂ ((Real.sqrt (1 - lam) : ℝ) : ℂ)) :
    ∀ x : ℝ, 0 ≤ x → f x = x ^ 2 * f 1 := by
  apply splitter_family_forces_born f hf0 hmono D hD
  intro lam hlamD hlam0 hlam1 s hs
  obtain ⟨n, B, j, k₁, k₂, hk, hiso, hcol⟩ := hstep lam hlamD hlam0 hlam1
  -- measure of a single- and two-coordinate state
  have hsing : ∀ (e : Fin n) (z : ℂ),
      ∑ i, f ‖(Pi.single e z : Fin n → ℂ) i‖ = f ‖z‖ := by
    intro e z
    rw [Finset.sum_eq_single e]
    · rw [Pi.single_eq_same]
    · intro i _ hne
      rw [Pi.single_eq_of_ne hne, norm_zero, hf0]
    · intro hmem
      exact absurd (Finset.mem_univ e) hmem
  have hpairf : ∀ c d : ℂ,
      ∑ i, f ‖(Pi.single k₁ c + Pi.single k₂ d : Fin n → ℂ) i‖
        = f ‖c‖ + f ‖d‖ := by
    intro c d
    have hsplit' : ∀ i : Fin n,
        f ‖(Pi.single k₁ c + Pi.single k₂ d : Fin n → ℂ) i‖
        = f ‖(Pi.single k₁ c : Fin n → ℂ) i‖
          + f ‖(Pi.single k₂ d : Fin n → ℂ) i‖ := by
      intro i
      by_cases h1 : i = k₁
      · subst h1
        simp [Pi.single_eq_same, Pi.single_eq_of_ne hk, hf0]
      · by_cases h2 : i = k₂
        · subst h2
          simp [Pi.single_eq_same, Pi.single_eq_of_ne h1, hf0]
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, hf0]
    rw [Finset.sum_congr rfl fun i _ => hsplit' i, Finset.sum_add_distrib,
      hsing k₁ c, hsing k₂ d]
  have hin : (s • (Pi.single j 1 : Fin n → ℂ))
      = Pi.single j ((s:ℝ) : ℂ) := by
    funext i
    simp only [Pi.smul_apply, Pi.single_apply, Complex.real_smul]
    split_ifs <;> simp
  have hout : B (s • (Pi.single j 1 : Fin n → ℂ))
      = Pi.single k₁ ((Real.sqrt lam * s : ℝ) : ℂ)
        + Pi.single k₂ ((Real.sqrt (1 - lam) * s : ℝ) : ℂ) := by
    rw [map_smul, hcol]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply,
      Complex.real_smul, Complex.ofReal_mul]
    split_ifs <;> ring
  have h := hiso (s • (Pi.single j 1 : Fin n → ℂ))
  rw [hout] at h
  rw [hin] at h
  rw [hpairf, hsing] at h
  rw [Complex.norm_real, Complex.norm_real, Complex.norm_real] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_of_nonneg hs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs)] at h
  exact h

/-! ## 20. ONE GENERIC ROTATION FORCES BORN: the density glue is
formalized — no cited facts remain in this chain

Pass 4 (§19) proved that a dense family of splitter transmittances
forces the Born function, and cited as classical the fact that ONE
irrational-angle rotation supplies such a family.  That citation is
now a theorem.  `cos_sq_orbit_dense`: for θ/π irrational, the
squared cosines {cos²(kθ) : k ∈ ℕ} are dense in (0,1) — via
`AddSubgroup.dense_or_cyclic` applied to ℤθ + ℤπ (cyclic would make
θ/π rational), continuity of cos², and the π-periodicity identity
cos²(x + nπ) = cos²(x).  `rotation_block_iterate`: iterating a
lossless step whose (k₁,k₂)-block is rotation by θ gives rotation
by kθ on the same block (angle-addition, by induction; the `module`
tactic closes the vector identity).

`generic_rotation_forces_born` — the assembled end-to-end theorem,
with NO citation anywhere in its proof tree: if a monotone measure
Σ f(‖·‖) (f monotone, f(0) = 0 — nothing else) is lossless under a
single real-linear step containing one rotation block of angle θ
with θ/π irrational, then f(x) = x² f(1).

Physics: ALMOST EVERY interference device — all but a measure-zero
set of angles — forces the Born rule by itself, through its own
iterates.  The rational-angle exceptions are exactly the devices
whose iterates close into a finite family.  Remaining wall (the
honest residue of Orlicz–Lamperti): a single mixing step of
arbitrary non-rotation form, and the rational-angle rotations other
than the 50/50 case of §18 — for these only the two-parameter probe
equations are available, and their functional-equation analysis is
open. -/

/-- The f-measure of a single-coordinate state. -/
theorem measure_single_sum (f : ℝ → ℝ) (hf0 : f 0 = 0) {n : ℕ}
    (e : Fin n) (z : ℂ) :
    ∑ i, f ‖(Pi.single e z : Fin n → ℂ) i‖ = f ‖z‖ := by
  rw [Finset.sum_eq_single e]
  · rw [Pi.single_eq_same]
  · intro i _ hne
    rw [Pi.single_eq_of_ne hne, norm_zero, hf0]
  · intro hmem
    exact absurd (Finset.mem_univ e) hmem

/-- The f-measure of a two-coordinate state. -/
theorem measure_pair_sum (f : ℝ → ℝ) (hf0 : f 0 = 0) {n : ℕ}
    {k₁ k₂ : Fin n} (hk : k₁ ≠ k₂) (c d : ℂ) :
    ∑ i, f ‖(Pi.single k₁ c + Pi.single k₂ d : Fin n → ℂ) i‖
      = f ‖c‖ + f ‖d‖ := by
  have hsplit' : ∀ i : Fin n,
      f ‖(Pi.single k₁ c + Pi.single k₂ d : Fin n → ℂ) i‖
      = f ‖(Pi.single k₁ c : Fin n → ℂ) i‖
        + f ‖(Pi.single k₂ d : Fin n → ℂ) i‖ := by
    intro i
    by_cases h1 : i = k₁
    · subst h1
      simp [Pi.single_eq_same, Pi.single_eq_of_ne hk, hf0]
    · by_cases h2 : i = k₂
      · subst h2
        simp [Pi.single_eq_same, Pi.single_eq_of_ne h1, hf0]
      · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, hf0]
  rw [Finset.sum_congr rfl fun i _ => hsplit' i, Finset.sum_add_distrib,
    measure_single_sum f hf0 k₁ c, measure_single_sum f hf0 k₂ d]

/-- The subgroup ℤθ + ℤπ of ℝ. -/
def thetaPiSubgroup (θ : ℝ) : AddSubgroup ℝ where
  carrier := {x : ℝ | ∃ m k : ℤ, x = m * θ + k * Real.pi}
  zero_mem' := ⟨0, 0, by push_cast; ring⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨m1, k1, rfl⟩ := ha
    obtain ⟨m2, k2, rfl⟩ := hb
    exact ⟨m1 + m2, k1 + k2, by push_cast; ring⟩
  neg_mem' := by
    intro a ha
    obtain ⟨m, k, rfl⟩ := ha
    exact ⟨-m, -k, by push_cast; ring⟩

/-- ORBIT DENSITY: for θ/π irrational, the squared cosines of the
rotation orbit {cos²(kθ) : k ∈ ℕ} are dense in (0,1). -/
theorem cos_sq_orbit_dense (θ : ℝ) (hirr : Irrational (θ / Real.pi)) :
    ∀ u v : ℝ, 0 < u → u < v → v < 1 →
      ∃ lam, lam ∈ {l : ℝ | ∃ k : ℕ, l = Real.cos ((k:ℝ) * θ) ^ 2}
        ∧ u < lam ∧ lam < v := by
  intro u v hu huv hv
  -- the subgroup ℤθ + ℤπ is dense (not cyclic, by irrationality)
  have hdense : Dense ((thetaPiSubgroup θ : AddSubgroup ℝ) : Set ℝ) := by
    rcases (thetaPiSubgroup θ).dense_or_cyclic with h | ⟨a, ha⟩
    · exact h
    · exfalso
      have hθS : θ ∈ thetaPiSubgroup θ := ⟨1, 0, by push_cast; ring⟩
      have hπS : Real.pi ∈ thetaPiSubgroup θ := ⟨0, 1, by push_cast; ring⟩
      rw [ha, AddSubgroup.mem_closure_singleton] at hθS hπS
      obtain ⟨m, hm⟩ := hθS
      obtain ⟨n, hn⟩ := hπS
      rw [zsmul_eq_mul] at hm hn
      have hπ0 : Real.pi ≠ 0 := Real.pi_ne_zero
      have hn0 : (n:ℝ) ≠ 0 := by
        intro h
        rw [h, zero_mul] at hn
        exact hπ0 hn.symm
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, mul_zero] at hn
        exact hπ0 hn.symm
      apply hirr
      refine ⟨(m : ℚ)/(n : ℚ), ?_⟩
      rw [← hm, ← hn]
      push_cast
      rw [mul_div_mul_right _ _ ha0]
  -- the target set of angles is open and nonempty
  have hcont : Continuous (fun w : ℝ => Real.cos w ^ 2) :=
    Real.continuous_cos.pow 2
  have hUopen : IsOpen ((fun w : ℝ => Real.cos w ^ 2) ⁻¹' Set.Ioo u v) :=
    hcont.isOpen_preimage _ isOpen_Ioo
  have hUne : ((fun w : ℝ => Real.cos w ^ 2) ⁻¹' Set.Ioo u v).Nonempty := by
    refine ⟨Real.arccos (Real.sqrt ((u+v)/2)), ?_⟩
    have hmid0 : (0:ℝ) ≤ (u+v)/2 := by linarith
    have hmid1 : (u+v)/2 ≤ 1 := by linarith
    have hs0 : (-1:ℝ) ≤ Real.sqrt ((u+v)/2) :=
      le_trans (by norm_num) (Real.sqrt_nonneg _)
    have hs1 : Real.sqrt ((u+v)/2) ≤ 1 := Real.sqrt_le_one.mpr hmid1
    show Real.cos (Real.arccos (Real.sqrt ((u+v)/2))) ^ 2 ∈ Set.Ioo u v
    rw [Real.cos_arccos hs0 hs1, Real.sq_sqrt hmid0]
    constructor <;> [linarith; linarith]
  obtain ⟨x, hxS, hxU⟩ := hdense.exists_mem_open hUopen hUne
  obtain ⟨m, nn, rfl⟩ := hxS
  have hxU' : Real.cos ((m:ℝ)*θ + (nn:ℝ)*Real.pi) ^ 2 ∈ Set.Ioo u v := hxU
  -- π-periodicity of cos²
  have hper : Real.cos ((m:ℝ)*θ + (nn:ℝ)*Real.pi) ^ 2
      = Real.cos ((m:ℝ)*θ) ^ 2 := by
    rw [Real.cos_add]
    have hsin : Real.sin ((nn:ℝ)*Real.pi) = 0 := Real.sin_int_mul_pi nn
    have hcos2 : Real.cos ((nn:ℝ)*Real.pi) ^ 2 = 1 := by
      have h := Real.sin_sq_add_cos_sq ((nn:ℝ)*Real.pi)
      rw [hsin] at h
      nlinarith [h]
    rw [hsin, mul_zero, sub_zero, mul_pow, hcos2, mul_one]
  rw [hper] at hxU'
  refine ⟨Real.cos ((m:ℝ)*θ) ^ 2, ⟨m.natAbs, ?_⟩, hxU'.1, hxU'.2⟩
  have hcast : ((m.natAbs : ℕ) : ℝ) = |(m:ℝ)| := by
    rw [Int.cast_natAbs, Int.cast_abs]
  rw [hcast]
  rcases abs_cases ((m:ℝ)) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]
  · rw [heq, neg_mul, Real.cos_neg]

/-- Iterating a lossless step whose block at (k₁, k₂) is rotation by
θ produces the rotation by kθ on the same block. -/
theorem rotation_block_iterate {n : ℕ} (θ : ℝ)
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ)) {k₁ k₂ : Fin n} (_hk : k₁ ≠ k₂)
    (hcol1 : B (Pi.single k₁ 1)
      = Pi.single k₁ ((Real.cos θ : ℝ) : ℂ)
        + Pi.single k₂ ((Real.sin θ : ℝ) : ℂ))
    (hcol2 : B (Pi.single k₂ 1)
      = Pi.single k₁ ((-Real.sin θ : ℝ) : ℂ)
        + Pi.single k₂ ((Real.cos θ : ℝ) : ℂ)) :
    ∀ k : ℕ, (⇑B)^[k] (Pi.single k₁ 1)
      = Pi.single k₁ ((Real.cos ((k:ℝ)*θ) : ℝ) : ℂ)
        + Pi.single k₂ ((Real.sin ((k:ℝ)*θ) : ℝ) : ℂ) := by
  have hreal : ∀ (e : Fin n) (r : ℝ),
      (Pi.single e ((r : ℝ) : ℂ) : Fin n → ℂ)
        = r • (Pi.single e 1 : Fin n → ℂ) := by
    intro e r
    funext i
    simp only [Pi.smul_apply, Pi.single_apply, Complex.real_smul]
    split_ifs <;> simp
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul,
      Real.cos_zero, Real.sin_zero, Complex.ofReal_one,
      Complex.ofReal_zero]
    rw [Pi.single_zero, add_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hcos : Real.cos (((k + 1 : ℕ) : ℝ) * θ)
        = Real.cos ((k:ℝ)*θ) * Real.cos θ
          - Real.sin ((k:ℝ)*θ) * Real.sin θ := by
      push_cast
      rw [show ((k:ℝ)+1)*θ = (k:ℝ)*θ + θ by ring, Real.cos_add]
    have hsin : Real.sin (((k + 1 : ℕ) : ℝ) * θ)
        = Real.sin ((k:ℝ)*θ) * Real.cos θ
          + Real.cos ((k:ℝ)*θ) * Real.sin θ := by
      push_cast
      rw [show ((k:ℝ)+1)*θ = (k:ℝ)*θ + θ by ring, Real.sin_add]
    rw [hreal k₁ (Real.cos ((k:ℝ)*θ)), hreal k₂ (Real.sin ((k:ℝ)*θ))]
    rw [map_add, map_smul, map_smul, hcol1, hcol2]
    rw [hreal k₁ (Real.cos θ), hreal k₂ (Real.sin θ),
      hreal k₁ (-Real.sin θ), hreal k₂ (Real.cos θ)]
    rw [hreal k₁ (Real.cos (((k + 1 : ℕ) : ℝ) * θ)),
      hreal k₂ (Real.sin (((k + 1 : ℕ) : ℝ) * θ))]
    rw [hcos, hsin]
    module

/-- ONE GENERIC ROTATION FORCES BORN. -/
theorem generic_rotation_forces_born {n : ℕ} (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (θ : ℝ) (hirr : Irrational (θ / Real.pi))
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, f ‖B x i‖ = ∑ i, f ‖x i‖)
    {k₁ k₂ : Fin n} (hk : k₁ ≠ k₂)
    (hcol1 : B (Pi.single k₁ 1)
      = Pi.single k₁ ((Real.cos θ : ℝ) : ℂ)
        + Pi.single k₂ ((Real.sin θ : ℝ) : ℂ))
    (hcol2 : B (Pi.single k₂ 1)
      = Pi.single k₁ ((-Real.sin θ : ℝ) : ℂ)
        + Pi.single k₂ ((Real.cos θ : ℝ) : ℂ)) :
    ∀ x : ℝ, 0 ≤ x → f x = x ^ 2 * f 1 := by
  have hiso_iter : ∀ (k : ℕ) (x : Fin n → ℂ),
      ∑ i, f ‖(⇑B)^[k] x i‖ = ∑ i, f ‖x i‖ := by
    intro k
    induction k with
    | zero =>
      intro x
      rw [Function.iterate_zero_apply]
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hiso, ih]
  have hsmul_iter : ∀ (k : ℕ) (c : ℝ) (x : Fin n → ℂ),
      (⇑B)^[k] (c • x) = c • (⇑B)^[k] x := by
    intro k
    induction k with
    | zero =>
      intro c x
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
    | succ k ih =>
      intro c x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, map_smul]
  have hcolk := rotation_block_iterate θ B hk hcol1 hcol2
  apply splitter_family_forces_born f hf0 hmono
    {l : ℝ | ∃ k : ℕ, l = Real.cos ((k:ℝ) * θ) ^ 2}
    (cos_sq_orbit_dense θ hirr)
  intro lam hlam _ _ s hs
  obtain ⟨k, rfl⟩ := hlam
  have h := hiso_iter k (s • (Pi.single k₁ 1 : Fin n → ℂ))
  rw [hsmul_iter k s _, hcolk k] at h
  have hvec : s • ((Pi.single k₁ ((Real.cos ((k:ℝ)*θ) : ℝ) : ℂ) : Fin n → ℂ)
      + Pi.single k₂ ((Real.sin ((k:ℝ)*θ) : ℝ) : ℂ))
      = Pi.single k₁ ((s * Real.cos ((k:ℝ)*θ) : ℝ) : ℂ)
        + Pi.single k₂ ((s * Real.sin ((k:ℝ)*θ) : ℝ) : ℂ) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply,
      Complex.real_smul]
    split_ifs <;> push_cast <;> ring
  have hin : (s • (Pi.single k₁ 1 : Fin n → ℂ))
      = Pi.single k₁ ((s : ℝ) : ℂ) := by
    funext i
    simp only [Pi.smul_apply, Pi.single_apply, Complex.real_smul]
    split_ifs <;> simp
  rw [hvec] at h
  rw [hin] at h
  rw [measure_pair_sum f hf0 hk, measure_single_sum f hf0] at h
  rw [Complex.norm_real, Complex.norm_real, Complex.norm_real] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_of_nonneg hs] at h
  -- convert |s·cos|, |s·sin| into √λ·s, √(1−λ)·s
  have hsin_sq : 1 - Real.cos ((k:ℝ)*θ) ^ 2 = Real.sin ((k:ℝ)*θ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq ((k:ℝ)*θ)
    linarith
  rw [Real.sqrt_sq_eq_abs, hsin_sq, Real.sqrt_sq_eq_abs]
  calc f (|Real.cos ((k:ℝ)*θ)| * s) + f (|Real.sin ((k:ℝ)*θ)| * s)
      = f |s * Real.cos ((k:ℝ)*θ)| + f |s * Real.sin ((k:ℝ)*θ)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs]
        ring_nf
    _ = f s := h

/-! ## 21. EXCHANGE TRANSPORT: every lopsided mixing block forces
continuity — the rational-angle residue is breached

The remaining wall after §20 was rational-angle rotations (iterates
close into a finite family, so density fails).  This section
attacks them with a new mechanism that needs NO iteration at all:
the two-parameter probes of a single mixing block.

Subtracting the (s,t) and (s,−t) probes cancels the input measure
and leaves the EXCHANGE IDENTITY
  g((u+v)²) − g((u−v)²) = g((κu+v/κ)²) − g((κu−v/κ)²),  κ = σ/c:
the measure's increment over the interval [(u−v)², (u+v)²] equals
its increment over a mirror interval near κ²·(u²).  Taking v → 0
brackets (finite, explicit — no limits), this TRANSPORTS JUMPS: a
jump of size J at w is copied, in full, to κ²w (`jump_transport`).
When the block is lopsided (c² ≠ σ²), κ² < 1 in one of the two
directions, and iterating the transport lays infinitely many
full-size copies of the jump along the geometric ladder κ²ᵏw —
finitely many of which already exceed the total variation of a
monotone function (`exchange_descent_no_jump`, reusing the sorted-
increments bound).  Order kills the jump, again.

`mixing_block_forces_measure_continuity`: a monotone measure
lossless under ONE real-linear step containing a rotation-form
block with cσ ≠ 0, c² ≠ σ² — ANY angle, rational or irrational, no
normalization of the block required — has no jumps anywhere.

Status of the wall after this section: balanced blocks force Born
(§18); irrational-angle blocks force Born (§20); EVERY other
mixing block forces continuity (this section).  The remaining
residue is exactly: continuous monotone g under the finite
per-scale constraint family of one rational-angle block.  In angle
variables the full constraint says K_y(φ) := g(y cos²φ)+g(y sin²φ)
is θ-periodic for every scale y; the registered attack is harmonic:
the Mellin symbols Ψ_s(φ) = cos²ˢφ + sin²ˢφ have Fourier
coefficients with Γ-function closed forms that vanish jointly only
at s ∈ {0, 1}, which would pin g linear — the coefficient
nonvanishing is the open lemma. -/

/-- JUMP TRANSPORT: the exchange identity copies a jump at w, in
full, to κ²·w. -/
theorem jump_transport (g : ℝ → ℝ)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hexch : ∀ u v : ℝ, g ((u + v)^2) - g ((u - v)^2)
      = g ((κ*u + v/κ)^2) - g ((κ*u - v/κ)^2))
    (w J : ℝ) (hw : 0 < w) (hJ : 0 < J)
    (hjump : ∀ p q : ℝ, 0 ≤ p → p < w → w < q → J ≤ g q - g p) :
    ∀ p q : ℝ, 0 ≤ p → p < κ^2 * w → κ^2 * w < q → J ≤ g q - g p := by
  intro a b ha haw hwb
  have hκ2 : 0 < κ^2 := by positivity
  set W : ℝ := Real.sqrt w with hWdef
  have hWpos : 0 < W := Real.sqrt_pos.mpr hw
  have hW2 : W^2 = w := Real.sq_sqrt (le_of_lt hw)
  -- the probe width
  set v : ℝ := min (min (W/2) 1)
    (min ((b - κ^2*w)/(1/κ^2 + 2*W)) ((κ^2*w - a)/(2*W))) with hvdef
  have hden1 : 0 < 1/κ^2 + 2*W := by positivity
  have hvpos : 0 < v := by
    apply lt_min (lt_min (by positivity) one_pos)
    apply lt_min
    · apply div_pos (by linarith) hden1
    · apply div_pos (by linarith) (by positivity)
  have hvW : v ≤ W/2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hv1 : v ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hvb : v ≤ (b - κ^2*w)/(1/κ^2 + 2*W) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hva : v ≤ (κ^2*w - a)/(2*W) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  -- source bracket around w
  have hsrc1 : (W - v)^2 < w := by nlinarith
  have hsrc2 : w < (W + v)^2 := by nlinarith
  have hsrc := hjump ((W - v)^2) ((W + v)^2) (sq_nonneg _) hsrc1 hsrc2
  -- the exchange
  have hex := hexch W v
  -- expand the mirror endpoints
  have hq_exp : (κ*W + v/κ)^2 = κ^2*w + v^2/κ^2 + 2*v*W := by
    have h1 : (κ*W + v/κ)^2 = κ^2*W^2 + 2*W*v*(κ/κ) + v^2/κ^2 := by
      field_simp
      ring
    rw [h1, hW2, div_self hκ]
    ring
  have hp_exp : (κ*W - v/κ)^2 = κ^2*w + v^2/κ^2 - 2*v*W := by
    have h1 : (κ*W - v/κ)^2 = κ^2*W^2 - 2*W*v*(κ/κ) + v^2/κ^2 := by
      field_simp
      ring
    rw [h1, hW2, div_self hκ]
    ring
  -- mirror lies inside (a, b)
  have hqb : (κ*W + v/κ)^2 ≤ b := by
    rw [hq_exp]
    have hv2 : v^2/κ^2 ≤ v * (1/κ^2) := by
      have hvv : v^2 ≤ v := by nlinarith
      rw [div_le_iff₀ hκ2]
      calc v^2 ≤ v := hvv
        _ = v * (1/κ^2) * κ^2 := by field_simp
    have hkey : v * (1/κ^2 + 2*W) ≤ b - κ^2*w := by
      calc v * (1/κ^2 + 2*W)
          ≤ ((b - κ^2*w)/(1/κ^2 + 2*W)) * (1/κ^2 + 2*W) :=
            mul_le_mul_of_nonneg_right hvb (le_of_lt hden1)
        _ = b - κ^2*w := by field_simp
    nlinarith
  have hap : a ≤ (κ*W - v/κ)^2 := by
    rw [hp_exp]
    have hkey : v * (2*W) ≤ κ^2*w - a := by
      calc v * (2*W)
          ≤ ((κ^2*w - a)/(2*W)) * (2*W) :=
            mul_le_mul_of_nonneg_right hva (by positivity)
        _ = κ^2*w - a := by field_simp
    nlinarith [sq_nonneg v, hκ2, div_nonneg (sq_nonneg v) (le_of_lt hκ2)]
  -- assemble
  have h1 : g a ≤ g ((κ*W - v/κ)^2) := hmono _ _ ha hap
  have h2 : g ((κ*W + v/κ)^2) ≤ g b :=
    hmono _ _ (sq_nonneg _) hqb
  linarith

/-- EXCHANGE DESCENT: an exchange identity with contraction ratio
κ² < 1 forbids jumps — each ratio application copies a jump one
contraction step down, and finitely many disjoint copies exceed the
total variation. -/
theorem exchange_descent_no_jump (g : ℝ → ℝ)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b)
    (κ : ℝ) (hκ0 : κ ≠ 0) (hκ1 : κ^2 < 1)
    (hexch : ∀ u v : ℝ, g ((u + v)^2) - g ((u - v)^2)
      = g ((κ*u + v/κ)^2) - g ((κ*u - v/κ)^2)) :
    ∀ y : ℝ, 0 < y → ∀ ε : ℝ, 0 < ε →
      ∃ p q : ℝ, 0 ≤ p ∧ p < y ∧ y < q ∧ g q - g p < ε := by
  intro y hy ε hε
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ p q, 0 ≤ p → p < y → y < q → ε ≤ g q - g p
  have hκ2 : 0 < κ^2 := by positivity
  -- transport the jump down the geometric ladder
  have htrans : ∀ N : ℕ, ∀ p q : ℝ,
      0 ≤ p → p < (κ^2)^N * y → (κ^2)^N * y < q → ε ≤ g q - g p := by
    intro N
    induction N with
    | zero =>
      intro p q hp h1 h2
      rw [pow_zero, one_mul] at h1 h2
      exact hcon p q hp h1 h2
    | succ N ih =>
      intro p q hp h1 h2
      have hw : 0 < (κ^2)^N * y := by positivity
      have hpow : (κ^2)^(N+1) * y = κ^2 * ((κ^2)^N * y) := by ring
      rw [hpow] at h1 h2
      exact jump_transport g hmono κ hκ0 hexch ((κ^2)^N * y) ε hw hε
        ih p q hp h1 h2
  -- the counting contradiction
  set τ : ℝ := κ^2 with hτdef
  have hτ0 : 0 < τ := hκ2
  have hτ1 : τ < 1 := hκ1
  set m : ℝ := (1 + τ)/2 with hmdef
  set M : ℝ := (1 + 1/τ)/2 with hMdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  have hm1 : m < 1 := by rw [hmdef]; linarith
  have hM1 : 1 < M := by
    rw [hMdef]
    have : 1 < 1/τ := by
      rw [lt_div_iff₀ hτ0]
      linarith
    linarith
  have hMτ : M * τ = m := by
    rw [hMdef, hmdef]
    field_simp
    ring
  obtain ⟨N, hN⟩ := exists_nat_gt ((g (M*y) - g 0)/ε)
  have hNε : g (M*y) - g 0 < (N:ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hN
    linarith
  have hsum_lo : (N:ℝ) * ε ≤
      ∑ i ∈ Finset.range N,
        (g (M * τ^(N-1-i) * y) - g (m * τ^(N-1-i) * y)) := by
    calc (N:ℝ) * ε = ∑ _i ∈ Finset.range N, ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          have hx : 0 < τ^(N-1-i) * y := by positivity
          have h1 : m * τ^(N-1-i) * y < τ^(N-1-i) * y := by nlinarith
          have h2 : τ^(N-1-i) * y < M * τ^(N-1-i) * y := by nlinarith
          have h := htrans (N-1-i) (m * τ^(N-1-i) * y)
            (M * τ^(N-1-i) * y) (by positivity)
            (by rw [show (κ^2)^(N-1-i) * y = τ^(N-1-i) * y from rfl]; exact h1)
            (by rw [show (κ^2)^(N-1-i) * y = τ^(N-1-i) * y from rfl]; exact h2)
          exact h
  have hsum_hi : ∑ i ∈ Finset.range N,
      (g (M * τ^(N-1-i) * y) - g (m * τ^(N-1-i) * y)) ≤ g (M*y) - g 0 := by
    apply sum_sorted_increments_le g hmono N
      (fun i => m * τ^(N-1-i) * y) (fun i => M * τ^(N-1-i) * y) (M*y)
    · intro i _
      positivity
    · intro i _
      have : 0 < τ^(N-1-i) * y := by positivity
      nlinarith
    · intro i j hij hj
      have hττ : τ^((N-1-i)-(N-1-j)) ≤ τ :=
        pow_le_of_le_one (le_of_lt hτ0) (le_of_lt hτ1) (by omega)
      have hpow2 : τ^(N-1-i) = τ^(N-1-j) * τ^((N-1-i)-(N-1-j)) := by
        rw [← pow_add]
        congr 1
        omega
      have hM0 : (0:ℝ) < M := lt_trans one_pos hM1
      have hMle : M * τ^(N-1-i) ≤ m * τ^(N-1-j) := by
        rw [hpow2]
        calc M * (τ^(N-1-j) * τ^((N-1-i)-(N-1-j)))
            ≤ M * (τ^(N-1-j) * τ) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hM0)
              exact mul_le_mul_of_nonneg_left hττ
                (le_of_lt (pow_pos hτ0 _))
          _ = (M * τ) * τ^(N-1-j) := by ring
          _ = m * τ^(N-1-j) := by rw [hMτ]
      have : M * τ^(N-1-i) * y ≤ m * τ^(N-1-j) * y :=
        mul_le_mul_of_nonneg_right hMle (le_of_lt hy)
      linarith
    · intro i _
      have hτpow : τ^(N-1-i) ≤ 1 :=
        pow_le_one₀ (le_of_lt hτ0) (le_of_lt hτ1)
      have : M * τ^(N-1-i) ≤ M * 1 := by
        apply mul_le_mul_of_nonneg_left hτpow
        linarith
      nlinarith
    · positivity
  linarith

/-- ANY LOPSIDED MIXING BLOCK FORCES CONTINUITY: a monotone measure
lossless under one real-linear step containing a rotation-form block
with c·σ ≠ 0 and c² ≠ σ² has no jumps.  Any angle — rational or
irrational, balanced excluded only because tan²θ = 1 gives no
contraction (and the balanced case is fully solved separately). -/
theorem mixing_block_forces_measure_continuity {n : ℕ} (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, f ‖B x i‖ = ∑ i, f ‖x i‖)
    {k₁ k₂ : Fin n} (hk : k₁ ≠ k₂) (c σ : ℝ)
    (hc : c ≠ 0) (hσ : σ ≠ 0) (hcσ : c^2 ≠ σ^2)
    (hcol1 : B (Pi.single k₁ 1)
      = Pi.single k₁ ((c : ℝ) : ℂ) + Pi.single k₂ ((σ : ℝ) : ℂ))
    (hcol2 : B (Pi.single k₂ 1)
      = Pi.single k₁ ((-σ : ℝ) : ℂ) + Pi.single k₂ ((c : ℝ) : ℂ)) :
    ∀ y : ℝ, 0 < y → ∀ ε : ℝ, 0 < ε →
      ∃ a b : ℝ, 0 ≤ a ∧ a < y ∧ y < b ∧ f b - f a < ε := by
  set g : ℝ → ℝ := fun x => f (Real.sqrt x) with hgdef
  have hmonog : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b := by
    intro a b _ hab
    exact hmono _ _ (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt hab)
  -- the probe identity in g-form
  have hreal : ∀ (e : Fin n) (r : ℝ),
      (Pi.single e ((r : ℝ) : ℂ) : Fin n → ℂ)
        = r • (Pi.single e 1 : Fin n → ℂ) := by
    intro e r
    funext i
    simp only [Pi.smul_apply, Pi.single_apply, Complex.real_smul]
    split_ifs <;> simp
  have hgz : ∀ z : ℝ, g (z^2) = f |z| := by
    intro z
    show f (Real.sqrt (z^2)) = f |z|
    rw [Real.sqrt_sq_eq_abs]
  have hE : ∀ s t : ℝ,
      g ((c*s - σ*t)^2) + g ((σ*s + c*t)^2) = g (s^2) + g (t^2) := by
    intro s t
    have hBx : B (Pi.single k₁ ((s : ℝ) : ℂ) + Pi.single k₂ ((t : ℝ) : ℂ))
        = Pi.single k₁ ((c*s - σ*t : ℝ) : ℂ)
          + Pi.single k₂ ((σ*s + c*t : ℝ) : ℂ) := by
      rw [hreal k₁ s, hreal k₂ t, map_add, map_smul, map_smul,
        hcol1, hcol2]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply,
        Complex.real_smul]
      split_ifs <;> push_cast <;> ring
    have h := hiso (Pi.single k₁ ((s : ℝ) : ℂ) + Pi.single k₂ ((t : ℝ) : ℂ))
    rw [hBx, measure_pair_sum f hf0 hk, measure_pair_sum f hf0 hk] at h
    rw [Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Complex.norm_real] at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs] at h
    rw [hgz, hgz, hgz, hgz]
    exact h
  -- the exchange identity, for a general column pair (c', σ')
  have hexch_gen : ∀ c' σ' : ℝ, c' ≠ 0 → σ' ≠ 0 →
      (∀ s t : ℝ, g ((c'*s - σ'*t)^2) + g ((σ'*s + c'*t)^2)
        = g (s^2) + g (t^2)) →
      ∀ u v : ℝ, g ((u + v)^2) - g ((u - v)^2)
        = g (((σ'/c')*u + v/(σ'/c'))^2)
          - g (((σ'/c')*u - v/(σ'/c'))^2) := by
    intro c' σ' hc' hσ' hE' u v
    have h1 := hE' (u/c') (-(v/σ'))
    have h2 := hE' (u/c') (v/σ')
    have e1 : c'*(u/c') - σ'*(-(v/σ')) = u + v := by
      field_simp <;> ring
    have e2 : σ'*(u/c') + c'*(-(v/σ')) = (σ'/c')*u - v/(σ'/c') := by
      field_simp <;> ring
    have e3 : c'*(u/c') - σ'*(v/σ') = u - v := by
      field_simp <;> ring
    have e4 : σ'*(u/c') + c'*(v/σ') = (σ'/c')*u + v/(σ'/c') := by
      field_simp <;> ring
    rw [e1, e2] at h1
    rw [e3, e4] at h2
    have e5 : (-(v/σ'))^2 = (v/σ')^2 := by ring
    rw [e5] at h1
    linarith
  -- the swapped probe identity
  have hE' : ∀ s t : ℝ,
      g ((σ*s - c*t)^2) + g ((c*s + σ*t)^2) = g (s^2) + g (t^2) := by
    intro s t
    have h := hE s (-t)
    have e1 : (c*s - σ*(-t))^2 = (c*s + σ*t)^2 := by ring
    have e2 : (σ*s + c*(-t))^2 = (σ*s - c*t)^2 := by ring
    have e3 : (-t)^2 = t^2 := by ring
    rw [e1, e2, e3] at h
    linarith
  -- no-jump in g, choosing the contracting direction
  have hgcont : ∀ y : ℝ, 0 < y → ∀ ε : ℝ, 0 < ε →
      ∃ p q : ℝ, 0 ≤ p ∧ p < y ∧ y < q ∧ g q - g p < ε := by
    rcases lt_or_gt_of_ne hcσ with hlt | hgt
    · -- c² < σ²: contract with κ = c/σ
      have hκ0 : c/σ ≠ 0 := div_ne_zero hc hσ
      have hκ1 : (c/σ)^2 < 1 := by
        rw [div_pow, div_lt_one (by positivity)]
        exact hlt
      exact exchange_descent_no_jump g hmonog (c/σ) hκ0 hκ1
        (hexch_gen σ c hσ hc hE')
    · -- σ² < c²: contract with κ = σ/c
      have hκ0 : σ/c ≠ 0 := div_ne_zero hσ hc
      have hκ1 : (σ/c)^2 < 1 := by
        rw [div_pow, div_lt_one (by positivity)]
        exact hgt
      exact exchange_descent_no_jump g hmonog (σ/c) hκ0 hκ1
        (hexch_gen c σ hc hσ hE)
  -- convert back to f
  intro y hy ε hε
  obtain ⟨p, q, hp0, hpy, hyq, hpq⟩ := hgcont (y^2) (by positivity) ε hε
  refine ⟨Real.sqrt p, Real.sqrt q, Real.sqrt_nonneg p, ?_, ?_, ?_⟩
  · have := Real.sqrt_lt_sqrt hp0 hpy
    rwa [Real.sqrt_sq (le_of_lt hy)] at this
  · have := Real.sqrt_lt_sqrt (sq_nonneg y) hyq
    rwa [Real.sqrt_sq (le_of_lt hy)] at this
  · exact hpq

/-! ## 22. STABILITY: approximate losslessness quantitatively bounds
Born deviation — the reconstruction becomes an experimental inequality

Every theorem so far assumed EXACT losslessness — an idealization no
laboratory meets.  This section makes the reconstruction robust:
if the balanced-splitter losslessness holds only to precision δ
(each probe's measure balance off by at most δ), the monotone
measure is uniformly within (4/3)·δ of an EXACT Born function.

Mechanism: Hyers' geometric sequence f(2ⁿx)/4ⁿ is Cauchy with
geometric increments controlled by the approximate doubling law;
its limit L satisfies the EXACT quadratic functional equation and
inherits monotonicity — and then §18's monotone rigidity (not
regularity, which we never have) classifies L as x²·L(1).  The
telescoping distance bound gives |f − L| ≤ δ'/3.

Physics: FINITE-PRECISION INTERFERENCE DATA BOUNDS BORN-RULE
DEVIATIONS.  A laboratory that certifies measure balance to δ
across one balanced interferometer's probe family certifies the
Born weighting itself to (4/3)·δ — in the same spirit as the
Sinha-type triple-slit bounds on the Sorkin parameter, but for the
measure exponent/function rather than third-order interference.
This is the experimentally usable form of the no-deformation no-go:
Born has no monotone deformation, and near-Born requires
near-losslessness, quantitatively. -/

open Filter Topology

/-- STABILITY OF THE BORN FUNCTION: a monotone approximate solution
of the quadratic functional equation is uniformly δ/3-close to an
exact Born function.  Hyers' geometric sequence provides the limit;
monotone rigidity (§18) classifies it — no regularity assumed. -/
theorem monotone_quadratic_stability (f : ℝ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (hquad : ∀ s t : ℝ, 0 ≤ t → t ≤ s →
      |f (s + t) + f (s - t) - 2 * f s - 2 * f t| ≤ δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, 0 ≤ x → |f x - c * x^2| ≤ δ / 3 := by
  have hdouble : ∀ s : ℝ, 0 ≤ s → |f (2*s) - 4 * f s| ≤ δ := by
    intro s hs
    have h := hquad s s hs le_rfl
    rw [show s + s = 2*s by ring, sub_self, hf0] at h
    rw [show f (2*s) - 4*f s = f (2*s) + 0 - 2*f s - 2*f s by ring]
    exact h
  set q : ℝ → ℕ → ℝ := fun x n => f (2^n * max x 0) / 4^n with hqdef
  have hq_eq : ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ, q x n = f (2^n * x) / 4^n := by
    intro x hx n
    rw [hqdef]
    simp [max_eq_left hx]
  have hstep : ∀ x : ℝ, ∀ n : ℕ,
      dist (q x n) (q x (n+1)) ≤ (δ/4) * (1/4)^n := by
    intro x n
    have hy : (0:ℝ) ≤ max x 0 := le_max_right x 0
    have hyn : (0:ℝ) ≤ 2^n * max x 0 := by positivity
    have hd := hdouble (2^n * max x 0) hyn
    rw [Real.dist_eq]
    have hval : q x n - q x (n+1)
        = -(f (2*(2^n * max x 0)) - 4 * f (2^n * max x 0)) / 4^(n+1) := by
      rw [hqdef]
      simp only []
      rw [show (2:ℝ)^(n+1) * max x 0 = 2*(2^n * max x 0) by ring]
      field_simp <;> ring
    rw [hval, abs_div, abs_neg]
    have h4 : |(4:ℝ)^(n+1)| = 4^(n+1) := abs_of_pos (by positivity)
    rw [h4]
    have hle : |f (2*(2^n * max x 0)) - 4 * f (2^n * max x 0)| / 4^(n+1)
        ≤ δ / 4^(n+1) :=
      div_le_div_of_nonneg_right hd (by positivity)
    calc |f (2*(2^n * max x 0)) - 4 * f (2^n * max x 0)| / 4^(n+1)
        ≤ δ / 4^(n+1) := hle
      _ = (δ/4) * (1/4)^n := by
          rw [pow_succ, one_div_pow]
          field_simp <;> ring
  have hcauchy : ∀ x : ℝ, CauchySeq (q x) := fun x =>
    cauchySeq_of_le_geometric (1/4) (δ/4) (by norm_num) (hstep x)
  choose L hL using fun x : ℝ => cauchySeq_tendsto_of_complete (hcauchy x)
  -- distance to the limit
  have hdist : ∀ x : ℝ, 0 ≤ x → |f x - L x| ≤ δ / 3 := by
    intro x hx
    have h := dist_le_of_le_geometric_of_tendsto₀ (1/4) (δ/4)
      (by norm_num) (hstep x) (hL x)
    have hq0 : q x 0 = f x := by
      rw [hq_eq x hx 0]
      simp
    rw [hq0, Real.dist_eq] at h
    calc |f x - L x| ≤ (δ/4) / (1 - 1/4) := h
      _ = δ / 3 := by ring
  -- limit is monotone on the cone
  have hLmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → L a ≤ L b := by
    intro a b ha hab
    apply le_of_tendsto_of_tendsto' (hL a) (hL b)
    intro n
    rw [hq_eq a ha n, hq_eq b (le_trans ha hab) n]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply hmono _ _ (by positivity)
    have : (0:ℝ) < 2^n := by positivity
    nlinarith
  -- limit vanishes at 0
  have hL0 : L 0 = 0 := by
    have h0 : ∀ n : ℕ, q 0 n = 0 := by
      intro n
      rw [hq_eq 0 le_rfl n, mul_zero, hf0, zero_div]
    have : Tendsto (q 0) atTop (𝓝 0) := by
      have hfun : q 0 = fun _ => (0:ℝ) := funext h0
      rw [hfun]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hL 0) this
  -- limit satisfies the exact quadratic equation on the cone
  have hLquad : ∀ s t : ℝ, 0 ≤ t → t ≤ s →
      L (s + t) + L (s - t) = 2 * L s + 2 * L t := by
    intro s t ht hts
    have hs : 0 ≤ s := le_trans ht hts
    have hcombo : Tendsto
        (fun n => q (s+t) n + q (s-t) n - 2 * q s n - 2 * q t n)
        atTop (𝓝 (L (s+t) + L (s-t) - 2 * L s - 2 * L t)) := by
      exact (((hL (s+t)).add (hL (s-t))).sub
        ((hL s).const_mul 2)).sub ((hL t).const_mul 2)
    have hbound : ∀ n : ℕ,
        |q (s+t) n + q (s-t) n - 2 * q s n - 2 * q t n| ≤ δ * (1/4)^n := by
      intro n
      rw [hq_eq (s+t) (by linarith) n, hq_eq (s-t) (by linarith) n,
        hq_eq s hs n, hq_eq t ht n]
      have h2n : (0:ℝ) < 2^n := by positivity
      have hq' := hquad (2^n * s) (2^n * t) (by positivity)
        (by nlinarith)
      rw [show (2:ℝ)^n * s + 2^n * t = 2^n * (s+t) by ring,
        show (2:ℝ)^n * s - 2^n * t = 2^n * (s-t) by ring] at hq'
      have hval : f (2^n*(s+t))/4^n + f (2^n*(s-t))/4^n
          - 2*(f (2^n*s)/4^n) - 2*(f (2^n*t)/4^n)
          = (f (2^n*(s+t)) + f (2^n*(s-t)) - 2*f (2^n*s) - 2*f (2^n*t))
            / 4^n := by
        field_simp
      rw [hval, abs_div, abs_of_pos (show (0:ℝ) < 4^n by positivity)]
      rw [one_div_pow]
      calc |f (2^n*(s+t)) + f (2^n*(s-t)) - 2*f (2^n*s) - 2*f (2^n*t)|
            / 4^n ≤ δ / 4^n :=
            div_le_div_of_nonneg_right hq' (by positivity)
        _ = δ * (1/4^n) := by ring
    have hzero : Tendsto
        (fun n => q (s+t) n + q (s-t) n - 2 * q s n - 2 * q t n)
        atTop (𝓝 0) := by
      apply squeeze_zero_norm hbound
      have : Tendsto (fun n : ℕ => (1/4:ℝ)^n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using this.const_mul δ
    have := tendsto_nhds_unique hcombo hzero
    linarith
  -- classify the limit by monotone rigidity (§18)
  have hLborn := monotone_quadratic_functional_eq L hL0 hLmono hLquad
  -- c := L 1 is nonnegative
  have hc0 : 0 ≤ L 1 := by
    apply ge_of_tendsto' (hL 1)
    intro n
    rw [hq_eq 1 zero_le_one n]
    apply div_nonneg _ (by positivity)
    have := hmono 0 (2^n * 1) le_rfl (by positivity)
    rw [hf0] at this
    exact this
  refine ⟨L 1, hc0, ?_⟩
  intro x hx
  have h := hLborn x hx
  rw [show L 1 * x^2 = x^2 * L 1 by ring, ← h]
  exact hdist x hx

/-- AN APPROXIMATELY LOSSLESS BEAM SPLITTER PINS THE MEASURE NEAR
BORN: if the balanced-splitter losslessness holds only to precision
δ, the monotone measure is within (4/3)·δ of an exact Born function,
uniformly.  Finite-precision interference data quantitatively bounds
Born-rule deviations. -/
theorem approximate_beam_splitter_near_born (f : ℝ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (hsplit : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      |f ((s + t)/Real.sqrt 2) + f (|s - t|/Real.sqrt 2) - f s - f t|
        ≤ δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, 0 ≤ x → |f x - c * x^2| ≤ (4/3) * δ := by
  have hhalf : ∀ s : ℝ, 0 ≤ s → |2 * f (s/Real.sqrt 2) - f s| ≤ δ := by
    intro s hs
    have h := hsplit s 0 hs le_rfl
    rw [add_zero, sub_zero, abs_of_nonneg hs, hf0] at h
    rw [show 2 * f (s/Real.sqrt 2) - f s
        = f (s/Real.sqrt 2) + f (s/Real.sqrt 2) - f s - 0 by ring]
    exact h
  have hquad4 : ∀ s t : ℝ, 0 ≤ t → t ≤ s →
      |f (s + t) + f (s - t) - 2 * f s - 2 * f t| ≤ 4 * δ := by
    intro s t ht hts
    have hs : 0 ≤ s := le_trans ht hts
    have h1 := hsplit s t hs ht
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)] at h1
    have h2 := hhalf (s + t) (by linarith)
    have h3 := hhalf (s - t) (by linarith)
    have hkey : f (s + t) + f (s - t) - 2 * f s - 2 * f t
        = 2 * (f ((s+t)/Real.sqrt 2) + f ((s-t)/Real.sqrt 2)
            - f s - f t)
          - (2 * f ((s+t)/Real.sqrt 2) - f (s+t))
          - (2 * f ((s-t)/Real.sqrt 2) - f (s-t)) := by
      ring
    rw [hkey]
    calc |2 * (f ((s+t)/Real.sqrt 2) + f ((s-t)/Real.sqrt 2)
            - f s - f t)
          - (2 * f ((s+t)/Real.sqrt 2) - f (s+t))
          - (2 * f ((s-t)/Real.sqrt 2) - f (s-t))|
        ≤ |2 * (f ((s+t)/Real.sqrt 2) + f ((s-t)/Real.sqrt 2)
            - f s - f t)
          - (2 * f ((s+t)/Real.sqrt 2) - f (s+t))|
          + |2 * f ((s-t)/Real.sqrt 2) - f (s-t)| := abs_sub _ _
      _ ≤ (|2 * (f ((s+t)/Real.sqrt 2) + f ((s-t)/Real.sqrt 2)
            - f s - f t)|
          + |2 * f ((s+t)/Real.sqrt 2) - f (s+t)|)
          + |2 * f ((s-t)/Real.sqrt 2) - f (s-t)| := by
          have := abs_sub
            (2 * (f ((s+t)/Real.sqrt 2) + f ((s-t)/Real.sqrt 2)
              - f s - f t))
            (2 * f ((s+t)/Real.sqrt 2) - f (s+t))
          linarith
      _ ≤ (2 * δ + δ) + δ := by
          have ha : |2 * (f ((s+t)/Real.sqrt 2)
              + f ((s-t)/Real.sqrt 2) - f s - f t)| ≤ 2 * δ := by
            rw [abs_mul]
            calc |(2:ℝ)| * |f ((s+t)/Real.sqrt 2)
                + f ((s-t)/Real.sqrt 2) - f s - f t|
                = 2 * |f ((s+t)/Real.sqrt 2)
                    + f ((s-t)/Real.sqrt 2) - f s - f t| := by
                  norm_num
              _ ≤ 2 * δ := by linarith
          linarith
      _ = 4 * δ := by ring
  obtain ⟨c, hc0, hc⟩ := monotone_quadratic_stability f (4*δ)
    (by linarith) hf0 hmono hquad4
  refine ⟨c, hc0, ?_⟩
  intro x hx
  calc |f x - c * x^2| ≤ (4*δ)/3 := hc x hx
    _ = (4/3) * δ := by ring

/-! ## 23. THE WALL FALLS: phase probes force additivity — one
mixing block, any angle, forces Born on all monotone measures

Sections 18–21 fought the Orlicz–Lamperti wall case by case:
balanced blocks (quadratic functional equation), dense transmittance
families (splitting rigidity), irrational angles (orbit density),
lopsided blocks (exchange-transport continuity) — leaving the
rational-angle residue open, with a Mellin attack registered.

The residue never needed any of it.  Every previous section probed
with REAL amplitudes only.  Probing the block with s·e₁ + t·e^{iψ}·e₂
leaves the input measure fixed while the output argument sweeps the
CONTINUOUS interval [(cs−σt)², (cs+σt)²] as ψ varies — so the
pair-sum g(u) + g(S−u) is constant on a continuum of overlapping
intervals whose union chains across the whole level.  The ladder
(explicit steps of size μ* = 4PQ/(P+Q)², finitely many, no limits)
gives EXACT Pythagorean additivity (`phase_interval_additivity`):
no continuity, no monotonicity, no density, no jump-killing.

`complex_mixing_block_forces_born`: a monotone measure Σ f(‖·‖)
(f(0) = 0, nothing else) lossless under one ℂ-linear step containing
a rotation-form mixing block — ANY angle, balanced or lopsided,
rational or irrational, unnormalized — is exactly f(x) = x² f(1).
Monotone Cauchy (§15) is the only place monotonicity enters.

This supersedes the case analysis of §§18–21 for the Born
conclusion (those sections retain independent content: they use
only REAL probes, and their derived-continuity theorems stand
alone).  The physical reading sharpens to its final form: ONE
INTERFERENCE DEVICE PLUS THE FREEDOM TO DIAL A PHASE forces the
Born rule over the entire monotone class.  What remains beyond:
blocks not of rotation form (two arbitrary complex columns). -/

/-- `a ≤ b` from `a² ≤ b²` on nonnegatives. -/
theorem le_of_sq_le_sq'' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a^2 ≤ b^2) : a ≤ b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

set_option maxHeartbeats 1600000 in
/-- PHASE-INTERVAL ADDITIVITY: the complex-phase probe relation of a
single mixing block forces exact Pythagorean additivity of g.  No
continuity, no monotonicity, no density — pure interval chaining. -/
theorem phase_interval_additivity (g : ℝ → ℝ) (hg0 : g 0 = 0)
    (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (hE : ∀ x y w : ℝ, 0 ≤ x → 0 ≤ y → -1 ≤ w → w ≤ 1 →
      g (P*x + Q*y - 2*Real.sqrt (P*Q*x*y) * w)
        + g (Q*x + P*y + 2*Real.sqrt (P*Q*x*y) * w)
      = g x + g y) :
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → g (a + b) = g a + g b := by
  -- overlapping-interval step: G Z μ = G Z ν when the centers are
  -- within the μ-interval's half-width
  have key : ∀ Z : ℝ, 0 < Z → ∀ μ ν : ℝ,
      0 < μ → μ < 1 → 0 ≤ ν → ν ≤ 1 →
      |(P - Q) * (μ - ν)| ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) →
      g (Z*μ) + g (Z*(1-μ)) = g (Z*ν) + g (Z*(1-ν)) := by
    intro Z hZ μ ν hμ0 hμ1 hν0 hν1 hcond
    have h1μ : (0:ℝ) < 1 - μ := by linarith
    have hZμ : (0:ℝ) ≤ Z*μ := by positivity
    have hZμ' : (0:ℝ) ≤ Z*(1-μ) := by positivity
    have hZν : (0:ℝ) ≤ Z*ν := by positivity
    have hZν' : (0:ℝ) ≤ Z*(1-ν) := by nlinarith
    have hs_pos : 0 < Real.sqrt (P*Q*μ*(1-μ)) := by
      apply Real.sqrt_pos.mpr
      positivity
    -- instance at (ν, w = 0)
    have h1 := hE (Z*ν) (Z*(1-ν)) 0 hZν hZν' (by norm_num) (by norm_num)
    rw [mul_zero, sub_zero, add_zero] at h1
    -- instance at (μ, w*) hitting the same point
    set w : ℝ := (P - Q) * (μ - ν) / (2 * Real.sqrt (P*Q*μ*(1-μ)))
      with hwdef
    have hw1 : |w| ≤ 1 := by
      rw [hwdef, abs_div]
      rw [div_le_one (by positivity)]
      calc |(P - Q) * (μ - ν)|
          ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) := hcond
        _ = |2 * Real.sqrt (P*Q*μ*(1-μ))| := by
            rw [abs_of_pos (by positivity)]
    have h2 := hE (Z*μ) (Z*(1-μ)) w hZμ hZμ'
      (neg_le_of_abs_le hw1) (le_of_abs_le hw1)
    have hsq : Real.sqrt (P*Q*(Z*μ)*(Z*(1-μ)))
        = Z * Real.sqrt (P*Q*μ*(1-μ)) := by
      rw [show P*Q*(Z*μ)*(Z*(1-μ)) = Z^2 * (P*Q*μ*(1-μ)) by ring,
        Real.sqrt_mul (sq_nonneg Z), Real.sqrt_sq (le_of_lt hZ)]
    rw [hsq] at h2
    -- cancel the sqrt against w
    have hws : w * (2 * Real.sqrt (P*Q*μ*(1-μ))) = (P - Q) * (μ - ν) := by
      rw [hwdef]
      exact div_mul_cancel₀ _ (by positivity)
    have hprod : 2*(Z*Real.sqrt (P*Q*μ*(1-μ)))*w = Z*((P-Q)*(μ-ν)) := by
      calc 2*(Z*Real.sqrt (P*Q*μ*(1-μ)))*w
          = Z*(w * (2*Real.sqrt (P*Q*μ*(1-μ)))) := by ring
        _ = Z*((P-Q)*(μ-ν)) := by rw [hws]
    have harg1 : P*(Z*μ) + Q*(Z*(1-μ)) - 2*(Z*Real.sqrt (P*Q*μ*(1-μ)))*w
        = P*(Z*ν) + Q*(Z*(1-ν)) := by
      rw [hprod]
      ring
    have harg2 : Q*(Z*μ) + P*(Z*(1-μ)) + 2*(Z*Real.sqrt (P*Q*μ*(1-μ)))*w
        = Q*(Z*ν) + P*(Z*(1-ν)) := by
      rw [hprod]
      ring
    rw [harg1, harg2] at h2
    linarith
  -- the threshold ratio and its algebraic identity
  set mustar : ℝ := 4*P*Q/(P+Q)^2 with hmustar
  have hmu0 : 0 < mustar := by positivity
  have hmu1 : mustar ≤ 1 := by
    rw [hmustar, div_le_one (by positivity)]
    nlinarith [sq_nonneg (P - Q)]
  have hkey_id : (P-Q)^2 * mustar = 4*P*Q*(1-mustar) := by
    rw [hmustar]
    field_simp
    ring
  -- one-step condition for steps of size μ*, valid on [μ*, 1/2]
  have hstep_cond : ∀ μ : ℝ, mustar ≤ μ → μ ≤ 1/2 →
      |P - Q| * mustar ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) := by
    intro μ hμl hμr
    have hμ0 : 0 < μ := lt_of_lt_of_le hmu0 hμl
    have h1μ : (0:ℝ) ≤ 1 - μ := by linarith
    have hmono : mustar * (1 - mustar) ≤ μ * (1 - μ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hμl)
        (by linarith : (0:ℝ) ≤ 1 - μ - mustar)]
    apply le_of_sq_le_sq'' (by positivity) (by positivity)
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ P*Q*μ*(1-μ) by positivity)
    calc (|P-Q| * mustar)^2 = (P-Q)^2 * mustar * mustar := by
          rw [mul_pow, sq_abs]
          ring
      _ = 4*P*Q*(1-mustar) * mustar := by rw [hkey_id]
      _ ≤ 4*(P*Q*μ*(1-μ)) := by
          nlinarith [mul_le_mul_of_nonneg_left hmono
            (show (0:ℝ) ≤ 4*(P*Q) by positivity)]
      _ = (2 * Real.sqrt (P*Q*μ*(1-μ)))^2 := by
          rw [mul_pow, hs]
          ring
  -- the ladder: every μ ≤ 1/2 connects to 0
  have hladder : ∀ Z : ℝ, 0 < Z → ∀ (k : ℕ) (μ : ℝ),
      0 ≤ μ → μ ≤ 1/2 → μ ≤ (k+1 : ℝ) * mustar →
      g (Z*μ) + g (Z*(1-μ)) = g 0 + g Z := by
    intro Z hZ k
    induction k with
    | zero =>
      intro μ hμ0 hμh hμk
      rcases eq_or_lt_of_le hμ0 with h0 | hpos
      · rw [← h0]
        norm_num
      have hμ1 : μ < 1 := by linarith
      have hμle : μ ≤ mustar := by
        have : ((0:ℕ)+1 : ℝ) = 1 := by norm_num
        rw [this, one_mul] at hμk
        exact hμk
      have hcond : |(P - Q) * (μ - 0)| ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) := by
        rw [sub_zero, abs_mul, abs_of_nonneg hμ0]
        have h1μ : (0:ℝ) ≤ 1 - μ := by linarith
        -- (P-Q)² μ ≤ (P-Q)² μ* = 4PQ(1-μ*) ≤ 4PQ(1-μ)
        have hchain : (P-Q)^2 * μ ≤ 4*P*Q*(1-μ) := by
          calc (P-Q)^2 * μ ≤ (P-Q)^2 * mustar :=
                mul_le_mul_of_nonneg_left hμle (sq_nonneg _)
            _ = 4*P*Q*(1-mustar) := hkey_id
            _ ≤ 4*P*Q*(1-μ) := by
                apply mul_le_mul_of_nonneg_left (by linarith)
                positivity
        apply le_of_sq_le_sq'' (by positivity) (by positivity)
        have hs := Real.sq_sqrt (show (0:ℝ) ≤ P*Q*μ*(1-μ) by positivity)
        calc (|P-Q| * μ)^2 = (P-Q)^2 * μ * μ := by
              rw [mul_pow, sq_abs]
              ring
          _ ≤ 4*P*Q*(1-μ) * μ := by
              nlinarith [mul_le_mul_of_nonneg_right hchain hμ0]
          _ = (2 * Real.sqrt (P*Q*μ*(1-μ)))^2 := by
              rw [mul_pow, hs]
              ring
      have h := key Z hZ μ 0 hpos hμ1 le_rfl (by norm_num) hcond
      rw [mul_zero, sub_zero, mul_one] at h
      exact h
    | succ k ih =>
      intro μ hμ0 hμh hμk
      by_cases hcase : μ ≤ (k+1 : ℝ) * mustar
      · exact ih μ hμ0 hμh hcase
      push_neg at hcase
      have hμstar : mustar ≤ μ := by
        have hk1 : (1:ℝ) ≤ (k:ℝ)+1 := by
          have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          linarith
        calc mustar = 1 * mustar := (one_mul _).symm
          _ ≤ ((k:ℝ)+1) * mustar :=
              mul_le_mul_of_nonneg_right hk1 (le_of_lt hmu0)
          _ ≤ μ := le_of_lt hcase
      have hμpos : 0 < μ := lt_of_lt_of_le hmu0 hμstar
      have hμ1 : μ < 1 := by linarith
      set ν : ℝ := μ - mustar with hνdef
      have hν0 : 0 ≤ ν := by rw [hνdef]; linarith
      have hν1 : ν ≤ 1 := by rw [hνdef]; linarith
      have hνh : ν ≤ 1/2 := by rw [hνdef]; linarith
      have hνk : ν ≤ (k+1 : ℝ) * mustar := by
        rw [hνdef]
        have : μ ≤ ((k:ℝ)+1+1) * mustar := by
          convert hμk using 2
          push_cast
          ring
        nlinarith
      have hcond : |(P - Q) * (μ - ν)| ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) := by
        rw [hνdef, show μ - (μ - mustar) = mustar by ring, abs_mul,
          abs_of_pos hmu0]
        exact hstep_cond μ hμstar hμh
      have h1 := key Z hZ μ ν hμpos hμ1 hν0 hν1 hcond
      have h2 := ih ν hν0 hνh hνk
      linarith
  -- conclusion
  have main : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b →
      g (a + b) = g a + g b := by
    intro a b hapos hbpos hab
    have hZ : 0 < a + b := by linarith
    set μ : ℝ := a / (a + b) with hμdef
    have hμ0 : 0 ≤ μ := by positivity
    have hμh : μ ≤ 1/2 := by
      rw [hμdef, div_le_iff₀ hZ]
      linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (μ / mustar)
    have hμk : μ ≤ (k+1 : ℝ) * mustar := by
      rw [div_lt_iff₀ hmu0] at hk
      nlinarith [hmu0]
    have h := hladder (a+b) hZ k μ hμ0 hμh hμk
    rw [hg0, zero_add] at h
    have e1 : (a+b) * μ = a := by
      rw [hμdef]
      field_simp
    have e2 : (a+b) * (1-μ) = b := by
      rw [hμdef]
      field_simp
      ring
    rw [e1, e2] at h
    linarith
  intro a b ha hb
  rcases eq_or_lt_of_le ha with h0 | hapos
  · rw [← h0, zero_add, hg0, zero_add]
  rcases eq_or_lt_of_le hb with h0 | hbpos
  · rw [← h0, add_zero, hg0, add_zero]
  rcases le_total a b with hab | hab
  · exact main a b hapos hbpos hab
  · rw [show a + b = b + a by ring, main b a hbpos hapos hab]
    ring


set_option maxHeartbeats 1600000 in
/-- ANY MIXING BLOCK FORCES BORN: a monotone measure Σ f(‖·‖)
lossless under one ℂ-linear step containing a rotation-form mixing
block — ANY angle, balanced or lopsided, rational or irrational, no
normalization — is exactly f(x) = x² f(1).  The complex-phase probe
continuum feeds `phase_interval_additivity`; monotone Cauchy
finishes.  Supersedes the case analysis of §§18–21. -/
theorem complex_mixing_block_forces_born {n : ℕ} (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (B : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hiso : ∀ x : Fin n → ℂ, ∑ i, f ‖B x i‖ = ∑ i, f ‖x i‖)
    {j₁ j₂ k₁ k₂ : Fin n} (hj : j₁ ≠ j₂) (hk : k₁ ≠ k₂)
    (c σ : ℝ) (hc : c ≠ 0) (hσ : σ ≠ 0)
    (hcol1 : B (Pi.single j₁ 1)
      = Pi.single k₁ ((c : ℝ) : ℂ) + Pi.single k₂ ((σ : ℝ) : ℂ))
    (hcol2 : B (Pi.single j₂ 1)
      = Pi.single k₁ ((-σ : ℝ) : ℂ) + Pi.single k₂ ((c : ℝ) : ℂ)) :
    ∀ x : ℝ, 0 ≤ x → f x = x ^ 2 * f 1 := by
  set g : ℝ → ℝ := fun t => f (Real.sqrt t) with hgdef
  have hg0 : g 0 = 0 := by
    rw [hgdef]
    simp [Real.sqrt_zero, hf0]
  have hgz : ∀ z : ℂ, g (‖z‖^2) = f ‖z‖ := by
    intro z
    rw [hgdef]
    simp only []
    rw [Real.sqrt_sq (norm_nonneg z)]
  have hmonog : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b := by
    intro a b _ hab
    exact hmono _ _ (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt hab)
  -- the probe relation in g-form
  have hE : ∀ x y w : ℝ, 0 ≤ x → 0 ≤ y → -1 ≤ w → w ≤ 1 →
      g (c^2*x + σ^2*y - 2*Real.sqrt (c^2*σ^2*x*y) * w)
        + g (σ^2*x + c^2*y + 2*Real.sqrt (c^2*σ^2*x*y) * w)
      = g x + g y := by
    intro x y w hx hy hw1 hw2
    -- absorb the sign of c*σ into the phase
    set e : ℝ := if 0 ≤ c*σ then w else -w with hedef
    have he1 : -1 ≤ e := by
      rw [hedef]
      split_ifs <;> linarith
    have he2 : e ≤ 1 := by
      rw [hedef]
      split_ifs <;> linarith
    have hesq : (0:ℝ) ≤ 1 - e^2 := by nlinarith
    set z : ℂ := ⟨e, Real.sqrt (1 - e^2)⟩ with hzdef
    have hz_normsq : Complex.normSq z = 1 := by
      rw [hzdef, Complex.normSq_mk]
      rw [show Real.sqrt (1-e^2) * Real.sqrt (1-e^2)
          = Real.sqrt (1-e^2) ^ 2 by ring]
      rw [Real.sq_sqrt hesq]
      ring
    have hz_norm : ‖z‖ = 1 := by
      have := Complex.normSq_eq_norm_sq z
      rw [hz_normsq] at this
      nlinarith [norm_nonneg z]
    set s : ℝ := Real.sqrt x with hsdef
    set t : ℝ := Real.sqrt y with htdef
    have hs2 : s^2 = x := Real.sq_sqrt hx
    have ht2 : t^2 = y := Real.sq_sqrt hy
    have hs0 : 0 ≤ s := Real.sqrt_nonneg x
    have ht0 : 0 ≤ t := Real.sqrt_nonneg y
    -- the probe state and its image
    have hstate : (Pi.single j₁ ((s:ℝ):ℂ)
        + Pi.single j₂ (((t:ℝ):ℂ) * z) : Fin n → ℂ)
        = (s:ℂ) • (Pi.single j₁ 1 : Fin n → ℂ)
          + ((t:ℂ) * z) • (Pi.single j₂ 1 : Fin n → ℂ) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul]
      split_ifs <;> ring
    have hBx : B (Pi.single j₁ ((s:ℝ):ℂ)
        + Pi.single j₂ (((t:ℝ):ℂ) * z))
        = Pi.single k₁ ((s:ℂ)*(c:ℂ) - ((t:ℂ)*z)*(σ:ℂ))
          + Pi.single k₂ ((s:ℂ)*(σ:ℂ) + ((t:ℂ)*z)*(c:ℂ)) := by
      rw [hstate, map_add, map_smul, map_smul, hcol1, hcol2]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul]
      split_ifs <;> push_cast <;> ring
    have h := hiso (Pi.single j₁ ((s:ℝ):ℂ)
      + Pi.single j₂ (((t:ℝ):ℂ) * z))
    rw [hBx, measure_pair_sum f hf0 hk, measure_pair_sum f hf0 hj] at h
    -- norms of the four entries
    have hz_re : z.re = e := rfl
    have hnorm1 : ‖(s:ℂ)*(c:ℂ) - ((t:ℂ)*z)*(σ:ℂ)‖^2
        = c^2*x + σ^2*y - 2*Real.sqrt (c^2*σ^2*x*y) * w := by
      rw [← Complex.normSq_eq_norm_sq]
      have hre : ((s:ℂ)*(c:ℂ) - ((t:ℂ)*z)*(σ:ℂ)).re
          = s*c - t*z.re*σ := by
        simp [Complex.sub_re, Complex.mul_re, Complex.mul_im]
      have him : ((s:ℂ)*(c:ℂ) - ((t:ℂ)*z)*(σ:ℂ)).im
          = -(t*z.im*σ) := by
        simp [Complex.sub_im, Complex.mul_re, Complex.mul_im]
      rw [Complex.normSq_apply, hre, him]
      have hzz : z.re^2 + z.im^2 = 1 := by
        have := hz_normsq
        rw [Complex.normSq_apply] at this
        nlinarith [this]
      have hsqrt : Real.sqrt (c^2*σ^2*x*y) = |c*σ| * (s*t) := by
        rw [show c^2*σ^2*x*y = (c*σ)^2 * (s*t)^2 by
              rw [← hs2, ← ht2]; ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hs0 ht0)]
      rw [hsqrt, hz_re]
      by_cases hcs : 0 ≤ c*σ
      · have habs : |c*σ| = c*σ := abs_of_nonneg hcs
        have hee : e = w := by rw [hedef, if_pos hcs]
        have hwim : w^2 + z.im^2 = 1 := by
          have h := hzz
          rw [hz_re, hee] at h
          exact h
        rw [habs, hee]
        linear_combination c^2 * hs2 + σ^2 * ht2 + σ^2*t^2 * hwim
      · have habs : |c*σ| = -(c*σ) := abs_of_neg (not_le.mp hcs)
        have hee : e = -w := by rw [hedef, if_neg hcs]
        have hwim : w^2 + z.im^2 = 1 := by
          have h := hzz
          rw [hz_re, hee] at h
          linear_combination h
        rw [habs, hee]
        linear_combination c^2 * hs2 + σ^2 * ht2 + σ^2*t^2 * hwim
    have hnorm2 : ‖(s:ℂ)*(σ:ℂ) + ((t:ℂ)*z)*(c:ℂ)‖^2
        = σ^2*x + c^2*y + 2*Real.sqrt (c^2*σ^2*x*y) * w := by
      rw [← Complex.normSq_eq_norm_sq]
      have hre : ((s:ℂ)*(σ:ℂ) + ((t:ℂ)*z)*(c:ℂ)).re
          = s*σ + t*z.re*c := by
        simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
      have him : ((s:ℂ)*(σ:ℂ) + ((t:ℂ)*z)*(c:ℂ)).im
          = t*z.im*c := by
        simp [Complex.add_im, Complex.mul_re, Complex.mul_im]
      rw [Complex.normSq_apply, hre, him]
      have hzz : z.re^2 + z.im^2 = 1 := by
        have := hz_normsq
        rw [Complex.normSq_apply] at this
        nlinarith [this]
      have hsqrt : Real.sqrt (c^2*σ^2*x*y) = |c*σ| * (s*t) := by
        rw [show c^2*σ^2*x*y = (c*σ)^2 * (s*t)^2 by
              rw [← hs2, ← ht2]; ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hs0 ht0)]
      rw [hsqrt, hz_re]
      by_cases hcs : 0 ≤ c*σ
      · have habs : |c*σ| = c*σ := abs_of_nonneg hcs
        have hee : e = w := by rw [hedef, if_pos hcs]
        have hwim : w^2 + z.im^2 = 1 := by
          have h := hzz
          rw [hz_re, hee] at h
          exact h
        rw [habs, hee]
        linear_combination σ^2 * hs2 + c^2 * ht2 + c^2*t^2 * hwim
      · have habs : |c*σ| = -(c*σ) := abs_of_neg (not_le.mp hcs)
        have hee : e = -w := by rw [hedef, if_neg hcs]
        have hwim : w^2 + z.im^2 = 1 := by
          have h := hzz
          rw [hz_re, hee] at h
          linear_combination h
        rw [habs, hee]
        linear_combination σ^2 * hs2 + c^2 * ht2 + c^2*t^2 * hwim
    -- convert to g and finish
    have h1 : f ‖(s:ℂ)*(c:ℂ) - ((t:ℂ)*z)*(σ:ℂ)‖
        = g (c^2*x + σ^2*y - 2*Real.sqrt (c^2*σ^2*x*y) * w) := by
      rw [← hnorm1, hgz]
    have h2 : f ‖(s:ℂ)*(σ:ℂ) + ((t:ℂ)*z)*(c:ℂ)‖
        = g (σ^2*x + c^2*y + 2*Real.sqrt (c^2*σ^2*x*y) * w) := by
      rw [← hnorm2, hgz]
    have h3 : f ‖((s:ℝ):ℂ)‖ = g x := by
      rw [← hgz]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, hs2]
    have h4 : f ‖((t:ℝ):ℂ) * z‖ = g y := by
      rw [← hgz]
      congr 1
      rw [norm_mul, hz_norm, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht0, ht2]
    rw [h1, h2, h3, h4] at h
    exact h
  -- additivity from the phase intervals, then monotone Cauchy
  have hadd := phase_interval_additivity g hg0 (c^2) (σ^2)
    (by positivity) (by positivity) hE
  have hlin := monotone_additive_on_cone_is_linear g hadd hmonog
  intro x hx
  have h := hlin (x^2) (sq_nonneg x)
  rw [hgdef] at h
  simp only [] at h
  rw [Real.sqrt_sq hx, Real.sqrt_one] at h
  exact h

/-! ## 24. THE TERMINAL THEOREM: quantum mechanics from a monotone
notion of probability, lossless time, gauge, and one beam splitter

The endgame assembly of the entire uniqueness leg.  Hypotheses, in
full — and note what is ABSENT: no Hilbert space, no amplitudes, no
power family, no linearity, no complex structure of the dynamics,
no continuity, no divisibility:

  * a monotone measure-function f with f(0) = 0, not identically
    zero (probability is monotone in amplitude, nothing has weight
    before it exists, and something has weight);
  * a dynamics F that is a bare SET-MAP of states — surjective,
    preserving the total measure and pairwise distinguishability
    (lossless time), and commuting with the global quarter-turn
    phase (gauge);
  * ONE lossless beam-splitter event: some set-map S, lossless for
    the same measure, acting on two-coordinate states as a
    rotation-form gate with a dialable input phase (cσ ≠ 0, no
    normalization).

Conclusion: f(x) = x² f(1) with f(1) > 0 — THE BORN RULE — and F
is complex-linear with orthonormal columns — UNITARY QUANTUM
MECHANICS.  Chain: the splitter's phase continuum forces g-additivity
(§23) hence f Born; nontriviality pins f(1) > 0; the derived measure
is ℓ², so Mazur–Ulam (§14) yields real-linearity RETROACTIVELY;
gauge upgrades it to ℂ-linearity (§17); the p = 2 probe machinery
(§9) delivers orthonormal columns.  Everything the textbook assumes
is here a theorem. -/

set_option maxHeartbeats 1600000 in
/-- THE TERMINAL THEOREM: a monotone notion of probability, a
lossless surjective distinguishability-preserving gauge-covariant
dynamics, and ONE lossless beam-splitter event force the Born
measure AND unitary dynamics — measure function, linearity, complex
structure, and unitarity all derived, none assumed. -/
theorem quantum_mechanics_from_a_beam_splitter {n : ℕ} (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b)
    (hnontriv : ∃ x : ℝ, 0 ≤ x ∧ f x ≠ 0)
    (F : (Fin n → ℂ) → (Fin n → ℂ))
    (hsurj : Function.Surjective F)
    (hmeas : ∀ x : Fin n → ℂ, ∑ i, f ‖F x i‖ = ∑ i, f ‖x i‖)
    (hdist : ∀ x y : Fin n → ℂ,
      ∑ i, f ‖F x i - F y i‖ = ∑ i, f ‖x i - y i‖)
    (hphase : ∀ x : Fin n → ℂ, F (Complex.I • x) = Complex.I • F x)
    (S : (Fin n → ℂ) → (Fin n → ℂ))
    (hSiso : ∀ x : Fin n → ℂ, ∑ i, f ‖S x i‖ = ∑ i, f ‖x i‖)
    {j₁ j₂ k₁ k₂ : Fin n} (hj : j₁ ≠ j₂) (hk : k₁ ≠ k₂)
    (c σ : ℝ) (hc : c ≠ 0) (hσ : σ ≠ 0)
    (hact : ∀ a b : ℂ, S (Pi.single j₁ a + Pi.single j₂ b)
      = Pi.single k₁ ((c:ℂ)*a - (σ:ℂ)*b)
        + Pi.single k₂ ((σ:ℂ)*a + (c:ℂ)*b)) :
    (∀ x : ℝ, 0 ≤ x → f x = x^2 * f 1) ∧ 0 < f 1 ∧
    ∃ U : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ),
      (∀ x : Fin n → ℂ, U x = F x) ∧
      ∀ i₁ i₂ : Fin n,
        ∑ i, (starRingEnd ℂ) (U (Pi.single i₁ 1) i)
          * U (Pi.single i₂ 1) i
        = if i₁ = i₂ then 1 else 0 := by
  -- ---------- step 1: the Born function from the splitter ----------
  set g : ℝ → ℝ := fun t => f (Real.sqrt t) with hgdef
  have hg0 : g 0 = 0 := by
    rw [hgdef]
    simp [Real.sqrt_zero, hf0]
  have hgz : ∀ z : ℂ, g (‖z‖^2) = f ‖z‖ := by
    intro z
    rw [hgdef]
    simp only []
    rw [Real.sqrt_sq (norm_nonneg z)]
  have hmonog : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g a ≤ g b := by
    intro a b _ hab
    exact hmono _ _ (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt hab)
  have hE : ∀ x y w : ℝ, 0 ≤ x → 0 ≤ y → -1 ≤ w → w ≤ 1 →
      g (c^2*x + σ^2*y - 2*Real.sqrt (c^2*σ^2*x*y) * w)
        + g (σ^2*x + c^2*y + 2*Real.sqrt (c^2*σ^2*x*y) * w)
      = g x + g y := by
    intro x y w hx hy hw1 hw2
    set e : ℝ := if 0 ≤ c*σ then w else -w with hedef
    have hesq : (0:ℝ) ≤ 1 - e^2 := by
      rw [hedef]
      split_ifs <;> nlinarith
    set z : ℂ := ⟨e, Real.sqrt (1 - e^2)⟩ with hzdef
    have hz_normsq : Complex.normSq z = 1 := by
      rw [hzdef, Complex.normSq_mk]
      rw [show Real.sqrt (1-e^2) * Real.sqrt (1-e^2)
          = Real.sqrt (1-e^2) ^ 2 by ring]
      rw [Real.sq_sqrt hesq]
      ring
    have hz_norm : ‖z‖ = 1 := by
      have := Complex.normSq_eq_norm_sq z
      rw [hz_normsq] at this
      nlinarith [norm_nonneg z]
    set s : ℝ := Real.sqrt x with hsdef
    set t : ℝ := Real.sqrt y with htdef
    have hs2 : s^2 = x := Real.sq_sqrt hx
    have ht2 : t^2 = y := Real.sq_sqrt hy
    have hs0 : 0 ≤ s := Real.sqrt_nonneg x
    have ht0 : 0 ≤ t := Real.sqrt_nonneg y
    have h := hSiso (Pi.single j₁ ((s:ℝ):ℂ)
      + Pi.single j₂ (((t:ℝ):ℂ) * z))
    rw [hact ((s:ℝ):ℂ) (((t:ℝ):ℂ) * z),
      measure_pair_sum f hf0 hk, measure_pair_sum f hf0 hj] at h
    have hz_re : z.re = e := rfl
    have hzz : z.re^2 + z.im^2 = 1 := by
      have := hz_normsq
      rw [Complex.normSq_apply] at this
      nlinarith [this]
    have hsqrt : Real.sqrt (c^2*σ^2*x*y) = |c*σ| * (s*t) := by
      rw [show c^2*σ^2*x*y = (c*σ)^2 * (s*t)^2 by
            rw [← hs2, ← ht2]; ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hs0 ht0)]
    have hnorm1 : ‖(c:ℂ)*((s:ℝ):ℂ) - (σ:ℂ)*(((t:ℝ):ℂ)*z)‖^2
        = c^2*x + σ^2*y - 2*Real.sqrt (c^2*σ^2*x*y) * w := by
      rw [← Complex.normSq_eq_norm_sq]
      have hre : ((c:ℂ)*((s:ℝ):ℂ) - (σ:ℂ)*(((t:ℝ):ℂ)*z)).re
          = c*s - σ*(t*z.re) := by
        simp [Complex.sub_re, Complex.mul_re, Complex.mul_im]
      have him : ((c:ℂ)*((s:ℝ):ℂ) - (σ:ℂ)*(((t:ℝ):ℂ)*z)).im
          = -(σ*(t*z.im)) := by
        simp [Complex.sub_im, Complex.mul_re, Complex.mul_im]
      rw [Complex.normSq_apply, hre, him, hsqrt, hz_re]
      by_cases hcs : 0 ≤ c*σ
      · have habs : |c*σ| = c*σ := abs_of_nonneg hcs
        have hee : e = w := by rw [hedef, if_pos hcs]
        have hwim : w^2 + z.im^2 = 1 := by
          have h' := hzz
          rw [hz_re, hee] at h'
          exact h'
        rw [habs, hee]
        linear_combination c^2 * hs2 + σ^2 * ht2 + σ^2*t^2 * hwim
      · have habs : |c*σ| = -(c*σ) := abs_of_neg (not_le.mp hcs)
        have hee : e = -w := by rw [hedef, if_neg hcs]
        have hwim : w^2 + z.im^2 = 1 := by
          have h' := hzz
          rw [hz_re, hee] at h'
          linear_combination h'
        rw [habs, hee]
        linear_combination c^2 * hs2 + σ^2 * ht2 + σ^2*t^2 * hwim
    have hnorm2 : ‖(σ:ℂ)*((s:ℝ):ℂ) + (c:ℂ)*(((t:ℝ):ℂ)*z)‖^2
        = σ^2*x + c^2*y + 2*Real.sqrt (c^2*σ^2*x*y) * w := by
      rw [← Complex.normSq_eq_norm_sq]
      have hre : ((σ:ℂ)*((s:ℝ):ℂ) + (c:ℂ)*(((t:ℝ):ℂ)*z)).re
          = σ*s + c*(t*z.re) := by
        simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
      have him : ((σ:ℂ)*((s:ℝ):ℂ) + (c:ℂ)*(((t:ℝ):ℂ)*z)).im
          = c*(t*z.im) := by
        simp [Complex.add_im, Complex.mul_re, Complex.mul_im]
      rw [Complex.normSq_apply, hre, him, hsqrt, hz_re]
      by_cases hcs : 0 ≤ c*σ
      · have habs : |c*σ| = c*σ := abs_of_nonneg hcs
        have hee : e = w := by rw [hedef, if_pos hcs]
        have hwim : w^2 + z.im^2 = 1 := by
          have h' := hzz
          rw [hz_re, hee] at h'
          exact h'
        rw [habs, hee]
        linear_combination σ^2 * hs2 + c^2 * ht2 + c^2*t^2 * hwim
      · have habs : |c*σ| = -(c*σ) := abs_of_neg (not_le.mp hcs)
        have hee : e = -w := by rw [hedef, if_neg hcs]
        have hwim : w^2 + z.im^2 = 1 := by
          have h' := hzz
          rw [hz_re, hee] at h'
          linear_combination h'
        rw [habs, hee]
        linear_combination σ^2 * hs2 + c^2 * ht2 + c^2*t^2 * hwim
    have e1 : f ‖(c:ℂ)*((s:ℝ):ℂ) - (σ:ℂ)*(((t:ℝ):ℂ)*z)‖
        = g (c^2*x + σ^2*y - 2*Real.sqrt (c^2*σ^2*x*y) * w) := by
      rw [← hnorm1, hgz]
    have e2 : f ‖(σ:ℂ)*((s:ℝ):ℂ) + (c:ℂ)*(((t:ℝ):ℂ)*z)‖
        = g (σ^2*x + c^2*y + 2*Real.sqrt (c^2*σ^2*x*y) * w) := by
      rw [← hnorm2, hgz]
    have e3 : f ‖((s:ℝ):ℂ)‖ = g x := by
      rw [← hgz]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, hs2]
    have e4 : f ‖((t:ℝ):ℂ) * z‖ = g y := by
      rw [← hgz]
      congr 1
      rw [norm_mul, hz_norm, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht0, ht2]
    rw [e1, e2, e3, e4] at h
    exact h
  have hadd := phase_interval_additivity g hg0 (c^2) (σ^2)
    (by positivity) (by positivity) hE
  have hglin := monotone_additive_on_cone_is_linear g hadd hmonog
  have hBorn : ∀ x : ℝ, 0 ≤ x → f x = x^2 * f 1 := by
    intro x hx
    have h := hglin (x^2) (sq_nonneg x)
    rw [hgdef] at h
    simp only [] at h
    rw [Real.sqrt_sq hx, Real.sqrt_one] at h
    exact h
  -- ---------- step 2: nontriviality pins f 1 > 0 ----------
  have hf1 : 0 < f 1 := by
    obtain ⟨x₀, hx₀, hfx₀⟩ := hnontriv
    have h := hBorn x₀ hx₀
    have hne : f 1 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h
      exact hfx₀ h
    have hge : 0 ≤ f 1 := by
      have := hmono 0 1 le_rfl zero_le_one
      linarith [hf0]
    exact lt_of_le_of_ne hge (Ne.symm hne)
  -- ---------- step 3: the derived measure is ℓ² ----------
  have hsq2 : ∀ z : ℂ, ‖z‖ ^ (2:ℝ) = ‖z‖^2 := by
    intro z
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hmeas2 : ∀ x : Fin n → ℂ,
      ∑ i, ‖F x i‖ ^ (2:ℝ) = ∑ i, ‖x i‖ ^ (2:ℝ) := by
    intro x
    have h := hmeas x
    have hL : ∀ v : Fin n → ℂ, ∑ i, f ‖v i‖
        = (∑ i, ‖v i‖ ^ (2:ℝ)) * f 1 := by
      intro v
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hBorn ‖v i‖ (norm_nonneg _), hsq2]
    rw [hL, hL] at h
    exact mul_right_cancel₀ (ne_of_gt hf1) h
  have hdist2 : ∀ x y : Fin n → ℂ,
      ∑ i, ‖F x i - F y i‖ ^ (2:ℝ) = ∑ i, ‖x i - y i‖ ^ (2:ℝ) := by
    intro x y
    have h := hdist x y
    have hL : ∀ v : Fin n → ℂ, ∑ i, f ‖v i‖
        = (∑ i, ‖v i‖ ^ (2:ℝ)) * f 1 := by
      intro v
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hBorn ‖v i‖ (norm_nonneg _), hsq2]
    have h' : (∑ i, ‖F x i - F y i‖ ^ (2:ℝ)) * f 1
        = (∑ i, ‖x i - y i‖ ^ (2:ℝ)) * f 1 := by
      rw [← hL, ← hL]
      exact h
    exact mul_right_cancel₀ (ne_of_gt hf1) h'
  -- ---------- step 4: linearity (Mazur–Ulam), then gauge ----------
  obtain ⟨haddF, hsmulR⟩ := lossless_bijection_is_real_linear
    (by norm_num : (1:ℝ) ≤ 2) F hsurj hmeas2 hdist2
  let L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := F
      map_add' := haddF
      map_smul' := fun r x => hsmulR r x }
  have hphaseL : ∀ x : Fin n → ℂ, L (Complex.I • x) = Complex.I • L x :=
    hphase
  have hsmulC := phase_covariant_real_linear_is_complex_linear L hphaseL
  let U : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := F
      map_add' := haddF
      map_smul' := fun z x => hsmulC z x }
  -- ---------- step 5: unitarity ----------
  have hsqm : ∀ z : ℂ, ‖z‖ ^ (2:ℝ) = ‖z‖ * ‖z‖ := by
    intro z
    rw [hsq2]
    ring
  have hms : ∀ x : Fin n → ℂ,
      ∑ i, ‖U x i‖ * ‖U x i‖ = ∑ i, ‖x i‖ * ‖x i‖ := by
    intro x
    have h := hmeas2 x
    calc ∑ i, ‖U x i‖ * ‖U x i‖
        = ∑ i, ‖F x i‖ ^ (2:ℝ) :=
          Finset.sum_congr rfl fun i _ => (hsqm _).symm
      _ = ∑ i, ‖x i‖ ^ (2:ℝ) := h
      _ = ∑ i, ‖x i‖ * ‖x i‖ :=
          Finset.sum_congr rfl fun i _ => hsqm _
  refine ⟨hBorn, hf1, U, fun x => rfl, ?_⟩
  intro i₁ i₂
  by_cases hii : i₁ = i₂
  · subst hii
    rw [if_pos rfl]
    have hcol : ∑ i, ‖U (Pi.single i₁ 1) i‖ * ‖U (Pi.single i₁ 1) i‖
        = 1 := (hms _).trans (single_probe_sum_sq i₁ 1 (by simp))
    calc ∑ i, (starRingEnd ℂ) (U (Pi.single i₁ 1) i)
          * U (Pi.single i₁ 1) i
        = ∑ i, ((‖U (Pi.single i₁ 1) i‖ * ‖U (Pi.single i₁ 1) i‖ : ℝ)
            : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_comm ((starRingEnd ℂ) _), Complex.mul_conj]
          norm_cast
          rw [Complex.normSq_eq_norm_sq]
          ring
      _ = ((∑ i, ‖U (Pi.single i₁ 1) i‖ * ‖U (Pi.single i₁ 1) i‖ : ℝ)
            : ℂ) := by
          rw [Complex.ofReal_sum]
      _ = 1 := by rw [hcol]; norm_num
  · rw [if_neg hii]
    exact l2_lossless_columns_orthogonal U hms i₁ i₂ hii

/-! ## 25. MASTER CHAINING: measure homogenization — one interference
event forces two sectors to share ONE probability calculus

`phase_interval_additivity` (§23) chained a single function against
itself.  A general additive measure is Σ fᵢ(‖xᵢ‖): each branch
alternative may carry its OWN weighting function.  `master_chaining`
removes the single-function restriction: two functions g₁, g₂ tied
by the interference exchange (the two input ports weighted by g₁, g₂
and the two output ports the same, with the physical normalization
P + Q = 1) are forced EQUAL and jointly linear — hence a common
Born function.  The ladder gives the increment law
g₂(s+m) = g₂(s) + g₁(m) (m ≤ s); the x = 0 probe then pins g₂ to
g₁'s slope with no residual constant.

Physics: ONE interference event between two sectors forces them onto
the SAME probability calculus — not merely the same exponent (the
old no-hybrid), the same measure FUNCTION, starting from arbitrary
monotone pairs.  A dualism in which gravity and matter carried
different probability weightings cannot survive a single
interference event between them: observing gravitationally-induced
interference (BMV-type experiments) would force gravity into
matter's Born calculus.  This is also the engine of the general
two-overlap Born-or-trivial result (arbitrary complex column pairs,
UNIQUENESS_LEG.md). -/

set_option maxHeartbeats 1600000 in
/-- MASTER CHAINING: two functions g₁, g₂ tied by a level-line
exchange with a nonneg amplitude force them EQUAL and jointly
additive.  Generalizes phase_interval_additivity (g₁ = g₂) and
covers the two-overlap and homogenization cases: for every level
Z and every phase w ∈ [-1,1],
  g₁(P x + Q y - 2√(PQ x y) w) + g₂(Q x + P y + 2√(PQ x y) w)
    = g₁-value + g₂-value  is w-independent, so both g's chain. -/
theorem master_chaining (g₁ g₂ : ℝ → ℝ)
    (hg10 : g₁ 0 = 0) (hg20 : g₂ 0 = 0)
    (hmono₁ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g₁ a ≤ g₁ b)
    (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) (hPQ : P + Q = 1)
    (hE : ∀ x y w : ℝ, 0 ≤ x → 0 ≤ y → -1 ≤ w → w ≤ 1 →
      g₁ (P*x + Q*y - 2*Real.sqrt (P*Q*x*y) * w)
        + g₂ (Q*x + P*y + 2*Real.sqrt (P*Q*x*y) * w)
      = g₁ x + g₂ y) :
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → g₁ (a + b) = g₁ a + g₂ b) ∧
    (∀ t : ℝ, 0 ≤ t → g₁ t = g₂ t) := by
  -- the w=1 vs w=-1 comparison at (x,y) and (y,x) will pin g₁=g₂.
  -- First: the interval-constancy step, identical structure to §23.
  have key : ∀ Z : ℝ, 0 < Z → ∀ μ ν : ℝ,
      0 < μ → μ < 1 → 0 ≤ ν → ν ≤ 1 →
      |(P - Q) * (μ - ν)| ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) →
      g₁ (Z*μ) + g₂ (Z*(1-μ)) = g₁ (Z*ν) + g₂ (Z*(1-ν)) := by
    intro Z hZ μ ν hμ0 hμ1 hν0 hν1 hcond
    have h1μ : (0:ℝ) < 1 - μ := by linarith
    have hZμ : (0:ℝ) ≤ Z*μ := by positivity
    have hZμ' : (0:ℝ) ≤ Z*(1-μ) := by positivity
    have hZν : (0:ℝ) ≤ Z*ν := by positivity
    have hZν' : (0:ℝ) ≤ Z*(1-ν) := by nlinarith
    have hs_pos : 0 < Real.sqrt (P*Q*μ*(1-μ)) := by
      apply Real.sqrt_pos.mpr; positivity
    have h1 := hE (Z*ν) (Z*(1-ν)) 0 hZν hZν' (by norm_num) (by norm_num)
    rw [mul_zero, sub_zero, add_zero] at h1
    set w : ℝ := (P - Q) * (μ - ν) / (2 * Real.sqrt (P*Q*μ*(1-μ)))
      with hwdef
    have hw1 : |w| ≤ 1 := by
      rw [hwdef, abs_div, div_le_one (by positivity)]
      calc |(P - Q) * (μ - ν)| ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) := hcond
        _ = |2 * Real.sqrt (P*Q*μ*(1-μ))| := by
            rw [abs_of_pos (by positivity)]
    have h2 := hE (Z*μ) (Z*(1-μ)) w hZμ hZμ'
      (neg_le_of_abs_le hw1) (le_of_abs_le hw1)
    have hsq : Real.sqrt (P*Q*(Z*μ)*(Z*(1-μ)))
        = Z * Real.sqrt (P*Q*μ*(1-μ)) := by
      rw [show P*Q*(Z*μ)*(Z*(1-μ)) = Z^2 * (P*Q*μ*(1-μ)) by ring,
        Real.sqrt_mul (sq_nonneg Z), Real.sqrt_sq (le_of_lt hZ)]
    rw [hsq] at h2
    have hws : w * (2 * Real.sqrt (P*Q*μ*(1-μ))) = (P - Q) * (μ - ν) := by
      rw [hwdef]; exact div_mul_cancel₀ _ (by positivity)
    have hprod : 2*(Z*Real.sqrt (P*Q*μ*(1-μ)))*w = Z*((P-Q)*(μ-ν)) := by
      calc 2*(Z*Real.sqrt (P*Q*μ*(1-μ)))*w
          = Z*(w * (2*Real.sqrt (P*Q*μ*(1-μ)))) := by ring
        _ = Z*((P-Q)*(μ-ν)) := by rw [hws]
    have harg1 : P*(Z*μ) + Q*(Z*(1-μ)) - 2*(Z*Real.sqrt (P*Q*μ*(1-μ)))*w
        = P*(Z*ν) + Q*(Z*(1-ν)) := by rw [hprod]; ring
    have harg2 : Q*(Z*μ) + P*(Z*(1-μ)) + 2*(Z*Real.sqrt (P*Q*μ*(1-μ)))*w
        = Q*(Z*ν) + P*(Z*(1-ν)) := by rw [hprod]; ring
    rw [harg1, harg2] at h2
    linarith
  -- reuse the exact ladder from §23 by noting g := fun t => the pair
  -- structure.  We prove the joint additive law first.
  set mustar : ℝ := 4*P*Q/(P+Q)^2 with hmustar
  have hmu0 : 0 < mustar := by positivity
  have hmu1 : mustar ≤ 1 := by
    rw [hmustar, div_le_one (by positivity)]; nlinarith [sq_nonneg (P - Q)]
  have hkey_id : (P-Q)^2 * mustar = 4*P*Q*(1-mustar) := by
    rw [hmustar]; field_simp; ring
  have hstep_cond : ∀ μ : ℝ, mustar ≤ μ → μ ≤ 1/2 →
      |P - Q| * mustar ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) := by
    intro μ hμl hμr
    have hμ0 : 0 < μ := lt_of_lt_of_le hmu0 hμl
    have h1μ : (0:ℝ) ≤ 1 - μ := by linarith
    have hmono : mustar * (1 - mustar) ≤ μ * (1 - μ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hμl)
        (by linarith : (0:ℝ) ≤ 1 - μ - mustar)]
    apply le_of_sq_le_sq'' (by positivity) (by positivity)
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ P*Q*μ*(1-μ) by positivity)
    calc (|P-Q| * mustar)^2 = (P-Q)^2 * mustar * mustar := by
          rw [mul_pow, sq_abs]; ring
      _ = 4*P*Q*(1-mustar) * mustar := by rw [hkey_id]
      _ ≤ 4*(P*Q*μ*(1-μ)) := by
          nlinarith [mul_le_mul_of_nonneg_left hmono
            (show (0:ℝ) ≤ 4*(P*Q) by positivity)]
      _ = (2 * Real.sqrt (P*Q*μ*(1-μ)))^2 := by rw [mul_pow, hs]; ring
  have hladder : ∀ Z : ℝ, 0 < Z → ∀ (k : ℕ) (μ : ℝ),
      0 ≤ μ → μ ≤ 1/2 → μ ≤ (k+1 : ℝ) * mustar →
      g₁ (Z*μ) + g₂ (Z*(1-μ)) = g₁ 0 + g₂ Z := by
    intro Z hZ k
    induction k with
    | zero =>
      intro μ hμ0 hμh hμk
      rcases eq_or_lt_of_le hμ0 with h0 | hpos
      · rw [← h0]; norm_num
      have hμ1 : μ < 1 := by linarith
      have hμle : μ ≤ mustar := by
        have : ((0:ℕ)+1 : ℝ) = 1 := by norm_num
        rw [this, one_mul] at hμk; exact hμk
      have hcond : |(P - Q) * (μ - 0)| ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) := by
        rw [sub_zero, abs_mul, abs_of_nonneg hμ0]
        have h1μ : (0:ℝ) ≤ 1 - μ := by linarith
        have hchain : (P-Q)^2 * μ ≤ 4*P*Q*(1-μ) := by
          calc (P-Q)^2 * μ ≤ (P-Q)^2 * mustar :=
                mul_le_mul_of_nonneg_left hμle (sq_nonneg _)
            _ = 4*P*Q*(1-mustar) := hkey_id
            _ ≤ 4*P*Q*(1-μ) := by
                apply mul_le_mul_of_nonneg_left (by linarith); positivity
        apply le_of_sq_le_sq'' (by positivity) (by positivity)
        have hs := Real.sq_sqrt (show (0:ℝ) ≤ P*Q*μ*(1-μ) by positivity)
        calc (|P-Q| * μ)^2 = (P-Q)^2 * μ * μ := by rw [mul_pow, sq_abs]; ring
          _ ≤ 4*P*Q*(1-μ) * μ := by
              nlinarith [mul_le_mul_of_nonneg_right hchain hμ0]
          _ = (2 * Real.sqrt (P*Q*μ*(1-μ)))^2 := by rw [mul_pow, hs]; ring
      have h := key Z hZ μ 0 hpos hμ1 le_rfl (by norm_num) hcond
      rw [mul_zero, sub_zero, mul_one] at h; exact h
    | succ k ih =>
      intro μ hμ0 hμh hμk
      by_cases hcase : μ ≤ (k+1 : ℝ) * mustar
      · exact ih μ hμ0 hμh hcase
      push_neg at hcase
      have hμstar : mustar ≤ μ := by
        have hk1 : (1:ℝ) ≤ (k:ℝ)+1 := by
          have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith
        calc mustar = 1 * mustar := (one_mul _).symm
          _ ≤ ((k:ℝ)+1) * mustar :=
              mul_le_mul_of_nonneg_right hk1 (le_of_lt hmu0)
          _ ≤ μ := le_of_lt hcase
      have hμpos : 0 < μ := lt_of_lt_of_le hmu0 hμstar
      have hμ1 : μ < 1 := by linarith
      set ν : ℝ := μ - mustar with hνdef
      have hν0 : 0 ≤ ν := by rw [hνdef]; linarith
      have hν1 : ν ≤ 1 := by rw [hνdef]; linarith
      have hνh : ν ≤ 1/2 := by rw [hνdef]; linarith
      have hνk : ν ≤ (k+1 : ℝ) * mustar := by
        rw [hνdef]
        have : μ ≤ ((k:ℝ)+1+1) * mustar := by
          convert hμk using 2; push_cast; ring
        nlinarith
      have hcond : |(P - Q) * (μ - ν)| ≤ 2 * Real.sqrt (P*Q*μ*(1-μ)) := by
        rw [hνdef, show μ - (μ - mustar) = mustar by ring, abs_mul,
          abs_of_pos hmu0]
        exact hstep_cond μ hμstar hμh
      have h1 := key Z hZ μ ν hμpos hμ1 hν0 hν1 hcond
      have h2 := ih ν hν0 hνh hνk
      linarith
  -- ---------- (INC): g₂(s+m) = g₂ s + g₁ m for s ≥ m ≥ 0 ----------
  have hINC : ∀ s m : ℝ, 0 ≤ m → m ≤ s → g₂ (s + m) = g₂ s + g₁ m := by
    intro s m hm hms
    have hspos : 0 < s + m ∨ s + m = 0 := by
      rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ s + m) with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    rcases hspos with hZ | hZ0
    · -- ladder on Z = s+m at μ = m/(s+m) ≤ 1/2
      set Z : ℝ := s + m with hZdef
      set μ : ℝ := m / Z with hμdef
      have hμ0 : 0 ≤ μ := by rw [hμdef]; positivity
      have hμh : μ ≤ 1/2 := by
        rw [hμdef, div_le_iff₀ hZ]; linarith
      obtain ⟨k, hk⟩ := exists_nat_gt (μ / mustar)
      have hμk : μ ≤ (k+1 : ℝ) * mustar := by
        rw [div_lt_iff₀ hmu0] at hk; nlinarith [hmu0]
      have h := hladder Z hZ k μ hμ0 hμh hμk
      rw [hg10, zero_add] at h
      have e1 : Z * μ = m := by rw [hμdef]; field_simp
      have e2 : Z * (1 - μ) = s := by rw [hμdef]; field_simp; ring
      rw [e1, e2] at h
      -- h : g₁ m + g₂ s = g₂ Z
      rw [hZdef] at h ⊢
      linarith
    · have hm0 : m = 0 := by linarith
      have hs0 : s = 0 := by linarith
      rw [hm0, hs0, hg10]; simp [hg20]
  -- ---------- g₁ is additive on the cone ----------
  have hg1add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → g₁ (a + b) = g₁ a + g₁ b := by
    intro a b ha hb
    -- pick x large: x = a + b works (x ≥ a+b, x ≥ a, x ≥ b)
    set x : ℝ := a + b with hxdef
    have hxa : a ≤ x := by rw [hxdef]; linarith
    have hxb : b ≤ x := by rw [hxdef]; linarith
    have hxab : a + b ≤ x := le_of_eq hxdef.symm
    have hxpos : 0 ≤ x := by rw [hxdef]; linarith
    -- g₂(x + (a+b)) via one step of size (a+b)
    have h1 := hINC x (a + b) (by linarith) hxab
    -- via two steps of size a then b
    have h2 := hINC x b hb hxb            -- g₂(x+b) = g₂ x + g₁ b
    have h3 := hINC (x + b) a ha (by linarith)  -- g₂(x+b+a) = g₂(x+b) + g₁ a
    have hcomm : x + b + a = x + (a + b) := by ring
    rw [hcomm, h2] at h3
    -- h3 : g₂(x+(a+b)) = (g₂ x + g₁ b) + g₁ a
    -- h1 : g₂(x+(a+b)) = g₂ x + g₁ (a+b)
    linarith
  -- ---------- g₁ linear; g₂ linear equal; conclusions ----------
  have hg1lin := monotone_additive_on_cone_is_linear g₁ hg1add hmono₁
  -- ---------- g₂ linear via the x=0 probe (needs P+Q=1) ----------
  have hA : ∀ x : ℝ, 0 ≤ x → g₁ (P*x) + g₂ (Q*x) = g₁ x := by
    intro x hx
    have h := hE x 0 0 hx le_rfl (by norm_num) (by norm_num)
    simp only [mul_zero, add_zero, sub_zero, Real.sqrt_zero, hg20] at h
    exact h
  have hg2lin : ∀ t : ℝ, 0 ≤ t → g₂ t = t * g₁ 1 := by
    intro t ht
    have hx : 0 ≤ t / Q := by positivity
    have h := hA (t / Q) hx
    have hPt : P * (t / Q) = (P / Q) * t := by ring
    have hQt : Q * (t / Q) = t := by field_simp
    rw [hPt, hQt] at h
    -- g₁(P/Q t) + g₂ t = g₁(t/Q); use g₁ linear
    have e1 : g₁ ((P / Q) * t) = (P / Q) * t * g₁ 1 :=
      hg1lin _ (by positivity)
    have e2 : g₁ (t / Q) = (t / Q) * g₁ 1 := hg1lin _ hx
    rw [e1, e2] at h
    -- (P/Q) t g₁1 + g₂ t = (t/Q) g₁1  ⇒ g₂ t = ((1-P)/Q) t g₁1 = t g₁1
    have hQ0 : Q ≠ 0 := ne_of_gt hQ
    have hval : g₂ t = (t / Q) * g₁ 1 - (P / Q) * t * g₁ 1 := by linarith
    have hPeq : P = 1 - Q := by linarith
    rw [hval, hPeq]
    field_simp
    ring
  refine ⟨fun a b ha hb => ?_, fun t ht => ?_⟩
  · rw [hg1lin (a + b) (by linarith), hg1lin a ha, hg2lin b hb]; ring
  · rw [hg1lin t ht, hg2lin t ht]

/-! ## 26. THE WIDTH–PHASE METER: the formal core of the quantum
expansion law

Numerics (tag quantum-expansion-law-2026-08-15) found that width-
restricted growth families admit double conservation only when deep
enough, that the wall is phase-starvation (abundant width classes
with phase-poor spectra fail), and that each unit of causal
in-degree rotates the amplitude phase by one octant at φ = π/4.
This section machine-checks the mechanism's four pillars:

  * `single_class_born` — the degenerate-spectrum no-go: one gap
    class of multiplicity μ supports double conservation iff its
    phase is trivial and μ = 1.  (The unique candidate has Born
    mass 1/μ.)
  * `halfplane_separation_infeasible` — octant-coverage necessity:
    if the available phases lie in a closed half-plane missing
    (1,0), the coherent moments have no nonnegative solution at
    all.  Feasibility of a growth family is a PHASE-COVERAGE
    property of its gap spectrum.
  * `antipodal_pair_reaches_born` — sufficiency of one antipodal
    pair: any nonnegative coherent solution with Born mass ≤ 1
    upgrades to exact double conservation by walking an explicit
    quadratic-root step along the recession direction the pair
    provides.  No limits, no IVT.
  * `gap_splits_width` + `width_phase_octant` + `octant_period` —
    the meter itself: every maximal element of a past contributes
    c(0) = −1 to the gap, so the amplitude character factors as
    (interior phase) · ζ^width with ζ = e^{−iπ/4}, and ζ⁸ = 1:
    ONE OCTANT OF PHASE PER CELL OF CAUSAL WIDTH, width counted
    mod 8 by the interference system.

Together: Born feasibility of a restricted growth family = octant
coverage of its gap phases; width is metered in phase.  This is the
theorem-level content behind the empirical expansion law
w_max(n) ≈ n/c* — the depth-gating happens because interior
diversity (which grows with depth) is what spreads a width class
across enough octants. -/

/-- Degenerate-spectrum no-go: a single gap class of multiplicity μ
supports double conservation iff its phase is trivial AND μ = 1. -/
theorem single_class_born (θ μ : ℝ) (hμ : 1 ≤ μ) :
    (∃ x : ℝ, 0 ≤ x ∧ μ * x * Real.cos θ = 1 ∧ μ * x * Real.sin θ = 0 ∧
      μ * x^2 = 1) ↔ (Real.cos θ = 1 ∧ Real.sin θ = 0 ∧ μ = 1) := by
  constructor
  · rintro ⟨x, hx0, hc, hs, hq⟩
    have hμ0 : 0 < μ := lt_of_lt_of_le one_pos hμ
    have hx : 0 < x := by
      rcases eq_or_lt_of_le hx0 with h | h
      · exfalso; rw [← h] at hc; simp at hc
      · exact h
    have hμx : 0 < μ * x := mul_pos hμ0 hx
    have hsin : Real.sin θ = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact absurd h (ne_of_gt hμx)
      · exact h
    have hpyth := Real.sin_sq_add_cos_sq θ
    rw [hsin] at hpyth
    have hcos2 : (Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by nlinarith
    have hcos : Real.cos θ = 1 := by
      rcases mul_eq_zero.mp hcos2 with h | h
      · linarith
      · exfalso
        have hcneg : Real.cos θ = -1 := by linarith
        rw [hcneg] at hc
        nlinarith
    rw [hcos, mul_one] at hc
    have h2 : x = 1 := by
      rw [sq, ← mul_assoc, hc, one_mul] at hq
      exact hq
    rw [h2, mul_one] at hc
    exact ⟨hcos, hsin, hc⟩
  · rintro ⟨hcos, hsin, hμ1⟩
    exact ⟨1, zero_le_one, by rw [hcos, hμ1]; ring, by rw [hsin]; ring,
      by rw [hμ1]; ring⟩

/-- Octant-coverage necessity: if every available phase direction
lies in a closed half-plane whose inner normal has positive first
component (the half-plane misses (1,0)), the coherent moment system
has no nonnegative solution — regardless of multiplicities and of
the Born constraint.  This is the separating-functional form of
"(1,0) must lie in the cone of available phases". -/
theorem halfplane_separation_infeasible {K : ℕ} (θ μ : Fin K → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (u₁ u₂ : ℝ) (hu : 0 < u₁)
    (hsep : ∀ i, Real.cos (θ i) * u₁ + Real.sin (θ i) * u₂ ≤ 0) :
    ¬ ∃ x : Fin K → ℝ, (∀ i, 0 ≤ x i) ∧
        ∑ i, μ i * x i * Real.cos (θ i) = 1 ∧
        ∑ i, μ i * x i * Real.sin (θ i) = 0 := by
  rintro ⟨x, hx, hc, hs⟩
  have key : ∑ i, (μ i * x i * Real.cos (θ i) * u₁
      + μ i * x i * Real.sin (θ i) * u₂) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have h1 : 0 ≤ μ i * x i := mul_nonneg (hμ i) (hx i)
    nlinarith [mul_le_mul_of_nonneg_left (hsep i) h1]
  have expand : ∑ i, (μ i * x i * Real.cos (θ i) * u₁
      + μ i * x i * Real.sin (θ i) * u₂)
      = (∑ i, μ i * x i * Real.cos (θ i)) * u₁
        + (∑ i, μ i * x i * Real.sin (θ i)) * u₂ := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [expand, hc, hs, one_mul, zero_mul, add_zero] at key
  linarith

/-- Antipodal reachability: a nonnegative solution of the coherent
moments with Born mass ≤ 1, plus one antipodal phase pair, yields an
exact double-conservation solution.  The antipodal pair provides the
recession direction; the required step is an explicit quadratic root
(no limits, no IVT). -/
theorem antipodal_pair_reaches_born {K : ℕ} (θ μ : Fin K → ℝ)
    (hμ : ∀ i, 0 < μ i) (x₀ : Fin K → ℝ) (hx₀ : ∀ i, 0 ≤ x₀ i)
    (hc : ∑ i, μ i * x₀ i * Real.cos (θ i) = 1)
    (hs : ∑ i, μ i * x₀ i * Real.sin (θ i) = 0)
    (hQ : ∑ i, μ i * (x₀ i)^2 ≤ 1)
    {j₁ j₂ : Fin K} (hj : j₁ ≠ j₂)
    (hac : Real.cos (θ j₂) = -Real.cos (θ j₁))
    (has : Real.sin (θ j₂) = -Real.sin (θ j₁)) :
    ∃ x : Fin K → ℝ, (∀ i, 0 ≤ x i) ∧
      ∑ i, μ i * x i * Real.cos (θ i) = 1 ∧
      ∑ i, μ i * x i * Real.sin (θ i) = 0 ∧
      ∑ i, μ i * (x i)^2 = 1 := by
  classical
  set d : Fin K → ℝ := fun i =>
    if i = j₁ then 1 / μ j₁ else if i = j₂ then 1 / μ j₂ else 0 with hd
  have hdj₁ : d j₁ = 1 / μ j₁ := by simp [hd]
  have hdj₂ : d j₂ = 1 / μ j₂ := by simp [hd, Ne.symm hj]
  have hd0 : ∀ i, 0 ≤ d i := by
    intro i
    have hi : d i = if i = j₁ then 1 / μ j₁ else if i = j₂ then 1 / μ j₂ else 0 := by
      simp [hd]
    rw [hi]
    split_ifs
    · have := hμ j₁
      positivity
    · have := hμ j₂
      positivity
    · exact le_rfl
  have hsum : ∀ f : Fin K → ℝ, ∑ i, μ i * d i * f i = f j₁ + f j₂ := by
    intro f
    have hterm : ∀ i, μ i * d i * f i
        = (if i = j₁ then f j₁ else 0) + (if i = j₂ then f j₂ else 0) := by
      intro i
      by_cases h1 : i = j₁
      · rw [h1, hdj₁, if_pos rfl, if_neg hj, add_zero]
        field_simp [(hμ j₁).ne']
      · by_cases h2 : i = j₂
        · rw [h2, hdj₂, if_neg (Ne.symm hj), if_pos rfl, zero_add]
          field_simp [(hμ j₂).ne']
        · have hi : d i = 0 := by simp [hd, h1, h2]
          rw [hi, if_neg h1, if_neg h2]
          ring
    calc ∑ i, μ i * d i * f i
        = ∑ i, ((if i = j₁ then f j₁ else 0) + (if i = j₂ then f j₂ else 0)) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = (∑ i, if i = j₁ then f j₁ else 0)
            + (∑ i, if i = j₂ then f j₂ else 0) := Finset.sum_add_distrib
      _ = f j₁ + f j₂ := by
          rw [Finset.sum_ite_eq' Finset.univ j₁ (fun _ => f j₁),
            Finset.sum_ite_eq' Finset.univ j₂ (fun _ => f j₂)]
          simp
  set q : ℝ := ∑ i, μ i * (x₀ i)^2 with hqdef
  set a : ℝ := 1 / μ j₁ + 1 / μ j₂ with hadef
  set b : ℝ := 2 * (x₀ j₁ + x₀ j₂) with hbdef
  have ha0 : 0 < a := by
    rw [hadef]
    have := hμ j₁; have := hμ j₂
    positivity
  have hb0 : 0 ≤ b := by
    rw [hbdef]
    have := hx₀ j₁; have := hx₀ j₂
    linarith
  set disc : ℝ := b^2 + 4*a*(1 - q) with hdiscdef
  have hdisc0 : 0 ≤ disc := by
    rw [hdiscdef]
    nlinarith [sq_nonneg b]
  set s : ℝ := Real.sqrt disc with hsdef
  have hs2 : s^2 = b^2 + 4*a*(1 - q) := by
    rw [hsdef, Real.sq_sqrt hdisc0, hdiscdef]
  have hsb : b ≤ s := by
    have h1 : Real.sqrt (b^2) ≤ s := by
      rw [hsdef]
      apply Real.sqrt_le_sqrt
      rw [hdiscdef]
      nlinarith
    rw [Real.sqrt_sq hb0] at h1
    exact h1
  set t : ℝ := (s - b) / (2*a) with htdef
  have h2a : (2*a) ≠ 0 := by positivity
  have ht0 : 0 ≤ t := by
    rw [htdef]
    apply div_nonneg (by linarith) (by linarith)
  have ht' : t * (2*a) = s - b := by
    rw [htdef]
    exact div_mul_cancel₀ _ h2a
  have hkey : a * t^2 + b * t = 1 - q := by
    have h4a : (4*a^2) ≠ 0 := by positivity
    have hexp : 4*a^2 * (a * t^2 + b * t) = 4*a^2 * (1 - q) := by
      calc 4*a^2 * (a * t^2 + b * t)
          = a * (t*(2*a))^2 + 2*a*b*(t*(2*a)) := by ring
        _ = a * (s - b)^2 + 2*a*b*(s - b) := by rw [ht']
        _ = a * s^2 - a * b^2 := by ring
        _ = a * (b^2 + 4*a*(1-q)) - a * b^2 := by rw [hs2]
        _ = 4*a^2 * (1-q) := by ring
    exact mul_left_cancel₀ h4a hexp
  refine ⟨fun i => x₀ i + t * d i, ?_, ?_, ?_, ?_⟩
  · intro i
    show 0 ≤ x₀ i + t * d i
    have := hd0 i
    have := hx₀ i
    nlinarith
  · show ∑ i, μ i * (x₀ i + t * d i) * Real.cos (θ i) = 1
    have expand : ∑ i, μ i * (x₀ i + t * d i) * Real.cos (θ i)
        = (∑ i, μ i * x₀ i * Real.cos (θ i))
          + t * ∑ i, μ i * d i * Real.cos (θ i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [expand, hc, hsum (fun i => Real.cos (θ i))]
    rw [hac]
    ring
  · show ∑ i, μ i * (x₀ i + t * d i) * Real.sin (θ i) = 0
    have expand : ∑ i, μ i * (x₀ i + t * d i) * Real.sin (θ i)
        = (∑ i, μ i * x₀ i * Real.sin (θ i))
          + t * ∑ i, μ i * d i * Real.sin (θ i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [expand, hs, hsum (fun i => Real.sin (θ i))]
    rw [has]
    ring
  · show ∑ i, μ i * (x₀ i + t * d i)^2 = 1
    have expand : ∑ i, μ i * (x₀ i + t * d i)^2
        = (∑ i, μ i * (x₀ i)^2)
          + 2*t * (∑ i, μ i * d i * x₀ i)
          + t^2 * (∑ i, μ i * d i * d i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hx0sum : ∑ i, μ i * d i * x₀ i = b / 2 := by
      rw [hsum x₀, hbdef]
      ring
    have hdsum : ∑ i, μ i * d i * d i = a := by
      rw [hsum d, hdj₁, hdj₂, hadef]
    rw [expand, ← hqdef, hx0sum, hdsum]
    linear_combination hkey

/-- The gap splits over the width: every maximal element of the past
(k = 0) contributes exactly c(0) = −1, so
gap = 1 − width + (interior terms). -/
theorem gap_splits_width {α : Type*} [DecidableEq α]
    (D : Finset α) (k : α → ℕ) (c : ℕ → ℤ) (hc0 : c 0 = -1) :
    1 + ∑ y ∈ D, c (k y)
      = 1 - ((D.filter fun y => k y = 0).card : ℤ)
        + ∑ y ∈ D.filter (fun y => ¬ k y = 0), c (k y) := by
  classical
  have hsplit : ∑ y ∈ D, c (k y)
      = (∑ y ∈ D.filter (fun y => k y = 0), c (k y))
        + ∑ y ∈ D.filter (fun y => ¬ k y = 0), c (k y) :=
    (Finset.sum_filter_add_sum_filter_not D _ _).symm
  have hzero : ∑ y ∈ D.filter (fun y => k y = 0), c (k y)
      = -((D.filter fun y => k y = 0).card : ℤ) := by
    calc ∑ y ∈ D.filter (fun y => k y = 0), c (k y)
        = ∑ _y ∈ D.filter (fun y => k y = 0), (-1 : ℤ) :=
          Finset.sum_congr rfl fun y hy => by
            rw [(Finset.mem_filter.mp hy).2, hc0]
      _ = ((D.filter fun y => k y = 0).card : ℤ) * (-1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = -((D.filter fun y => k y = 0).card : ℤ) := by ring
  rw [hsplit, hzero]
  ring

/-- The width–phase meter: subtracting the width from the gap
factors the amplitude character into (interior phase) × ζ^width. -/
theorem width_phase_octant (g₀ : ℤ) (w : ℕ) :
    Complex.exp ((Real.pi/4 : ℝ) * Complex.I * ((g₀ - (w:ℤ) : ℤ) : ℂ))
      = Complex.exp ((Real.pi/4 : ℝ) * Complex.I * (g₀ : ℂ))
        * Complex.exp (-((Real.pi/4 : ℝ) * Complex.I)) ^ w := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- One octant per cell, full circle every 8: the width meter ζ is
an exact 8th root of unity at the Born-quadrature phase π/4 — width
is counted mod 8 by the interference system. -/
theorem octant_period :
    Complex.exp (-((Real.pi/4 : ℝ) * Complex.I)) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  have h : ((8:ℕ):ℂ) * -((Real.pi/4 : ℝ) * Complex.I)
      = -(2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

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
#print axioms phase_covariant_real_linear_is_complex_linear
#print axioms quantum_mechanics_from_time_alone
#print axioms monotone_quadratic_functional_eq
#print axioms balanced_beam_splitter_forces_born
#print axioms lossless_beam_splitter_step_forces_born
#print axioms sum_sorted_increments_le
#print axioms dense_splitting_no_jump
#print axioms dense_splitting_forces_linear
#print axioms splitter_family_forces_born
#print axioms lossless_splitter_family_forces_born
#print axioms measure_single_sum
#print axioms measure_pair_sum
#print axioms cos_sq_orbit_dense
#print axioms rotation_block_iterate
#print axioms generic_rotation_forces_born
#print axioms jump_transport
#print axioms exchange_descent_no_jump
#print axioms mixing_block_forces_measure_continuity
#print axioms monotone_quadratic_stability
#print axioms approximate_beam_splitter_near_born
#print axioms le_of_sq_le_sq''
#print axioms phase_interval_additivity
#print axioms complex_mixing_block_forces_born
#print axioms quantum_mechanics_from_a_beam_splitter
#print axioms master_chaining
#print axioms single_class_born
#print axioms halfplane_separation_infeasible
#print axioms antipodal_pair_reaches_born
#print axioms gap_splits_width
#print axioms width_phase_octant
#print axioms octant_period

end UnifiedTheory.Audit.KFCausalUniquenessLeg
