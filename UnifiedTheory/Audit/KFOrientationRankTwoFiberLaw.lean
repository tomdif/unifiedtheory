/-
  Audit/KFOrientationRankTwoFiberLaw.lean

  PARAMETRIC RANK-TWO FIBER LAW

  For three consecutive ordered event fibers of sizes `(p,q,r)`, this file
  derives the transported rank-two orientation matrix from the same two-by-two
  determinant used by `kFOrientationAtRank`.

  The two native adjacent couplings count weakly ordered pairs in the shared
  outer fiber.  The generated long-range coupling counts strictly ordered
  pairs erased inside the middle fiber.  Consequently the three upper
  couplings are

    p*q*r*(p+1)/2,  p*q*r*(q-1)/2,  p*q*r*(r+1)/2.

  The exact scalar-closure classification is asymmetric: rank two closes if
  and only if `q = 1` and `p = r`.  Rank one instead requires `p = q = r`.
  Therefore simultaneous rank-one/rank-two scalar closure is possible only
  for the identity profile `(1,1,1)`.
-/

import UnifiedTheory.Audit.KFOrientationFiberLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationRankTwoFiberLaw

open scoped BigOperators

open UnifiedTheory.LayerB.NoBackgroundSpace
open UnifiedTheory.LayerB.KFFinitePoset
open UnifiedTheory.Audit.KFMultirankCoarseGraining
open UnifiedTheory.Audit.KFOrientationDefect
open UnifiedTheory.Audit.KFOrientationFiberLaw

/-! ## 1. The native two-by-two determinant on a total order -/

/-- Rational indicator of the order relation. -/
def orderIndicator {α : Type*} [LE α] [DecidableLE α] (a b : α) : ℚ :=
  if a ≤ b then 1 else 0

/-- The forward-minus-backward two-by-two order determinant, written without
reference to a particular finite carrier. -/
def rankTwoOrderOrientation {α : Type*} [LE α] [DecidableLE α]
    (a0 a1 b0 b1 : α) : ℚ :=
  (orderIndicator a0 b0 * orderIndicator a1 b1 -
      orderIndicator a0 b1 * orderIndicator a1 b0) -
    (orderIndicator b0 a0 * orderIndicator b1 a1 -
      orderIndicator b0 a1 * orderIndicator b1 a0)

/-- On any explicitly total finite poset, `rankTwoOrderOrientation` is exactly
the native determinant orientation channel—not a surrogate observable. -/
theorem kFOrientationAtRank_two_total_apply
    (P : FinPoset) (hrel : ∀ i j, P.rel i j = decide (i ≤ j))
    (A B : Chamber P 2) :
    kFOrientationAtRank P 2 A B =
      rankTwoOrderOrientation (A.1 0) (A.1 1) (B.1 0) (B.1 1) := by
  rw [kFOrientationAtRank_two_apply]
  simp only [orderKernel]
  simp_rw [hrel]
  simp [rankTwoOrderOrientation, orderIndicator]

/-! Three local interlacing laws.  The chamber labels are `01`, `02`, and
`12`; their event coordinates are placed in three consecutive blocks. -/

theorem rankTwo_orientation_01_02
    {p q r : ℕ} (i i' : Fin p) (j : Fin q) (k : Fin r) :
    rankTwoOrderOrientation (i : ℕ) (p + (j : ℕ))
      (i' : ℕ) (p + q + (k : ℕ)) =
        if i ≤ i' then 1 else 0 := by
  unfold rankTwoOrderOrientation orderIndicator
  split_ifs <;> norm_num <;> omega

theorem rankTwo_orientation_01_12
    {p q r : ℕ} (i : Fin p) (j j' : Fin q) (k : Fin r) :
    rankTwoOrderOrientation (i : ℕ) (p + (j : ℕ))
      (p + (j' : ℕ)) (p + q + (k : ℕ)) =
        if j' < j then 1 else 0 := by
  unfold rankTwoOrderOrientation orderIndicator
  split_ifs <;> norm_num <;> omega

theorem rankTwo_orientation_02_12
    {p q r : ℕ} (i : Fin p) (j : Fin q) (k k' : Fin r) :
    rankTwoOrderOrientation (i : ℕ) (p + q + (k : ℕ))
      (p + (j : ℕ)) (p + q + (k' : ℕ)) =
        if k ≤ k' then 1 else 0 := by
  unfold rankTwoOrderOrientation orderIndicator
  split_ifs <;> norm_num <;> omega

/-! ## 2. Exact weak- and strict-pair counts -/

/-- Number of weakly ordered pairs in an `n`-element fiber, cast to `ℚ`. -/
def weakPairCountQ (n : ℕ) : ℚ :=
  ∑ j : Fin n, ∑ i : Fin n, if i ≤ j then 1 else 0

/-- Number of strictly ordered pairs in an `n`-element fiber, cast to `ℚ`. -/
def strictPairCountQ (n : ℕ) : ℚ :=
  ∑ j : Fin n, ∑ i : Fin n, if i < j then 1 else 0

theorem weakPairCountQ_formula (n : ℕ) :
    weakPairCountQ n = (n : ℚ) * (n + 1) / 2 := by
  simp_rw [weakPairCountQ, Finset.sum_boole, Finset.filter_ge_eq_Iic,
    Fin.card_Iic]
  rw [Finset.sum_fin_eq_sum_range]
  have hsum :
      (∑ i ∈ Finset.range n,
        if h : i < n then (((i + 1 : ℕ) : ℚ)) else 0) =
        ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℚ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.1 hi]
  rw [hsum]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  by_cases hn : n = 0
  · subst n
    norm_num
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  have h := congrArg (fun x : ℕ => (x : ℚ))
    (Finset.sum_range_id_mul_two n)
  push_cast [Nat.cast_sub hnpos] at h
  nlinarith

theorem strictPairCountQ_formula (n : ℕ) :
    strictPairCountQ n = (n : ℚ) * (n - 1) / 2 := by
  simp_rw [strictPairCountQ, Finset.sum_boole, Finset.filter_gt_eq_Iio,
    Fin.card_Iio]
  rw [Finset.sum_fin_eq_sum_range]
  have hsum :
      (∑ i ∈ Finset.range n,
        if h : i < n then (i : ℚ) else 0) =
        ∑ i ∈ Finset.range n, (i : ℚ) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.1 hi]
  rw [hsum]
  by_cases hn : n = 0
  · subst n
    norm_num
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  have h := congrArg (fun x : ℕ => (x : ℚ))
    (Finset.sum_range_id_mul_two n)
  push_cast [Nat.cast_sub hnpos] at h
  nlinarith

/-! ## 3. Parametric rank-two fiber sums -/

/-- Transported coupling from coarse chamber `01` to `02`. -/
def rankTwoLeftCoupling (p q r : ℕ) : ℚ :=
  ∑ i : Fin p, ∑ j : Fin q, ∑ i' : Fin p, ∑ k : Fin r,
    rankTwoOrderOrientation (i : ℕ) (p + (j : ℕ))
      (i' : ℕ) (p + q + (k : ℕ))

/-- Generated long-range coupling from coarse chamber `01` to `12`. -/
def rankTwoLongCoupling (p q r : ℕ) : ℚ :=
  ∑ i : Fin p, ∑ j : Fin q, ∑ j' : Fin q, ∑ k : Fin r,
    rankTwoOrderOrientation (i : ℕ) (p + (j : ℕ))
      (p + (j' : ℕ)) (p + q + (k : ℕ))

/-- Transported coupling from coarse chamber `02` to `12`. -/
def rankTwoRightCoupling (p q r : ℕ) : ℚ :=
  ∑ i : Fin p, ∑ k : Fin r, ∑ j : Fin q, ∑ k' : Fin r,
    rankTwoOrderOrientation (i : ℕ) (p + q + (k : ℕ))
      (p + (j : ℕ)) (p + q + (k' : ℕ))

theorem rankTwoLeftCoupling_formula (p q r : ℕ) :
    rankTwoLeftCoupling p q r =
      (p : ℚ) * q * r * (p + 1) / 2 := by
  simp_rw [rankTwoLeftCoupling, rankTwo_orientation_01_02]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]
  simp_rw [← Finset.mul_sum]
  rw [show (∑ i : Fin p, ∑ i' : Fin p,
      if i ≤ i' then (1 : ℚ) else 0) = weakPairCountQ p by
    rw [weakPairCountQ, Finset.sum_comm]]
  rw [weakPairCountQ_formula]
  ring

theorem rankTwoLongCoupling_formula (p q r : ℕ) :
    rankTwoLongCoupling p q r =
      (p : ℚ) * q * r * (q - 1) / 2 := by
  simp_rw [rankTwoLongCoupling, rankTwo_orientation_01_12]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  rw [show (∑ j : Fin q, ∑ j' : Fin q,
      if j' < j then (1 : ℚ) else 0) = strictPairCountQ q by rfl]
  rw [strictPairCountQ_formula]
  ring

theorem rankTwoRightCoupling_formula (p q r : ℕ) :
    rankTwoRightCoupling p q r =
      (p : ℚ) * q * r * (r + 1) / 2 := by
  simp_rw [rankTwoRightCoupling, rankTwo_orientation_02_12]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rw [show (∑ k : Fin r, ∑ k' : Fin r,
      if k ≤ k' then (1 : ℚ) else 0) = weakPairCountQ r by
    rw [weakPairCountQ, Finset.sum_comm]]
  rw [weakPairCountQ_formula]
  ring

/-- The exact skew rank-two matrix transported by a three-fiber profile. -/
def rankTwoFiberPush (p q r : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, rankTwoLeftCoupling p q r, rankTwoLongCoupling p q r;
     -rankTwoLeftCoupling p q r, 0, rankTwoRightCoupling p q r;
     -rankTwoLongCoupling p q r, -rankTwoRightCoupling p q r, 0]

theorem rankTwoFiberPush_skew (p q r : ℕ) :
    (rankTwoFiberPush p q r).transpose = -rankTwoFiberPush p q r := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [rankTwoFiberPush]

/-- Closed form of the full parametric transported matrix. -/
theorem rankTwoFiberPush_formula (p q r : ℕ) :
    rankTwoFiberPush p q r =
      !![0, (p : ℚ) * q * r * (p + 1) / 2,
            (p : ℚ) * q * r * (q - 1) / 2;
         -((p : ℚ) * q * r * (p + 1) / 2), 0,
            (p : ℚ) * q * r * (r + 1) / 2;
         -((p : ℚ) * q * r * (q - 1) / 2),
         -((p : ℚ) * q * r * (r + 1) / 2), 0] := by
  simp [rankTwoFiberPush, rankTwoLeftCoupling_formula,
    rankTwoLongCoupling_formula, rankTwoRightCoupling_formula]

/-- The parametric law reproduces the independently enumerated native
six-event computation at the uniform profile `(2,2,2)`. -/
theorem rankTwoFiberPush_two_eq_chainSixUniform_pushforward :
    rankTwoFiberPush 2 2 2 =
      pushForwardMatrix chainSixUniformRankTwoBlock
        chainSixOrientationOperatorRankTwo := by
  rw [chainSixUniform_rankTwo_pushforward]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rankTwoFiberPush, rankTwoLeftCoupling_formula,
      rankTwoLongCoupling_formula, rankTwoRightCoupling_formula,
      chainThreeOrientationRankTwo, chainSixUniformRankTwoGenerated,
      Fin.ext_iff]

/-! ## 4. Exact scalar-closure classifications -/

/-- Rank two alone admits scalar closure precisely for a singleton middle
fiber and equal outer fibers. -/
theorem rankTwo_scalar_closure_iff_middle_singleton_outer_equal
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (∃ weight : ℚ,
      weight • rankTwoFiberPush p q r = chainThreeOrientationRankTwo) ↔
        q = 1 ∧ p = r := by
  constructor
  · rintro ⟨weight, h⟩
    have h01 := congrFun (congrFun h 0) 1
    have h02 := congrFun (congrFun h 0) 2
    have h12 := congrFun (congrFun h 1) 2
    change weight * rankTwoLeftCoupling p q r = 1 at h01
    change weight * rankTwoLongCoupling p q r = 0 at h02
    change weight * rankTwoRightCoupling p q r = 1 at h12
    rw [rankTwoLeftCoupling_formula] at h01
    rw [rankTwoLongCoupling_formula] at h02
    rw [rankTwoRightCoupling_formula] at h12
    have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
    have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
    have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
    have hbase : (0 : ℚ) < (p : ℚ) * q * r := by positivity
    have hleftpos : (0 : ℚ) <
        (p : ℚ) * q * r * (p + 1) / 2 := by positivity
    have hw : 0 < weight := by nlinarith [h01, hleftpos]
    have hqoneQ : (q : ℚ) = 1 := by nlinarith [h02]
    have hqone : q = 1 := by exact_mod_cast hqoneQ
    subst q
    constructor
    · rfl
    · have hcommon : (0 : ℚ) < weight * (p : ℚ) * r := by positivity
      have hprQ : (p : ℚ) = r := by nlinarith [h01, h12]
      exact_mod_cast hprQ
  · rintro ⟨hqone, hpr⟩
    subst q
    subst r
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
    refine ⟨2 / ((p : ℚ) ^ 2 * (p + 1)), ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [rankTwoFiberPush, rankTwoLeftCoupling_formula,
        rankTwoLongCoupling_formula, rankTwoRightCoupling_formula,
        chainThreeOrientationRankTwo, Fin.ext_iff] <;>
      field_simp [hpQ]

/-- Rank-one transport specialized to a three-fiber cardinality profile.  Its
entries are the fiber products proved abstractly by `rankOne_fiber_product`. -/
def rankOneFiberPush (p q r : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, (p : ℚ) * q, (p : ℚ) * r;
     -((p : ℚ) * q), 0, (q : ℚ) * r;
     -((p : ℚ) * r), -((q : ℚ) * r), 0]

theorem orderedOrientation_finThree :
    orderedOrientation (Fin 3) =
      !![0, 1, 1; -1, 0, 1; -1, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Profile form of the existing rank-one equal-fiber closure theorem. -/
theorem rankOne_scalar_closure_iff_uniform_profile
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (∃ weight : ℚ,
      weight • rankOneFiberPush p q r = orderedOrientation (Fin 3)) ↔
        p = q ∧ q = r := by
  rw [orderedOrientation_finThree]
  constructor
  · rintro ⟨weight, h⟩
    have h01 := congrFun (congrFun h 0) 1
    have h02 := congrFun (congrFun h 0) 2
    have h12 := congrFun (congrFun h 1) 2
    change weight * ((p : ℚ) * q) = 1 at h01
    change weight * ((p : ℚ) * r) = 1 at h02
    change weight * ((q : ℚ) * r) = 1 at h12
    have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
    have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
    have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
    have hleftpos : (0 : ℚ) < (p : ℚ) * q := by positivity
    have hw : 0 < weight := by nlinarith [h01, hleftpos]
    have hwp : 0 < weight * (p : ℚ) := by positivity
    have hwr : 0 < weight * (r : ℚ) := by positivity
    have hqrQ : (q : ℚ) = r := by nlinarith [h01, h02]
    have hpqQ : (p : ℚ) = q := by nlinarith [h02, h12]
    constructor
    · exact_mod_cast hpqQ
    · exact_mod_cast hqrQ
  · rintro ⟨hpq, hqr⟩
    subst q
    subst r
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
    refine ⟨1 / (p : ℚ) ^ 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [rankOneFiberPush, Fin.ext_iff] <;>
      field_simp [hpQ]

/-- Main no-go theorem: preserving the rank-one and rank-two orientation
profiles with independent scalar renormalizations forces every fiber to be a
singleton. -/
theorem simultaneous_multirank_scalar_closure_iff_trivial
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    ((∃ rankOneWeight : ℚ,
        rankOneWeight • rankOneFiberPush p q r = orderedOrientation (Fin 3)) ∧
      (∃ rankTwoWeight : ℚ,
        rankTwoWeight • rankTwoFiberPush p q r =
          chainThreeOrientationRankTwo)) ↔
      p = 1 ∧ q = 1 ∧ r = 1 := by
  rw [rankOne_scalar_closure_iff_uniform_profile p q r hp hq hr,
    rankTwo_scalar_closure_iff_middle_singleton_outer_equal p q r hp hq hr]
  omega

theorem no_nontrivial_simultaneous_multirank_scalar_closure
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hNontrivial : p ≠ 1 ∨ q ≠ 1 ∨ r ≠ 1) :
    ¬ ((∃ rankOneWeight : ℚ,
          rankOneWeight • rankOneFiberPush p q r = orderedOrientation (Fin 3)) ∧
        ∃ rankTwoWeight : ℚ,
          rankTwoWeight • rankTwoFiberPush p q r =
            chainThreeOrientationRankTwo) := by
  rw [simultaneous_multirank_scalar_closure_iff_trivial p q r hp hq hr]
  omega

/-! ## 5. Uniform profiles: the obstruction survives at large fiber size -/

/-- For uniform fibers, the generated-to-adjacent ratio is exactly
`1 - 2/(s+1)`.  In particular it is not suppressed as the fibers grow. -/
theorem uniform_rankTwo_generated_to_adjacent_ratio
    (s : ℕ) (hs : 0 < s) :
    rankTwoLongCoupling s s s / rankTwoLeftCoupling s s s =
      1 - 2 / ((s : ℚ) + 1) := by
  rw [rankTwoLongCoupling_formula, rankTwoLeftCoupling_formula]
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hsoneQ : (s : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hsQ, hsoneQ]
  ring

/-! ## Trust regression -/

#print axioms kFOrientationAtRank_two_total_apply
#print axioms rankTwoFiberPush_formula
#print axioms rankTwoFiberPush_two_eq_chainSixUniform_pushforward
#print axioms rankTwo_scalar_closure_iff_middle_singleton_outer_equal
#print axioms rankOne_scalar_closure_iff_uniform_profile
#print axioms simultaneous_multirank_scalar_closure_iff_trivial
#print axioms no_nontrivial_simultaneous_multirank_scalar_closure
#print axioms uniform_rankTwo_generated_to_adjacent_ratio

end UnifiedTheory.Audit.KFOrientationRankTwoFiberLaw
