/-
  Audit/KFOrientationRankTwoConsequences.lean

  OPERATOR ALGEBRA, SCALE SEMIGROUP, TOMOGRAPHY, AND SPECTRAL LIMIT

  Consequences of the parametric rank-two three-fiber law:

  * the native, generated-long-range, and outer-imbalance channels form a
    unique three-coordinate skew basis and close under matrix commutators;
  * every nontrivial uniform push together with the native channel recovers
    that full basis;
  * the uniform obstruction parameter obeys an exact Mobius composition law,
    with multiplicative inverse coordinate and half-log rapidity;
  * rank-two/rank-one coupling ratios reconstruct every positive fiber profile
    and obey odd-square integrality certificates;
  * the skew characteristic polynomial retains only the squared coupling norm,
    so reflected unequal profiles are distinct matrices with equal charpoly.

  These are finite rational-matrix statements.  They do not assert a physical
  gauge group, a continuum spectrum, or a dynamical renormalization flow.
-/

import UnifiedTheory.Audit.KFOrientationRankTwoFiberLaw
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationRankTwoConsequences

open scoped BigOperators Polynomial
open UnifiedTheory.Audit.KFOrientationRankTwoFiberLaw
open UnifiedTheory.Audit.KFMultirankCoarseGraining

/-! ## 1. Three-channel operator algebra -/

/-- Rational three-by-three chamber-orientation matrices. -/
abbrev SkewThree := Matrix (Fin 3) (Fin 3) ℚ

def nativeChannel : SkewThree := chainThreeOrientationRankTwo

def longChannel : SkewThree :=
  !![0, 0, 1; 0, 0, 0; -1, 0, 0]

def imbalanceChannel : SkewThree :=
  !![0, 1, 0; -1, 0, -1; 0, 1, 0]

def skewMatrix (x y z : ℚ) : SkewThree :=
  !![0, x, y; -x, 0, z; -y, -z, 0]

def matrixCommutator (A B : SkewThree) : SkewThree := A * B - B * A

def nativeCoefficient (p q r : ℕ) : ℚ :=
  (p : ℚ) * q * r * (p + r + 2) / 4

def longCoefficient (p q r : ℕ) : ℚ :=
  (p : ℚ) * q * r * (q - 1) / 2

def imbalanceCoefficient (p q r : ℕ) : ℚ :=
  (p : ℚ) * q * r * (p - r) / 4

theorem rankTwoFiberPush_decomposition (p q r : ℕ) :
    rankTwoFiberPush p q r =
      nativeCoefficient p q r • nativeChannel +
        longCoefficient p q r • longChannel +
          imbalanceCoefficient p q r • imbalanceChannel := by
  rw [rankTwoFiberPush_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nativeCoefficient, longCoefficient, imbalanceCoefficient,
      nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Fin.ext_iff] <;> ring

theorem longCoefficient_eq_zero_iff
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    longCoefficient p q r = 0 ↔ q = 1 := by
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hbase : (0 : ℚ) < (p : ℚ) * q * r := by positivity
  constructor
  · intro h
    unfold longCoefficient at h
    have hqOneQ : (q : ℚ) = 1 := by nlinarith
    exact_mod_cast hqOneQ
  · rintro rfl
    simp [longCoefficient]

theorem imbalanceCoefficient_eq_zero_iff
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    imbalanceCoefficient p q r = 0 ↔ p = r := by
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hbase : (0 : ℚ) < (p : ℚ) * q * r := by positivity
  constructor
  · intro h
    unfold imbalanceCoefficient at h
    have hprQ : (p : ℚ) = r := by nlinarith
    exact_mod_cast hprQ
  · rintro rfl
    simp [imbalanceCoefficient]

theorem commutator_native_long :
    matrixCommutator nativeChannel longChannel = imbalanceChannel := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixCommutator, nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.ext_iff]

theorem commutator_long_imbalance :
    matrixCommutator longChannel imbalanceChannel = nativeChannel := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixCommutator, nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.ext_iff]

theorem commutator_imbalance_native :
    matrixCommutator imbalanceChannel nativeChannel = (2 : ℚ) • longChannel := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixCommutator, nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.ext_iff]

theorem skewMatrix_channel_decomposition (x y z : ℚ) :
    skewMatrix x y z =
      ((x + z) / 2) • nativeChannel + y • longChannel +
        ((x - z) / 2) • imbalanceChannel := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewMatrix, nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Fin.ext_iff] <;> ring

theorem channel_coordinates_unique (a b c a' b' c' : ℚ) :
    a • nativeChannel + b • longChannel + c • imbalanceChannel =
      a' • nativeChannel + b' • longChannel + c' • imbalanceChannel ↔
        a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    have h02 := congrFun (congrFun h 0) 2
    have h12 := congrFun (congrFun h 1) 2
    norm_num [nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff] at h01 h02 h12
    change a + c = a' + c' at h01
    change b = b' at h02
    constructor
    · linarith
    · constructor
      · exact h02
      · linarith
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-! ## 2. Uniform profiles generate the full skew basis -/

def uniformNativeCoefficient (s : ℕ) : ℚ :=
  (s : ℚ) ^ 3 * ((s : ℚ) + 1) / 2

def uniformLongCoefficient (s : ℕ) : ℚ :=
  (s : ℚ) ^ 3 * ((s : ℚ) - 1) / 2

theorem uniform_rankTwoFiberPush_decomposition (s : ℕ) :
    rankTwoFiberPush s s s =
      uniformNativeCoefficient s • nativeChannel +
        uniformLongCoefficient s • longChannel := by
  rw [rankTwoFiberPush_decomposition]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nativeCoefficient, longCoefficient, imbalanceCoefficient,
      uniformNativeCoefficient, uniformLongCoefficient,
      nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Fin.ext_iff] <;> ring_nf <;> simp

theorem uniform_native_push_commutator (s : ℕ) :
    matrixCommutator nativeChannel (rankTwoFiberPush s s s) =
      uniformLongCoefficient s • imbalanceChannel := by
  rw [uniform_rankTwoFiberPush_decomposition]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixCommutator, uniformNativeCoefficient,
      uniformLongCoefficient, nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.ext_iff]

theorem uniformLongCoefficient_ne_zero (s : ℕ) (hs : 1 < s) :
    uniformLongCoefficient s ≠ 0 := by
  have hsQ : (0 : ℚ) < s := by exact_mod_cast (by omega : 0 < s)
  have hsoneQ : (1 : ℚ) < s := by exact_mod_cast hs
  have hsmQ : (0 : ℚ) < (s : ℚ) - 1 := by linarith
  unfold uniformLongCoefficient
  positivity

theorem uniform_native_and_push_recover_full_skew_basis
    (s : ℕ) (hs : 1 < s) :
    longChannel =
        (uniformLongCoefficient s)⁻¹ •
          (rankTwoFiberPush s s s - uniformNativeCoefficient s • nativeChannel)
    ∧ imbalanceChannel =
        (uniformLongCoefficient s)⁻¹ •
          matrixCommutator nativeChannel (rankTwoFiberPush s s s)
    ∧ ∀ x y z : ℚ, ∃ a b c : ℚ,
        skewMatrix x y z =
          a • nativeChannel + b • longChannel + c • imbalanceChannel := by
  have hβ := uniformLongCoefficient_ne_zero s hs
  constructor
  · rw [uniform_rankTwoFiberPush_decomposition]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nativeChannel, longChannel, chainThreeOrientationRankTwo,
        Fin.ext_iff] <;> field_simp [hβ]
  · constructor
    · rw [uniform_native_push_commutator]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [imbalanceChannel, Fin.ext_iff] <;> field_simp [hβ]
    · intro x y z
      exact ⟨(x + z) / 2, y, (x - z) / 2,
        skewMatrix_channel_decomposition x y z⟩

/-! ## 3. Exact Mobius scale semigroup -/

/-- Normalized generated-to-adjacent coupling for a uniform fiber. -/
def uniformProfileParameter (s : ℕ) : ℚ :=
  ((s : ℚ) - 1) / ((s : ℚ) + 1)

theorem uniformProfileParameter_eq_coupling_ratio
    (s : ℕ) (hs : 0 < s) :
    uniformProfileParameter s =
      rankTwoLongCoupling s s s / rankTwoLeftCoupling s s s := by
  rw [uniform_rankTwo_generated_to_adjacent_ratio s hs]
  unfold uniformProfileParameter
  have hsplus : (s : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hsplus]
  ring

theorem uniformProfileParameter_mul
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    uniformProfileParameter (s * t) =
      (uniformProfileParameter s + uniformProfileParameter t) /
        (1 + uniformProfileParameter s * uniformProfileParameter t) := by
  have hsone : 1 ≤ s := hs
  have htone : 1 ≤ t := ht
  have hsQ : (1 : ℚ) ≤ s := by exact_mod_cast hsone
  have htQ : (1 : ℚ) ≤ t := by exact_mod_cast htone
  have hus : 0 ≤ uniformProfileParameter s := by
    unfold uniformProfileParameter
    exact div_nonneg (by linarith) (by positivity)
  have hut : 0 ≤ uniformProfileParameter t := by
    unfold uniformProfileParameter
    exact div_nonneg (by linarith) (by positivity)
  have hsplus : (s : ℚ) + 1 ≠ 0 := by positivity
  have htplus : (t : ℚ) + 1 ≠ 0 := by positivity
  have hstplus : ((s * t : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  have hden :
      1 + uniformProfileParameter s * uniformProfileParameter t ≠ 0 := by
    positivity
  apply (eq_div_iff hden).2
  unfold uniformProfileParameter
  push_cast
  field_simp [hsplus, htplus, hstplus]
  ring

theorem uniformProfileParameter_inverse
    (s : ℕ) (hs : 0 < s) :
    (1 + uniformProfileParameter s) /
        (1 - uniformProfileParameter s) = (s : ℚ) := by
  have hsplus : (s : ℚ) + 1 ≠ 0 := by positivity
  have huLt : uniformProfileParameter s < 1 := by
    unfold uniformProfileParameter
    apply (div_lt_one (by positivity)).2
    linarith
  have hden : 1 - uniformProfileParameter s ≠ 0 :=
    ne_of_gt (sub_pos.mpr huLt)
  apply (div_eq_iff hden).2
  unfold uniformProfileParameter
  field_simp [hsplus]
  ring

def uniformProfileParameterReal (s : ℕ) : ℝ :=
  (uniformProfileParameter s : ℝ)

theorem uniformProfileParameterReal_inverse
    (s : ℕ) (hs : 0 < s) :
    (1 + uniformProfileParameterReal s) /
        (1 - uniformProfileParameterReal s) = (s : ℝ) := by
  have hQ := uniformProfileParameter_inverse s hs
  unfold uniformProfileParameterReal
  exact_mod_cast hQ

theorem uniformProfileRapidity
    (s : ℕ) (hs : 0 < s) :
    (1 / 2 : ℝ) * Real.log
        ((1 + uniformProfileParameterReal s) /
          (1 - uniformProfileParameterReal s)) =
      (1 / 2 : ℝ) * Real.log (s : ℝ) := by
  rw [uniformProfileParameterReal_inverse s hs]

theorem uniformProfileParameter_pos
    (s : ℕ) (hs : 1 < s) : 0 < uniformProfileParameter s := by
  have hsQ : (1 : ℚ) < s := by exact_mod_cast hs
  unfold uniformProfileParameter
  exact div_pos (by linarith) (by positivity)

theorem uniformMobius_fixed_points
    (t : ℕ) (ht : 1 < t) (x : ℚ)
    (hden : 1 + x * uniformProfileParameter t ≠ 0) :
    x = (x + uniformProfileParameter t) /
          (1 + x * uniformProfileParameter t) ↔
      x = 1 ∨ x = -1 := by
  have huPos := uniformProfileParameter_pos t ht
  have hu : uniformProfileParameter t ≠ 0 := ne_of_gt huPos
  constructor
  · intro h
    field_simp [hden] at h
    have hfactor : uniformProfileParameter t * (x ^ 2 - 1) = 0 := by
      nlinarith
    have hxSq : x ^ 2 = 1 := by
      rcases mul_eq_zero.mp hfactor with hzero | hsq
      · exact (hu hzero).elim
      · linarith
    have hsplit : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hsplit with hx | hx
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · apply (eq_div_iff hden).2
      ring
    · apply (eq_div_iff hden).2
      ring

/-! ## 4. Cross-rank fiber tomography -/

theorem left_crossRank_tomography
    (p q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    rankTwoLeftCoupling p q r / rankOneFiberPush p q r 1 2 =
      (p : ℚ) * ((p : ℚ) + 1) / 2 := by
  change rankTwoLeftCoupling p q r / ((q : ℚ) * r) = _
  rw [rankTwoLeftCoupling_formula]
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  field_simp [hqQ, hrQ]

theorem middle_crossRank_tomography
    (p q r : ℕ) (hp : 0 < p) (hr : 0 < r) :
    rankTwoLongCoupling p q r / rankOneFiberPush p q r 0 2 =
      (q : ℚ) * ((q : ℚ) - 1) / 2 := by
  change rankTwoLongCoupling p q r / ((p : ℚ) * r) = _
  rw [rankTwoLongCoupling_formula]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  field_simp [hpQ, hrQ]

theorem right_crossRank_tomography
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) :
    rankTwoRightCoupling p q r / rankOneFiberPush p q r 0 1 =
      (r : ℚ) * ((r : ℚ) + 1) / 2 := by
  change rankTwoRightCoupling p q r / ((p : ℚ) * q) = _
  rw [rankTwoRightCoupling_formula]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hpQ, hqQ]

def fiberTomographySignature (p q r : ℕ) : ℚ × ℚ × ℚ :=
  ((p : ℚ) * ((p : ℚ) + 1) / 2,
    (q : ℚ) * ((q : ℚ) - 1) / 2,
    (r : ℚ) * ((r : ℚ) + 1) / 2)

theorem multirank_tomography_ratios
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (rankTwoLeftCoupling p q r / rankOneFiberPush p q r 1 2,
      rankTwoLongCoupling p q r / rankOneFiberPush p q r 0 2,
      rankTwoRightCoupling p q r / rankOneFiberPush p q r 0 1) =
        fiberTomographySignature p q r := by
  rw [left_crossRank_tomography p q r hq hr,
    middle_crossRank_tomography p q r hp hr,
    right_crossRank_tomography p q r hp hq]
  rfl

theorem fiberTomographySignature_injective_on_positive
    {p q r p' q' r' : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hp' : 0 < p') (hq' : 0 < q') (hr' : 0 < r')
    (h : fiberTomographySignature p q r =
      fiberTomographySignature p' q' r') :
    p = p' ∧ q = q' ∧ r = r' := by
  have hP := congrArg Prod.fst h
  have hQ := congrArg (fun x => x.2.1) h
  have hR := congrArg (fun x => x.2.2) h
  simp only [fiberTomographySignature] at hP hQ hR
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hpQ' : (0 : ℚ) < p' := by exact_mod_cast hp'
  have hqQ' : (0 : ℚ) < q' := by exact_mod_cast hq'
  have hrQ' : (0 : ℚ) < r' := by exact_mod_cast hr'
  have hqOneQ : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hqOneQ' : (1 : ℚ) ≤ q' := by exact_mod_cast hq'
  have hpEqQ : (p : ℚ) = p' := by nlinarith [hP]
  have hqEqQ : (q : ℚ) = q' := by nlinarith [hQ]
  have hrEqQ : (r : ℚ) = r' := by nlinarith [hR]
  constructor
  · exact_mod_cast hpEqQ
  · constructor
    · exact_mod_cast hqEqQ
    · exact_mod_cast hrEqQ

theorem multirank_tomography_odd_square_certificates
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    1 + 8 *
        (rankTwoLeftCoupling p q r / rankOneFiberPush p q r 1 2) =
          (2 * (p : ℚ) + 1) ^ 2
    ∧ 1 + 8 *
        (rankTwoLongCoupling p q r / rankOneFiberPush p q r 0 2) =
          (2 * (q : ℚ) - 1) ^ 2
    ∧ 1 + 8 *
        (rankTwoRightCoupling p q r / rankOneFiberPush p q r 0 1) =
          (2 * (r : ℚ) + 1) ^ 2 := by
  rw [left_crossRank_tomography p q r hq hr,
    middle_crossRank_tomography p q r hp hr,
    right_crossRank_tomography p q r hp hq]
  constructor
  · ring
  · constructor <;> ring

/-! ## 5. Spectral blind spot under outer-fiber reflection -/

theorem skewMatrix_charpoly_eval (x y z t : ℚ) :
    (skewMatrix x y z).charpoly.eval t =
      t * (t ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  norm_num [skewMatrix, Matrix.scalar_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff]
  ring

theorem skewMatrix_charpoly (x y z : ℚ) :
    (skewMatrix x y z).charpoly =
      Polynomial.X ^ 3 +
        Polynomial.C (x ^ 2 + y ^ 2 + z ^ 2) * Polynomial.X := by
  apply Polynomial.funext
  intro t
  rw [skewMatrix_charpoly_eval]
  simp
  ring

theorem rankTwoFiberPush_as_skewMatrix (p q r : ℕ) :
    rankTwoFiberPush p q r =
      skewMatrix (rankTwoLeftCoupling p q r)
        (rankTwoLongCoupling p q r) (rankTwoRightCoupling p q r) := by
  rfl

theorem rankTwoFiberPush_charpoly (p q r : ℕ) :
    (rankTwoFiberPush p q r).charpoly =
      Polynomial.X ^ 3 +
        Polynomial.C
          (rankTwoLeftCoupling p q r ^ 2 +
            rankTwoLongCoupling p q r ^ 2 +
            rankTwoRightCoupling p q r ^ 2) * Polynomial.X := by
  rw [rankTwoFiberPush_as_skewMatrix, skewMatrix_charpoly]

theorem outerFiberReflection_decomposition (p q r : ℕ) :
    rankTwoFiberPush r q p =
      nativeCoefficient p q r • nativeChannel +
        longCoefficient p q r • longChannel -
          imbalanceCoefficient p q r • imbalanceChannel := by
  rw [rankTwoFiberPush_decomposition]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nativeCoefficient, longCoefficient, imbalanceCoefficient,
      nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Fin.ext_iff] <;> ring_nf <;> simp

theorem outerFiberReflection_charpoly_invariant (p q r : ℕ) :
    (rankTwoFiberPush p q r).charpoly =
      (rankTwoFiberPush r q p).charpoly := by
  rw [rankTwoFiberPush_charpoly, rankTwoFiberPush_charpoly]
  rw [rankTwoLeftCoupling_formula, rankTwoLongCoupling_formula,
    rankTwoRightCoupling_formula, rankTwoLeftCoupling_formula,
    rankTwoLongCoupling_formula, rankTwoRightCoupling_formula]
  congr 2
  ring_nf

theorem outerFiberReflection_matrix_ne_of_ne
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≠ r) :
    rankTwoFiberPush p q r ≠ rankTwoFiberPush r q p := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  change rankTwoLeftCoupling p q r = rankTwoLeftCoupling r q p at h01
  rw [rankTwoLeftCoupling_formula, rankTwoLeftCoupling_formula] at h01
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hbase : (0 : ℚ) < (p : ℚ) * q * r := by positivity
  have hprQ : (p : ℚ) = r := by nlinarith [h01]
  have : p = r := by exact_mod_cast hprQ
  exact hpr this

theorem outerFiberReflection_spectral_blind_spot
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≠ r) :
    rankTwoFiberPush p q r ≠ rankTwoFiberPush r q p
      ∧ (rankTwoFiberPush p q r).charpoly =
        (rankTwoFiberPush r q p).charpoly :=
  ⟨outerFiberReflection_matrix_ne_of_ne p q r hp hq hr hpr,
    outerFiberReflection_charpoly_invariant p q r⟩

/-! ## Trust regression -/

#print axioms rankTwoFiberPush_decomposition
#print axioms commutator_native_long
#print axioms uniform_native_and_push_recover_full_skew_basis
#print axioms uniformProfileParameter_mul
#print axioms uniformProfileRapidity
#print axioms fiberTomographySignature_injective_on_positive
#print axioms multirank_tomography_odd_square_certificates
#print axioms rankTwoFiberPush_charpoly
#print axioms outerFiberReflection_spectral_blind_spot

end UnifiedTheory.Audit.KFOrientationRankTwoConsequences
