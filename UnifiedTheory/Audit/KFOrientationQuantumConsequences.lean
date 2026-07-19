/-
  Audit/KFOrientationQuantumConsequences.lean

  CONDITIONAL QUANTUM CONSEQUENCES OF THE RANK-TWO ORIENTATION FLOW

  This module proves four exact consequences of the finite three-fiber law:

  * the uniform obstruction has a continuous exponential interpolation with
    beta equation u' = (1-u^2)/2 and endpoint u -> 1;
  * multiplying the real skew push by i gives an exact Hermitian three-level
    matrix, with both raw and adjacent-normalized level formulas;
  * commutator evolution from the native channel under every nontrivial
    uniform push spans exactly the full three-channel skew sector;
  * every functional depending only on the Hamiltonian characteristic
    polynomial is blind to distinct outer-reflected profiles.

  The Hamiltonian is a mathematically canonical finite matrix realization.
  No state space over causal orders, quantum measure, physical Hamiltonian,
  constraint algebra, continuum limit, or recovery of GR/QFT is asserted.
-/

import UnifiedTheory.Audit.KFOrientationRankTwoConsequences
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationQuantumConsequences

noncomputable section

open scoped BigOperators Polynomial ComplexConjugate
open UnifiedTheory.Audit.KFOrientationRankTwoFiberLaw
open UnifiedTheory.Audit.KFOrientationRankTwoConsequences
open UnifiedTheory.Audit.KFMultirankCoarseGraining

/-! Continuous interpolation of the exact uniform scale semigroup. -/

def continuousProfileParameter (ell : ℝ) : ℝ :=
  (Real.exp ell - 1) / (Real.exp ell + 1)

theorem continuousProfileParameter_hasDerivAt (ell : ℝ) :
    HasDerivAt continuousProfileParameter
      ((1 - continuousProfileParameter ell ^ 2) / 2) ell := by
  have hden : Real.exp ell + 1 ≠ 0 := by positivity
  have h := ((Real.hasDerivAt_exp ell).sub_const 1).div
    ((Real.hasDerivAt_exp ell).add_const 1) hden
  convert h using 1
  unfold continuousProfileParameter
  field_simp [hden]
  ring

theorem continuousProfileParameter_beta (ell : ℝ) :
    deriv continuousProfileParameter ell =
      (1 - continuousProfileParameter ell ^ 2) / 2 :=
  (continuousProfileParameter_hasDerivAt ell).deriv

theorem continuousProfileParameter_one_sub (ell : ℝ) :
    1 - continuousProfileParameter ell = 2 / (Real.exp ell + 1) := by
  unfold continuousProfileParameter
  have hden : Real.exp ell + 1 ≠ 0 := by positivity
  field_simp [hden]
  ring

theorem continuousProfileParameter_log_nat
    (s : ℕ) (hs : 0 < s) :
    continuousProfileParameter (Real.log s) = uniformProfileParameterReal s := by
  unfold continuousProfileParameter uniformProfileParameterReal uniformProfileParameter
  rw [Real.exp_log]
  · norm_num
  · exact_mod_cast hs

theorem continuousProfileParameter_tendsto_one :
    Filter.Tendsto continuousProfileParameter Filter.atTop (nhds 1) := by
  have hden : Filter.Tendsto (fun ell : ℝ => Real.exp ell + 1)
      Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.atTop_add tendsto_const_nhds
  have hinv : Filter.Tendsto (fun ell : ℝ => (Real.exp ell + 1)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hsmall : Filter.Tendsto (fun ell : ℝ => 2 / (Real.exp ell + 1))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  have hmain : Filter.Tendsto
      (fun ell : ℝ => 1 - 2 / (Real.exp ell + 1))
      Filter.atTop (nhds (1 - 0)) := hone.sub hsmall
  convert hmain using 1
  · funext ell
    have h := continuousProfileParameter_one_sub ell
    linarith
  · norm_num

/-! Hermitian realization and its exact three-level polynomial. -/

def skewHamiltonian (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, Complex.I * x, Complex.I * y;
     -(Complex.I * x), 0, Complex.I * z;
     -(Complex.I * y), -(Complex.I * z), 0]

theorem skewHamiltonian_isHermitian (x y z : ℝ) :
    (skewHamiltonian x y z).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewHamiltonian, Matrix.conjTranspose_apply]

theorem skewHamiltonian_charpoly_eval (x y z : ℝ) (t : ℂ) :
    (skewHamiltonian x y z).charpoly.eval t =
      t * (t ^ 2 - ((x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ)) := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  norm_num [skewHamiltonian, Matrix.scalar_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem skewHamiltonian_charpoly (x y z : ℝ) :
    (skewHamiltonian x y z).charpoly =
      Polynomial.X ^ 3 -
        Polynomial.C ((x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ) * Polynomial.X := by
  apply Polynomial.funext
  intro t
  rw [skewHamiltonian_charpoly_eval]
  simp
  ring

def orientationHamiltonian (p q r : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  skewHamiltonian (rankTwoLeftCoupling p q r : ℝ)
    (rankTwoLongCoupling p q r : ℝ) (rankTwoRightCoupling p q r : ℝ)

theorem orientationHamiltonian_eq_I_smul_push (p q r : ℕ) :
    orientationHamiltonian p q r =
      Complex.I • (rankTwoFiberPush p q r).map (Rat.castHom ℂ) := by
  rw [rankTwoFiberPush_as_skewMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orientationHamiltonian, skewHamiltonian, skewMatrix,
      Fin.ext_iff]

theorem orientationHamiltonian_isHermitian (p q r : ℕ) :
    (orientationHamiltonian p q r).IsHermitian :=
  skewHamiltonian_isHermitian _ _ _

theorem orientationHamiltonian_charpoly (p q r : ℕ) :
    (orientationHamiltonian p q r).charpoly =
      Polynomial.X ^ 3 -
        Polynomial.C
          (((rankTwoLeftCoupling p q r : ℝ) ^ 2 +
            (rankTwoLongCoupling p q r : ℝ) ^ 2 +
            (rankTwoRightCoupling p q r : ℝ) ^ 2 : ℝ) : ℂ) *
          Polynomial.X := by
  exact skewHamiltonian_charpoly _ _ _

def normalizedUniformHamiltonian (s : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  skewHamiltonian 1 (uniformProfileParameterReal s) 1

def normalizedLevelRadius (s : ℕ) : ℝ :=
  Real.sqrt (2 + uniformProfileParameterReal s ^ 2)

theorem normalizedLevelRadius_sq (s : ℕ) :
    normalizedLevelRadius s ^ 2 = 2 + uniformProfileParameterReal s ^ 2 := by
  unfold normalizedLevelRadius
  rw [Real.sq_sqrt]
  positivity

theorem normalizedUniformHamiltonian_isHermitian (s : ℕ) :
    (normalizedUniformHamiltonian s).IsHermitian :=
  skewHamiltonian_isHermitian _ _ _

theorem normalizedUniformHamiltonian_charpoly (s : ℕ) :
    (normalizedUniformHamiltonian s).charpoly =
      Polynomial.X ^ 3 -
        Polynomial.C (((2 + uniformProfileParameterReal s ^ 2 : ℝ) : ℂ)) *
          Polynomial.X := by
  apply Polynomial.funext
  intro t
  rw [normalizedUniformHamiltonian, skewHamiltonian_charpoly_eval]
  simp
  ring

theorem normalizedUniformHamiltonian_three_roots (s : ℕ) :
    (normalizedUniformHamiltonian s).charpoly.eval 0 = 0
    ∧ (normalizedUniformHamiltonian s).charpoly.eval
        (normalizedLevelRadius s : ℂ) = 0
    ∧ (normalizedUniformHamiltonian s).charpoly.eval
        (-(normalizedLevelRadius s : ℂ)) = 0 := by
  rw [normalizedUniformHamiltonian_charpoly]
  have hr := normalizedLevelRadius_sq s
  have hrC : (normalizedLevelRadius s : ℂ) ^ 2 =
      ((2 + uniformProfileParameterReal s ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast hr
  constructor
  · simp
  · constructor
    · simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_C]
      calc
        (normalizedLevelRadius s : ℂ) ^ 3 -
              ((2 + uniformProfileParameterReal s ^ 2 : ℝ) : ℂ) *
                normalizedLevelRadius s =
            (normalizedLevelRadius s : ℂ) *
              ((normalizedLevelRadius s : ℂ) ^ 2 -
                ((2 + uniformProfileParameterReal s ^ 2 : ℝ) : ℂ)) := by ring
        _ = 0 := by rw [hrC]; ring
    · simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_C]
      calc
        (-(normalizedLevelRadius s : ℂ)) ^ 3 -
              ((2 + uniformProfileParameterReal s ^ 2 : ℝ) : ℂ) *
                (-(normalizedLevelRadius s : ℂ)) =
            -(normalizedLevelRadius s : ℂ) *
              ((normalizedLevelRadius s : ℂ) ^ 2 -
                ((2 + uniformProfileParameterReal s ^ 2 : ℝ) : ℂ)) := by ring
        _ = 0 := by rw [hrC]; ring

def uniformLevelRadiusSq (s : ℕ) : ℚ :=
  2 * uniformNativeCoefficient s ^ 2 + uniformLongCoefficient s ^ 2

theorem uniformLevelRadiusSq_formula (s : ℕ) :
    uniformLevelRadiusSq s =
      (s : ℚ) ^ 6 / 4 * (3 * (s : ℚ) ^ 2 + 2 * s + 3) := by
  unfold uniformLevelRadiusSq uniformNativeCoefficient uniformLongCoefficient
  ring

def uniformLevelRadius (s : ℕ) : ℝ :=
  Real.sqrt (uniformLevelRadiusSq s : ℝ)

theorem uniformLevelRadius_sq (s : ℕ) :
    uniformLevelRadius s ^ 2 = (uniformLevelRadiusSq s : ℝ) := by
  unfold uniformLevelRadius uniformLevelRadiusSq
  rw [Real.sq_sqrt]
  push_cast
  positivity

theorem uniformOrientationHamiltonian_charpoly (s : ℕ) :
    (orientationHamiltonian s s s).charpoly =
      Polynomial.X ^ 3 -
        Polynomial.C (((uniformLevelRadiusSq s : ℚ) : ℂ)) * Polynomial.X := by
  rw [orientationHamiltonian_charpoly]
  have hQ : rankTwoLeftCoupling s s s ^ 2 +
        rankTwoLongCoupling s s s ^ 2 + rankTwoRightCoupling s s s ^ 2 =
      uniformLevelRadiusSq s := by
    unfold uniformLevelRadiusSq uniformNativeCoefficient uniformLongCoefficient
    rw [rankTwoLeftCoupling_formula, rankTwoLongCoupling_formula,
      rankTwoRightCoupling_formula]
    ring
  have hC :
      (((rankTwoLeftCoupling s s s : ℝ) ^ 2 +
        (rankTwoLongCoupling s s s : ℝ) ^ 2 +
        (rankTwoRightCoupling s s s : ℝ) ^ 2 : ℝ) : ℂ) =
          ((uniformLevelRadiusSq s : ℚ) : ℂ) := by
    exact_mod_cast hQ
  rw [hC]

theorem uniformOrientationHamiltonian_three_roots (s : ℕ) :
    (orientationHamiltonian s s s).charpoly.eval 0 = 0
    ∧ (orientationHamiltonian s s s).charpoly.eval
        (uniformLevelRadius s : ℂ) = 0
    ∧ (orientationHamiltonian s s s).charpoly.eval
        (-(uniformLevelRadius s : ℂ)) = 0 := by
  rw [uniformOrientationHamiltonian_charpoly]
  have hr := uniformLevelRadius_sq s
  have hrC : (uniformLevelRadius s : ℂ) ^ 2 =
      ((uniformLevelRadiusSq s : ℚ) : ℂ) := by
    exact_mod_cast hr
  constructor
  · simp
  · constructor
    · simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_C]
      calc
        (uniformLevelRadius s : ℂ) ^ 3 -
              ((uniformLevelRadiusSq s : ℚ) : ℂ) * uniformLevelRadius s =
            (uniformLevelRadius s : ℂ) *
              ((uniformLevelRadius s : ℂ) ^ 2 -
                ((uniformLevelRadiusSq s : ℚ) : ℂ)) := by ring
        _ = 0 := by rw [hrC]; ring
    · simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_C]
      calc
        (-(uniformLevelRadius s : ℂ)) ^ 3 -
              ((uniformLevelRadiusSq s : ℚ) : ℂ) *
                (-(uniformLevelRadius s : ℂ)) =
            -(uniformLevelRadius s : ℂ) *
              ((uniformLevelRadius s : ℂ) ^ 2 -
                ((uniformLevelRadiusSq s : ℚ) : ℂ)) := by ring
        _ = 0 := by rw [hrC]; ring

/-! Exact finite commutator/Krylov closure. -/

def uniformFirstHeisenbergStep (s : ℕ) : SkewThree :=
  matrixCommutator (rankTwoFiberPush s s s) nativeChannel

def uniformSecondHeisenbergStep (s : ℕ) : SkewThree :=
  matrixCommutator (rankTwoFiberPush s s s) (uniformFirstHeisenbergStep s)

theorem uniformFirstHeisenbergStep_formula (s : ℕ) :
    uniformFirstHeisenbergStep s =
      -(uniformLongCoefficient s) • imbalanceChannel := by
  unfold uniformFirstHeisenbergStep
  rw [uniform_rankTwoFiberPush_decomposition]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixCommutator, uniformNativeCoefficient,
      uniformLongCoefficient, nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.ext_iff]

theorem uniformSecondHeisenbergStep_formula (s : ℕ) :
    uniformSecondHeisenbergStep s =
      -(uniformLongCoefficient s ^ 2) • nativeChannel +
        (2 * uniformNativeCoefficient s * uniformLongCoefficient s) •
          longChannel := by
  unfold uniformSecondHeisenbergStep
  rw [uniformFirstHeisenbergStep_formula,
    uniform_rankTwoFiberPush_decomposition]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixCommutator, uniformNativeCoefficient,
      uniformLongCoefficient, nativeChannel, longChannel, imbalanceChannel,
      chainThreeOrientationRankTwo, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.ext_iff] <;> ring

theorem uniformNativeCoefficient_ne_zero (s : ℕ) (hs : 1 < s) :
    uniformNativeCoefficient s ≠ 0 := by
  have hs0 : (0 : ℚ) < s := by exact_mod_cast (by omega : 0 < s)
  unfold uniformNativeCoefficient
  positivity

theorem uniform_heisenberg_krylov_spans_full_skew
    (s : ℕ) (hs : 1 < s) :
    ∀ x y z : ℚ, ∃ a b c : ℚ,
      skewMatrix x y z =
        a • nativeChannel + b • uniformFirstHeisenbergStep s +
          c • uniformSecondHeisenbergStep s := by
  intro x y z
  have hα := uniformNativeCoefficient_ne_zero s hs
  have hβ := uniformLongCoefficient_ne_zero s hs
  let a := (x + z) / 2 + uniformLongCoefficient s * y /
    (2 * uniformNativeCoefficient s)
  let b := -((x - z) / 2) / uniformLongCoefficient s
  let c := y / (2 * uniformNativeCoefficient s * uniformLongCoefficient s)
  refine ⟨a, b, c, ?_⟩
  rw [uniformFirstHeisenbergStep_formula, uniformSecondHeisenbergStep_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a, b, c, skewMatrix, nativeChannel, longChannel,
      imbalanceChannel, chainThreeOrientationRankTwo, Fin.ext_iff] <;>
    field_simp [hα, hβ] <;> ring

/-! Universal spectral-functional no-go. -/

theorem orientationHamiltonian_outer_reflection_charpoly (p q r : ℕ) :
    (orientationHamiltonian p q r).charpoly =
      (orientationHamiltonian r q p).charpoly := by
  rw [orientationHamiltonian_charpoly, orientationHamiltonian_charpoly]
  rw [rankTwoLeftCoupling_formula, rankTwoLongCoupling_formula,
    rankTwoRightCoupling_formula, rankTwoLeftCoupling_formula,
    rankTwoLongCoupling_formula, rankTwoRightCoupling_formula]
  congr 2
  push_cast
  ring_nf

theorem every_hamiltonian_charpoly_functional_blind
    {X : Type*} (F : Polynomial ℂ → X) (p q r : ℕ) :
    F (orientationHamiltonian p q r).charpoly =
      F (orientationHamiltonian r q p).charpoly := by
  rw [orientationHamiltonian_outer_reflection_charpoly]

theorem orientationHamiltonian_matrix_ne_of_outer_ne
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≠ r) :
    orientationHamiltonian p q r ≠ orientationHamiltonian r q p := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  change Complex.I * (rankTwoLeftCoupling p q r : ℝ) =
    Complex.I * (rankTwoLeftCoupling r q p : ℝ) at h01
  have hcast : (rankTwoLeftCoupling p q r : ℝ) =
      (rankTwoLeftCoupling r q p : ℝ) := by
    have hc : ((rankTwoLeftCoupling p q r : ℝ) : ℂ) =
        ((rankTwoLeftCoupling r q p : ℝ) : ℂ) :=
      mul_left_cancel₀ Complex.I_ne_zero h01
    exact Complex.ofReal_injective hc
  rw [rankTwoLeftCoupling_formula, rankTwoLeftCoupling_formula] at hcast
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  push_cast at hcast
  let base : ℝ := p * q * r
  have hbase : base ≠ 0 := by
    unfold base
    positivity
  have hcast' : base * ((p : ℝ) + 1) / 2 =
      base * ((r : ℝ) + 1) / 2 := by
    simpa [base, mul_comm, mul_left_comm, mul_assoc] using hcast
  have hprod : base * ((p : ℝ) + 1) = base * ((r : ℝ) + 1) := by
    linarith
  have hsum : (p : ℝ) + 1 = (r : ℝ) + 1 :=
    mul_left_cancel₀ hbase hprod
  have hprR : (p : ℝ) = r := by linarith
  exact hpr (by exact_mod_cast hprR)

theorem spectral_functional_blind_to_distinct_hamiltonians
    {X : Type*} (F : Polynomial ℂ → X)
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≠ r) :
    orientationHamiltonian p q r ≠ orientationHamiltonian r q p
      ∧ F (orientationHamiltonian p q r).charpoly =
        F (orientationHamiltonian r q p).charpoly :=
  ⟨orientationHamiltonian_matrix_ne_of_outer_ne p q r hp hq hr hpr,
    every_hamiltonian_charpoly_functional_blind F p q r⟩

end

/-! ## Trust regression -/

#print axioms continuousProfileParameter_beta
#print axioms continuousProfileParameter_tendsto_one
#print axioms orientationHamiltonian_eq_I_smul_push
#print axioms orientationHamiltonian_isHermitian
#print axioms normalizedUniformHamiltonian_three_roots
#print axioms uniformLevelRadiusSq_formula
#print axioms uniformOrientationHamiltonian_three_roots
#print axioms uniform_heisenberg_krylov_spans_full_skew
#print axioms every_hamiltonian_charpoly_functional_blind
#print axioms spectral_functional_blind_to_distinct_hamiltonians

end UnifiedTheory.Audit.KFOrientationQuantumConsequences
