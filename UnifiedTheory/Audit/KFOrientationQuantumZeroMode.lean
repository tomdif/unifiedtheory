/-
  Audit/KFOrientationQuantumZeroMode.lean

  ZERO-MODE GEOMETRY AND FINITE POLYNOMIAL CLOSURE

  The Hermitian rank-two orientation model has an exact protected zero mode.
  Its endpoint asymmetry is precisely twice the outer-imbalance coefficient,
  so it retains the reflection sign erased by the characteristic polynomial.
  Unequal outer-reflected profiles are isospectral but have different kernels.

  The same Hamiltonian obeys a cubic identity, has an exact quadratic Casimir,
  and reduces every polynomial observable to degree below three.  These are
  finite matrix statements, not a graviton, physical constraint equation, or
  continuum quantum-gravity dynamics.
-/

import UnifiedTheory.Audit.KFOrientationQuantumConsequences
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationQuantumZeroMode

noncomputable section

open scoped BigOperators Polynomial ComplexConjugate
open UnifiedTheory.Audit.KFOrientationRankTwoFiberLaw
open UnifiedTheory.Audit.KFOrientationRankTwoConsequences
open UnifiedTheory.Audit.KFOrientationQuantumConsequences

/-! ## 1. Generic protected zero mode -/

def skewHamiltonianZeroMode (x y z : ℝ) : Fin 3 → ℂ :=
  ![(z : ℂ), -(y : ℂ), (x : ℂ)]

theorem skewHamiltonian_mulVec_zeroMode (x y z : ℝ) :
    (skewHamiltonian x y z).mulVec (skewHamiltonianZeroMode x y z) = 0 := by
  ext i
  fin_cases i <;>
    norm_num [skewHamiltonian, skewHamiltonianZeroMode, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff] <;> ring

theorem skewHamiltonianZeroMode_ne_zero_of_z_ne_zero
    (x y z : ℝ) (hz : z ≠ 0) :
    skewHamiltonianZeroMode x y z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [skewHamiltonianZeroMode, Fin.ext_iff] at h0
  exact hz h0

theorem reflected_skewHamiltonian_mulVec_zeroMode (x y z : ℝ) :
    (skewHamiltonian z y x).mulVec (skewHamiltonianZeroMode x y z) =
      ![Complex.I * y * (x - z),
        Complex.I * (x ^ 2 - z ^ 2),
        Complex.I * y * (x - z)] := by
  ext i
  fin_cases i <;>
    norm_num [skewHamiltonian, skewHamiltonianZeroMode, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff] <;> ring

theorem reflected_skewHamiltonian_does_not_kill_zeroMode
    (x y z : ℝ) (hx : 0 < x) (hz : 0 < z) (hxz : x ≠ z) :
    (skewHamiltonian z y x).mulVec (skewHamiltonianZeroMode x y z) ≠ 0 := by
  rw [reflected_skewHamiltonian_mulVec_zeroMode]
  intro h
  have h1 := congrFun h 1
  norm_num [Fin.ext_iff] at h1
  have hsq : x ^ 2 = z ^ 2 := by
    have : x ^ 2 - z ^ 2 = 0 := by exact_mod_cast h1
    linarith
  have : x = z := by nlinarith
  exact hxz this

/-! ## 2. The missing reflection sign lives in the zero-mode direction -/

def orientationZeroMode (p q r : ℕ) : Fin 3 → ℂ :=
  skewHamiltonianZeroMode (rankTwoLeftCoupling p q r : ℝ)
    (rankTwoLongCoupling p q r : ℝ) (rankTwoRightCoupling p q r : ℝ)

def orientationZeroModeEndpointAsymmetry (p q r : ℕ) : ℝ :=
  (orientationZeroMode p q r 2 - orientationZeroMode p q r 0).re

theorem orientationHamiltonian_mulVec_zeroMode (p q r : ℕ) :
    (orientationHamiltonian p q r).mulVec (orientationZeroMode p q r) = 0 := by
  exact skewHamiltonian_mulVec_zeroMode _ _ _

theorem orientationZeroMode_ne_zero
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    orientationZeroMode p q r ≠ 0 := by
  have hz : (rankTwoRightCoupling p q r : ℝ) ≠ 0 := by
    rw [rankTwoRightCoupling_formula]
    positivity
  exact skewHamiltonianZeroMode_ne_zero_of_z_ne_zero _ _ _ hz

theorem orientationZeroMode_endpoint_asymmetry
    (p q r : ℕ) :
    orientationZeroModeEndpointAsymmetry p q r =
      2 * (imbalanceCoefficient p q r : ℝ) := by
  change (rankTwoLeftCoupling p q r : ℝ) -
      (rankTwoRightCoupling p q r : ℝ) =
        2 * (imbalanceCoefficient p q r : ℝ)
  unfold imbalanceCoefficient
  rw [rankTwoLeftCoupling_formula, rankTwoRightCoupling_formula]
  push_cast
  ring

theorem orientationZeroMode_endpoint_asymmetry_ne_zero_iff
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    orientationZeroModeEndpointAsymmetry p q r ≠ 0 ↔ p ≠ r := by
  rw [orientationZeroMode_endpoint_asymmetry]
  have hiff := imbalanceCoefficient_eq_zero_iff p q r hp hq hr
  constructor
  · intro hne hpr
    apply hne
    have hg := hiff.mpr hpr
    rw [hg]
    norm_num
  · intro hpr hzero
    have hgammaR : (imbalanceCoefficient p q r : ℝ) = 0 := by
      nlinarith
    have hgammaQ : imbalanceCoefficient p q r = 0 := by
      exact_mod_cast hgammaR
    exact hpr (hiff.mp hgammaQ)

theorem rankTwo_couplings_outer_reflection (p q r : ℕ) :
    rankTwoLeftCoupling r q p = rankTwoRightCoupling p q r
    ∧ rankTwoLongCoupling r q p = rankTwoLongCoupling p q r
    ∧ rankTwoRightCoupling r q p = rankTwoLeftCoupling p q r := by
  rw [rankTwoLeftCoupling_formula, rankTwoLongCoupling_formula,
    rankTwoLongCoupling_formula, rankTwoRightCoupling_formula,
    rankTwoRightCoupling_formula, rankTwoLeftCoupling_formula]
  constructor
  · ring
  · constructor <;> ring

theorem orientationHamiltonian_outer_reflection_as_swap (p q r : ℕ) :
    orientationHamiltonian r q p =
      skewHamiltonian (rankTwoRightCoupling p q r : ℝ)
        (rankTwoLongCoupling p q r : ℝ) (rankTwoLeftCoupling p q r : ℝ) := by
  rcases rankTwo_couplings_outer_reflection p q r with ⟨hL, hM, hR⟩
  simp only [orientationHamiltonian, hL, hM, hR]

theorem rankTwoLeftCoupling_pos
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (0 : ℝ) < rankTwoLeftCoupling p q r := by
  rw [rankTwoLeftCoupling_formula]
  positivity

theorem rankTwoRightCoupling_pos
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (0 : ℝ) < rankTwoRightCoupling p q r := by
  rw [rankTwoRightCoupling_formula]
  positivity

theorem rankTwoLeftCoupling_ne_right_of_outer_ne
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≠ r) :
    (rankTwoLeftCoupling p q r : ℝ) ≠ rankTwoRightCoupling p q r := by
  intro h
  rw [rankTwoLeftCoupling_formula, rankTwoRightCoupling_formula] at h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  push_cast at h
  let base : ℝ := p * q * r
  have hbase : base ≠ 0 := by
    unfold base
    positivity
  have h' : base * ((p : ℝ) + 1) / 2 =
      base * ((r : ℝ) + 1) / 2 := by
    simpa [base, mul_comm, mul_left_comm, mul_assoc] using h
  have hprod : base * ((p : ℝ) + 1) = base * ((r : ℝ) + 1) := by
    linarith
  have hsum : (p : ℝ) + 1 = (r : ℝ) + 1 :=
    mul_left_cancel₀ hbase hprod
  exact hpr (by exact_mod_cast (show (p : ℝ) = r by linarith))

theorem reflected_orientationHamiltonian_has_different_kernel_witness
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≠ r) :
    (orientationHamiltonian p q r).mulVec (orientationZeroMode p q r) = 0
    ∧ (orientationHamiltonian r q p).mulVec (orientationZeroMode p q r) ≠ 0 := by
  constructor
  · exact orientationHamiltonian_mulVec_zeroMode p q r
  · rw [orientationHamiltonian_outer_reflection_as_swap]
    exact reflected_skewHamiltonian_does_not_kill_zeroMode _ _ _
      (rankTwoLeftCoupling_pos p q r hp hq hr)
      (rankTwoRightCoupling_pos p q r hp hq hr)
      (rankTwoLeftCoupling_ne_right_of_outer_ne p q r hp hq hr hpr)

def hamiltonianKernel (H : Matrix (Fin 3) (Fin 3) ℂ) : Set (Fin 3 → ℂ) :=
  {v | H.mulVec v = 0}

theorem reflected_orientationHamiltonian_kernels_ne
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≠ r) :
    hamiltonianKernel (orientationHamiltonian p q r) ≠
      hamiltonianKernel (orientationHamiltonian r q p) := by
  intro hker
  have hw := reflected_orientationHamiltonian_has_different_kernel_witness
    p q r hp hq hr hpr
  have hmem :
      orientationZeroMode p q r ∈
        hamiltonianKernel (orientationHamiltonian p q r) := hw.1
  rw [hker] at hmem
  exact hw.2 hmem

/-! ## 3. Cubic closure and the retained quadratic Casimir -/

theorem skewHamiltonian_cubic (x y z : ℝ) :
    skewHamiltonian x y z ^ 3 =
      (((x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ)) • skewHamiltonian x y z := by
  have hc := Matrix.aeval_self_charpoly (skewHamiltonian x y z)
  rw [skewHamiltonian_charpoly] at hc
  simpa [sub_eq_zero, Algebra.smul_def] using hc

theorem skewHamiltonian_trace (x y z : ℝ) :
    Matrix.trace (skewHamiltonian x y z) = 0 := by
  norm_num [Matrix.trace, skewHamiltonian, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem skewHamiltonian_sq_trace (x y z : ℝ) :
    Matrix.trace (skewHamiltonian x y z ^ 2) =
      2 * ((x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ) := by
  norm_num [Matrix.trace, skewHamiltonian, pow_two, Matrix.mul_apply,
    Fin.sum_univ_three]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem orientationHamiltonian_cubic (p q r : ℕ) :
    orientationHamiltonian p q r ^ 3 =
      ((((rankTwoLeftCoupling p q r : ℝ) ^ 2 +
        (rankTwoLongCoupling p q r : ℝ) ^ 2 +
        (rankTwoRightCoupling p q r : ℝ) ^ 2 : ℝ) : ℂ)) •
          orientationHamiltonian p q r := by
  exact skewHamiltonian_cubic _ _ _

theorem orientationHamiltonian_sq_trace (p q r : ℕ) :
    Matrix.trace (orientationHamiltonian p q r ^ 2) =
      2 * ((((rankTwoLeftCoupling p q r : ℝ) ^ 2 +
        (rankTwoLongCoupling p q r : ℝ) ^ 2 +
        (rankTwoRightCoupling p q r : ℝ) ^ 2 : ℝ) : ℂ)) := by
  exact skewHamiltonian_sq_trace _ _ _

def orientationHamiltonianCasimir (p q r : ℕ) : ℂ :=
  Matrix.trace (orientationHamiltonian p q r ^ 2) / 2

theorem orientationHamiltonianCasimir_eq_coupling_norm (p q r : ℕ) :
    orientationHamiltonianCasimir p q r =
      (((rankTwoLeftCoupling p q r : ℝ) ^ 2 +
        (rankTwoLongCoupling p q r : ℝ) ^ 2 +
        (rankTwoRightCoupling p q r : ℝ) ^ 2 : ℝ) : ℂ) := by
  unfold orientationHamiltonianCasimir
  rw [orientationHamiltonian_sq_trace]
  ring

theorem orientationHamiltonianCasimir_outer_reflection (p q r : ℕ) :
    orientationHamiltonianCasimir p q r =
      orientationHamiltonianCasimir r q p := by
  rw [orientationHamiltonianCasimir_eq_coupling_norm,
    orientationHamiltonianCasimir_eq_coupling_norm]
  rw [rankTwoLeftCoupling_formula, rankTwoLongCoupling_formula,
    rankTwoRightCoupling_formula, rankTwoLeftCoupling_formula,
    rankTwoLongCoupling_formula, rankTwoRightCoupling_formula]
  norm_num
  ring

/-! ## 4. Every polynomial observable reduces to degree below three -/

theorem orientationHamiltonian_polynomial_reduction
    (p q r : ℕ) (f : Polynomial ℂ) :
    ∃ g : Polynomial ℂ,
      g.natDegree < 3
      ∧ Polynomial.aeval (orientationHamiltonian p q r) f =
        Polynomial.aeval (orientationHamiltonian p q r) g := by
  let H := orientationHamiltonian p q r
  let g := f %ₘ H.charpoly
  refine ⟨g, ?_, ?_⟩
  · have hne : H.charpoly ≠ 1 := by
      intro h
      have hd := congrArg Polynomial.natDegree h
      simp [H] at hd
    have hlt := Polynomial.natDegree_modByMonic_lt f H.charpoly_monic hne
    simpa [H, g] using hlt
  · exact Matrix.aeval_eq_aeval_mod_charpoly H f

end

/-! ## Trust regression -/

#print axioms skewHamiltonian_mulVec_zeroMode
#print axioms orientationZeroMode_endpoint_asymmetry_ne_zero_iff
#print axioms reflected_orientationHamiltonian_kernels_ne
#print axioms orientationHamiltonian_cubic
#print axioms orientationHamiltonianCasimir_outer_reflection
#print axioms orientationHamiltonian_polynomial_reduction

end UnifiedTheory.Audit.KFOrientationQuantumZeroMode
