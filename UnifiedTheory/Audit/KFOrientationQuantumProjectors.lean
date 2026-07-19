/-
  Audit/KFOrientationQuantumProjectors.lean

  EXACT SPECTRAL PROJECTORS AND CONDITIONAL UNITARY EVOLUTION

  For every positive three-fiber profile, the finite Hermitian orientation
  Hamiltonian admits explicit zero, positive, and negative spectral projectors.
  They are Hermitian, idempotent, mutually orthogonal, and complete.  The
  positive and negative sectors have eigenvalues +rho and -rho, while the
  protected zero sector is stationary.

  The projector algebra yields a closed propagator with U(0)=1,
  U(t+u)=U(t)U(u), U(t)ᴴU(t)=1, and exact preservation of the zero mode.
  This is a conditional finite matrix dynamics.  It does not select a physical
  causal-set Hamiltonian, impose gravitational constraints, or establish a
  continuum quantum-gravity theory.
-/

import UnifiedTheory.Audit.KFOrientationQuantumZeroMode
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationQuantumProjectors

noncomputable section

open scoped BigOperators Polynomial ComplexConjugate
open Matrix
open UnifiedTheory.Audit.KFOrientationRankTwoFiberLaw
open UnifiedTheory.Audit.KFOrientationRankTwoConsequences
open UnifiedTheory.Audit.KFOrientationQuantumConsequences
open UnifiedTheory.Audit.KFOrientationQuantumZeroMode

abbrev ComplexThreeMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-! ## 1. Positive level radius -/

def orientationRadiusSq (p q r : ℕ) : ℝ :=
  (rankTwoLeftCoupling p q r : ℝ) ^ 2 +
    (rankTwoLongCoupling p q r : ℝ) ^ 2 +
      (rankTwoRightCoupling p q r : ℝ) ^ 2

def orientationRadius (p q r : ℕ) : ℝ :=
  Real.sqrt (orientationRadiusSq p q r)

theorem orientationRadiusSq_pos
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    0 < orientationRadiusSq p q r := by
  have hL := rankTwoLeftCoupling_pos p q r hp hq hr
  unfold orientationRadiusSq
  positivity

theorem orientationRadius_pos
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    0 < orientationRadius p q r := by
  unfold orientationRadius
  exact Real.sqrt_pos.2 (orientationRadiusSq_pos p q r hp hq hr)

theorem orientationRadius_sq
    (p q r : ℕ) :
    orientationRadius p q r ^ 2 = orientationRadiusSq p q r := by
  unfold orientationRadius
  rw [Real.sq_sqrt]
  unfold orientationRadiusSq
  positivity

def orientationRangeProjector (p q r : ℕ) : ComplexThreeMatrix :=
  ((orientationRadiusSq p q r : ℂ)⁻¹) • orientationHamiltonian p q r ^ 2

def orientationKernelProjector (p q r : ℕ) : ComplexThreeMatrix :=
  1 - orientationRangeProjector p q r

def orientationSignOperator (p q r : ℕ) : ComplexThreeMatrix :=
  ((orientationRadius p q r : ℂ)⁻¹) • orientationHamiltonian p q r

def orientationPositiveProjector (p q r : ℕ) : ComplexThreeMatrix :=
  (1 / 2 : ℂ) •
    (orientationRangeProjector p q r + orientationSignOperator p q r)

def orientationNegativeProjector (p q r : ℕ) : ComplexThreeMatrix :=
  (1 / 2 : ℂ) •
    (orientationRangeProjector p q r - orientationSignOperator p q r)

/-! ## 2. Projector algebra -/

theorem orientationHamiltonian_fourth (p q r : ℕ) :
    orientationHamiltonian p q r ^ 4 =
      (orientationRadiusSq p q r : ℂ) •
        orientationHamiltonian p q r ^ 2 := by
  calc
    orientationHamiltonian p q r ^ 4 =
        orientationHamiltonian p q r ^ 3 * orientationHamiltonian p q r := by
      rw [show 4 = 3 + 1 by omega, pow_succ]
    _ = ((orientationRadiusSq p q r : ℂ) •
          orientationHamiltonian p q r) * orientationHamiltonian p q r := by
      have h3 := orientationHamiltonian_cubic p q r
      simpa [orientationRadiusSq] using
        congrArg (fun M => M * orientationHamiltonian p q r) h3
    _ = (orientationRadiusSq p q r : ℂ) •
          (orientationHamiltonian p q r * orientationHamiltonian p q r) := by
      rw [smul_mul_assoc]
    _ = (orientationRadiusSq p q r : ℂ) •
          orientationHamiltonian p q r ^ 2 := by rw [pow_two]

theorem orientationRangeProjector_idempotent
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationRangeProjector p q r * orientationRangeProjector p q r =
      orientationRangeProjector p q r := by
  unfold orientationRangeProjector
  rw [smul_mul_smul_comm]
  have hpow :
      orientationHamiltonian p q r ^ 2 * orientationHamiltonian p q r ^ 2 =
        orientationHamiltonian p q r ^ 4 := by noncomm_ring
  rw [hpow, orientationHamiltonian_fourth, smul_smul]
  congr 1
  have hρC : (orientationRadiusSq p q r : ℂ) ≠ 0 := by exact_mod_cast hρ
  field_simp

theorem orientationHamiltonian_mul_rangeProjector
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationHamiltonian p q r * orientationRangeProjector p q r =
      orientationHamiltonian p q r := by
  unfold orientationRangeProjector
  rw [mul_smul_comm]
  have hpow :
      orientationHamiltonian p q r * orientationHamiltonian p q r ^ 2 =
        orientationHamiltonian p q r ^ 3 := by noncomm_ring
  rw [hpow]
  have h3 : orientationHamiltonian p q r ^ 3 =
      (orientationRadiusSq p q r : ℂ) • orientationHamiltonian p q r := by
    simpa [orientationRadiusSq] using orientationHamiltonian_cubic p q r
  rw [h3, smul_smul]
  have hρC : (orientationRadiusSq p q r : ℂ) ≠ 0 := by exact_mod_cast hρ
  field_simp
  simp

theorem orientationRangeProjector_mul_hamiltonian
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationRangeProjector p q r * orientationHamiltonian p q r =
      orientationHamiltonian p q r := by
  unfold orientationRangeProjector
  rw [smul_mul_assoc]
  have hpow :
      orientationHamiltonian p q r ^ 2 * orientationHamiltonian p q r =
        orientationHamiltonian p q r ^ 3 := by noncomm_ring
  rw [hpow]
  have h3 : orientationHamiltonian p q r ^ 3 =
      (orientationRadiusSq p q r : ℂ) • orientationHamiltonian p q r := by
    simpa [orientationRadiusSq] using orientationHamiltonian_cubic p q r
  rw [h3, smul_smul]
  have hρC : (orientationRadiusSq p q r : ℂ) ≠ 0 := by exact_mod_cast hρ
  field_simp
  simp

theorem orientationKernelProjector_add_rangeProjector (p q r : ℕ) :
    orientationKernelProjector p q r + orientationRangeProjector p q r = 1 := by
  unfold orientationKernelProjector
  abel

theorem orientationKernelProjector_idempotent
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationKernelProjector p q r * orientationKernelProjector p q r =
      orientationKernelProjector p q r := by
  unfold orientationKernelProjector
  have hQ := orientationRangeProjector_idempotent p q r hρ
  calc
    (1 - orientationRangeProjector p q r) *
          (1 - orientationRangeProjector p q r) =
        1 - orientationRangeProjector p q r -
          orientationRangeProjector p q r +
            orientationRangeProjector p q r *
              orientationRangeProjector p q r := by noncomm_ring
    _ = 1 - orientationRangeProjector p q r := by rw [hQ]; noncomm_ring

theorem orientationKernelProjector_mul_rangeProjector
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationKernelProjector p q r * orientationRangeProjector p q r = 0 := by
  unfold orientationKernelProjector
  have hQ := orientationRangeProjector_idempotent p q r hρ
  calc
    (1 - orientationRangeProjector p q r) *
          orientationRangeProjector p q r =
        orientationRangeProjector p q r -
          orientationRangeProjector p q r *
            orientationRangeProjector p q r := by noncomm_ring
    _ = 0 := by rw [hQ]; exact sub_self _

theorem orientationRangeProjector_mul_kernelProjector
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationRangeProjector p q r * orientationKernelProjector p q r = 0 := by
  unfold orientationKernelProjector
  have hQ := orientationRangeProjector_idempotent p q r hρ
  calc
    orientationRangeProjector p q r *
          (1 - orientationRangeProjector p q r) =
        orientationRangeProjector p q r -
          orientationRangeProjector p q r *
            orientationRangeProjector p q r := by noncomm_ring
    _ = 0 := by rw [hQ]; exact sub_self _

theorem orientationHamiltonian_mul_kernelProjector
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationHamiltonian p q r * orientationKernelProjector p q r = 0 := by
  unfold orientationKernelProjector
  rw [Matrix.mul_sub, Matrix.mul_one,
    orientationHamiltonian_mul_rangeProjector p q r hρ]
  exact sub_self _

theorem orientationKernelProjector_mul_hamiltonian
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationKernelProjector p q r * orientationHamiltonian p q r = 0 := by
  unfold orientationKernelProjector
  rw [Matrix.sub_mul, Matrix.one_mul,
    orientationRangeProjector_mul_hamiltonian p q r hρ]
  exact sub_self _

theorem orientationSignOperator_sq
    (p q r : ℕ) :
    orientationSignOperator p q r * orientationSignOperator p q r =
      orientationRangeProjector p q r := by
  unfold orientationSignOperator orientationRangeProjector
  rw [smul_mul_smul_comm]
  have hmul :
      orientationHamiltonian p q r * orientationHamiltonian p q r =
        orientationHamiltonian p q r ^ 2 := by rw [pow_two]
  rw [hmul]
  have hr := orientationRadius_sq p q r
  have hrC : (orientationRadius p q r : ℂ) ^ 2 =
      (orientationRadiusSq p q r : ℂ) := by exact_mod_cast hr
  congr 1
  calc
    (orientationRadius p q r : ℂ)⁻¹ *
          (orientationRadius p q r : ℂ)⁻¹ =
        ((orientationRadius p q r : ℂ)⁻¹) ^ 2 := by rw [pow_two]
    _ = ((orientationRadius p q r : ℂ) ^ 2)⁻¹ := by rw [inv_pow]
    _ = (orientationRadiusSq p q r : ℂ)⁻¹ := by rw [hrC]

theorem orientationRangeProjector_mul_signOperator
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationRangeProjector p q r * orientationSignOperator p q r =
      orientationSignOperator p q r := by
  unfold orientationSignOperator
  rw [mul_smul_comm,
    orientationRangeProjector_mul_hamiltonian p q r hρ]

theorem orientationSignOperator_mul_rangeProjector
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationSignOperator p q r * orientationRangeProjector p q r =
      orientationSignOperator p q r := by
  unfold orientationSignOperator
  rw [smul_mul_assoc,
    orientationHamiltonian_mul_rangeProjector p q r hρ]

theorem orientationPositiveProjector_idempotent
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationPositiveProjector p q r * orientationPositiveProjector p q r =
      orientationPositiveProjector p q r := by
  unfold orientationPositiveProjector
  rw [smul_mul_smul_comm]
  have hinside :
      (orientationRangeProjector p q r + orientationSignOperator p q r) *
          (orientationRangeProjector p q r + orientationSignOperator p q r) =
        2 • (orientationRangeProjector p q r + orientationSignOperator p q r) := by
    calc
      _ = orientationRangeProjector p q r * orientationRangeProjector p q r +
            orientationRangeProjector p q r * orientationSignOperator p q r +
            orientationSignOperator p q r * orientationRangeProjector p q r +
            orientationSignOperator p q r * orientationSignOperator p q r := by
          noncomm_ring
      _ = _ := by
        rw [orientationRangeProjector_idempotent p q r hρ,
          orientationRangeProjector_mul_signOperator p q r hρ,
          orientationSignOperator_mul_rangeProjector p q r hρ,
          orientationSignOperator_sq p q r]
        module
  rw [hinside]
  module

theorem orientationNegativeProjector_idempotent
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationNegativeProjector p q r * orientationNegativeProjector p q r =
      orientationNegativeProjector p q r := by
  unfold orientationNegativeProjector
  rw [smul_mul_smul_comm]
  have hinside :
      (orientationRangeProjector p q r - orientationSignOperator p q r) *
          (orientationRangeProjector p q r - orientationSignOperator p q r) =
        2 • (orientationRangeProjector p q r - orientationSignOperator p q r) := by
    calc
      _ = orientationRangeProjector p q r * orientationRangeProjector p q r -
            orientationRangeProjector p q r * orientationSignOperator p q r -
            orientationSignOperator p q r * orientationRangeProjector p q r +
            orientationSignOperator p q r * orientationSignOperator p q r := by
          noncomm_ring
      _ = _ := by
        rw [orientationRangeProjector_idempotent p q r hρ,
          orientationRangeProjector_mul_signOperator p q r hρ,
          orientationSignOperator_mul_rangeProjector p q r hρ,
          orientationSignOperator_sq p q r]
        module
  rw [hinside]
  module

theorem orientationPositiveProjector_mul_negativeProjector
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationPositiveProjector p q r * orientationNegativeProjector p q r = 0 := by
  unfold orientationPositiveProjector orientationNegativeProjector
  rw [smul_mul_smul_comm]
  have hinside :
      (orientationRangeProjector p q r + orientationSignOperator p q r) *
          (orientationRangeProjector p q r - orientationSignOperator p q r) = 0 := by
    calc
      _ = orientationRangeProjector p q r * orientationRangeProjector p q r -
            orientationRangeProjector p q r * orientationSignOperator p q r +
            orientationSignOperator p q r * orientationRangeProjector p q r -
            orientationSignOperator p q r * orientationSignOperator p q r := by
          noncomm_ring
      _ = 0 := by
        rw [orientationRangeProjector_idempotent p q r hρ,
          orientationRangeProjector_mul_signOperator p q r hρ,
          orientationSignOperator_mul_rangeProjector p q r hρ,
          orientationSignOperator_sq p q r]
        module
  rw [hinside, smul_zero]

theorem orientationNegativeProjector_mul_positiveProjector
    (p q r : ℕ) (hρ : orientationRadiusSq p q r ≠ 0) :
    orientationNegativeProjector p q r * orientationPositiveProjector p q r = 0 := by
  unfold orientationPositiveProjector orientationNegativeProjector
  rw [smul_mul_smul_comm]
  have hinside :
      (orientationRangeProjector p q r - orientationSignOperator p q r) *
          (orientationRangeProjector p q r + orientationSignOperator p q r) = 0 := by
    calc
      _ = orientationRangeProjector p q r * orientationRangeProjector p q r +
            orientationRangeProjector p q r * orientationSignOperator p q r -
            orientationSignOperator p q r * orientationRangeProjector p q r -
            orientationSignOperator p q r * orientationSignOperator p q r := by
          noncomm_ring
      _ = 0 := by
        rw [orientationRangeProjector_idempotent p q r hρ,
          orientationRangeProjector_mul_signOperator p q r hρ,
          orientationSignOperator_mul_rangeProjector p q r hρ,
          orientationSignOperator_sq]
        module
  rw [hinside, smul_zero]

theorem orientationPositive_add_negative (p q r : ℕ) :
    orientationPositiveProjector p q r + orientationNegativeProjector p q r =
      orientationRangeProjector p q r := by
  unfold orientationPositiveProjector orientationNegativeProjector
  module

theorem orientationSpectralProjectors_complete (p q r : ℕ) :
    orientationKernelProjector p q r +
        orientationPositiveProjector p q r +
          orientationNegativeProjector p q r = 1 := by
  calc
    orientationKernelProjector p q r +
          orientationPositiveProjector p q r +
            orientationNegativeProjector p q r =
        orientationKernelProjector p q r +
          (orientationPositiveProjector p q r +
            orientationNegativeProjector p q r) := by abel
    _ = orientationKernelProjector p q r + orientationRangeProjector p q r := by
      rw [orientationPositive_add_negative]
    _ = 1 := orientationKernelProjector_add_rangeProjector p q r

theorem orientationRadius_smul_signOperator
    (p q r : ℕ) (hρ : orientationRadius p q r ≠ 0) :
    (orientationRadius p q r : ℂ) • orientationSignOperator p q r =
      orientationHamiltonian p q r := by
  unfold orientationSignOperator
  rw [smul_smul]
  have hρC : (orientationRadius p q r : ℂ) ≠ 0 := by exact_mod_cast hρ
  field_simp
  simp

theorem orientationSignOperator_mul_positiveProjector
    (p q r : ℕ) (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationSignOperator p q r * orientationPositiveProjector p q r =
      orientationPositiveProjector p q r := by
  unfold orientationPositiveProjector
  rw [mul_smul_comm, Matrix.mul_add,
    orientationSignOperator_mul_rangeProjector p q r hρsq,
    orientationSignOperator_sq]
  module

theorem orientationSignOperator_mul_negativeProjector
    (p q r : ℕ) (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationSignOperator p q r * orientationNegativeProjector p q r =
      -orientationNegativeProjector p q r := by
  unfold orientationNegativeProjector
  rw [mul_smul_comm, Matrix.mul_sub,
    orientationSignOperator_mul_rangeProjector p q r hρsq,
    orientationSignOperator_sq]
  module

theorem orientationHamiltonian_mul_positiveProjector
    (p q r : ℕ) (hρ : orientationRadius p q r ≠ 0)
    (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationHamiltonian p q r * orientationPositiveProjector p q r =
      (orientationRadius p q r : ℂ) • orientationPositiveProjector p q r := by
  rw [← orientationRadius_smul_signOperator p q r hρ,
    smul_mul_assoc,
    orientationSignOperator_mul_positiveProjector p q r hρsq]

theorem orientationHamiltonian_mul_negativeProjector
    (p q r : ℕ) (hρ : orientationRadius p q r ≠ 0)
    (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationHamiltonian p q r * orientationNegativeProjector p q r =
      -(orientationRadius p q r : ℂ) • orientationNegativeProjector p q r := by
  rw [← orientationRadius_smul_signOperator p q r hρ,
    smul_mul_assoc,
    orientationSignOperator_mul_negativeProjector p q r hρsq]
  module

theorem orientationRangeProjector_isHermitian (p q r : ℕ) :
    (orientationRangeProjector p q r).IsHermitian := by
  unfold Matrix.IsHermitian orientationRangeProjector
  rw [Matrix.conjTranspose_smul]
  simp [(orientationHamiltonian_isHermitian p q r).eq]

theorem orientationKernelProjector_isHermitian (p q r : ℕ) :
    (orientationKernelProjector p q r).IsHermitian := by
  exact Matrix.isHermitian_one.sub (orientationRangeProjector_isHermitian p q r)

theorem orientationSignOperator_isHermitian (p q r : ℕ) :
    (orientationSignOperator p q r).IsHermitian := by
  unfold Matrix.IsHermitian orientationSignOperator
  rw [Matrix.conjTranspose_smul]
  simp [(orientationHamiltonian_isHermitian p q r).eq]

theorem orientationPositiveProjector_isHermitian (p q r : ℕ) :
    (orientationPositiveProjector p q r).IsHermitian := by
  unfold Matrix.IsHermitian orientationPositiveProjector
  rw [Matrix.conjTranspose_smul]
  simp [(orientationRangeProjector_isHermitian p q r).eq,
    (orientationSignOperator_isHermitian p q r).eq]

theorem orientationNegativeProjector_isHermitian (p q r : ℕ) :
    (orientationNegativeProjector p q r).IsHermitian := by
  unfold Matrix.IsHermitian orientationNegativeProjector
  rw [Matrix.conjTranspose_smul]
  simp [(orientationRangeProjector_isHermitian p q r).eq,
    (orientationSignOperator_isHermitian p q r).eq]

/-! ## 3. Closed conditional propagator -/

theorem orientationKernelProjector_mul_signOperator
    (p q r : ℕ) (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationKernelProjector p q r * orientationSignOperator p q r = 0 := by
  unfold orientationSignOperator
  rw [mul_smul_comm,
    orientationKernelProjector_mul_hamiltonian p q r hρsq, smul_zero]

theorem orientationSignOperator_mul_kernelProjector
    (p q r : ℕ) (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationSignOperator p q r * orientationKernelProjector p q r = 0 := by
  unfold orientationSignOperator
  rw [smul_mul_assoc,
    orientationHamiltonian_mul_kernelProjector p q r hρsq, smul_zero]

theorem orientationKernelProjector_mul_positiveProjector
    (p q r : ℕ) (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationKernelProjector p q r * orientationPositiveProjector p q r = 0 := by
  unfold orientationPositiveProjector
  rw [mul_smul_comm, Matrix.mul_add,
    orientationKernelProjector_mul_rangeProjector p q r hρsq,
    orientationKernelProjector_mul_signOperator p q r hρsq,
    zero_add, smul_zero]

theorem orientationPositiveProjector_mul_kernelProjector
    (p q r : ℕ) (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationPositiveProjector p q r * orientationKernelProjector p q r = 0 := by
  unfold orientationPositiveProjector
  rw [smul_mul_assoc, Matrix.add_mul,
    orientationRangeProjector_mul_kernelProjector p q r hρsq,
    orientationSignOperator_mul_kernelProjector p q r hρsq,
    zero_add, smul_zero]

theorem orientationKernelProjector_mul_negativeProjector
    (p q r : ℕ) (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationKernelProjector p q r * orientationNegativeProjector p q r = 0 := by
  unfold orientationNegativeProjector
  rw [mul_smul_comm, Matrix.mul_sub,
    orientationKernelProjector_mul_rangeProjector p q r hρsq,
    orientationKernelProjector_mul_signOperator p q r hρsq,
    sub_self, smul_zero]

theorem orientationNegativeProjector_mul_kernelProjector
    (p q r : ℕ) (hρsq : orientationRadiusSq p q r ≠ 0) :
    orientationNegativeProjector p q r * orientationKernelProjector p q r = 0 := by
  unfold orientationNegativeProjector
  rw [smul_mul_assoc, Matrix.sub_mul,
    orientationRangeProjector_mul_kernelProjector p q r hρsq,
    orientationSignOperator_mul_kernelProjector p q r hρsq,
    sub_self, smul_zero]

def orientationPropagator (p q r : ℕ) (t : ℝ) : ComplexThreeMatrix :=
  orientationKernelProjector p q r +
      (Real.cos (orientationRadius p q r * t) : ℂ) •
        orientationRangeProjector p q r -
    (Complex.I * Real.sin (orientationRadius p q r * t)) •
      orientationSignOperator p q r

theorem orientationPropagator_zero (p q r : ℕ) :
    orientationPropagator p q r 0 = 1 := by
  unfold orientationPropagator
  norm_num
  exact orientationKernelProjector_add_rangeProjector p q r

theorem orientationPropagator_conjTranspose (p q r : ℕ) (t : ℝ) :
    (orientationPropagator p q r t)ᴴ =
      orientationKernelProjector p q r +
          (Real.cos (orientationRadius p q r * t) : ℂ) •
            orientationRangeProjector p q r +
        (Complex.I * Real.sin (orientationRadius p q r * t)) •
          orientationSignOperator p q r := by
  unfold orientationPropagator
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
  simp [(orientationKernelProjector_isHermitian p q r).eq,
    (orientationRangeProjector_isHermitian p q r).eq,
    (orientationSignOperator_isHermitian p q r).eq,
    -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem orientationPropagator_unitary
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (t : ℝ) :
    (orientationPropagator p q r t)ᴴ * orientationPropagator p q r t = 1 := by
  have hρsq : orientationRadiusSq p q r ≠ 0 :=
    ne_of_gt (orientationRadiusSq_pos p q r hp hq hr)
  rw [orientationPropagator_conjTranspose]
  unfold orientationPropagator
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub,
    smul_mul_assoc, mul_smul_comm]
  rw [orientationKernelProjector_idempotent p q r hρsq,
    orientationKernelProjector_mul_rangeProjector p q r hρsq,
    orientationKernelProjector_mul_signOperator p q r hρsq,
    orientationRangeProjector_mul_kernelProjector p q r hρsq,
    orientationRangeProjector_idempotent p q r hρsq,
    orientationRangeProjector_mul_signOperator p q r hρsq,
    orientationSignOperator_mul_kernelProjector p q r hρsq,
    orientationSignOperator_mul_rangeProjector p q r hρsq,
    orientationSignOperator_sq]
  simp only [smul_zero, add_zero, zero_add]
  have htrig := Real.cos_sq_add_sin_sq (orientationRadius p q r * t)
  have htrigC :
      (Real.cos (orientationRadius p q r * t) : ℂ) ^ 2 +
          (Real.sin (orientationRadius p q r * t) : ℂ) ^ 2 = 1 := by
    exact_mod_cast htrig
  rw [← orientationKernelProjector_add_rangeProjector p q r]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  change
    orientationKernelProjector p q r i j +
        (Real.cos (orientationRadius p q r * t) : ℂ) *
          ((Real.cos (orientationRadius p q r * t) : ℂ) *
              orientationRangeProjector p q r i j +
            Complex.I * (Real.sin (orientationRadius p q r * t) : ℂ) *
              orientationSignOperator p q r i j) -
        Complex.I * (Real.sin (orientationRadius p q r * t) : ℂ) *
          ((Real.cos (orientationRadius p q r * t) : ℂ) *
              orientationSignOperator p q r i j +
            Complex.I * (Real.sin (orientationRadius p q r * t) : ℂ) *
              orientationRangeProjector p q r i j) =
      orientationKernelProjector p q r i j +
        orientationRangeProjector p q r i j
  calc
    _ = orientationKernelProjector p q r i j +
          ((Real.cos (orientationRadius p q r * t) : ℂ) ^ 2 +
            (Real.sin (orientationRadius p q r * t) : ℂ) ^ 2) *
              orientationRangeProjector p q r i j := by
        ring_nf
        rw [Complex.I_sq]
        ring
    _ = _ := by rw [htrigC]; ring

theorem orientationPropagator_add
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (t u : ℝ) :
    orientationPropagator p q r (t + u) =
      orientationPropagator p q r t * orientationPropagator p q r u := by
  have hρsq : orientationRadiusSq p q r ≠ 0 :=
    ne_of_gt (orientationRadiusSq_pos p q r hp hq hr)
  unfold orientationPropagator
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.sub_mul, smul_mul_assoc, mul_smul_comm]
  rw [orientationKernelProjector_idempotent p q r hρsq,
    orientationKernelProjector_mul_rangeProjector p q r hρsq,
    orientationKernelProjector_mul_signOperator p q r hρsq,
    orientationRangeProjector_mul_kernelProjector p q r hρsq,
    orientationRangeProjector_idempotent p q r hρsq,
    orientationRangeProjector_mul_signOperator p q r hρsq,
    orientationSignOperator_mul_kernelProjector p q r hρsq,
    orientationSignOperator_mul_rangeProjector p q r hρsq,
    orientationSignOperator_sq]
  simp only [smul_zero, add_zero, zero_add]
  have hcos :
      Real.cos (orientationRadius p q r * (t + u)) =
        Real.cos (orientationRadius p q r * t) *
            Real.cos (orientationRadius p q r * u) -
          Real.sin (orientationRadius p q r * t) *
            Real.sin (orientationRadius p q r * u) := by
    rw [mul_add, Real.cos_add]
  have hsin :
      Real.sin (orientationRadius p q r * (t + u)) =
        Real.sin (orientationRadius p q r * t) *
            Real.cos (orientationRadius p q r * u) +
          Real.cos (orientationRadius p q r * t) *
            Real.sin (orientationRadius p q r * u) := by
    rw [mul_add, Real.sin_add]
  rw [hcos, hsin]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.zero_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem orientationPropagator_preserves_zeroMode
    (p q r : ℕ) (t : ℝ) :
    (orientationPropagator p q r t).mulVec (orientationZeroMode p q r) =
      orientationZeroMode p q r := by
  have hHz := orientationHamiltonian_mulVec_zeroMode p q r
  have hH2z :
      (orientationHamiltonian p q r ^ 2).mulVec (orientationZeroMode p q r) = 0 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hHz, Matrix.mulVec_zero]
  have hQz :
      (orientationRangeProjector p q r).mulVec (orientationZeroMode p q r) = 0 := by
    unfold orientationRangeProjector
    rw [Matrix.smul_mulVec, hH2z, smul_zero]
  have hJz :
      (orientationSignOperator p q r).mulVec (orientationZeroMode p q r) = 0 := by
    unfold orientationSignOperator
    rw [Matrix.smul_mulVec, hHz, smul_zero]
  have hKz :
      (orientationKernelProjector p q r).mulVec (orientationZeroMode p q r) =
        orientationZeroMode p q r := by
    unfold orientationKernelProjector
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hQz, sub_zero]
  unfold orientationPropagator
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, hKz, hQz, hJz, smul_zero, smul_zero]
  module

end

/-! ## Trust regression -/

#print axioms orientationRadiusSq_pos
#print axioms orientationSpectralProjectors_complete
#print axioms orientationPositiveProjector_idempotent
#print axioms orientationNegativeProjector_mul_positiveProjector
#print axioms orientationPositiveProjector_isHermitian
#print axioms orientationHamiltonian_mul_positiveProjector
#print axioms orientationPropagator_unitary
#print axioms orientationPropagator_add
#print axioms orientationPropagator_preserves_zeroMode

end UnifiedTheory.Audit.KFOrientationQuantumProjectors
