/-
  LayerA/AdjointCarrierSpinor.lean — the adjoint (zero-sum) carrier is a
  Cl(3) / Weyl SPINOR: explicit Pauli operators, transported onto the carrier
  through the framework's own coordinate equivalence, satisfy the Clifford
  relations γᵢ² = 1 and {γᵢ,γⱼ} = 0.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS ESTABLISHES (and its honest scope).

  The matter-measure program (`MATTER_MEASURE_SCOPE.md`) needs a first-order
  Dirac operator D_adj on the adjoint carrier. Furey (arXiv:2607.18450) observes
  that the endomorphism algebra of a division-algebra module is a Clifford
  algebra — the natural home of a Dirac operator. Here that observation is made
  concrete IN THE FRAMEWORK'S OWN TYPES: the adjoint carrier
  `ZeroSumCarrier (Fin 3)` is 2-complex-dimensional (`zeroSumCarrier_finrank_eq_
  two`), so its endomorphism algebra is M₂(ℂ) ≅ Cl(3)⊗ℂ, and the carrier is the
  Cl(3) spinor. We transport the three Pauli matrices onto the carrier via the
  framework's coordinate equivalence `zeroSumFinThreeCoordinateLinearEquiv` and
  prove they generate a Clifford system. Hence the adjoint carrier is a WEYL
  (2-component) spinor — the object D_adj acts on.

  SCOPE — this proves the CARRIER carries a Clifford structure (the object side
  of G2), NOT that the causal geometry canonically SELECTS the γ-matrices. The
  Pauli operators here are the abstract generators of M₂(ℂ); tying them to the
  causal-diamond DIRECTIONS (the conjectural "three direction classes") is the
  remaining, unproved construction. This file is the provable half; the
  direction→γ map is the open half.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation

namespace UnifiedTheory.LayerA.AdjointCarrierSpinor

open UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier
open Matrix

/-! ## 1. The Pauli matrices and the Clifford relations (matrix level) -/

/-- Pauli σ₁. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli σ₂. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- Pauli σ₃. -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem σ₁_sq : σ₁ * σ₁ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₂_sq : σ₂ * σ₂ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.I_mul_I]

theorem σ₃_sq : σ₃ * σ₃ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ_anticomm_12 : σ₁ * σ₂ + σ₂ * σ₁ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂]

theorem σ_anticomm_23 : σ₂ * σ₃ + σ₃ * σ₂ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ₂, σ₃]

theorem σ_anticomm_13 : σ₁ * σ₃ + σ₃ * σ₁ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₃]

/-- The Pauli matrices are Hermitian. -/
theorem σ₁_herm : σ₁.conjTranspose = σ₁ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, Matrix.conjTranspose_apply]
theorem σ₂_herm : σ₂.conjTranspose = σ₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, Matrix.conjTranspose_apply]
theorem σ₃_herm : σ₃.conjTranspose = σ₃ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃, Matrix.conjTranspose_apply]

/-! ## 2. Transport onto the adjoint carrier -/

/-- Abbreviation for the framework's coordinate equivalence
    `ZeroSumCarrier (Fin 3) ≃ₗ[ℂ] (Fin 2 → ℂ)`. -/
noncomputable abbrev e := zeroSumFinThreeCoordinateLinearEquiv

/-- A 2×2 complex matrix as an endomorphism of the adjoint carrier, via the
    coordinate equivalence: `γ M = e⁻¹ ∘ (M·) ∘ e`. -/
noncomputable def γ (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Module.End ℂ (ZeroSumCarrier (Fin 3)) :=
  e.symm.toLinearMap ∘ₗ (Matrix.toLin' M) ∘ₗ e.toLinearMap

theorem γ_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) : γ (A * B) = γ A * γ B := by
  ext v
  simp only [γ, Module.End.mul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Matrix.toLin'_mul, LinearEquiv.apply_symm_apply]

theorem γ_add (A B : Matrix (Fin 2) (Fin 2) ℂ) : γ (A + B) = γ A + γ B := by
  ext v
  simp only [γ, LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    map_add]

theorem γ_one : γ 1 = 1 := by
  ext v
  simp only [γ, LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_one,
    LinearMap.id_coe, id_eq, LinearEquiv.symm_apply_apply, Module.End.one_apply]

theorem γ_zero : γ 0 = 0 := by
  ext v
  simp only [γ, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero,
    LinearMap.zero_apply]

/-! ## 3. The Clifford system on the carrier -/

/-- Anticommutator identity transported from the matrix level. -/
theorem γ_anticomm (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    γ A * γ B + γ B * γ A = γ (A * B + B * A) := by
  rw [γ_add, γ_mul, γ_mul]

/-- **The adjoint carrier is a Cl(3) module (a Weyl spinor).**
    Three endomorphisms of `ZeroSumCarrier (Fin 3)` square to the identity and
    pairwise anticommute — the defining relations of the Clifford algebra
    Cl(3), of which the 2-dimensional carrier is the spinor representation. -/
theorem adjoint_carrier_is_clifford_module :
    (γ σ₁ * γ σ₁ = 1 ∧ γ σ₂ * γ σ₂ = 1 ∧ γ σ₃ * γ σ₃ = 1) ∧
    (γ σ₁ * γ σ₂ + γ σ₂ * γ σ₁ = 0 ∧
     γ σ₂ * γ σ₃ + γ σ₃ * γ σ₂ = 0 ∧
     γ σ₁ * γ σ₃ + γ σ₃ * γ σ₁ = 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [← γ_mul, σ₁_sq, γ_one]
  · rw [← γ_mul, σ₂_sq, γ_one]
  · rw [← γ_mul, σ₃_sq, γ_one]
  · rw [γ_anticomm, σ_anticomm_12, γ_zero]
  · rw [γ_anticomm, σ_anticomm_23, γ_zero]
  · rw [γ_anticomm, σ_anticomm_13, γ_zero]

end UnifiedTheory.LayerA.AdjointCarrierSpinor
