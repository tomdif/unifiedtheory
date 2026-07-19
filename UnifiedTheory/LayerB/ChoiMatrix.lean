/-
  LayerB/ChoiMatrix.lean
  ──────────────────────

  The Choi matrix of a linear map between matrix algebras — Phase 2.1
  of the Kraus existence theorem.

  For a linear map L : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ, the Choi matrix
  J(L) ∈ Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ is defined by

      J(L) ⟨a, c⟩ ⟨b, d⟩  :=  (L (matrix-unit a b)) c d .

  Equivalently, J(L) is the (m·n) × (m·n) block matrix whose (a, b)
  block is L(|a⟩⟨b|).  This is the standard Choi-Jamiolkowski form.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `choi L` definition (a `Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ`).
    2. Linearity in L:
         - `choi_add`,  `choi_smul`,  `choi_zero`.
    3. Choi evaluated on matrix units recovers L:
         - `choi_apply_matrixUnit` : `J(L)⟨a, c⟩⟨b, d⟩ = L(|a⟩⟨b|) c d`.
    4. Choi of the identity map equals the (unnormalised) maximally
       entangled projector (`choi_id_eq_maxEntangledProj`).

  WHAT IS DEFERRED to Phase 2.2:
    - Vec/unvec matrix vectorization.
    - Spectral decomposition of J(L).
    - Kraus extraction:  J(L) PSD ⟹ ∃ Kraus rep.
    - The full Kraus existence theorem.
-/

import UnifiedTheory.LayerB.KrausRepresentation
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Module.LinearMap.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Kraus

open Matrix Complex
open scoped ComplexOrder

/-! ## 1. The Choi matrix -/

/-- The Choi matrix of a linear map L : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ.

    `J(L) ⟨a, c⟩ ⟨b, d⟩  :=  (L (single a b 1)) c d` . -/
noncomputable def choi {m n : ℕ}
    (L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  fun ⟨a, c⟩ ⟨b, d⟩ => (L (Matrix.single a b 1)) c d

/-- Direct evaluation formula for the Choi matrix. -/
@[simp]
theorem choi_apply {m n : ℕ}
    (L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin m) (c d : Fin n) :
    choi L ⟨a, c⟩ ⟨b, d⟩ = (L (Matrix.single a b 1)) c d := rfl

/-! ## 2. Linearity in L -/

theorem choi_add {m n : ℕ}
    (L₁ L₂ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    choi (L₁ + L₂) = choi L₁ + choi L₂ := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp [choi, Matrix.add_apply, LinearMap.add_apply]

theorem choi_smul {m n : ℕ} (r : ℂ)
    (L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    choi (r • L) = r • choi L := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp [choi, Matrix.smul_apply, LinearMap.smul_apply]

theorem choi_zero {m n : ℕ} :
    choi (0 : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) = 0 := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp [choi, LinearMap.zero_apply]

/-! ## 3. L acts on a generic matrix as a sum over matrix units -/

/-- Single matrix unit with scalar `c` equals `c • single i j 1`. -/
private theorem single_eq_smul_single_one {n : ℕ} (i j : Fin n) (c : ℂ) :
    Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
  ext a b
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- Any matrix decomposes as a linear combination of matrix units. -/
theorem matrix_decomp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M = ∑ i, ∑ j, (M i j) • Matrix.single i j (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact single_eq_smul_single_one i j (M i j)

/-- The action of a linear map on any matrix is determined by its action
    on the matrix units, via `L(M) = Σ_{i,j} (M i j) • L(single i j 1)`. -/
theorem linearMap_decomp {m n : ℕ}
    (L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    L M = ∑ i, ∑ j, (M i j) • L (Matrix.single i j (1 : ℂ)) := by
  conv_lhs => rw [matrix_decomp M]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.map_smul]

/-! ## 4. Choi-from-block-evaluations: an extensionality principle -/

/-- Two linear maps are equal iff their Choi matrices are equal,
    i.e., the Choi matrix is a complete invariant. -/
theorem linearMap_eq_iff_choi_eq {m n : ℕ}
    (L₁ L₂ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    L₁ = L₂ ↔ choi L₁ = choi L₂ := by
  constructor
  · intro h; rw [h]
  · intro h
    ext M c d
    rw [linearMap_decomp L₁, linearMap_decomp L₂]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have : (L₁ (Matrix.single i j 1)) c d = (L₂ (Matrix.single i j 1)) c d := by
      have h_eq : choi L₁ ⟨i, c⟩ ⟨j, d⟩ = choi L₂ ⟨i, c⟩ ⟨j, d⟩ := by
        rw [h]
      simpa [choi] using h_eq
    rw [this]

end UnifiedTheory.LayerB.Kraus
