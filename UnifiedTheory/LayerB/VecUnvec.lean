/-
  LayerB/VecUnvec.lean
  ────────────────────

  Matrix vectorization — Phase 2.2 of the Kraus existence theorem.

  A vector `v : Fin m × Fin n → ℂ` (i.e., an element of ℂ^(m·n))
  corresponds bijectively to a matrix `V : Matrix (Fin n) (Fin m) ℂ`
  via

      vec V ⟨a, c⟩  :=  V c a
      unvec v c a   :=  v ⟨a, c⟩ .

  The pair (vec, unvec) is a linear inverse pair.  This isomorphism
  is the engine that turns spectral-decomposition eigenvectors of the
  Choi matrix into Kraus operators in Phase 2.3.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `vec`, `unvec` definitions.
    2. They are mutual inverses (`vec_unvec`, `unvec_vec`).
    3. Linearity:  `vec_add`, `vec_smul`, `unvec_add`, `unvec_smul`.
-/

import UnifiedTheory.LayerB.ChoiMatrix

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Kraus

open Matrix Complex
open scoped ComplexOrder

/-! ## 1. The vec/unvec correspondence -/

/-- Vectorize a matrix `V : Matrix n m ℂ` to a function on `Fin m × Fin n`:
    `vec V ⟨a, c⟩ := V c a`.
    The convention matches the Choi-Jamiolkowski indexing
    `J(L)⟨a,c⟩⟨b,d⟩ = L(single a b)c d`. -/
def vec {m n : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) : Fin m × Fin n → ℂ :=
  fun ⟨a, c⟩ => V c a

/-- Unvectorize a function `v : Fin m × Fin n → ℂ` to a matrix:
    `unvec v c a := v ⟨a, c⟩`. -/
def unvec {m n : ℕ} (v : Fin m × Fin n → ℂ) : Matrix (Fin n) (Fin m) ℂ :=
  fun c a => v ⟨a, c⟩

/-! ## 2. Inverse relations -/

@[simp]
theorem vec_unvec {m n : ℕ} (v : Fin m × Fin n → ℂ) :
    vec (unvec v) = v := by
  funext ⟨a, c⟩
  rfl

@[simp]
theorem unvec_vec {m n : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) :
    unvec (vec V) = V := by
  funext c a
  rfl

/-! ## 3. Linearity -/

theorem vec_add {m n : ℕ} (V W : Matrix (Fin n) (Fin m) ℂ) :
    vec (V + W) = vec V + vec W := by
  funext ⟨a, c⟩
  simp [vec, Matrix.add_apply]

theorem vec_smul {m n : ℕ} (r : ℂ) (V : Matrix (Fin n) (Fin m) ℂ) :
    vec (r • V) = r • vec V := by
  funext ⟨a, c⟩
  simp [vec, Matrix.smul_apply]

theorem vec_zero {m n : ℕ} :
    vec (0 : Matrix (Fin n) (Fin m) ℂ) = 0 := by
  funext ⟨a, c⟩
  simp [vec]

theorem unvec_add {m n : ℕ} (v w : Fin m × Fin n → ℂ) :
    unvec (v + w) = unvec v + unvec w := by
  funext c a
  simp [unvec, Pi.add_apply, Matrix.add_apply]

theorem unvec_smul {m n : ℕ} (r : ℂ) (v : Fin m × Fin n → ℂ) :
    unvec (r • v) = r • unvec v := by
  funext c a
  simp [unvec, Pi.smul_apply, Matrix.smul_apply]

theorem unvec_zero {m n : ℕ} :
    unvec (0 : Fin m × Fin n → ℂ) = 0 := by
  funext c a
  simp [unvec]

/-! ## 4. vec/unvec evaluation lemmas -/

@[simp]
theorem vec_apply {m n : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (a : Fin m) (c : Fin n) :
    vec V ⟨a, c⟩ = V c a := rfl

@[simp]
theorem unvec_apply {m n : ℕ} (v : Fin m × Fin n → ℂ)
    (c : Fin n) (a : Fin m) :
    unvec v c a = v ⟨a, c⟩ := rfl

end UnifiedTheory.LayerB.Kraus
