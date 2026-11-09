/- The linear algebra of one renormalization step as a Schur complement. For a block quadratic form
`Q(x, y) = xᵀAx + 2 xᵀBy + yᵀDy` with `A` symmetric and invertible, completing the square gives
`Q(x, y) = (x + A⁻¹By)ᵀ A (x + A⁻¹By) + yᵀ S y` with `S = D − Bᵀ A⁻¹ B`. Hence, when `A` is positive
semidefinite, `yᵀ S y` is the minimum of `Q(·, y)`, attained at `x = −A⁻¹By`. Two consequences carry a
lower bound on the Hessian of the coarse marginal from one scale to the next (README, "One RG step as a
Schur complement"): the Schur complement is monotone in the form, and it is concave, so the Schur
complement of an average is at least the average of the Schur complements. Nothing here is about the
Yang-Mills measure; the Brascamp-Lieb step that turns the Hessian into an average of Schur complements
is not formalized. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- The block quadratic form `xᵀAx + 2 xᵀBy + yᵀDy`. -/
def Q (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) (x : m → ℝ) (y : n → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) + 2 * (x ⬝ᵥ (B *ᵥ y)) + y ⬝ᵥ (D *ᵥ y)

/-- The Schur complement `D − Bᵀ A⁻¹ B`. -/
noncomputable def schur (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) : Matrix n n ℝ :=
  D - Bᵀ * A⁻¹ * B

/-- The minimizer `−A⁻¹ B y`. -/
noncomputable def argmin (A : Matrix m m ℝ) (B : Matrix m n ℝ) (y : n → ℝ) : m → ℝ :=
  -(A⁻¹ *ᵥ (B *ᵥ y))

/-- **Completing the square.** -/
theorem complete_square (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (x : m → ℝ) (y : n → ℝ) :
    Q A B D x y = (x - argmin A B y) ⬝ᵥ (A *ᵥ (x - argmin A B y)) + y ⬝ᵥ (schur A B D *ᵥ y) := by
  have hAinv : A * A⁻¹ = 1 := mul_nonsing_inv A hdet
  set z := A⁻¹ *ᵥ (B *ᵥ y) with hz
  have hAz : A *ᵥ z = B *ᵥ y := by rw [hz, mulVec_mulVec, hAinv, one_mulVec]
  have hsym (u v : m → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  have hzz : z ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ ((Bᵀ * A⁻¹ * B) *ᵥ y) := by
    rw [hz, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y Bᵀ, vecMul_transpose,
      dotProduct_comm]
  have hx : x - argmin A B y = x + z := by simp [argmin, hz, sub_neg_eq_add]
  rw [hx, Q, schur, sub_mulVec, dotProduct_sub, mulVec_add, dotProduct_add, add_dotProduct,
    add_dotProduct, hAz, hsym z x, hAz, hzz]
  ring

/-- With `A` positive semidefinite, `yᵀ S y` is a lower bound for `Q(·, y)`. -/
theorem schur_le (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (hpsd : ∀ u : m → ℝ, 0 ≤ u ⬝ᵥ (A *ᵥ u))
    (x : m → ℝ) (y : n → ℝ) : y ⬝ᵥ (schur A B D *ᵥ y) ≤ Q A B D x y := by
  rw [complete_square A B D hA hdet x y]
  linarith [hpsd (x - argmin A B y)]

/-- The bound is attained at `x = −A⁻¹ B y`. -/
theorem schur_attained (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (y : n → ℝ) :
    Q A B D (argmin A B y) y = y ⬝ᵥ (schur A B D *ᵥ y) := by
  rw [complete_square A B D hA hdet, sub_self, mulVec_zero, dotProduct_zero, zero_add]

/-- **Monotonicity.** If the form `(A, B, D)` dominates `(A', B', D')` pointwise and `A'` is positive
semidefinite, the Schur complements are ordered the same way. Only `A` needs to be invertible. -/
theorem schur_mono (A A' : Matrix m m ℝ) (B B' : Matrix m n ℝ) (D D' : Matrix n n ℝ)
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (hA' : A'ᵀ = A') (hdet' : IsUnit A'.det)
    (hpsd' : ∀ u : m → ℝ, 0 ≤ u ⬝ᵥ (A' *ᵥ u))
    (hle : ∀ x y, Q A' B' D' x y ≤ Q A B D x y) (y : n → ℝ) :
    y ⬝ᵥ (schur A' B' D' *ᵥ y) ≤ y ⬝ᵥ (schur A B D *ᵥ y) := by
  calc y ⬝ᵥ (schur A' B' D' *ᵥ y) ≤ Q A' B' D' (argmin A B y) y :=
        schur_le A' B' D' hA' hdet' hpsd' _ y
    _ ≤ Q A B D (argmin A B y) y := hle _ y
    _ = y ⬝ᵥ (schur A B D *ᵥ y) := schur_attained A B D hA hdet y

omit [DecidableEq m] in
/-- `Q` is linear in the form. -/
theorem Q_combo (t : ℝ) (A₁ A₂ : Matrix m m ℝ) (B₁ B₂ : Matrix m n ℝ) (D₁ D₂ : Matrix n n ℝ)
    (x : m → ℝ) (y : n → ℝ) :
    Q (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) (t • D₁ + (1 - t) • D₂) x y =
      t * Q A₁ B₁ D₁ x y + (1 - t) * Q A₂ B₂ D₂ x y := by
  simp only [Q, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

/-- **Concavity.** The Schur complement of an average of two forms is at least the average of their
Schur complements. So averaging between RG steps never does worse than the one-shot step. -/
theorem schur_concave (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A₁ A₂ : Matrix m m ℝ) (B₁ B₂ : Matrix m n ℝ) (D₁ D₂ : Matrix n n ℝ)
    (h₁ : A₁ᵀ = A₁) (h₂ : A₂ᵀ = A₂) (hd₁ : IsUnit A₁.det) (hd₂ : IsUnit A₂.det)
    (hp₁ : ∀ u : m → ℝ, 0 ≤ u ⬝ᵥ (A₁ *ᵥ u)) (hp₂ : ∀ u : m → ℝ, 0 ≤ u ⬝ᵥ (A₂ *ᵥ u))
    (hdet : IsUnit (t • A₁ + (1 - t) • A₂).det) (y : n → ℝ) :
    t * (y ⬝ᵥ (schur A₁ B₁ D₁ *ᵥ y)) + (1 - t) * (y ⬝ᵥ (schur A₂ B₂ D₂ *ᵥ y)) ≤
      y ⬝ᵥ (schur (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) (t • D₁ + (1 - t) • D₂) *ᵥ y) := by
  set A := t • A₁ + (1 - t) • A₂
  have hA : Aᵀ = A := by simp [A, transpose_add, transpose_smul, h₁, h₂]
  set x := argmin A (t • B₁ + (1 - t) • B₂) y
  rw [← schur_attained A _ _ hA hdet y, Q_combo]
  have e₁ := schur_le A₁ B₁ D₁ h₁ hd₁ hp₁ x y
  have e₂ := schur_le A₂ B₂ D₂ h₂ hd₂ hp₂ x y
  nlinarith [mul_le_mul_of_nonneg_left e₁ ht0, mul_le_mul_of_nonneg_left e₂ (sub_nonneg.mpr ht1)]

end UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep
