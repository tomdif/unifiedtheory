import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Hermitian
/-!
# Operator convexity of the matrix inverse (variational form, unconditional)
For positive-definite `A B`, the inverse is operator convex:
`4 · ⟨x,(A+B)⁻¹x⟩ ≤ ⟨x,A⁻¹x⟩ + ⟨x,B⁻¹x⟩`.
Proof: completing the square (only "PSD ⇒ ⟨w,Cw⟩ ≥ 0"), summed over the two terms.
This is the foundational atom of the Lieb-1973 / operator-concavity-of `xᵖ` cascade.
-/
open Matrix
open scoped ComplexOrder MatrixOrder
variable {n : ℕ}
namespace OperatorConvexInverse

/-- `C *ᵥ (C⁻¹ *ᵥ x) = x`. -/
lemma cancel (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosDef) (x : Fin n → ℂ) :
    C *ᵥ (C⁻¹ *ᵥ x) = x := by
  have hCu : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hCu, one_mulVec]

/-- Adjoint move: `star (C⁻¹ *ᵥ x) ⬝ᵥ (C *ᵥ z) = star x ⬝ᵥ z`. -/
lemma adj (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosDef) (x z : Fin n → ℂ) :
    star (C⁻¹ *ᵥ x) ⬝ᵥ (C *ᵥ z) = star x ⬝ᵥ z := by
  have hCu : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have hHinv : C⁻¹ᴴ = C⁻¹ := hC.1.inv
  rw [dotProduct_mulVec, star_mulVec, hHinv, vecMul_vecMul,
      Matrix.nonsing_inv_mul _ hCu, vecMul_one]

/-- `star (C⁻¹ *ᵥ x) ⬝ᵥ x = star x ⬝ᵥ (C⁻¹ *ᵥ x)` (self-adjointness of `C⁻¹`). -/
lemma hxx (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosDef) (x : Fin n → ℂ) :
    star (C⁻¹ *ᵥ x) ⬝ᵥ x = star x ⬝ᵥ (C⁻¹ *ᵥ x) := by
  have := adj C hC x (C⁻¹ *ᵥ x); rwa [cancel C hC] at this

/-- Completing the square: the PSD expansion. -/
lemma var (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosDef) (x y : Fin n → ℂ) :
    0 ≤ star y ⬝ᵥ (C *ᵥ y) - star y ⬝ᵥ x - star x ⬝ᵥ y + star x ⬝ᵥ (C⁻¹ *ᵥ x) := by
  have h := hC.posSemidef.dotProduct_mulVec_nonneg (y - C⁻¹ *ᵥ x)
  have e : star (y - C⁻¹ *ᵥ x) ⬝ᵥ (C *ᵥ (y - C⁻¹ *ᵥ x))
      = star y ⬝ᵥ (C *ᵥ y) - star y ⬝ᵥ x - star x ⬝ᵥ y + star x ⬝ᵥ (C⁻¹ *ᵥ x) := by
    rw [mulVec_sub, cancel C hC, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        adj C hC, hxx C hC]; ring
  rw [e] at h; exact h

theorem operator_convex_inv (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (x : Fin n → ℂ) :
    (4 : ℂ) * (star x ⬝ᵥ ((A + B)⁻¹ *ᵥ x))
      ≤ star x ⬝ᵥ (A⁻¹ *ᵥ x) + star x ⬝ᵥ (B⁻¹ *ᵥ x) := by
  have hAB : (A + B).PosDef := hA.add hB
  set y : Fin n → ℂ := (2 : ℂ) • ((A + B)⁻¹ *ᵥ x) with hy
  have hA' := var A hA x y
  have hB' := var B hB x y
  have k1 : star y ⬝ᵥ (A *ᵥ y) + star y ⬝ᵥ (B *ᵥ y)
      = (4 : ℂ) * (star x ⬝ᵥ ((A + B)⁻¹ *ᵥ x)) := by
    rw [← dotProduct_add, ← add_mulVec, hy, mulVec_smul, cancel (A + B) hAB,
        star_smul, smul_dotProduct, dotProduct_smul, hxx (A + B) hAB]
    simp only [star_ofNat, smul_eq_mul]; ring
  have k2 : star y ⬝ᵥ x = (2 : ℂ) * (star x ⬝ᵥ ((A + B)⁻¹ *ᵥ x)) := by
    rw [hy, star_smul, smul_dotProduct, hxx (A + B) hAB]; simp only [star_ofNat, smul_eq_mul]
  have k3 : star x ⬝ᵥ y = (2 : ℂ) * (star x ⬝ᵥ ((A + B)⁻¹ *ᵥ x)) := by
    rw [hy, dotProduct_smul]; simp only [smul_eq_mul]
  have hsum := add_nonneg hA' hB'
  have heq : (star y ⬝ᵥ (A *ᵥ y) - star y ⬝ᵥ x - star x ⬝ᵥ y + star x ⬝ᵥ (A⁻¹ *ᵥ x))
      + (star y ⬝ᵥ (B *ᵥ y) - star y ⬝ᵥ x - star x ⬝ᵥ y + star x ⬝ᵥ (B⁻¹ *ᵥ x))
      = (star x ⬝ᵥ (A⁻¹ *ᵥ x) + star x ⬝ᵥ (B⁻¹ *ᵥ x))
          - (4 : ℂ) * (star x ⬝ᵥ ((A + B)⁻¹ *ᵥ x)) := by
    linear_combination k1 - 2 * k2 - 2 * k3
  rw [heq] at hsum
  exact sub_nonneg.mp hsum

/-- **Operator convexity of the inverse, Löwner/PSD form.**
The matrix difference is positive semidefinite (i.e. `4·(A+B)⁻¹ ≤ A⁻¹ + B⁻¹`). -/
theorem operator_convex_inv_psd (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) :
    (A⁻¹ + B⁻¹ - (4 : ℂ) • (A + B)⁻¹).PosSemidef := by
  have hAB : (A + B).PosDef := hA.add hB
  have hHsmul : ((4 : ℂ) • (A + B)⁻¹).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hAB.1.inv, star_ofNat]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (((hA.1.inv).add (hB.1.inv)).sub hHsmul) ?_
  intro x
  rw [sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
  exact sub_nonneg.mpr (operator_convex_inv A B hA hB x)

end OperatorConvexInverse

-- Axiom-cleanliness check
#print axioms OperatorConvexInverse.operator_convex_inv
#print axioms OperatorConvexInverse.operator_convex_inv_psd
