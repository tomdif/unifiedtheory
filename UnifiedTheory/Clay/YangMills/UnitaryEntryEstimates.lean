/- Explicit entrywise estimates for actual unitary matrix products.
These crude dimension-dependent constants suffice for a computable Haar
neighborhood and do not identify the holonomy with continuum curvature. -/
import UnifiedTheory.Clay.YangMills.UnitaryHolonomyDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.UnitaryEntryEstimates
noncomputable section
open Matrix UnitaryCharacterObservables UnitaryHolonomyDefect WilsonCrossingKernel

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem left_mul_entry (A : Matrix.unitaryGroup d ℂ) (M : Matrix d d ℂ) (r : ℝ)
    (hM : ∀ i j, ‖M i j‖ ≤ r) (i j : d) :
    ‖((A : Matrix d d ℂ) * M) i j‖ ≤ (Fintype.card d : ℝ) * r := by
  rw [Matrix.mul_apply]
  calc
    ‖∑ k, A i k * M k j‖ ≤ ∑ k, ‖A i k * M k j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : d, r := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      calc
        ‖A i k‖ * ‖M k j‖ ≤ 1 * ‖M k j‖ :=
          mul_le_mul_of_nonneg_right (unitary_entry_bound A i k) (norm_nonneg _)
        _ ≤ r := by simpa using hM k j
    _ = _ := by simp

theorem translate_to_identity (A B : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (h : ∀ i j, ‖B i j - A i j‖ ≤ r) (i j : d) :
    ‖((A⁻¹ * B : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) i j -
      (1 : Matrix d d ℂ) i j‖ ≤ (Fintype.card d : ℝ)*r := by
  have he : (((A⁻¹ * B : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) - 1) =
      ((A⁻¹ : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) *
        ((B : Matrix d d ℂ) - (A : Matrix d d ℂ)) := by
    simp only [mul_sub, ← UnitaryGroup.mul_val, inv_mul_cancel, UnitaryGroup.one_val]
  change ‖((((A⁻¹ * B : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) - 1) i j)‖ ≤ _
  rw [he]
  exact left_mul_entry A⁻¹ _ r h i j

theorem inverse_close (A : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix d d ℂ) i j‖ ≤ r) (i j : d) :
    ‖((A⁻¹ : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) i j -
      (1 : Matrix d d ℂ) i j‖ ≤ r := by
  have h := hA j i
  have he : ((A⁻¹ : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) =
      (A : Matrix d d ℂ)ᴴ := rfl
  rw [he]
  rw [conjTranspose_apply]
  calc
    ‖star (A j i) - (1 : Matrix d d ℂ) i j‖ =
        ‖star (A j i - (1 : Matrix d d ℂ) j i)‖ := by
      congr 1
      simp [star_sub, Matrix.one_apply, eq_comm]
    _ = ‖A j i - (1 : Matrix d d ℂ) j i‖ := norm_star _
    _ ≤ r := h

theorem product_close (A B : Matrix.unitaryGroup d ℂ) (r s : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix d d ℂ) i j‖ ≤ r)
    (hB : ∀ i j, ‖B i j - (1 : Matrix d d ℂ) i j‖ ≤ s) (i j : d) :
    ‖((A*B : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) i j -
      (1 : Matrix d d ℂ) i j‖ ≤ r + (Fintype.card d : ℝ)*s := by
  have he : (((A*B : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) - 1) =
      (A : Matrix d d ℂ) * ((B : Matrix d d ℂ) - 1) + ((A : Matrix d d ℂ) - 1) := by
    simp only [mul_sub, mul_one, UnitaryGroup.mul_val]
    abel
  change ‖((((A*B : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) - 1) i j)‖ ≤ _
  rw [he, Matrix.add_apply]
  exact (norm_add_le _ _).trans (by
    have hleft := left_mul_entry A ((B : Matrix d d ℂ)-1) s hB i j
    have hright := hA i j
    change ‖((A : Matrix d d ℂ)*((B : Matrix d d ℂ)-1)) i j‖ +
      ‖A i j-(1 : Matrix d d ℂ) i j‖ ≤ _
    linarith)

/-- Three multiplications cost at most three dimension factors. -/
theorem four_product_close (A B C D : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix d d ℂ) i j‖ ≤ r)
    (hB : ∀ i j, ‖B i j - (1 : Matrix d d ℂ) i j‖ ≤ r)
    (hC : ∀ i j, ‖C i j - (1 : Matrix d d ℂ) i j‖ ≤ r)
    (hD : ∀ i j, ‖D i j - (1 : Matrix d d ℂ) i j‖ ≤ r) (i j : d) :
    ‖((A*B*C⁻¹*D⁻¹ : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) i j -
      (1 : Matrix d d ℂ) i j‖ ≤ (1 + 3*(Fintype.card d : ℝ))*r := by
  have hab := product_close A B r r hA hB
  have habc := product_close (A*B) C⁻¹ (r+(Fintype.card d : ℝ)*r) r hab
    (inverse_close C r hC)
  have habcd := product_close (A*B*C⁻¹) D⁻¹
    ((r+(Fintype.card d : ℝ)*r)+(Fintype.card d : ℝ)*r) r habc (inverse_close D r hD) i j
  convert habcd using 1 <;> ring

theorem trace_defect_le (A : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix d d ℂ) i j‖ ≤ r) :
    (Fintype.card d : ℝ) - (Matrix.trace (A : Matrix d d ℂ)).re ≤
      (Fintype.card d : ℝ)*r := by
  have ht : ‖Matrix.trace ((A : Matrix d d ℂ)-1)‖ ≤ (Fintype.card d : ℝ)*r := by
    unfold Matrix.trace
    calc
      ‖∑ i, ((A : Matrix d d ℂ)-1) i i‖ ≤ ∑ i, ‖A i i-(1 : Matrix d d ℂ) i i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _ : d, r := Finset.sum_le_sum (fun i _ => hA i i)
      _ = _ := by simp
  have hr := Complex.abs_re_le_norm (Matrix.trace ((A : Matrix d d ℂ)-1))
  have hneg := neg_abs_le (Matrix.trace ((A : Matrix d d ℂ)-1)).re
  simp only [Matrix.trace_sub, Matrix.trace_one, Complex.sub_re, Complex.natCast_re] at hr hneg ht
  linarith

theorem square_trace (M : Matrix d d ℂ) :
    (Matrix.trace (Mᴴ*M)).re = ∑ i, ∑ j, ‖M j i‖^2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, neg_mul, sub_neg_eq_add, ← Complex.normSq_apply,
    Complex.normSq_eq_norm_sq]

/-- The exact positive matrix-square identity improves the defect estimate
from a linear entry error to its square. -/
theorem trace_defect_square_le (A : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hA : ∀ i j, ‖A i j - (1 : Matrix d d ℂ) i j‖ ≤ r) :
    (Fintype.card d : ℝ) - (Matrix.trace (A : Matrix d d ℂ)).re ≤
      (Fintype.card d : ℝ)^2*r^2/2 := by
  have hsum : (∑ i, ∑ j, ‖((1 : Matrix d d ℂ)-(A : Matrix d d ℂ)) j i‖^2) ≤
      (Fintype.card d : ℝ)^2*r^2 := by
    calc
      _ ≤ ∑ _ : d, ∑ _ : d, r^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [Matrix.sub_apply, norm_sub_rev]
        exact pow_le_pow_left₀ (norm_nonneg _) (hA j i) 2
      _ = _ := by simp; ring
  rw [← square_trace, matrix_square_trace] at hsum
  linarith

end
end UnifiedTheory.Clay.YangMills.UnitaryEntryEstimates
