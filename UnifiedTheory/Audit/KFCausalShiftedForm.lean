/- Invertibility and the variational equation for a positive shift of
the energy form, expressed on one fixed reference Hilbert space. -/
import UnifiedTheory.Audit.KFCausalCoerciveInverse
import UnifiedTheory.Audit.KFCausalBoundedFormCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalShiftedForm
noncomputable section
open UnifiedTheory.Audit.KFCausalCoerciveInverse
open UnifiedTheory.Audit.KFCausalBoundedFormCurve

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem formOperator_symmetric (A B : E →L[ℂ] H) (t : ℝ) :
    (formOperator A B t).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℂ (A.adjoint (A u) + Real.exp (2*t) • B.adjoint (B u)) v =
    inner ℂ u (formOperator A B t v)
  rw [formOperator_pairing,inner_add_left,inner_smul_left_eq_smul,
    A.adjoint_inner_left,B.adjoint_inner_left]
  rfl

theorem formOperator_inner_symm (A B : E →L[ℂ] H) (t : ℝ) (u v : E) :
    inner ℂ (formOperator A B t u) v = inner ℂ u (formOperator A B t v) :=
  formOperator_symmetric A B t u v

def shiftForm (J A B : E →L[ℂ] H) (a t : ℝ) : E →L[ℂ] E :=
  a • gram J + formOperator A B t

theorem shiftForm_pairing (J A B : E →L[ℂ] H) (a t : ℝ) (u v : E) :
    inner ℂ u (shiftForm J A B a t v) =
      (a:ℂ)*inner ℂ (J u) (J v) + inner ℂ u (formOperator A B t v) := by
  change inner ℂ u (a • J.adjoint (J v) + formOperator A B t v) = _
  rw [inner_add_right,inner_smul_right_eq_smul,J.adjoint_inner_right]
  rfl

theorem shiftForm_symmetric (J A B : E →L[ℂ] H) (a t : ℝ) :
    (shiftForm J A B a t).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℂ (a • J.adjoint (J u) + formOperator A B t u) v =
    inner ℂ u (a • J.adjoint (J v) + formOperator A B t v)
  rw [inner_add_left,inner_add_right,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
    J.adjoint_inner_left,J.adjoint_inner_right,formOperator_inner_symm A B t u v]

theorem shiftForm_inner_symm (J A B : E →L[ℂ] H) (a t : ℝ) (u v : E) :
    inner ℂ (shiftForm J A B a t u) v = inner ℂ u (shiftForm J A B a t v) :=
  shiftForm_symmetric J A B a t u v

omit [CompleteSpace H] in
theorem complex_inner_square (x : H) : inner ℂ x x = ((‖x‖^2 : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x)

theorem shiftForm_diagonal (J A B : E →L[ℂ] H) (a t : ℝ) (u : E) :
    (inner ℂ (shiftForm J A B a t u) u).re =
      a*‖J u‖^2 + (‖A u‖^2 + Real.exp (2*t)*‖B u‖^2) := by
  rw [shiftForm_inner_symm J A B a t u u, shiftForm_pairing,formOperator_pairing,
    complex_inner_square (J u),complex_inner_square (A u),complex_inner_square (B u)]
  simp only [← Complex.ofReal_mul,← Complex.ofReal_add,Complex.ofReal_re]

def lowerConstant (a t : ℝ) : ℝ := min a (min 1 (Real.exp (2*t)))

theorem lowerConstant_positive (a t : ℝ) (ha : 0 < a) : 0 < lowerConstant a t :=
  lt_min ha (lt_min zero_lt_one (Real.exp_pos _))

theorem shiftForm_coercive (J A B : E →L[ℂ] H) (a t : ℝ)
    (hn : ∀ u, ‖u‖^2 = ‖J u‖^2 + ‖A u‖^2 + ‖B u‖^2) (u : E) :
    lowerConstant a t * ‖u‖^2 ≤ (inner ℂ (shiftForm J A B a t u) u).re := by
  rw [shiftForm_diagonal,hn u]
  have hj := mul_le_mul_of_nonneg_right (min_le_left a (min 1 (Real.exp (2*t)))) (sq_nonneg ‖J u‖)
  have ha := mul_le_mul_of_nonneg_right
    ((min_le_right a (min 1 (Real.exp (2*t)))).trans (min_le_left 1 (Real.exp (2*t)))) (sq_nonneg ‖A u‖)
  have hb := mul_le_mul_of_nonneg_right
    ((min_le_right a (min 1 (Real.exp (2*t)))).trans (min_le_right 1 (Real.exp (2*t)))) (sq_nonneg ‖B u‖)
  unfold lowerConstant
  nlinarith

theorem shiftForm_isUnit (J A B : E →L[ℂ] H) (a t : ℝ) (ha : 0 < a)
    (hn : ∀ u, ‖u‖^2 = ‖J u‖^2 + ‖A u‖^2 + ‖B u‖^2) :
    IsUnit (shiftForm J A B a t) :=
  coercive_isUnit _ _ (lowerConstant_positive a t ha) (shiftForm_coercive J A B a t hn)
    (shiftForm_symmetric J A B a t)

theorem shiftForm_inverse_norm (J A B : E →L[ℂ] H) (a t : ℝ) (ha : 0 < a)
    (hn : ∀ u, ‖u‖^2 = ‖J u‖^2 + ‖A u‖^2 + ‖B u‖^2) :
    ‖Ring.inverse (shiftForm J A B a t)‖ ≤ (lowerConstant a t)⁻¹ :=
  inverse_norm_bound _ _ (lowerConstant_positive a t ha) (shiftForm_coercive J A B a t hn)
    (shiftForm_symmetric J A B a t)

theorem shifted_variational (J A B : E →L[ℂ] H) (a t : ℝ) (u : E) (f : H)
    (hu : shiftForm J A B a t u = J.adjoint f) (v : E) :
    inner ℂ u (formOperator A B t v) = inner ℂ (f-a • J u) (J v) := by
  have hp := congrArg (fun w : E => inner ℂ w v) hu
  change inner ℂ (shiftForm J A B a t u) v = inner ℂ (J.adjoint f) v at hp
  rw [shiftForm_inner_symm J A B a t u v,shiftForm_pairing,J.adjoint_inner_left] at hp
  rw [inner_sub_left,inner_smul_left_eq_smul]
  change inner ℂ u (formOperator A B t v) = inner ℂ f (J v) - (a:ℂ)*inner ℂ (J u) (J v)
  linear_combination hp

#print axioms formOperator_symmetric
#print axioms shiftForm_symmetric
#print axioms shiftForm_diagonal
#print axioms shiftForm_coercive
#print axioms shiftForm_isUnit
#print axioms shiftForm_inverse_norm
#print axioms shifted_variational

end
end UnifiedTheory.Audit.KFCausalShiftedForm
