/- Positive shifted energy forms when the physical embedding and energy
output have different Hilbert targets. Coercivity constructs the inverse;
no invertibility or dynamics conclusion is assumed. -/
import UnifiedTheory.Audit.KFCausalShiftedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSplitTargetShiftedForm
noncomputable section
open UnifiedTheory.Audit.KFCausalCoerciveInverse
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalShiftedForm (formOperator_inner_symm complex_inner_square lowerConstant lowerConstant_positive)

variable {E H K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def shiftForm (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) : E →L[ℂ] E :=
  a • gram J + formOperator A B t

theorem shiftForm_pairing (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (u v : E) :
    inner ℂ u (shiftForm J A B a t v) =
      (a:ℂ)*inner ℂ (J u) (J v) + inner ℂ u (formOperator A B t v) := by
  change inner ℂ u (a • J.adjoint (J v) + formOperator A B t v) = _
  rw [inner_add_right,inner_smul_right_eq_smul,J.adjoint_inner_right]
  rfl

theorem shiftForm_symmetric (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) :
    (shiftForm J A B a t).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℂ (a • J.adjoint (J u) + formOperator A B t u) v =
    inner ℂ u (a • J.adjoint (J v) + formOperator A B t v)
  rw [inner_add_left,inner_add_right,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
    J.adjoint_inner_left,J.adjoint_inner_right,formOperator_inner_symm A B t u v]

theorem shiftForm_inner_symm (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (u v : E) :
    inner ℂ (shiftForm J A B a t u) v = inner ℂ u (shiftForm J A B a t v) :=
  shiftForm_symmetric J A B a t u v

theorem shiftForm_diagonal (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (u : E) :
    (inner ℂ (shiftForm J A B a t u) u).re =
      a*‖J u‖^2 + (‖A u‖^2 + Real.exp (2*t)*‖B u‖^2) := by
  rw [shiftForm_inner_symm J A B a t u u, shiftForm_pairing,formOperator_pairing,
    complex_inner_square (J u),complex_inner_square (A u),complex_inner_square (B u)]
  simp only [← Complex.ofReal_mul,← Complex.ofReal_add,Complex.ofReal_re]

theorem shiftForm_coercive (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ)
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

theorem shiftForm_isUnit (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (ha : 0 < a)
    (hn : ∀ u, ‖u‖^2 = ‖J u‖^2 + ‖A u‖^2 + ‖B u‖^2) :
    IsUnit (shiftForm J A B a t) :=
  coercive_isUnit _ _ (lowerConstant_positive a t ha) (shiftForm_coercive J A B a t hn)
    (shiftForm_symmetric J A B a t)

theorem shiftForm_inverse_norm (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (ha : 0 < a)
    (hn : ∀ u, ‖u‖^2 = ‖J u‖^2 + ‖A u‖^2 + ‖B u‖^2) :
    ‖Ring.inverse (shiftForm J A B a t)‖ ≤ (lowerConstant a t)⁻¹ :=
  inverse_norm_bound _ _ (lowerConstant_positive a t ha) (shiftForm_coercive J A B a t hn)
    (shiftForm_symmetric J A B a t)

theorem shifted_variational (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (u : E) (f : H)
    (hu : shiftForm J A B a t u = J.adjoint f) (v : E) :
    inner ℂ u (formOperator A B t v) = inner ℂ (f-a • J u) (J v) := by
  have hp := congrArg (fun w : E => inner ℂ w v) hu
  change inner ℂ (shiftForm J A B a t u) v = inner ℂ (J.adjoint f) v at hp
  rw [shiftForm_inner_symm J A B a t u v,shiftForm_pairing,J.adjoint_inner_left] at hp
  rw [inner_sub_left,inner_smul_left_eq_smul]
  change inner ℂ u (formOperator A B t v) = inner ℂ f (J v) - (a:ℂ)*inner ℂ (J u) (J v)
  linear_combination hp

#print axioms shiftForm_symmetric
#print axioms shiftForm_diagonal
#print axioms shiftForm_coercive
#print axioms shiftForm_isUnit
#print axioms shiftForm_inverse_norm
#print axioms shifted_variational

end
end UnifiedTheory.Audit.KFCausalSplitTargetShiftedForm
