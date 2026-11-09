/- A variational resolvent has a quantitative approximation estimate on
the entire form domain. No Hamiltonian operator-domain regularity is
required. The constant is independent of the particular closed form. -/
import UnifiedTheory.Audit.KFCausalShiftedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFormResolventError
noncomputable section
open UnifiedTheory.Audit.KFCausalShiftedForm (complex_inner_square)

variable {V H K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem cross_re_bound (x y : K) : (inner ℂ y (x-y)).re ≤ ‖x‖^2/4 := by
  rw [inner_sub_right,Complex.sub_re,complex_inner_square,Complex.ofReal_re]
  have hi := (Complex.re_le_norm (inner ℂ y x)).trans (norm_inner_le_norm y x)
  nlinarith [sq_nonneg (‖y‖-‖x‖/2)]

theorem variational_error_square (J : V →L[ℂ] H) (L : V →L[ℂ] K)
    (a : ℝ) (ha : 0 < a) (x y : V)
    (hv : ∀ z, inner ℂ (L y) (L z) = (a:ℂ)*inner ℂ (J x-J y) (J z)) :
    ‖J x-J y‖^2 ≤ ‖L x‖^2/(4*a) := by
  have he := congrArg Complex.re (hv (x-y))
  simp only [map_sub,complex_inner_square,← Complex.ofReal_mul,Complex.ofReal_re] at he
  have hb := cross_re_bound (L x) (L y)
  rw [he] at hb
  apply (le_div_iff₀ (by positivity : 0 < 4*a)).mpr
  nlinarith

theorem variational_error_norm (J : V →L[ℂ] H) (L : V →L[ℂ] K)
    (a : ℝ) (ha : 0 < a) (x y : V)
    (hv : ∀ z, inner ℂ (L y) (L z) = (a:ℂ)*inner ℂ (J x-J y) (J z)) :
    ‖J x-J y‖ ≤ Real.sqrt (‖L x‖^2/(4*a)) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (variational_error_square J L a ha x y hv)

theorem sandwich_expectation_error (R D : H →L[ℂ] H)
    (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (x : H) :
    ‖inner ℂ x (R (D (R x)))-inner ℂ x (D x)‖ ≤
      2*‖D‖*‖x‖*‖R x-x‖ := by
  have he : inner ℂ x (R (D (R x)))-inner ℂ x (D x) =
      inner ℂ (R x-x) (D (R x))+inner ℂ x (D (R x-x)) := by
    rw [← hs,inner_sub_left,map_sub,inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℂ (R x-x) (D (R x))‖+‖inner ℂ x (D (R x-x))‖ := norm_add_le _ _
    _ ≤ ‖R x-x‖*(‖D‖*‖R x‖)+‖x‖*(‖D‖*‖R x-x‖) :=
      add_le_add ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _)))
        ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _)))
    _ ≤ ‖R x-x‖*(‖D‖*‖x‖)+‖x‖*(‖D‖*‖R x-x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hR x) (norm_nonneg D)) (norm_nonneg _)) le_rfl
    _ = _ := by ring

#print axioms cross_re_bound
#print axioms variational_error_square
#print axioms variational_error_norm
#print axioms sandwich_expectation_error

end
end UnifiedTheory.Audit.KFCausalFormResolventError
