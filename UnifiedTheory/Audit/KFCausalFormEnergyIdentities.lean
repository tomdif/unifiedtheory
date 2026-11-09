/- Exact quadratic identities for the form resolvent. Completing the
square controls the bounded Yosida energy by the original closed form. -/
import UnifiedTheory.Audit.KFCausalShiftedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFormEnergyIdentities
noncomputable section
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalShiftedForm

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def quadratic (A B : E →L[ℂ] H) (t : ℝ) (u : E) : ℝ :=
  (inner ℂ u (formOperator A B t u)).re

theorem quadratic_eq (A B : E →L[ℂ] H) (t : ℝ) (u : E) :
    quadratic A B t u = ‖A u‖^2+Real.exp (2*t)*‖B u‖^2 := by
  rw [quadratic,formOperator_pairing,complex_inner_square,complex_inner_square]
  simp only [← Complex.ofReal_mul,← Complex.ofReal_add,Complex.ofReal_re]

theorem quadratic_nonneg (A B : E →L[ℂ] H) (t : ℝ) (u : E) : 0 ≤ quadratic A B t u := by
  rw [quadratic_eq]
  positivity

theorem quadratic_smul (A B : E →L[ℂ] H) (t r : ℝ) (u : E) :
    quadratic A B t (r • u) = r^2*quadratic A B t u := by
  simp only [quadratic,ContinuousLinearMap.map_smul_of_tower,inner_smul_left_eq_smul,
    inner_smul_right_eq_smul,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem quadratic_sub_smul (A B : E →L[ℂ] H) (t a : ℝ) (w u : E) :
    quadratic A B t (w-a • u) = quadratic A B t w -
      2*a*(inner ℂ u (formOperator A B t w)).re + a^2*quadratic A B t u := by
  have hc : (inner ℂ w (formOperator A B t u)).re = (inner ℂ u (formOperator A B t w)).re := by
    rw [← formOperator_inner_symm A B t w u]
    exact inner_re_symm (𝕜 := ℂ) _ _
  simp only [quadratic,map_sub,ContinuousLinearMap.map_smul_of_tower,
    inner_sub_left,inner_sub_right,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
    Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  rw [hc]
  ring

omit [CompleteSpace H] in
theorem vector_energy_split (a : ℝ) (f r : H) (q : ℝ)
    (hq : q = (inner ℂ (f-a • r) r).re) :
    (inner ℂ (a • (f-a • r)) f).re = a*‖f-a • r‖^2+a^2*q := by
  let g := f-a • r
  have he : f = g+a • r := (sub_add_cancel f (a • r)).symm
  change (inner ℂ (a • g) f).re = a*‖g‖^2+a^2*q
  calc
    _ = (inner ℂ (a • g) (g+a • r)).re := congrArg (fun v => (inner ℂ (a • g) v).re) he
    _ = a*‖g‖^2+a^2*(inner ℂ g r).re := by
      rw [inner_add_right,inner_smul_left_eq_smul,inner_smul_left_eq_smul,
        inner_smul_right_eq_smul,complex_inner_square]
      simp only [Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      ring
    _ = _ := by rw [hq]

theorem resolvent_energy_identity (J A B : E →L[ℂ] H) (a t : ℝ) (f : H) (u : E)
    (hu : shiftForm J A B a t u = J.adjoint f) :
    (inner ℂ (a • (f-a • J u)) f).re =
      a*‖f-a • J u‖^2+a^2*quadratic A B t u :=
  vector_energy_split a f (J u) _ (congrArg Complex.re (shifted_variational J A B a t u f hu u))

theorem completed_square (J A B : E →L[ℂ] H) (a t : ℝ) (w u : E)
    (hu : shiftForm J A B a t u = J.adjoint (J w)) :
    quadratic A B t w = (inner ℂ (a • (J w-a • J u)) (J w)).re +
      quadratic A B t (w-a • u)+a*‖J w-a • J u‖^2 := by
  have he := resolvent_energy_identity J A B a t (J w) u hu
  have hq := quadratic_sub_smul A B t a w u
  have hc := congrArg Complex.re (shifted_variational J A B a t u (J w) hu w)
  have hs : (inner ℂ (a • (J w-a • J u)) (J w)).re =
      a*(inner ℂ (J w-a • J u) (J w)).re := by
    rw [inner_smul_left_eq_smul]
    simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hc] at hq
  linear_combination he - hq - 2*hs

theorem resolvent_energy_le_form (J A B : E →L[ℂ] H) (a t : ℝ) (ha : 0 < a) (w u : E)
    (hu : shiftForm J A B a t u = J.adjoint (J w)) :
    (inner ℂ (a • (J w-a • J u)) (J w)).re ≤ quadratic A B t w := by
  rw [completed_square J A B a t w u hu]
  have hq := quadratic_nonneg A B t (w-a • u)
  have hn := mul_nonneg ha.le (sq_nonneg ‖J w-a • J u‖)
  linarith

theorem resolvent_energy_derivative_bounds (J A B : E →L[ℂ] H) (a t : ℝ) (ha : 0 < a)
    (f : H) (u : E) (hu : shiftForm J A B a t u = J.adjoint f) :
    0 ≤ a^2*(2*Real.exp (2*t)*‖B u‖^2) ∧
      a^2*(2*Real.exp (2*t)*‖B u‖^2) ≤ 2*(inner ℂ (a • (f-a • J u)) f).re := by
  constructor
  · positivity
  · rw [resolvent_energy_identity J A B a t f u hu,quadratic_eq]
    have hq := mul_nonneg (sq_nonneg a) (sq_nonneg ‖A u‖)
    have hn := mul_nonneg ha.le (sq_nonneg ‖f-a • J u‖)
    nlinarith

#print axioms quadratic_smul
#print axioms quadratic_sub_smul
#print axioms resolvent_energy_identity
#print axioms completed_square
#print axioms resolvent_energy_le_form
#print axioms resolvent_energy_derivative_bounds

end
end UnifiedTheory.Audit.KFCausalFormEnergyIdentities
