/- Completing-square energy bounds and derivative pairings when the
physical embedding and energy outputs have different Hilbert targets. -/
import UnifiedTheory.Audit.KFCausalSplitTargetShiftedForm
import UnifiedTheory.Audit.KFCausalFormEnergyIdentities
import UnifiedTheory.Audit.KFCausalSandwichCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSplitTargetEnergyIdentities
noncomputable section
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalSplitTargetShiftedForm
open UnifiedTheory.Audit.KFCausalShiftedForm (complex_inner_square)
open UnifiedTheory.Audit.KFCausalFormEnergyIdentities (quadratic quadratic_eq quadratic_nonneg quadratic_sub_smul vector_energy_split)
open UnifiedTheory.Audit.KFCausalSandwichCalculus (sandwichMap sandwich_triple_pairing)

variable {E H K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem resolvent_energy_identity (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (f : H) (u : E)
    (hu : shiftForm J A B a t u = J.adjoint f) :
    (inner ℂ (a • (f-a • J u)) f).re =
      a*‖f-a • J u‖^2+a^2*quadratic A B t u :=
  vector_energy_split a f (J u) _ (congrArg Complex.re (shifted_variational J A B a t u f hu u))

theorem completed_square (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (w u : E)
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

theorem resolvent_energy_le_form (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (ha : 0 < a) (w u : E)
    (hu : shiftForm J A B a t u = J.adjoint (J w)) :
    (inner ℂ (a • (J w-a • J u)) (J w)).re ≤ quadratic A B t w := by
  rw [completed_square J A B a t w u hu]
  have hq := quadratic_nonneg A B t (w-a • u)
  have hn := mul_nonneg ha.le (sq_nonneg ‖J w-a • J u‖)
  linarith

theorem resolvent_energy_derivative_bounds (J : E →L[ℂ] H) (A B : E →L[ℂ] K) (a t : ℝ) (ha : 0 < a)
    (f : H) (u : E) (hu : shiftForm J A B a t u = J.adjoint f) :
    0 ≤ a^2*(2*Real.exp (2*t)*‖B u‖^2) ∧
      a^2*(2*Real.exp (2*t)*‖B u‖^2) ≤ 2*(inner ℂ (a • (f-a • J u)) f).re := by
  constructor
  · positivity
  · rw [resolvent_energy_identity J A B a t f u hu,quadratic_eq]
    have hq := mul_nonneg (sq_nonneg a) (sq_nonneg ‖A u‖)
    have hn := mul_nonneg ha.le (sq_nonneg ‖f-a • J u‖)
    nlinarith

theorem sandwich_gram_diagonal (J : E →L[ℂ] H) (B : E →L[ℂ] K) (P : E →L[ℂ] E)
    (hs : ∀ u v, inner ℂ (P u) v = inner ℂ u (P v)) (r : ℝ) (f : H) :
    (inner ℂ (sandwichMap J (P*(r • gram B)*P) f) f).re = r*‖B (P (J.adjoint f))‖^2 := by
  rw [sandwich_triple_pairing J P (r • gram B) hs]
  change (inner ℂ (r • B.adjoint (B (P (J.adjoint f)))) (P (J.adjoint f))).re = _
  rw [inner_smul_left_eq_smul,B.adjoint_inner_left,complex_inner_square]
  simp only [Complex.real_smul,← Complex.ofReal_mul,Complex.ofReal_re]

#print axioms resolvent_energy_identity
#print axioms completed_square
#print axioms resolvent_energy_le_form
#print axioms resolvent_energy_derivative_bounds
#print axioms sandwich_gram_diagonal

end
end UnifiedTheory.Audit.KFCausalSplitTargetEnergyIdentities
