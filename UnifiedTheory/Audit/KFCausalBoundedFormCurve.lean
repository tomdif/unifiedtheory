/- A differentiable curve of bounded form operators on a fixed Hilbert
form space. This does not identify these bounded operators with the
unbounded physical Hamiltonians. -/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBoundedFormCurve
noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def gram (A : E →L[ℂ] H) : E →L[ℂ] E := A.adjoint.comp A

def formOperator (A B : E →L[ℂ] H) (t : ℝ) : E →L[ℂ] E :=
  gram A + Real.exp (2*t) • gram B

theorem formOperator_pairing (A B : E →L[ℂ] H) (t : ℝ) (u v : E) :
    inner ℂ u (formOperator A B t v) = inner ℂ (A u) (A v) +
      (Real.exp (2*t) : ℂ) * inner ℂ (B u) (B v) := by
  change inner ℂ u (A.adjoint (A v) + Real.exp (2*t) • B.adjoint (B v)) = _
  rw [inner_add_right, inner_smul_right_eq_smul, A.adjoint_inner_right, B.adjoint_inner_right]
  rfl

theorem formOperator_derivative (A B : E →L[ℂ] H) (t : ℝ) :
    HasDerivAt (formOperator A B) ((2*Real.exp (2*t)) • gram B) t := by
  have he := (Real.hasDerivAt_exp (2*t)).comp t ((hasDerivAt_id t).const_mul 2)
  have he' : HasDerivAt (fun s : ℝ => Real.exp (2*s)) (2*Real.exp (2*t)) t := by
    convert he using 1
    ring
  exact (he'.smul_const (gram B)).const_add (gram A)

theorem formOperator_continuous (A B : E →L[ℂ] H) : Continuous (formOperator A B) :=
  continuous_iff_continuousAt.mpr fun t => (formOperator_derivative A B t).continuousAt

theorem formOperator_derivative_continuous (B : E →L[ℂ] H) :
    Continuous (fun t : ℝ => (2*Real.exp (2*t)) • gram B) := by
  fun_prop

theorem gram_norm_le (A : E →L[ℂ] H) : ‖gram A‖ ≤ ‖A‖^2 := by
  calc
    ‖gram A‖ ≤ ‖A.adjoint‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖A‖^2 := by rw [ContinuousLinearMap.adjoint, LinearIsometryEquiv.norm_map, pow_two]

theorem formOperator_norm_le (A B : E →L[ℂ] H) (t : ℝ)
    (ha : ‖A‖ ≤ 1) (hb : ‖B‖ ≤ 1) : ‖formOperator A B t‖ ≤ 1+Real.exp (2*t) := by
  have hga : ‖gram A‖ ≤ 1 := (gram_norm_le A).trans (by nlinarith [norm_nonneg A])
  have hgb : ‖gram B‖ ≤ 1 := (gram_norm_le B).trans (by nlinarith [norm_nonneg B])
  calc
    ‖formOperator A B t‖ ≤ ‖gram A‖ + ‖Real.exp (2*t) • gram B‖ := norm_add_le _ _
    _ = ‖gram A‖ + Real.exp (2*t)*‖gram B‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    _ ≤ _ := by nlinarith [Real.exp_pos (2*t)]

theorem formOperator_derivative_norm_le (B : E →L[ℂ] H) (t : ℝ) (hb : ‖B‖ ≤ 1) :
    ‖(2*Real.exp (2*t)) • gram B‖ ≤ 2*Real.exp (2*t) := by
  have hgb : ‖gram B‖ ≤ 1 := (gram_norm_le B).trans (by nlinarith [norm_nonneg B])
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*Real.exp (2*t))]
  nlinarith [Real.exp_pos (2*t)]

#print axioms formOperator_pairing
#print axioms formOperator_derivative
#print axioms formOperator_continuous
#print axioms formOperator_derivative_continuous
#print axioms formOperator_norm_le
#print axioms formOperator_derivative_norm_le

end
end UnifiedTheory.Audit.KFCausalBoundedFormCurve
