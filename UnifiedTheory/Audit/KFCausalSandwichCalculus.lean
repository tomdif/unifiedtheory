/- Real-time differentiation and quadratic pairings of a fixed embedding
sandwich. These lemmas transfer the form-space inverse derivative to the
physical Hilbert space. -/
import UnifiedTheory.Audit.KFCausalShiftedForm
import UnifiedTheory.Audit.KFCausalInverseCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSandwichCalculus
noncomputable section
open UnifiedTheory.Audit.KFCausalCoerciveInverse
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalShiftedForm

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def sandwichMap (J : E →L[ℂ] H) : (E →L[ℂ] E) →L[ℂ] (H →L[ℂ] H) :=
  (ContinuousLinearMap.compL ℂ H E H J).comp
    ((ContinuousLinearMap.compL ℂ H E E).flip J.adjoint)

theorem sandwichMap_apply (J : E →L[ℂ] H) (P : E →L[ℂ] E) :
    sandwichMap J P = J.comp (P.comp J.adjoint) := rfl

theorem sandwich_neg_scale (J : E →L[ℂ] H) (P : E →L[ℂ] E) (a : ℝ) :
    -(a • (a • sandwichMap J (-P))) = a • (a • sandwichMap J P) := by
  rw [map_neg,smul_neg,smul_neg,neg_neg]

theorem sandwich_derivative (J : E →L[ℂ] H) (P : ℝ → E →L[ℂ] E) (P' : E →L[ℂ] E)
    (t : ℝ) (hd : HasDerivAt P P' t) :
    HasDerivAt (fun s => sandwichMap J (P s)) (sandwichMap J P') t :=
  (sandwichMap J |>.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd

omit [CompleteSpace E] in
theorem inverse_inner_symm (S : E →L[ℂ] E) (hi : IsUnit S)
    (hs : ∀ u v, inner ℂ (S u) v = inner ℂ u (S v)) (x y : E) :
    inner ℂ (Ring.inverse S x) y = inner ℂ x (Ring.inverse S y) := by
  calc
    _ = inner ℂ (Ring.inverse S x) (S (Ring.inverse S y)) := by rw [inverse_apply_right S hi]
    _ = inner ℂ (S (Ring.inverse S x)) (Ring.inverse S y) := (hs _ _).symm
    _ = _ := by rw [inverse_apply_right S hi]

theorem sandwich_triple_pairing (J : E →L[ℂ] H) (P K : E →L[ℂ] E)
    (hs : ∀ u v, inner ℂ (P u) v = inner ℂ u (P v)) (f g : H) :
    inner ℂ (sandwichMap J (P*K*P) f) g = inner ℂ (K (P (J.adjoint f))) (P (J.adjoint g)) := by
  change inner ℂ (J (P (K (P (J.adjoint f))))) g = _
  rw [← J.adjoint_inner_right,hs]

theorem sandwich_gram_diagonal (J B : E →L[ℂ] H) (P : E →L[ℂ] E)
    (hs : ∀ u v, inner ℂ (P u) v = inner ℂ u (P v)) (r : ℝ) (f : H) :
    (inner ℂ (sandwichMap J (P*(r • gram B)*P) f) f).re = r*‖B (P (J.adjoint f))‖^2 := by
  rw [sandwich_triple_pairing J P (r • gram B) hs]
  change (inner ℂ (r • B.adjoint (B (P (J.adjoint f)))) (P (J.adjoint f))).re = _
  rw [inner_smul_left_eq_smul,B.adjoint_inner_left,complex_inner_square]
  simp only [Complex.real_smul,← Complex.ofReal_mul,Complex.ofReal_re]

#print axioms sandwich_derivative
#print axioms inverse_inner_symm
#print axioms sandwich_triple_pairing
#print axioms sandwich_gram_diagonal

end
end UnifiedTheory.Audit.KFCausalSandwichCalculus
