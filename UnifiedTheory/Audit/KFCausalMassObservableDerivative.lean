/- A bounded physical observable preserving the form domain has an
exact derivative along a form-continuous curve with a strong mass-dual
derivative. No physical strong derivative of the state is assumed. -/
import UnifiedTheory.Audit.KFCausalFormCrossDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMassObservableDerivative
noncomputable section
open scoped Topology
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mass_intertwines (J : V →L[ℂ] H) (D : H →L[ℂ] H) (R : V →L[ℂ] V)
    (hR : ∀ x, J (R x)=D (J x)) (hD : ∀ x y, inner ℂ (D x) y=inner ℂ x (D y)) (x : V) :
    KFCausalBoundedFormCurve.gram J (R x)=R.adjoint (KFCausalBoundedFormCurve.gram J x) := by
  apply ext_inner_left ℂ
  intro y
  rw [KFCausalMassGram.gram_right_pairing,ContinuousLinearMap.adjoint_inner_right,
    KFCausalMassGram.gram_right_pairing,hR,hR,hD]

theorem expectation_derivative (J : V →L[ℂ] H) (D : H →L[ℂ] H) (R : V →L[ℂ] V)
    (hR : ∀ x, J (R x)=D (J x)) (hD : ∀ x y, inner ℂ (D x) y=inner ℂ x (D y))
    (u : ℝ → V) (p : V) (s : ℝ) (hu : ContinuousAt u s)
    (hd : HasDerivAt (fun t => KFCausalBoundedFormCurve.gram J (u t)) p s) :
    HasDerivAt (fun t => (inner ℂ (J (u t)) (D (J (u t)))).re)
      (2*(inner ℂ p (R (u s))).re) s := by
  have hr : HasDerivAt (fun t => KFCausalBoundedFormCurve.gram J (R (u t))) (R.adjoint p) s := by
    simpa only [mass_intertwines J D R hR hD] using (R.adjoint.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hd
  have hp := KFCausalFormCrossDerivative.physical_pairing_derivative J u (fun t => R (u t))
    p (R.adjoint p) s (R.continuous.continuousAt.comp hu) hd hr
  have hx := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hp
  have he : (inner ℂ (R (u s)) p).re=(inner ℂ p (R (u s))).re := inner_re_symm (𝕜 := ℂ) (R (u s)) p
  simpa only [hR,Function.comp_def,Complex.reCLM_apply,Complex.add_re,
    ContinuousLinearMap.adjoint_inner_right,he,← two_mul] using hx

omit [CompleteSpace H] in
theorem quadratic_difference_bound (D : H →L[ℂ] H) (hD : ∀ x, ‖D x‖ ≤ ‖x‖) (x y : H) :
    |(inner ℂ x (D x)).re-(inner ℂ y (D y)).re| ≤ (‖x‖+‖y‖)*‖x-y‖ := by
  have he : inner ℂ x (D x)-inner ℂ y (D y)=inner ℂ (x-y) (D x)+inner ℂ y (D (x-y)) := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    ring
  have hb := (Complex.abs_re_le_norm (inner ℂ x (D x)-inner ℂ y (D y))).trans
    ((congrArg norm he).le.trans (norm_add_le _ _))
  have h1 := (norm_inner_le_norm (𝕜 := ℂ) (x-y) (D x)).trans
    (mul_le_mul_of_nonneg_left (hD x) (norm_nonneg _))
  have h2 := (norm_inner_le_norm (𝕜 := ℂ) y (D (x-y))).trans
    (mul_le_mul_of_nonneg_left (hD (x-y)) (norm_nonneg _))
  simp only [Complex.sub_re] at hb
  nlinarith only [hb,h1,h2]

#print axioms mass_intertwines
#print axioms expectation_derivative
#print axioms quadratic_difference_bound
end
end UnifiedTheory.Audit.KFCausalMassObservableDerivative
