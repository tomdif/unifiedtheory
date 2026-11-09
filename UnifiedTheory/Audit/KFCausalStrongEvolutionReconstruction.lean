/- Product differentiation for strongly continuous isometries and a
bounded moving coordinate map. No operator-norm derivative of an
isometry family is required. -/
import UnifiedTheory.Audit.KFCausalStrongIsometryDerivative
import UnifiedTheory.Audit.KFCausalHilbertStateEvolution
import UnifiedTheory.Audit.KFCausalMassFormOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalStrongEvolutionReconstruction
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem moving_isometry_derivative (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hc : ∀ x, Continuous (fun t => U t x)) (f : ℝ → H) (v z : H) (s : ℝ)
    (hf : HasDerivAt f v s) (hU : HasDerivAt (fun t => U t (f s)) z s) :
    HasDerivAt (fun t => U t (f t)) (U s v+z) s := by
  have hd := KFCausalStrongIsometryDerivative.derivative_at_zero_vector U hc
    (fun t => f t-f s) v s (hf.sub_const (f s)) (sub_self (f s))
  have hp : HasDerivAt (fun t => U t (f t-f s)+U t (f s)) (U s v+z) s := hd.add hU
  simpa only [map_sub,sub_add_cancel] using hp

theorem moving_coordinates_derivative (J : V →L[ℂ] H) (S : ℝ → V →L[ℂ] V)
    (f : ℝ → V) (D : V →L[ℂ] V) (v q : V) (c : ℂ) (s : ℝ)
    (hS : HasDerivAt S D s) (hf : HasDerivAt f v s)
    (he : D (f s)+S s v = c • q) :
    HasDerivAt (fun t => J (S t (f t))) (c • J q) s := by
  have hd := KFCausalHilbertStateEvolution.operator_apply_derivative S f D v s hS hf
  have hj := (J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hd
  exact hj.congr_deriv ((congrArg J he).trans (map_smul J c q))

theorem graph_reconstruction (J : V →L[ℂ] H) (S : ℝ → V →L[ℂ] V)
    (f : ℝ → V) (D : V →L[ℂ] V) (v q : V) (c : ℂ) (s : ℝ)
    (T : H →ₗ.[ℂ] H) (hg : (J (S s (f s)),J q) ∈ T.graph)
    (hS : HasDerivAt S D s) (hf : HasDerivAt f v s)
    (he : D (f s)+S s v = c • q) :
    ∃ hx : J (S s (f s)) ∈ T.domain,
      HasDerivAt (fun t => J (S t (f t))) (c • T ⟨J (S s (f s)),hx⟩) s := by
  obtain ⟨hx,hval⟩ := (KFCausalMassFormOperator.graph_domain_iff T _ _).mp hg
  refine ⟨hx,?_⟩
  exact (moving_coordinates_derivative J S f D v q c s hS hf he).congr_deriv
    (congrArg (fun y : H => c • y) hval.symm)

#print axioms moving_isometry_derivative
#print axioms moving_coordinates_derivative
#print axioms graph_reconstruction
end
end UnifiedTheory.Audit.KFCausalStrongEvolutionReconstruction
