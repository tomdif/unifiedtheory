/- Strong initial differentiability for every represented Hamiltonian
vector; its Hamiltonian output need only lie in the physical Hilbert space. -/
import UnifiedTheory.Audit.KFCausalFormInitialStrongDerivative
import UnifiedTheory.Audit.KFCausalWeakInitialStrongDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalFormDomainInitialDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalInitialStrongDerivativeCalculus
open UnifiedTheory.Audit.KFCausalFormInitialStrongDerivative
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalMassGram
open UnifiedTheory.Audit.KFCausalShiftedForm
variable {V H G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace H] in
theorem represented_phase_pairing (J : V →L[ℂ] H) (A B : V →L[ℂ] G)
    (r s : ℝ) (w : V) (z : H)
    (hw : ∀ y, inner ℂ w (formOperator A B s y) = inner ℂ z (J y)) (y : V) :
    inner ℂ (phase r • formOperator A B s w) y = inner ℂ (phase r • z) (J y) := by
  rw [inner_smul_left,formOperator_inner_symm,hw,inner_smul_left]

omit [CompleteSpace H] in
theorem represented_slope_split (J : V →L[ℂ] H) (A B : V →L[ℂ] G)
    (r s t : ℝ) (w x : V) (z : H)
    (hw : ∀ y, inner ℂ w (formOperator A B s y) = inner ℂ z (J y)) :
    (inner ℂ (phase r • formOperator A B t x) w).re =
      -(inner ℂ (J x) (phase r • z)).re+
        (Real.exp (2*t)-Real.exp (2*s))*(inner ℂ (phase r • gram B x) w).re := by
  have hq : formOperator A B t x = formOperator A B s x+
      (Real.exp (2*t)-Real.exp (2*s)) • gram B x := by
    simp only [formOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,sub_smul]
    abel
  have hp : inner ℂ (formOperator A B s x) w = inner ℂ (J x) z := by
    rw [← inner_conj_symm (formOperator A B s x) w,hw,inner_conj_symm]
  have hs : (inner ℂ (phase r • formOperator A B s x) w).re =
      -(inner ℂ (J x) (phase r • z)).re := by
    rw [phase_pair,inner_smul_right,hp,inner_smul_right]
  rw [hq,smul_add,inner_add_left,Complex.add_re,hs,smul_comm,
    inner_smul_left_eq_smul,Complex.smul_re,smul_eq_mul]

theorem initial_derivative (J : V →L[ℂ] H) (hJ : DenseRange J)
    (A B : V →L[ℂ] G) (r s : ℝ) (u : ℝ → V) (z : H)
    (hu : Continuous u) (hn : ∀ t, ‖J (u t)‖ = ‖J (u s)‖)
    (hd : ∀ t, HasDerivAt (fun y => gram J (u y))
      (phase r • formOperator A B t (u t)) t)
    (hw : ∀ y, inner ℂ (u s) (formOperator A B s y) = inner ℂ z (J y)) :
    HasDerivAt (fun t => J (u t)) (phase r • z) s := by
  let d := fun t => (inner ℂ (phase r • formOperator A B t (u t)) (u s)).re
  let g := fun t => (inner ℂ (phase r • gram B (u t)) (u s)).re
  let q := fun t => (Real.exp (2*t)-Real.exp (2*s))*g t
  have hg : Continuous g := Complex.continuous_re.comp
    ((((gram B).continuous.comp hu).const_smul (phase r)).inner (𝕜 := ℂ) continuous_const)
  have hq : HasDerivAt q 0 s :=
    vanishing_product_derivative (fun t => Real.exp (2*t)-Real.exp (2*s))
      g s (Real.exp (2*s)*2)
      (by simpa only [mul_one] using
        (((Real.hasDerivAt_exp (2*s)).comp s ((hasDerivAt_id s).const_mul 2)).sub_const (Real.exp (2*s))))
      hg.continuousAt (sub_self _) (phase_gram_diagonal B r (u s))
  have hz : (inner ℂ (J (u s)) (phase r • z)).re = 0 := by
    have hp := congrArg Complex.re (represented_phase_pairing J A B r s (u s) z hw (u s))
    rw [phase_form_diagonal] at hp
    have hr : (inner ℂ (J (u s)) (phase r • z)).re =
        (inner ℂ (phase r • z) (J (u s))).re := inner_re_symm (𝕜 := ℂ) _ _
    exact hr.trans hp.symm
  apply KFCausalWeakInitialStrongDerivative.strong_derivative J hJ
    (fun t => J (u t)) (phase r • z) d q s (J.continuous.comp hu) hn
    (fun t => weak_physical_pairing J u _ hd (u s) t)
    (by simp only [q,sub_self,zero_mul]) hq
  · intro t
    have hp := represented_slope_split J A B r s t (u s) (u t) z hw
    simpa only [inner_sub_left,Complex.sub_re,hz,sub_zero] using hp
  · intro y
    exact (weak_physical_pairing J u _ hd y s).congr_deriv
      (congrArg Complex.re (represented_phase_pairing J A B r s (u s) z hw y))

#print axioms represented_phase_pairing
#print axioms represented_slope_split
#print axioms initial_derivative
end
end UnifiedTheory.Audit.KFCausalFormDomainInitialDerivative
