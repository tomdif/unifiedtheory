/- A weak form trajectory has its actual strong physical derivative at
the initial time when its initial Hamiltonian output is in the form space. -/
import UnifiedTheory.Audit.KFCausalInitialStrongDerivativeCalculus
import UnifiedTheory.Audit.KFCausalMassGram
import UnifiedTheory.Audit.KFCausalShiftedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFormInitialStrongDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalInitialStrongDerivativeCalculus
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalMassGram
open UnifiedTheory.Audit.KFCausalShiftedForm
variable {V H G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def phase (r : ℝ) : ℂ := -Complex.I*(r:ℂ)

omit [CompleteSpace V] in
theorem phase_pair (r : ℝ) (x y : V) :
    (inner ℂ (phase r • x) y).re = -(inner ℂ x (phase r • y)).re := by
  simp only [phase,inner_smul_left,inner_smul_right,map_mul,map_neg,
    Complex.conj_I,Complex.conj_ofReal,neg_neg,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem phase_form_diagonal (A B : V →L[ℂ] G) (r t : ℝ) (w : V) :
    (inner ℂ (phase r • formOperator A B t w) w).re = 0 := by
  rw [phase_pair,inner_smul_right,formOperator_inner_symm,
    formOperator_pairing,complex_inner_square,complex_inner_square]
  simp only [phase,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.add_re,Complex.add_im]
  ring

theorem phase_gram_diagonal (B : V →L[ℂ] G) (r : ℝ) (w : V) :
    (inner ℂ (phase r • gram B w) w).re = 0 := by
  rw [phase_pair,inner_smul_right,gram_left_pairing,complex_inner_square]
  simp only [phase,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem slope_split (J : V →L[ℂ] H) (A B : V →L[ℂ] G) (r s t : ℝ) (w v x : V)
    (hw : formOperator A B s w = gram J v) :
    (inner ℂ (phase r • formOperator A B t x) w).re =
      -(inner ℂ (J x) (phase r • J v)).re+
        (Real.exp (2*t)-Real.exp (2*s))*(inner ℂ (phase r • gram B x) w).re := by
  have hq : formOperator A B t x = formOperator A B s x+
      (Real.exp (2*t)-Real.exp (2*s)) • gram B x := by
    simp only [formOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,sub_smul]
    abel
  have hs : (inner ℂ (phase r • formOperator A B s x) w).re =
      -(inner ℂ (J x) (phase r • J v)).re := by
    rw [phase_pair,formOperator_inner_symm,map_smul,hw,
      ← map_smul (gram J) (phase r) v,gram_right_pairing,map_smul]
  rw [hq,smul_add,inner_add_left,Complex.add_re,hs,smul_comm,
    inner_smul_left_eq_smul,Complex.smul_re,smul_eq_mul]

theorem weak_physical_pairing (J : V →L[ℂ] H) (u q : ℝ → V)
    (hd : ∀ t, HasDerivAt (fun z => gram J (u z)) (q t) t) (y : V) (t : ℝ) :
    HasDerivAt (fun z => (inner ℂ (J (u z)) (J y)).re) (inner ℂ (q t) y).re t := by
  have hp := (hd t).inner ℂ (hasDerivAt_const t y)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
  simpa only [Function.comp_def,gram_left_pairing,inner_zero_right,zero_add,Complex.reCLM_apply] using hr

theorem initial_strong_derivative (J : V →L[ℂ] H) (A B : V →L[ℂ] G)
    (r s : ℝ) (u : ℝ → V) (v : V) (hu : Continuous u)
    (hn : ∀ t, ‖J (u t)‖ = ‖J (u s)‖)
    (hd : ∀ t, HasDerivAt (fun z => gram J (u z))
      (phase r • formOperator A B t (u t)) t)
    (hw : formOperator A B s (u s) = gram J v) :
    HasDerivAt (fun t => J (u t)) (phase r • J v) s := by
  let d := fun t => (inner ℂ (phase r • formOperator A B t (u t)) (u s)).re
  have hv : HasDerivAt (fun t => (inner ℂ (J (u t)) (phase r • J v)).re)
      (‖phase r • J v‖^2) s := by
    have hp := weak_physical_pairing J u _ hd (phase r • v) s
    have he : (inner ℂ (phase r • formOperator A B s (u s)) (phase r • v)).re =
        ‖phase r • J v‖^2 := by
      rw [hw,← map_smul (gram J) (phase r) v,gram_left_pairing,map_smul]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    simpa only [map_smul,he] using hp
  apply initial_derivative_of_scalar_jets (fun t => J (u t)) (phase r • J v) s d hn
    (fun t => weak_physical_pairing J u _ hd (u s) t)
    (phase_form_diagonal A B r s (u s)) _ hv
  let g := fun t => (inner ℂ (phase r • gram B (u t)) (u s)).re
  have hg : Continuous g := Complex.continuous_re.comp
    ((((gram B).continuous.comp hu).const_smul (phase r)).inner (𝕜 := ℂ) continuous_const)
  have hp := vanishing_product_derivative (fun t => Real.exp (2*t)-Real.exp (2*s))
    g s (Real.exp (2*s)*2)
    (by simpa only [mul_one] using
      (((Real.hasDerivAt_exp (2*s)).comp s ((hasDerivAt_id s).const_mul 2)).sub_const (Real.exp (2*s))))
    hg.continuousAt (sub_self _) (phase_gram_diagonal B r (u s))
  have he : d = fun t => -(inner ℂ (J (u t)) (phase r • J v)).re+
      (Real.exp (2*t)-Real.exp (2*s))*g t :=
    funext (fun t => slope_split J A B r s t (u s) v (u t) hw)
  rw [he]
  simpa only [add_zero] using hv.neg.add hp

#print axioms phase_pair
#print axioms phase_form_diagonal
#print axioms phase_gram_diagonal
#print axioms slope_split
#print axioms weak_physical_pairing
#print axioms initial_strong_derivative
end
end UnifiedTheory.Audit.KFCausalFormInitialStrongDerivative
