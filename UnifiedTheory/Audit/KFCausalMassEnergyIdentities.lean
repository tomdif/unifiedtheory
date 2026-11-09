/- Identities for regularized physical energy. The symmetric Schrodinger
term cancels exactly, leaving an error with a vanishing mass damping factor. -/
import UnifiedTheory.Audit.KFCausalMassRegularization
import UnifiedTheory.Audit.KFCausalWeakQuadraticDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMassEnergyIdentities
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalMassRegularization
open UnifiedTheory.Audit.KFCausalWeakQuadraticDerivative
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalMassGram
open UnifiedTheory.Audit.KFCausalShiftedForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem schrodinger_diagonal_zero (F : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (F x) y = inner ℂ x (F y)) (hbar : ℝ) (x : E) :
    (inner ℂ ((-Complex.I*((1/hbar:ℝ):ℂ)) • F x) x).re = 0 := by
  have hs' : F.toLinearMap.IsSymmetric := hs
  have hi : (inner ℂ (F x) x).im = 0 := hs'.im_inner_apply_self x
  rw [inner_smul_left]
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,one_mul,mul_zero,sub_zero,zero_add,hi]

theorem energy_error_norm_bound (d y : E) :
    ‖-2*(inner ℂ d y).re‖ ≤ 2*‖d‖*‖y‖ := by
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  norm_num
  have hh := (Complex.abs_re_le_norm (inner ℂ d y)).trans (norm_inner_le_norm d y)
  nlinarith

variable [CompleteSpace E]

theorem regularized_slope_error (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (δ : ℝ) (hδ : 0 < δ)
    (x d : E) (hz : (inner ℂ d x).re = 0) :
    2*(inner ℂ d (massInverse G δ (G x))).re = -2*(inner ℂ d (damping G δ x)).re := by
  rw [massInverse_split G hs hp δ hδ,inner_sub_right,Complex.sub_re,hz]
  ring

theorem regularized_energy_limit (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (hG : DenseRange G)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => energy (massInverse G (δ n)) (G x)) atTop (𝓝 (inner ℂ (G x) x).re) := by
  have hi := (tendsto_const_nhds (x := G x)).inner (𝕜 := ℂ)
    (massInverse_gram_limit G hs hp hG δ hδ hlim x)
  exact Complex.continuous_re.continuousAt.tendsto.comp hi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem embedded_energy_limit (J : E →L[ℂ] H) (hj : Function.Injective J)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => energy (massInverse (gram J) (δ n)) (gram J x)) atTop (𝓝 (‖J x‖^2)) := by
  have hp (v : E) : 0 ≤ (inner ℂ (gram J v) v).re := by
    rw [gram_left_pairing,complex_inner_square,Complex.ofReal_re]
    positivity
  have hh := regularized_energy_limit (gram J) (gram_inner_symm J) hp (gram_dense J hj) δ hδ hlim x
  simpa only [gram_left_pairing,complex_inner_square,Complex.ofReal_re] using hh

theorem embedded_damping_pairing_limit (J : E →L[ℂ] H) (hj : Function.Injective J)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (x d : E) :
    Tendsto (fun n => -2*(inner ℂ d (damping (gram J) (δ n) x)).re) atTop (𝓝 0) := by
  have hp (v : E) : 0 ≤ (inner ℂ (gram J v) v).re := by
    rw [gram_left_pairing,complex_inner_square,Complex.ofReal_re]
    positivity
  have hd := damping_strong_limit (gram J) (gram_inner_symm J) hp (gram_dense J hj) δ hδ hlim x
  have hi := (tendsto_const_nhds (x := d)).inner (𝕜 := ℂ) hd
  have hr := (Complex.continuous_re.continuousAt.tendsto.comp hi).const_mul (-2)
  simpa only [Function.comp_def,inner_zero_right,Complex.zero_re,mul_zero] using hr

#print axioms schrodinger_diagonal_zero
#print axioms energy_error_norm_bound
#print axioms regularized_slope_error
#print axioms regularized_energy_limit
#print axioms embedded_energy_limit
#print axioms embedded_damping_pairing_limit

end
end UnifiedTheory.Audit.KFCausalMassEnergyIdentities
