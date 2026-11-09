/- The homogeneous regularized form admits all momentum modulations of
the dressed Gaussian. Their totality is proved by L1 Fourier uniqueness.
Closedness, a self-adjoint Hamiltonian and the six-mode limit remain separate. -/
import UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
import UnifiedTheory.Audit.KFCausalFourierUniqueness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalFourierUniqueness

def modulate (p : ℝ) (f : ℝ → ℂ) (q : ℝ) : ℂ :=
  (Real.fourierChar (p*q) : ℂ)*f q

theorem modulate_norm (p : ℝ) (f : ℝ → ℂ) (q : ℝ) : ‖modulate p f q‖=‖f q‖ := by
  simp [modulate]

theorem modulate_continuous (p : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    Continuous (modulate p f) := by
  exact ((continuous_subtype_val.comp Real.continuous_fourierChar).comp
    (continuous_const.mul continuous_id)).mul hf

theorem modulate_integrable (p : ℝ) (f : ℝ → ℂ) (hf : Integrable f) :
    Integrable (modulate p f) := by
  apply hf.norm.mono'
    (((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with q
  exact (modulate_norm p f q).le

theorem fourier_modulate (p : ℝ) (f : ℝ → ℂ) (k : ℝ) :
    (𝓕 (modulate p f)) k=(𝓕 f) (k-p) := by
  simp only [Real.fourier_real_eq,Circle.smul_def,smul_eq_mul,modulate]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← mul_assoc,← Circle.coe_mul,← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem inverseHalf_modulate (ε : ℝ) (hε : 0 < ε) (p : ℝ) :
    inverseHalfApply ε hε (modulate p (trial ε hε))=modulate p gaussian := by
  funext q
  have h := congrFun (trial_inverseHalf ε hε) q
  simpa only [inverseHalfApply,modulate,mul_div_assoc] using
    congrArg (fun z : ℂ => (Real.fourierChar (p*q) : ℂ)*z) h

theorem modulated_momentum_integrable (hbar p : ℝ) :
    Integrable (fun k : ℝ => Real.exp (2*Real.pi*hbar*k)*‖(𝓕 (modulate p gaussian)) k‖^2) := by
  have h := (integrable_cexp_quadratic (b := ((2*Real.pi : ℝ) : ℂ))
    (by simpa using (show (0 : ℝ)<2*Real.pi by positivity))
    ((2*Real.pi*hbar+4*Real.pi*p : ℝ) : ℂ) ((-2*Real.pi*p^2 : ℝ) : ℂ)).norm
  convert h using 1
  funext k
  rw [fourier_modulate,gaussian_fourier,gaussian_norm_square,← Real.exp_add,Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]
  ring

theorem modulatedTrial_mem_formCore (ε : ℝ) (hε : 0 < ε) (hbar p : ℝ) :
    FormCore ε hε hbar (modulate p (trial ε hε)) := by
  refine ⟨(modulate_continuous p _ (trial_continuous ε hε)).measurable,?_,?_,?_,?_⟩
  · simpa only [modulate_norm] using trial_square_integrable ε hε
  · simpa only [modulate_norm] using trial_clock_integrable ε hε
  · rw [inverseHalf_modulate]
    exact modulate_integrable p gaussian gaussian_integrable
  · rw [inverseHalf_modulate]
    exact modulated_momentum_integrable hbar p

theorem trial_memLp (ε : ℝ) (hε : 0 < ε) : MemLp (trial ε hε) 2 :=
  (memLp_two_iff_integrable_sq_norm (trial_continuous ε hε).aestronglyMeasurable).mpr
    (trial_square_integrable ε hε)

theorem modulatedTrial_memLp (ε : ℝ) (hε : 0 < ε) (p : ℝ) :
    MemLp (modulate p (trial ε hε)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (modulate_continuous p _ (trial_continuous ε hε)).aestronglyMeasurable).mpr
  simpa only [modulate_norm] using trial_square_integrable ε hε

theorem trial_ne_zero (ε : ℝ) (hε : 0 < ε) (q : ℝ) : trial ε hε q ≠ 0 := by
  have hs : (Real.sqrt (clockQ ε hε q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (clockQ_positive ε hε q)).ne'
  exact mul_ne_zero hs (Complex.exp_ne_zero _)

/-- There is no nonzero L2 vector orthogonal to the explicit family. -/
theorem ae_zero_of_orthogonal_modulations (ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℂ) (hf : MemLp f 2)
    (ho : ∀ p : ℝ, (∫ q, star (modulate p (trial ε hε) q)*f q)=0) :
    ∀ᵐ q, f q=0 := by
  let g : ℝ → ℂ := fun q => star (trial ε hε q)*f q
  have hg : Integrable g := (trial_memLp ε hε).star.integrable_mul hf
  have hF : ∀ p : ℝ, (𝓕 g) p=0 := by
    intro p
    rw [Real.fourier_real_eq]
    convert ho p using 1
    congr 1
    funext q
    simp only [g,modulate,Circle.smul_def,smul_eq_mul,star_mul,Complex.star_def,
      ← Circle.coe_inv_eq_conj,← AddChar.map_neg_eq_inv]
    rw [mul_comm p q]
    ring
  have hz := integrable_zero_of_fourier_zero g hg hF
  filter_upwards [hz] with q hq
  exact (mul_eq_zero.mp hq).resolve_left (star_ne_zero.mpr (trial_ne_zero ε hε q))

def modulatedTrialLp (ε : ℝ) (hε : 0 < ε) (p : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (modulatedTrial_memLp ε hε p).toLp (modulate p (trial ε hε))

/-- The explicit family has dense complex linear span in the full
homogeneous Hilbert space, not merely a nontrivial span. -/
theorem dense_modulated_span (ε : ℝ) (hε : 0 < ε) :
    (Submodule.span ℂ (Set.range (modulatedTrialLp ε hε))).topologicalClosure=⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff,Submodule.eq_bot_iff]
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply ae_zero_of_orthogonal_modulations ε hε f (Lp.memLp f)
  intro p
  have hm : modulatedTrialLp ε hε p ∈
      Submodule.span ℂ (Set.range (modulatedTrialLp ε hε)) :=
    Submodule.subset_span ⟨p,rfl⟩
  have ho := Submodule.inner_right_of_mem_orthogonal hm hf
  rw [L2.inner_def] at ho
  convert ho using 1
  apply integral_congr_ae
  filter_upwards [(modulatedTrial_memLp ε hε p).coeFn_toLp] with q hq
  change star (modulate p (trial ε hε) q)*f q =
    inner ℂ (((modulatedTrial_memLp ε hε p).toLp _) q) (f q)
  rw [hq,RCLike.inner_apply']
  rfl

#print axioms fourier_modulate
#print axioms inverseHalf_modulate
#print axioms modulated_momentum_integrable
#print axioms modulatedTrial_mem_formCore
#print axioms ae_zero_of_orthogonal_modulations
#print axioms dense_modulated_span

end
end UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
