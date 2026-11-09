/- A nonzero finite-energy vector for the proposed homogeneous regularized
quantum form, in the global q-coordinate. Its Fourier term is proved from
the Gaussian transform, not assumed as a spectral or integrability input.
This does not establish closedness/density of the form or the six-mode limit. -/
import UnifiedTheory.Audit.KFCausalRegularizedLongitudinalPullback
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart

def clockQ (ε : ℝ) (hε : 0 < ε) (q : ℝ) : ℝ := Real.exp ((chartIso ε hε).symm q)

theorem clockQ_positive (ε : ℝ) (hε : 0 < ε) (q : ℝ) : 0 < clockQ ε hε q := Real.exp_pos _

theorem clockQ_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (clockQ ε hε) :=
  Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous

/-- The positive clock grows at most linearly in the global q coordinate. -/
theorem clockQ_bound (ε : ℝ) (hε : 0 < ε) (q : ℝ) : clockQ ε hε q ≤ 1+|q| := by
  have he : chart ε ((chartIso ε hε).symm q)=q := (chartIso ε hε).apply_symm_apply q
  by_cases hs : (chartIso ε hε).symm q ≤ 0
  · have hc : clockQ ε hε q ≤ 1 := by simpa [clockQ] using Real.exp_le_exp.mpr hs
    linarith [abs_nonneg q]
  · have hs' : 0 ≤ (chartIso ε hε).symm q := le_of_lt (lt_of_not_ge hs)
    have hprod := mul_nonneg hε.le hs'
    dsimp [chart] at he
    change Real.exp ((chartIso ε hε).symm q) ≤ 1+|q|
    linarith [le_abs_self q]

theorem clockQ_polynomial_bounds (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    clockQ ε hε q ≤ 2+2*q^2 ∧ (clockQ ε hε q)^2 ≤ 2+2*q^2 := by
  have hc := clockQ_bound ε hε q
  have hp := (clockQ_positive ε hε q).le
  have hs : (clockQ ε hε q)^2 ≤ (1+|q|)^2 :=
    (sq_le_sq₀ hp (by positivity)).mpr hc
  have ha := sq_abs q
  have hb := sq_nonneg (|q|-1)
  constructor <;> nlinarith

def gaussian (q : ℝ) : ℂ := Complex.exp (-Real.pi*(q : ℂ)^2)

theorem gaussian_fourier : 𝓕 gaussian=gaussian := by
  unfold gaussian
  simpa using (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num))

theorem gaussian_norm_square (q : ℝ) : ‖gaussian q‖^2=Real.exp (-2*Real.pi*q^2) := by
  simp only [gaussian,← Complex.ofReal_pow,← Complex.ofReal_neg,← Complex.ofReal_mul,
    Complex.norm_exp,Complex.ofReal_re,← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem gaussian_integrable : Integrable gaussian := by
  exact integrable_cexp_neg_mul_sq (by simpa using Real.pi_pos)

theorem polynomial_gaussian_integrable :
    Integrable (fun q : ℝ => (2+2*q^2)*Real.exp (-2*Real.pi*q^2)) := by
  have h0 := integrable_exp_neg_mul_sq (by positivity : 0 < 2*Real.pi)
  have h2 : Integrable (fun q : ℝ => q^2*Real.exp (-(2*Real.pi)*q^2)) := by
    simpa using integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 2*Real.pi)
      (by norm_num : (-1 : ℝ)<(2 : ℝ))
  convert (h0.const_mul 2).add (h2.const_mul 2) using 1
  funext q
  dsimp only [Pi.add_apply]
  ring

/-- Exponential momentum weight of the actual Fourier Gaussian. -/
theorem gaussian_exponential_momentum_integrable (hbar : ℝ) :
    Integrable (fun k : ℝ => Real.exp (2*Real.pi*hbar*k)*‖(𝓕 gaussian) k‖^2) := by
  have h := (integrable_cexp_quadratic (b := ((2*Real.pi : ℝ) : ℂ))
    (by simpa using (show (0 : ℝ)<2*Real.pi by positivity))
    ((2*Real.pi*hbar : ℝ) : ℂ) 0).norm
  convert h using 1
  funext k
  rw [gaussian_fourier,gaussian_norm_square,← Real.exp_add,Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]
  ring

def trial (ε : ℝ) (hε : 0 < ε) (q : ℝ) : ℂ := (Real.sqrt (clockQ ε hε q) : ℂ)*gaussian q

def inverseHalfApply (ε : ℝ) (hε : 0 < ε) (ψ : ℝ → ℂ) (q : ℝ) : ℂ :=
  ψ q/(Real.sqrt (clockQ ε hε q) : ℂ)

theorem trial_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (trial ε hε) := by
  have hc := clockQ_continuous ε hε
  unfold trial gaussian
  fun_prop

theorem trial_norm_square (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    ‖trial ε hε q‖^2=clockQ ε hε q*Real.exp (-2*Real.pi*q^2) := by
  simp only [trial,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt (clockQ_positive ε hε q).le,gaussian_norm_square]

theorem trial_inverseHalf (ε : ℝ) (hε : 0 < ε) : inverseHalfApply ε hε (trial ε hε)=gaussian := by
  funext q
  have hn : (Real.sqrt (clockQ ε hε q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (clockQ_positive ε hε q)).ne'
  simp only [inverseHalfApply,trial]
  field_simp

theorem trial_square_integrable (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun q => ‖trial ε hε q‖^2) := by
  apply polynomial_gaussian_integrable.mono' ((trial_continuous ε hε).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),trial_norm_square]
  exact mul_le_mul_of_nonneg_right (clockQ_polynomial_bounds ε hε q).1 (Real.exp_pos _).le

theorem trial_clock_integrable (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun q => clockQ ε hε q*‖trial ε hε q‖^2) := by
  apply polynomial_gaussian_integrable.mono'
    ((clockQ_continuous ε hε).mul ((trial_continuous ε hε).norm.pow 2)).aestronglyMeasurable
  filter_upwards [] with q
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (clockQ_positive ε hε q).le (sq_nonneg _)),trial_norm_square]
  calc
    _ = (clockQ ε hε q)^2*Real.exp (-2*Real.pi*q^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (clockQ_polynomial_bounds ε hε q).2 (Real.exp_pos _).le

/-- The ordinary Fourier integral is used only on an explicitly L1
inverse-clock-dressed vector. The three quadratic-form terms are finite. -/
def FormCore (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (ψ : ℝ → ℂ) : Prop :=
  Measurable ψ ∧ Integrable (fun q => ‖ψ q‖^2) ∧
  Integrable (fun q => clockQ ε hε q*‖ψ q‖^2) ∧
  Integrable (inverseHalfApply ε hε ψ) ∧
  Integrable (fun k => Real.exp (2*Real.pi*hbar*k)*‖(𝓕 (inverseHalfApply ε hε ψ)) k‖^2)

theorem trial_mem_formCore (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : FormCore ε hε hbar (trial ε hε) := by
  refine ⟨(trial_continuous ε hε).measurable,trial_square_integrable ε hε,trial_clock_integrable ε hε,?_,?_⟩
  · rw [trial_inverseHalf]
    exact gaussian_integrable
  · rw [trial_inverseHalf]
    exact gaussian_exponential_momentum_integrable hbar

theorem trial_norm_integral_positive (ε : ℝ) (hε : 0 < ε) :
    0 < ∫ q, ‖trial ε hε q‖^2 := by
  apply integral_pos_of_integrable_nonneg_nonzero ((trial_continuous ε hε).norm.pow 2)
    (trial_square_integrable ε hε) (fun _ => sq_nonneg _) (x := 0)
  rw [trial_norm_square]
  exact mul_ne_zero (clockQ_positive ε hε 0).ne' (Real.exp_ne_zero _)

/-- A constructed nonzero vector, not a supplied finite-energy premise. -/
theorem exists_nonzero_formCore (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    ∃ ψ : ℝ → ℂ, FormCore ε hε hbar ψ ∧ 0 < ∫ q, ‖ψ q‖^2 :=
  ⟨trial ε hε,trial_mem_formCore ε hε hbar,trial_norm_integral_positive ε hε⟩

#print axioms clockQ_bound
#print axioms clockQ_polynomial_bounds
#print axioms gaussian_fourier
#print axioms gaussian_norm_square
#print axioms gaussian_exponential_momentum_integrable
#print axioms trial_inverseHalf
#print axioms trial_square_integrable
#print axioms trial_clock_integrable
#print axioms trial_mem_formCore
#print axioms trial_norm_integral_positive
#print axioms exists_nonzero_formCore

end
end UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
