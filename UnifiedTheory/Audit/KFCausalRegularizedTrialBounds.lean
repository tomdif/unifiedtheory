/- Regulator-independent estimates for the constructed homogeneous trial
family. These are initial-state form estimates in the common q-coordinate,
not a capacity/regulator convergence theorem or six-mode domain theorem. -/
import UnifiedTheory.Audit.KFCausalRegularizedGaussianCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedTrialBounds
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore

theorem clockQ_lower (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    min q 1 ≤ clockQ ε hε q := by
  have he : chart ε ((chartIso ε hε).symm q)=q :=
    (chartIso ε hε).apply_symm_apply q
  by_cases hs : (chartIso ε hε).symm q ≤ 0
  · have hm := mul_nonpos_of_nonneg_of_nonpos hε.le hs
    dsimp [chart] at he
    exact (min_le_left q 1).trans (by dsimp [clockQ]; linarith)
  · exact (min_le_right q 1).trans (by
      dsimp [clockQ]
      exact Real.one_le_exp (le_of_lt (lt_of_not_ge hs)))

def normFloor : ℝ := Real.exp (-Real.pi/2)/16
def formCeiling : ℝ := ∫ q : ℝ, (2+2*q^2)*Real.exp (-2*Real.pi*q^2)
def normSquare (ε : ℝ) (hε : 0 < ε) : ℝ := ∫ q, ‖trial ε hε q‖^2
def clockForm (ε : ℝ) (hε : 0 < ε) : ℝ := ∫ q, clockQ ε hε q*‖trial ε hε q‖^2
def momentumForm (hbar : ℝ) : ℝ :=
  ∫ k : ℝ, Real.exp (2*Real.pi*hbar*k)*‖(𝓕 gaussian) k‖^2

theorem normFloor_positive : 0 < normFloor := by unfold normFloor; positivity

/-- The interval [1/4,1/2] gives a positive lower norm bound for every
positive regulator, including arbitrarily small regulators. -/
theorem uniform_norm_lower (ε : ℝ) (hε : 0 < ε) : normFloor ≤ normSquare ε hε := by
  have hp : ∀ q ∈ Icc (1/4 : ℝ) (1/2),
      Real.exp (-Real.pi/2)/4 ≤ ‖trial ε hε q‖^2 := by
    intro q hq
    have hc : (1/4 : ℝ) ≤ clockQ ε hε q := by
      have hm : min q 1=q := min_eq_left (by linarith [hq.2])
      have h := clockQ_lower ε hε q
      rw [hm] at h
      linarith [hq.1]
    have hq2 : q^2 ≤ (1/4 : ℝ) := by nlinarith [hq.1,hq.2]
    have hg : Real.exp (-Real.pi/2) ≤ Real.exp (-2*Real.pi*q^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    rw [trial_norm_square]
    calc
      _ = (1/4 : ℝ)*Real.exp (-Real.pi/2) := by ring
      _ ≤ _ := mul_le_mul hc hg (Real.exp_pos _).le (clockQ_positive ε hε q).le
  have hi := setIntegral_ge_of_const_le_real measurableSet_Icc
    (by simp : volume (Icc (1/4 : ℝ) (1/2)) ≠ ⊤) hp
    (trial_square_integrable ε hε).integrableOn
  have hv : volume.real (Icc (1/4 : ℝ) (1/2))=1/4 := by
    rw [Real.volume_real_Icc]; norm_num
  rw [hv] at hi
  have hs := setIntegral_le_integral (s := Icc (1/4 : ℝ) (1/2))
    (trial_square_integrable ε hε) (Filter.Eventually.of_forall (fun q => sq_nonneg ‖trial ε hε q‖))
  dsimp [normFloor,normSquare]
  linarith

theorem uniform_norm_upper (ε : ℝ) (hε : 0 < ε) : normSquare ε hε ≤ formCeiling := by
  apply integral_mono (trial_square_integrable ε hε) polynomial_gaussian_integrable
  intro q
  dsimp only
  rw [trial_norm_square]
  exact mul_le_mul_of_nonneg_right (clockQ_polynomial_bounds ε hε q).1 (Real.exp_pos _).le

theorem uniform_clock_upper (ε : ℝ) (hε : 0 < ε) : clockForm ε hε ≤ formCeiling := by
  apply integral_mono (trial_clock_integrable ε hε) polynomial_gaussian_integrable
  intro q
  dsimp only
  rw [trial_norm_square]
  calc
    _ = (clockQ ε hε q)^2*Real.exp (-2*Real.pi*q^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (clockQ_polynomial_bounds ε hε q).2 (Real.exp_pos _).le

theorem formCeiling_nonnegative : 0 ≤ formCeiling :=
  integral_nonneg (fun _ => by positivity)

theorem momentumForm_nonnegative (hbar : ℝ) : 0 ≤ momentumForm hbar :=
  integral_nonneg (fun _ => by positivity)

theorem inverseHalf_const_mul (ε : ℝ) (hε : 0 < ε) (a : ℂ) (ψ : ℝ → ℂ) :
    inverseHalfApply ε hε (fun q => a*ψ q)=fun q => a*inverseHalfApply ε hε ψ q := by
  funext q
  simp only [inverseHalfApply,mul_div_assoc]

theorem fourier_const_mul (a : ℂ) (ψ : ℝ → ℂ) :
    𝓕 (fun q => a*ψ q)=fun k => a*(𝓕 ψ) k := by
  funext k
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul]
  simp_rw [mul_left_comm _ a,integral_const_mul]

theorem formCore_const_mul (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (ψ : ℝ → ℂ) (hψ : FormCore ε hε hbar ψ) (a : ℂ) :
    FormCore ε hε hbar (fun q => a*ψ q) := by
  rcases hψ with ⟨hm,hn,hc,hi,hp⟩
  refine ⟨measurable_const.mul hm,?_,?_,?_,?_⟩
  · simpa only [norm_mul,mul_pow] using hn.const_mul (‖a‖^2)
  · convert hc.const_mul (‖a‖^2) using 1
    funext q
    simp only [norm_mul,mul_pow]
    ring
  · rw [inverseHalf_const_mul]
    exact hi.const_mul a
  · rw [inverseHalf_const_mul,fourier_const_mul]
    convert hp.const_mul (‖a‖^2) using 1
    funext q
    simp only [norm_mul,mul_pow]
    ring

def normalizedTrial (ε : ℝ) (hε : 0 < ε) (q : ℝ) : ℂ :=
  ((Real.sqrt (normSquare ε hε))⁻¹ : ℝ)*trial ε hε q

theorem normalization_square (ε : ℝ) (hε : 0 < ε) :
    ‖(((Real.sqrt (normSquare ε hε))⁻¹ : ℝ) : ℂ)‖^2=(normSquare ε hε)⁻¹ := by
  have hn : 0 ≤ normSquare ε hε := (trial_norm_integral_positive ε hε).le
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow]
  rw [Real.sq_sqrt hn]

theorem normalizedTrial_mem_formCore (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    FormCore ε hε hbar (normalizedTrial ε hε) :=
  formCore_const_mul ε hε hbar _ (trial_mem_formCore ε hε hbar) _

theorem normalizedTrial_norm_one (ε : ℝ) (hε : 0 < ε) :
    ∫ q, ‖normalizedTrial ε hε q‖^2=1 := by
  simp only [normalizedTrial,norm_mul,mul_pow,normalization_square,integral_const_mul]
  exact inv_mul_cancel₀ (trial_norm_integral_positive ε hε).ne'

/-- This Rayleigh quotient is the energy of the normalized homogeneous
trial vector. Lambda is the nonnegative vacuum coupling. -/
def trialEnergy (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) : ℝ :=
  (clockForm ε hε/2+coupling*Real.exp (2*t)*momentumForm hbar)/normSquare ε hε

theorem uniform_trial_energy (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (hcoupling : 0 ≤ coupling) :
    trialEnergy ε hε hbar coupling t ≤
      (formCeiling/2+coupling*Real.exp (2*t)*momentumForm hbar)/normFloor := by
  have hn := uniform_norm_lower ε hε
  have hnpos := lt_of_lt_of_le normFloor_positive hn
  have hu : clockForm ε hε/2+coupling*Real.exp (2*t)*momentumForm hbar ≤
      formCeiling/2+coupling*Real.exp (2*t)*momentumForm hbar := by
    linarith [uniform_clock_upper ε hε]
  have hb : 0 ≤ formCeiling/2+coupling*Real.exp (2*t)*momentumForm hbar :=
    add_nonneg (div_nonneg formCeiling_nonnegative (by norm_num))
      (mul_nonneg (mul_nonneg hcoupling (Real.exp_pos _).le) (momentumForm_nonnegative hbar))
  exact (div_le_div_of_nonneg_right hu hnpos.le).trans
    (div_le_div_of_nonneg_left hb normFloor_positive hn)

theorem normalizedTrial_energy (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    (∫ q, clockQ ε hε q*‖normalizedTrial ε hε q‖^2)/2+
      coupling*Real.exp (2*t)*(∫ k, Real.exp (2*Real.pi*hbar*k)*
        ‖(𝓕 (inverseHalfApply ε hε (normalizedTrial ε hε))) k‖^2)=
      trialEnergy ε hε hbar coupling t := by
  unfold normalizedTrial
  simp only [inverseHalf_const_mul,trial_inverseHalf,fourier_const_mul,
    norm_mul,mul_pow,normalization_square]
  simp_rw [mul_left_comm _ ((normSquare ε hε)⁻¹),integral_const_mul]
  dsimp [trialEnergy,clockForm,momentumForm]
  ring

#print axioms clockQ_lower
#print axioms uniform_norm_lower
#print axioms uniform_norm_upper
#print axioms uniform_clock_upper
#print axioms uniform_trial_energy
#print axioms formCore_const_mul
#print axioms normalizedTrial_mem_formCore
#print axioms normalizedTrial_norm_one
#print axioms normalizedTrial_energy

end
end UnifiedTheory.Audit.KFCausalRegularizedTrialBounds
