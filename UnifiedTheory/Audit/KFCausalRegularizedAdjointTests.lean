/- Explicit adjoint test vectors for the homogeneous exponential-momentum
form factor. All growth and integrability obligations are derived for the
regulated clock. This module does not assume an infinite Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalRegularizedFormDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedFormDomain
open UnifiedTheory.Audit.KFCausalFourierUniqueness

theorem inverse_clock_bound (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    (clockQ ε hε q)⁻¹ ≤ 1+Real.exp ((1-q)/ε) := by
  have he : Real.exp ((chartIso ε hε).symm q)+ε*((chartIso ε hε).symm q)=q :=
    (chartIso ε hε).apply_symm_apply q
  by_cases hs : (chartIso ε hε).symm q ≤ 0
  · have hc : Real.exp ((chartIso ε hε).symm q) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr hs
    have hb : -((chartIso ε hε).symm q) ≤ (1-q)/ε := by
      apply (le_div_iff₀ hε).mpr
      nlinarith
    have hg := Real.exp_le_exp.mpr hb
    rw [Real.exp_neg] at hg
    exact hg.trans (by linarith)
  · have hc : 1 ≤ Real.exp ((chartIso ε hε).symm q) :=
      Real.one_le_exp (le_of_lt (lt_of_not_ge hs))
    have hi : (clockQ ε hε q)⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ hc
    linarith [Real.exp_pos ((1-q)/ε)]

theorem quadratic_exp_integrable (b a d : ℝ) (hb : 0 < b) :
    Integrable (fun q : ℝ => Real.exp (-b*q^2+a*q+d)) := by
  have h := (integrable_cexp_quadratic (b := (b : ℂ)) (by simpa using hb)
    (a : ℂ) (d : ℂ)).norm
  convert h using 1
  funext q
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

theorem gaussian_continuous : Continuous gaussian := by unfold gaussian; fun_prop

def inputTest (ε : ℝ) (hε : 0 < ε) (p q : ℝ) : ℂ :=
  gaussian (q-p)/(Real.sqrt (clockQ ε hε q) : ℂ)

theorem inputTest_continuous (ε : ℝ) (hε : 0 < ε) (p : ℝ) : Continuous (inputTest ε hε p) := by
  apply (gaussian_continuous.comp (continuous_id.sub continuous_const)).div
    ((Complex.continuous_ofReal).comp (clockQ_continuous ε hε).sqrt)
  intro q
  change (Real.sqrt (clockQ ε hε q) : ℂ) ≠ 0
  exact_mod_cast (Real.sqrt_pos.mpr (clockQ_positive ε hε q)).ne'

theorem inputTest_square (ε : ℝ) (hε : 0 < ε) (p q : ℝ) :
    ‖inputTest ε hε p q‖^2=(clockQ ε hε q)⁻¹*Real.exp (-2*Real.pi*(q-p)^2) := by
  simp only [inputTest,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (clockQ_positive ε hε q).le,gaussian_norm_square]
  ring

theorem inputTest_memLp (ε : ℝ) (hε : 0 < ε) (p : ℝ) : MemLp (inputTest ε hε p) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (inputTest_continuous ε hε p).aestronglyMeasurable).mpr
  have h0 : Integrable (fun q : ℝ => Real.exp (-2*Real.pi*(q-p)^2)) := by
    convert quadratic_exp_integrable (2*Real.pi) (4*Real.pi*p) (-2*Real.pi*p^2) (by positivity) using 1
    funext q
    congr 1
    ring
  have h1 : Integrable (fun q : ℝ => Real.exp ((1-q)/ε)*Real.exp (-2*Real.pi*(q-p)^2)) := by
    convert quadratic_exp_integrable (2*Real.pi) (4*Real.pi*p-1/ε)
      (1/ε-2*Real.pi*p^2) (by positivity) using 1
    funext q
    rw [← Real.exp_add]
    congr 1
    ring
  apply (h0.add h1).mono' ((inputTest_continuous ε hε p).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),inputTest_square]
  dsimp only [Pi.add_apply]
  have h := mul_le_mul_of_nonneg_right (inverse_clock_bound ε hε q)
    (Real.exp_pos (-2*Real.pi*(q-p)^2)).le
  nlinarith

def testEnvelope (hbar k : ℝ) : ℂ := (Real.exp (-Real.pi*hbar*k) : ℂ)*gaussian k
def outputTest (hbar p : ℝ) : ℝ → ℂ := modulate p (testEnvelope hbar)

theorem testEnvelope_continuous (hbar : ℝ) : Continuous (testEnvelope hbar) := by
  unfold testEnvelope
  have hg := gaussian_continuous
  fun_prop

theorem testEnvelope_memLp (hbar : ℝ) : MemLp (testEnvelope hbar) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (testEnvelope_continuous hbar).aestronglyMeasurable).mpr
  convert quadratic_exp_integrable (2*Real.pi) (-2*Real.pi*hbar) 0 (by positivity) using 1
  funext k
  simp only [testEnvelope,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_pow,gaussian_norm_square,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  push_cast
  ring

theorem testEnvelope_ne_zero (hbar k : ℝ) : testEnvelope hbar k ≠ 0 := by
  exact mul_ne_zero (by exact_mod_cast Real.exp_ne_zero (-Real.pi*hbar*k)) (Complex.exp_ne_zero _)

theorem outputTest_memLp (hbar p : ℝ) : MemLp (outputTest hbar p) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (modulate_continuous p _ (testEnvelope_continuous hbar)).aestronglyMeasurable).mpr
  simpa only [outputTest,modulate_norm] using
    (memLp_two_iff_integrable_sq_norm (testEnvelope_continuous hbar).aestronglyMeasurable).mp
      (testEnvelope_memLp hbar)

def momentumOutput (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : ℝ → ℂ) (k : ℝ) : ℂ :=
  (Real.exp (Real.pi*hbar*k) : ℂ)*(𝓕 (inverseHalfApply ε hε f)) k

/-- The form factor is paired with actual square-integrable input and
output tests. The identity follows from Fourier Fubini, not a formal
exchange of unbounded operators. -/
theorem momentum_pairing (ε : ℝ) (hε : 0 < ε) (hbar p : ℝ)
    (f : ℝ → ℂ) (hf : Integrable (inverseHalfApply ε hε f)) :
    (∫ k, outputTest hbar p k*momentumOutput ε hε hbar f k)=
      ∫ q, inputTest ε hε p q*f q := by
  have hc (k : ℝ) : outputTest hbar p k*momentumOutput ε hε hbar f k=
      (𝓕 (inverseHalfApply ε hε f)) k*modulate p gaussian k := by
    have he : (Real.exp (-Real.pi*hbar*k) : ℂ)*(Real.exp (Real.pi*hbar*k) : ℂ)=1 := by
      rw [← Complex.ofReal_mul,← Real.exp_add]
      simp
    dsimp [outputTest,testEnvelope,momentumOutput,modulate]
    calc
      _ = ((Real.exp (-Real.pi*hbar*k) : ℂ)*(Real.exp (Real.pi*hbar*k) : ℂ))*
        ((𝓕 (inverseHalfApply ε hε f)) k*((Real.fourierChar (p*k) : ℂ)*gaussian k)) := by ring
      _ = _ := by rw [he,one_mul]
  simp_rw [hc]
  rw [integral_fourier_mul _ _ hf (modulate_integrable p gaussian gaussian_integrable)]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [fourier_modulate,gaussian_fourier]
  dsimp [inputTest,inverseHalfApply]
  ring

/-- The output tests separate L2 vectors; this will rule out a vertical
fiber in the closure of the form-factor graph. -/
theorem output_tests_separate (hbar : ℝ) (f : ℝ → ℂ) (hf : MemLp f 2)
    (ho : ∀ p : ℝ, (∫ k, outputTest hbar p k*f k)=0) : ∀ᵐ k, f k=0 := by
  let g : ℝ → ℂ := fun k => testEnvelope hbar k*f k
  have hg : Integrable g := (testEnvelope_memLp hbar).integrable_mul hf
  have hF : ∀ p : ℝ, (𝓕 g) p=0 := by
    intro p
    rw [Real.fourier_real_eq]
    convert ho (-p) using 1
    congr 1
    funext k
    simp only [g,outputTest,modulate,Circle.smul_def,smul_eq_mul]
    rw [show -(k*p)=(-p)*k by ring]
    ring
  have hz := integrable_zero_of_fourier_zero g hg hF
  filter_upwards [hz] with k hk
  exact (mul_eq_zero.mp hk).resolve_left (testEnvelope_ne_zero hbar k)

#print axioms inverse_clock_bound
#print axioms quadratic_exp_integrable
#print axioms inputTest_memLp
#print axioms outputTest_memLp
#print axioms momentum_pairing
#print axioms output_tests_separate

end
end UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
