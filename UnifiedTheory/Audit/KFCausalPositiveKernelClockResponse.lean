/- A full-line clock integration-by-parts lemma for positive transverse
kernels. Integrability of the boundary and its derivative removes both
endpoints. Applications must supply actual energy/response integrability
and a proved kernel derivative bound. -/
import UnifiedTheory.Audit.KFCausalClockResponseTransport
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPositiveKernelClockResponse
noncomputable section
open MeasureTheory
open KFCausalClockResponseTransport (clock coefficient weakSlope pair weakPair)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalShiftedGaussianLongitudinalDifferential
  (inverseClock inverseClock_bound inverseClock_continuous)

def clockWeight (ε a p y s : ℝ) : ℝ := ‖clockAmplitude ε a p y s‖^2
def energy (ε a p y : ℝ) (K : ℝ → ℝ) (s : ℝ) : ℝ := clockWeight ε a p y s*K s
def weakResponse (ε a p y : ℝ) (K : ℝ → ℝ) (s : ℝ) : ℝ :=
  2*(weakSlope ε a p y s).re*energy ε a p y K s
def reducedResponse (ε a p y : ℝ) (K : ℝ → ℝ) (s : ℝ) : ℝ :=
  clockWeight ε a p y s*(coefficient ε y s*K s-deriv K s/clock ε s)
def boundary (ε a p y : ℝ) (K : ℝ → ℝ) (s : ℝ) : ℝ :=
  energy ε a p y K s/clock ε s

theorem pair_self (ε a p y s : ℝ) :
    pair ε a a p p y s = (clockWeight ε a p y s:ℂ) := by
  simp only [pair, Complex.star_def, Complex.conj_mul', clockWeight, Complex.ofReal_pow]

theorem weakPair_self (ε a p y s : ℝ) :
    weakPair ε a a p p y s =
      (2*(weakSlope ε a p y s).re*clockWeight ε a p y s:ℝ) := by
  rw [weakPair, pair_self]
  have he := Complex.re_eq_add_conj (weakSlope ε a p y s)
  simp only [Complex.star_def]
  rw [show starRingEnd ℂ (weakSlope ε a p y s)+weakSlope ε a p y s =
    2*((weakSlope ε a p y s).re:ℂ) by
      rw [he]; ring]
  push_cast
  ring

theorem boundary_derivative (ε a p y s : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hK : Differentiable ℝ K) :
    HasDerivAt (boundary ε a p y K)
      (weakResponse ε a p y K s-reducedResponse ε a p y K s) s := by
  have hd := KFCausalClockResponseTransport.boundary_derivative ε a a p p y s hε hy
    (fun x => (K x:ℂ)) (Complex.ofReal (deriv K s)) ((hK s).hasDerivAt.ofReal_comp)
  simp only [pair_self, weakPair_self, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    ← Complex.ofReal_sub] at hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd
  convert hr using 1
  · ext x
    simp only [boundary, energy, Function.comp_apply, Complex.reCLM_apply, Complex.ofReal_re]
    ring
  · simp only [weakResponse, reducedResponse, energy, Complex.reCLM_apply, Complex.ofReal_re]
    ring

theorem coefficient_abs_bound (ε y s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) : |coefficient ε y s| ≤ 4/ε := by
  have hi := inverseClock_bound ε y s hε hy
  have hn : ‖inverseClock ε y s+(ε:ℂ)*(inverseClock ε y s)^2‖ ≤ 2/ε := by
    calc
      _ ≤ ‖inverseClock ε y s‖+‖(ε:ℂ)*(inverseClock ε y s)^2‖ := norm_add_le _ _
      _ = ‖inverseClock ε y s‖+ε*‖inverseClock ε y s‖^2 := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
      _ ≤ 1/ε+ε*(1/ε)^2 := add_le_add hi
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hi 2) hε.le)
      _ = 2/ε := by field_simp; ring
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hce : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  calc
    _ ≤ |2/clock ε s|+|(inverseClock ε y s+(ε:ℂ)*(inverseClock ε y s)^2).re| := abs_sub _ _
    _ ≤ 2/ε+2/ε := add_le_add
      (by rw [abs_of_pos (div_pos (by norm_num) hc)]
          exact div_le_div_of_nonneg_left (by norm_num) hε hce)
      ((Complex.abs_re_le_norm _).trans hn)
    _ = _ := by ring

theorem coefficient_continuous (ε y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) : Continuous (coefficient ε y) := by
  have hi := inverseClock_continuous ε y hε hy
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hn (s : ℝ) : clock ε s ≠ 0 := by unfold clock; positivity
  exact (continuous_const.div hc hn).sub
    (Complex.continuous_re.comp (hi.add (continuous_const.mul (hi.pow 2))))

theorem reduced_lower (ε a p y C s : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hC : 0 ≤ C)
    (hK : 0 ≤ K s) (hd : deriv K s ≤ C*K s) :
    -((C+2)/ε)*energy ε a p y K s ≤ reducedResponse ε a p y K s := by
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hce : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hcoef := mul_le_mul_of_nonneg_right
    (KFCausalClockResponseTransport.coefficient_lower ε y s hε hy) hK
  have hder : deriv K s/clock ε s ≤ (C/ε)*K s := by
    calc
      _ ≤ (C*K s)/clock ε s := div_le_div_of_nonneg_right hd hc.le
      _ = (C/clock ε s)*K s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC hε hce) hK
  have hh : -((C+2)/ε)*K s ≤ coefficient ε y s*K s-deriv K s/clock ε s := by
    have he : -((C+2)/ε)*K s = -(2/ε)*K s-(C/ε)*K s := by ring
    rw [he]
    linarith
  have hw : 0 ≤ clockWeight ε a p y s := sq_nonneg _
  convert mul_le_mul_of_nonneg_left hh hw using 1
  simp only [energy]
  ring

theorem full_clock_identity_and_bound (ε a p y C : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hC : 0 ≤ C)
    (hK : ContDiff ℝ 1 K) (hpos : ∀ s, 0 ≤ K s)
    (hd : ∀ s, |deriv K s| ≤ C*K s)
    (hE : Integrable (energy ε a p y K) volume)
    (hW : Integrable (weakResponse ε a p y K) volume) :
    (∫ s, weakResponse ε a p y K s) = ∫ s, reducedResponse ε a p y K s ∧
      -((C+2)/ε)*(∫ s, energy ε a p y K s) ≤ ∫ s, weakResponse ε a p y K s := by
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hcn (s : ℝ) : clock ε s ≠ 0 := by unfold clock; positivity
  have hcp (s : ℝ) : 0 < clock ε s := by unfold clock; positivity
  have hce (s : ℝ) : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hρ : Continuous (clockWeight ε a p y) :=
    (clockAmplitude_smooth ε a p y hε hy).continuous.norm.pow 2
  have hEn (s : ℝ) : 0 ≤ energy ε a p y K s := mul_nonneg (sq_nonneg _) (hpos s)
  have hB : Integrable (boundary ε a p y K) volume := by
    apply (hE.const_mul (1/ε)).mono'
      ((hρ.mul hK.continuous).div hc hcn).aestronglyMeasurable
    filter_upwards [] with s
    change ‖energy ε a p y K s/clock ε s‖ ≤ (1/ε)*energy ε a p y K s
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hEn s) (hcp s).le)]
    change energy ε a p y K s/clock ε s ≤ (1/ε)*energy ε a p y K s
    calc
      _ ≤ energy ε a p y K s/ε := div_le_div_of_nonneg_left (hEn s) hε (hce s)
      _ = _ := by ring
  have hR : Integrable (reducedResponse ε a p y K) volume := by
    apply (hE.const_mul ((4+C)/ε)).mono'
      (hρ.mul (((coefficient_continuous ε y hε hy).mul hK.continuous).sub
        (hK.continuous_deriv_one.div hc hcn))).aestronglyMeasurable
    filter_upwards [] with s
    change ‖clockWeight ε a p y s*(coefficient ε y s*K s-deriv K s/clock ε s)‖ ≤
      ((4+C)/ε)*energy ε a p y K s
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hder : |deriv K s/clock ε s| ≤ (C/ε)*K s := by
      rw [abs_div, abs_of_pos (hcp s)]
      calc
        _ ≤ (C*K s)/clock ε s := div_le_div_of_nonneg_right (hd s) (hcp s).le
        _ = (C/clock ε s)*K s := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left hC hε (hce s)) (hpos s)
    have hcoef : |coefficient ε y s*K s| ≤ (4/ε)*K s := by
      rw [abs_mul, abs_of_nonneg (hpos s)]
      exact mul_le_mul_of_nonneg_right (coefficient_abs_bound ε y s hε hy) (hpos s)
    have hb := (abs_sub (coefficient ε y s*K s) (deriv K s/clock ε s)).trans
      (add_le_add hcoef hder)
    convert mul_le_mul_of_nonneg_left hb (sq_nonneg ‖clockAmplitude ε a p y s‖) using 1
    simp only [clockWeight, energy]
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun s => boundary_derivative ε a p y s K hε hy (hK.differentiable (by norm_num)))
    (hW.sub hR) hB
  rw [integral_sub hW hR] at hz
  have he := sub_eq_zero.mp hz
  refine ⟨he, ?_⟩
  rw [he, ← integral_const_mul]
  exact integral_mono (hE.const_mul _) hR
    (fun s => reduced_lower ε a p y C s K hε hy hC (hpos s)
      ((le_abs_self _).trans (hd s)))

#print axioms pair_self
#print axioms weakPair_self
#print axioms boundary_derivative
#print axioms coefficient_abs_bound
#print axioms coefficient_continuous
#print axioms reduced_lower
#print axioms full_clock_identity_and_bound
end
end UnifiedTheory.Audit.KFCausalPositiveKernelClockResponse
