/- Full-line integration by parts for a moving coefficient vector.
Here E already includes all clock amplitudes, while G is only the geometric
part of its derivative. Applications must prove the boundary identity and
integrability for their actual E and W. -/
import UnifiedTheory.Audit.KFCausalPositiveKernelClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalMovingKernelClockResponse
noncomputable section
open MeasureTheory
open KFCausalClockResponseTransport (clock coefficient)
open KFCausalPositiveKernelClockResponse (coefficient_abs_bound coefficient_continuous)

def reduced (ε y : ℝ) (E G : ℝ → ℝ) (s : ℝ) : ℝ :=
  coefficient ε y s*E s-G s/clock ε s
def boundary (ε : ℝ) (E : ℝ → ℝ) (s : ℝ) : ℝ := E s/clock ε s

theorem reduced_lower (ε y C s : ℝ) (E G : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hC : 0 ≤ C)
    (hE : 0 ≤ E s) (hG : G s ≤ C*E s) :
    -((C+2)/ε)*E s ≤ reduced ε y E G s := by
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hce : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hcoef := mul_le_mul_of_nonneg_right
    (KFCausalClockResponseTransport.coefficient_lower ε y s hε hy) hE
  have hder : G s/clock ε s ≤ (C/ε)*E s := by
    calc
      _ ≤ (C*E s)/clock ε s := div_le_div_of_nonneg_right hG hc.le
      _ = (C/clock ε s)*E s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC hε hce) hE
  unfold reduced
  have he : -((C+2)/ε)*E s = -(2/ε)*E s-(C/ε)*E s := by ring
  rw [he]
  linarith

theorem full_clock_identity_and_bound (ε y C : ℝ) (E G W : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hC : 0 ≤ C)
    (hcE : Continuous E) (hcG : Continuous G) (hpos : ∀ s, 0 ≤ E s)
    (hG : ∀ s, |G s| ≤ C*E s)
    (hd : ∀ s, HasDerivAt (boundary ε E) (W s-reduced ε y E G s) s)
    (hE : Integrable E volume) (hW : Integrable W volume) :
    (∫ s, W s) = ∫ s, reduced ε y E G s ∧
      -((C+2)/ε)*(∫ s, E s) ≤ ∫ s, W s := by
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hcn (s : ℝ) : clock ε s ≠ 0 := by unfold clock; positivity
  have hcp (s : ℝ) : 0 < clock ε s := by unfold clock; positivity
  have hce (s : ℝ) : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hB : Integrable (boundary ε E) volume := by
    apply (hE.const_mul (1/ε)).mono' (hcE.div hc hcn).aestronglyMeasurable
    filter_upwards [] with s
    change ‖E s/clock ε s‖ ≤ (1/ε)*E s
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hpos s) (hcp s).le)]
    calc
      _ ≤ E s/ε := div_le_div_of_nonneg_left (hpos s) hε (hce s)
      _ = _ := by ring
  have hR : Integrable (reduced ε y E G) volume := by
    apply (hE.const_mul ((4+C)/ε)).mono'
      (((coefficient_continuous ε y hε hy).mul hcE).sub
        (hcG.div hc hcn)).aestronglyMeasurable
    filter_upwards [] with s
    change ‖coefficient ε y s*E s-G s/clock ε s‖ ≤ ((4+C)/ε)*E s
    rw [Real.norm_eq_abs]
    have hder : |G s/clock ε s| ≤ (C/ε)*E s := by
      rw [abs_div,abs_of_pos (hcp s)]
      calc
        _ ≤ (C*E s)/clock ε s := div_le_div_of_nonneg_right (hG s) (hcp s).le
        _ = (C/clock ε s)*E s := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left hC hε (hce s)) (hpos s)
    have hcoef : |coefficient ε y s*E s| ≤ (4/ε)*E s := by
      rw [abs_mul,abs_of_nonneg (hpos s)]
      exact mul_le_mul_of_nonneg_right (coefficient_abs_bound ε y s hε hy) (hpos s)
    calc
      _ ≤ |coefficient ε y s*E s|+|G s/clock ε s| := abs_sub _ _
      _ ≤ (4/ε)*E s+(C/ε)*E s := add_le_add hcoef hder
      _ = _ := by ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd (hW.sub hR) hB
  rw [integral_sub hW hR] at hz
  have he := sub_eq_zero.mp hz
  refine ⟨he,?_⟩
  rw [he,← integral_const_mul]
  exact integral_mono (hE.const_mul _) hR
    (fun s => reduced_lower ε y C s E G hε hy hC (hpos s)
      ((le_abs_self _).trans (hG s)))

#print axioms reduced_lower
#print axioms full_clock_identity_and_bound
end
end UnifiedTheory.Audit.KFCausalMovingKernelClockResponse
