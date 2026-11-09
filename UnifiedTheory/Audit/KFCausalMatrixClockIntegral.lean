/- Integrating a matrix clock-response identity needs an upper kernel
rate bound and integrability of the physical energy and response. The
boundary is controlled by the positive clock floor. -/
import UnifiedTheory.Audit.KFCausalOneSidedIntegral
import UnifiedTheory.Audit.KFCausalClockResponseTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalMatrixClockIntegral
noncomputable section
open MeasureTheory
open KFCausalClockResponseTransport (clock coefficient)

theorem reduced_lower (ε y C s E D : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hC : 0 ≤ C) (hE : 0 ≤ E) (hD : D ≤ C*E) :
    -((C+2)/ε)*E ≤ coefficient ε y s*E-D/clock ε s := by
  have hclock : 0 < clock ε s := by unfold clock; positivity
  have hfloor : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hd : D/clock ε s ≤ (C/ε)*E := by
    calc
      _ ≤ (C*E)/clock ε s := div_le_div_of_nonneg_right hD hclock.le
      _ ≤ (C*E)/ε := div_le_div_of_nonneg_left (mul_nonneg hC hE) hε hfloor
      _ = _ := by ring
  have hc := mul_le_mul_of_nonneg_right
    (KFCausalClockResponseTransport.coefficient_lower ε y s hε hy) hE
  have he : -((C+2)/ε)*E = -(2/ε)*E-(C/ε)*E := by ring
  rw [he]
  linarith

theorem boundary_integrable (ε : ℝ) (E : ℝ → ℝ) (hε : 0 < ε)
    (hE : Integrable E) (hpos : ∀ s, 0 ≤ E s) : Integrable (fun s => E s/clock ε s) := by
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hi : Continuous (fun s => (clock ε s)⁻¹) := hc.inv₀ (fun s => by unfold clock; positivity)
  have hm : AEStronglyMeasurable (fun s => E s/clock ε s) volume := by
    simpa only [Pi.mul_apply,div_eq_mul_inv] using hE.aestronglyMeasurable.mul hi.aestronglyMeasurable
  apply (hE.const_mul (1/ε)).mono' hm
  filter_upwards [] with s
  have hclock : 0 < clock ε s := by unfold clock; positivity
  have hfloor : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hpos s) hclock.le)]
  calc
    E s/clock ε s ≤ E s/ε := div_le_div_of_nonneg_left (hpos s) hε hfloor
    _ = _ := by ring

theorem full_clock_bound (ε y C : ℝ) (E W D : ℝ → ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hC : 0 ≤ C)
    (hE : Integrable E) (hW : Integrable W) (hpos : ∀ s, 0 ≤ E s)
    (hderiv : ∀ s, HasDerivAt (fun u => E u/clock ε u)
      (W s-coefficient ε y s*E s+D s/clock ε s) s)
    (hD : ∀ s, D s ≤ C*E s) :
    -((C+2)/ε)*(∫ s, E s) ≤ ∫ s, W s := by
  have hi := KFCausalOneSidedIntegral.integral_nonneg_of_derivative_upper
    (fun s => E s/clock ε s)
    (fun s => W s-coefficient ε y s*E s+D s/clock ε s)
    (fun s => W s+((C+2)/ε)*E s) hderiv (boundary_integrable ε E hε hE hpos)
    (hW.add (hE.const_mul ((C+2)/ε))) (fun s => by
      have hl := reduced_lower ε y C s (E s) (D s) hε hy hC (hpos s) (hD s)
      linarith)
  rw [integral_add hW (hE.const_mul ((C+2)/ε)),integral_const_mul] at hi
  linarith

#print axioms reduced_lower
#print axioms boundary_integrable
#print axioms full_clock_bound
end
end UnifiedTheory.Audit.KFCausalMatrixClockIntegral
