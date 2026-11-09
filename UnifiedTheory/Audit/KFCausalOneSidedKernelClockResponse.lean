/- Full-clock lower response estimates need only an upper kernel derivative
bound. Integrability of the actual energy and response supplies vanishing
boundary sequences; no absolute derivative estimate is needed. -/
import UnifiedTheory.Audit.KFCausalOneSidedIntegral
import UnifiedTheory.Audit.KFCausalPositiveKernelClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalOneSidedKernelClockResponse
noncomputable section
open MeasureTheory
open KFCausalPositiveKernelClockResponse
open KFCausalClockResponseTransport (clock coefficient)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude_smooth)

theorem boundary_integrable (ε a p y : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hK : Differentiable ℝ K) (hpos : ∀ s, 0 ≤ K s)
    (hE : Integrable (energy ε a p y K) volume) :
    Integrable (boundary ε a p y K) volume := by
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hcn (s : ℝ) : clock ε s ≠ 0 := by unfold clock; positivity
  have hcp (s : ℝ) : 0 < clock ε s := by unfold clock; positivity
  have hce (s : ℝ) : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hρ : Continuous (clockWeight ε a p y) :=
    (clockAmplitude_smooth ε a p y hε hy).continuous.norm.pow 2
  have hEn (s : ℝ) : 0 ≤ energy ε a p y K s := mul_nonneg (sq_nonneg _) (hpos s)
  apply (hE.const_mul (1/ε)).mono'
    ((hρ.mul hK.continuous).div hc hcn).aestronglyMeasurable
  filter_upwards [] with s
  change ‖energy ε a p y K s/clock ε s‖ ≤ (1/ε)*energy ε a p y K s
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hEn s) (hcp s).le)]
  calc
    energy ε a p y K s/clock ε s ≤ energy ε a p y K s/ε :=
      div_le_div_of_nonneg_left (hEn s) hε (hce s)
    _ = _ := by ring

theorem full_clock_bound_of_reduced_lower (ε a p y κ : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hK : Differentiable ℝ K) (hpos : ∀ s, 0 ≤ K s)
    (hE : Integrable (energy ε a p y K) volume)
    (hW : Integrable (weakResponse ε a p y K) volume)
    (hlower : ∀ s, -κ*energy ε a p y K s ≤ reducedResponse ε a p y K s) :
    -κ*(∫ s, energy ε a p y K s) ≤ ∫ s, weakResponse ε a p y K s := by
  have hB := boundary_integrable ε a p y K hε hy hK hpos hE
  have hi := KFCausalOneSidedIntegral.integral_nonneg_of_derivative_upper
    (boundary ε a p y K)
    (fun s => weakResponse ε a p y K s-reducedResponse ε a p y K s)
    (fun s => weakResponse ε a p y K s+κ*energy ε a p y K s)
    (fun s => boundary_derivative ε a p y s K hε hy hK) hB
    (hW.add (hE.const_mul κ)) (fun s => by linarith [hlower s])
  rw [integral_add hW (hE.const_mul κ), integral_const_mul] at hi
  linarith

theorem full_clock_bound (ε a p y C : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hC : 0 ≤ C)
    (hK : Differentiable ℝ K) (hpos : ∀ s, 0 ≤ K s)
    (hd : ∀ s, deriv K s ≤ C*K s)
    (hE : Integrable (energy ε a p y K) volume)
    (hW : Integrable (weakResponse ε a p y K) volume) :
    -((C+2)/ε)*(∫ s, energy ε a p y K s) ≤ ∫ s, weakResponse ε a p y K s :=
  full_clock_bound_of_reduced_lower ε a p y ((C+2)/ε) K hε hy hK hpos hE hW
    (fun s => reduced_lower ε a p y C s K hε hy hC (hpos s) (hd s))

theorem reduced_lower_of_weighted_upper (ε a p y C s : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hK : 0 ≤ K s) (hd : deriv K s/clock ε s ≤ (C/ε)*K s) :
    -((C+2)/ε)*energy ε a p y K s ≤ reducedResponse ε a p y K s := by
  have hcoef := mul_le_mul_of_nonneg_right
    (KFCausalClockResponseTransport.coefficient_lower ε y s hε hy) hK
  have hh : -((C+2)/ε)*K s ≤ coefficient ε y s*K s-deriv K s/clock ε s := by
    have he : -((C+2)/ε)*K s = -(2/ε)*K s-(C/ε)*K s := by ring
    rw [he]
    linarith
  convert mul_le_mul_of_nonneg_left hh (sq_nonneg ‖
    KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a p y s‖) using 1
  simp only [energy, clockWeight]
  ring

theorem full_clock_bound_of_weighted_upper (ε a p y C : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hK : Differentiable ℝ K) (hpos : ∀ s, 0 ≤ K s)
    (hd : ∀ s, deriv K s/clock ε s ≤ (C/ε)*K s)
    (hE : Integrable (energy ε a p y K) volume)
    (hW : Integrable (weakResponse ε a p y K) volume) :
    -((C+2)/ε)*(∫ s, energy ε a p y K s) ≤ ∫ s, weakResponse ε a p y K s :=
  full_clock_bound_of_reduced_lower ε a p y ((C+2)/ε) K hε hy hK hpos hE hW
    (fun s => reduced_lower_of_weighted_upper ε a p y C s K hε hy (hpos s) (hd s))

theorem full_clock_identity_of_reduced_lower (ε a p y κ : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hK : ContDiff ℝ 1 K) (hpos : ∀ s, 0 ≤ K s)
    (hE : Integrable (energy ε a p y K) volume)
    (hW : Integrable (weakResponse ε a p y K) volume)
    (hlower : ∀ s, -κ*energy ε a p y K s ≤ reducedResponse ε a p y K s) :
    Integrable (reducedResponse ε a p y K) volume ∧
      (∫ s, weakResponse ε a p y K s) = ∫ s, reducedResponse ε a p y K s := by
  have hKd := hK.differentiable (by norm_num)
  have hB := boundary_integrable ε a p y K hε hy hKd hpos hE
  have hi := KFCausalShiftedGaussianLongitudinalDifferential.inverseClock_continuous ε y hε hy
  have hz := (KFCausalClockFloorRelativeShift.argument_smooth ε y).continuous
  have hs : Continuous (KFCausalClockResponseTransport.weakSlope ε a p y) := by
    unfold KFCausalClockResponseTransport.weakSlope
    fun_prop
  have hρ : Continuous (clockWeight ε a p y) :=
    (clockAmplitude_smooth ε a p y hε hy).continuous.norm.pow 2
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hcn (s : ℝ) : clock ε s ≠ 0 := by unfold clock; positivity
  have hWc : Continuous (weakResponse ε a p y K) :=
    (continuous_const.mul (Complex.continuous_re.comp hs)).mul (hρ.mul hK.continuous)
  have hRc : Continuous (reducedResponse ε a p y K) :=
    hρ.mul (((coefficient_continuous ε y hε hy).mul hK.continuous).sub
      (hK.continuous_deriv_one.div hc hcn))
  have hD := KFCausalOneSidedIntegral.derivative_integrable_of_upper
    (boundary ε a p y K)
    (fun s => weakResponse ε a p y K s-reducedResponse ε a p y K s)
    (fun s => weakResponse ε a p y K s+κ*energy ε a p y K s)
    (fun s => boundary_derivative ε a p y s K hε hy hKd)
    (hWc.sub hRc) hB (hW.add (hE.const_mul κ))
    (fun s => by linarith [hlower s])
  have hR : Integrable (reducedResponse ε a p y K) volume := by
    convert hW.sub hD using 1
    ext s
    simp only [Pi.sub_apply]
    ring
  refine ⟨hR, ?_⟩
  have he := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun s => boundary_derivative ε a p y s K hε hy hKd) hD hB
  rw [integral_sub hW hR] at he
  exact sub_eq_zero.mp he

theorem full_clock_identity_and_bound (ε a p y C : ℝ) (K : ℝ → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hC : 0 ≤ C)
    (hK : ContDiff ℝ 1 K) (hpos : ∀ s, 0 ≤ K s)
    (hd : ∀ s, deriv K s ≤ C*K s)
    (hE : Integrable (energy ε a p y K) volume)
    (hW : Integrable (weakResponse ε a p y K) volume) :
    Integrable (reducedResponse ε a p y K) volume ∧
      (∫ s, weakResponse ε a p y K s) = ∫ s, reducedResponse ε a p y K s ∧
      -((C+2)/ε)*(∫ s, energy ε a p y K s) ≤ ∫ s, weakResponse ε a p y K s := by
  obtain ⟨hR, he⟩ := full_clock_identity_of_reduced_lower ε a p y ((C+2)/ε) K
    hε hy hK hpos hE hW
    (fun s => reduced_lower ε a p y C s K hε hy hC (hpos s) (hd s))
  exact ⟨hR, he, full_clock_bound ε a p y C K hε hy hC
    (hK.differentiable (by norm_num)) hpos hd hE hW⟩

#print axioms boundary_integrable
#print axioms full_clock_bound_of_reduced_lower
#print axioms full_clock_bound
#print axioms reduced_lower_of_weighted_upper
#print axioms full_clock_bound_of_weighted_upper
#print axioms full_clock_identity_of_reduced_lower
#print axioms full_clock_identity_and_bound
end
end UnifiedTheory.Audit.KFCausalOneSidedKernelClockResponse
