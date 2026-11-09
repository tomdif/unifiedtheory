/- A uniform quadratic pointwise remainder gives an operator-norm
derivative for actual L2 multipliers. This will be instantiated with the
Gaussian cutoff rather than assuming momentum-domain preservation. -/
import UnifiedTheory.Audit.KFCausalBoundedLpMultiplier
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalLpMultiplierDerivative
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (B : ℝ → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (D : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
  (b : ℝ → X → ℂ) (d : X → ℂ)
  (hB : ∀ t f, B t f =ᵐ[μ] fun x => b t x*f x)
  (hD : ∀ f, D f =ᵐ[μ] fun x => d x*f x)
  (K : ℝ) (hK : 0 ≤ K)
  (hR : ∀ t x, ‖b t x-b 0 x-(t:ℂ)*d x‖ ≤ K*t^2)

include hB hD hK hR in
theorem remainder_bound (t : ℝ) : ‖B t-B 0-t • D‖ ≤ K*t^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (sq_nonneg t))
  intro f
  change ‖B t f-B 0 f-t • D f‖ ≤ _
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (B t f-B 0 f) (t • D f),Lp.coeFn_sub (B t f) (B 0 f),
    Lp.coeFn_smul t (D f),hB t f,hB 0 f,hD f] with x hs ht hc hb h0 hd
  rw [hs]
  simp only [Pi.sub_apply,ht,hc,Pi.smul_apply,hb,h0,hd,Complex.real_smul]
  rw [show b t x*f x-b 0 x*f x-(t:ℂ)*(d x*f x) = (b t x-b 0 x-(t:ℂ)*d x)*f x by ring,norm_mul]
  exact mul_le_mul_of_nonneg_right (hR t x) (norm_nonneg _)

include hB hD hK hR in
theorem operator_derivative : HasDerivAt B D 0 := by
  apply hasDerivAt_iff_tendsto.mpr
  simp only [sub_zero]
  apply squeeze_zero (fun t => mul_nonneg (inv_nonneg.mpr (norm_nonneg t)) (norm_nonneg _))
    (fun t => (mul_le_mul_of_nonneg_left (remainder_bound B D b d hB hD K hK hR t)
      (inv_nonneg.mpr (norm_nonneg t))).trans_eq (show ‖t‖⁻¹*(K*t^2)=K*‖t‖ by
        rw [Real.norm_eq_abs]
        by_cases ht : t=0
        · simp [ht]
        · rw [← sq_abs t]
          field_simp [abs_ne_zero.mpr ht]))
  simpa only [norm_zero,mul_zero] using
    (tendsto_const_nhds (x := K)).mul (continuous_norm.tendsto (0:ℝ))

#print axioms remainder_bound
#print axioms operator_derivative

end
end UnifiedTheory.Audit.KFCausalLpMultiplierDerivative
