/- A continuous periodic function with nonnegative sums of four translates
has nonnegative mean. Only the final function needs integrability; this
allows initial endpoint terms to cancel before taking an integral. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalPeriodicFourTermAverage
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

theorem shift_integral (f : ℝ → ℝ) (hp : Function.Periodic f 1) (d : ℝ) :
    (∫ t, f (t+d) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by
  change (∫ t in Set.Ioc 0 1, f (t+d)) = ∫ t in Set.Ioc 0 1, f t
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_comm 1 d] using hp.intervalIntegral_add_eq d 0

theorem shift_integrable (f : ℝ → ℝ) (hf : Continuous f) (d : ℝ) :
    Integrable (fun t => f (t+d)) angleMeasure :=
  (continuous_angle_memLp _ (hf.comp (continuous_id.add continuous_const))).integrable (by norm_num)

theorem nonnegative (f : ℝ → ℝ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (d₁ d₂ d₃ : ℝ) (hn : ∀ t, 0 ≤ f t+f (t+d₁)+f (t+d₂)+f (t+d₃)) :
    0 ≤ ∫ t, f t ∂angleMeasure := by
  have h0 : Integrable f angleMeasure := (continuous_angle_memLp _ hf).integrable (by norm_num)
  have h1 := shift_integrable f hf d₁
  have h2 := shift_integrable f hf d₂
  have h3 := shift_integrable f hf d₃
  have h01 : Integrable (fun t => f t+f (t+d₁)) angleMeasure := h0.add h1
  have h012 : Integrable (fun t => f t+f (t+d₁)+f (t+d₂)) angleMeasure := h01.add h2
  have hi : 0 ≤ ∫ t, f t+f (t+d₁)+f (t+d₂)+f (t+d₃) ∂angleMeasure := integral_nonneg hn
  rw [integral_add h012 h3,integral_add h01 h2,integral_add h0 h1,
    shift_integral f hp d₁,shift_integral f hp d₂,shift_integral f hp d₃] at hi
  linarith

#print axioms shift_integral
#print axioms shift_integrable
#print axioms nonnegative
end
end UnifiedTheory.Audit.KFCausalPeriodicFourTermAverage
