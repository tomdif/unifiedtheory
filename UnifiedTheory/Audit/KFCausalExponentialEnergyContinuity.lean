/- Continuity at zero of an exponential energy integral, derived from
integrable exponential moments on both sides. The domination is proved,
not supplied as a convergence assumption. -/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalExponentialEnergyContinuity
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem exponential_bound (r t k : ℝ) (ht : |t| ≤ r) :
    Real.exp (t*k) ≤ Real.exp (r*k)+Real.exp (-r*k) := by
  rcases le_total 0 k with hk | hk
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (abs_le.mp ht).2 hk)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (abs_le.mp ht).1 hk)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)

theorem integral_continuousAt_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (k ρ : X → ℝ) (hk : Measurable k)
    (hρ : AEStronglyMeasurable ρ μ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (r : ℝ) (hr : 0 < r)
    (hp : Integrable (fun x => Real.exp (r*k x)*ρ x) μ)
    (hm : Integrable (fun x => Real.exp (-r*k x)*ρ x) μ) :
    ContinuousAt (fun t : ℝ => ∫ x, Real.exp (t*k x)*ρ x ∂μ) 0 := by
  have hb : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ r := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with t ht
    simpa only [Real.dist_eq,sub_zero] using (Metric.mem_ball.mp ht).le
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => Real.exp (r*k x)*ρ x+Real.exp (-r*k x)*ρ x)
  · exact Eventually.of_forall (fun t =>
      ((Real.measurable_exp.comp (measurable_const.mul hk)).aestronglyMeasurable).mul hρ)
  · filter_upwards [hb] with t ht
    exact ae_of_all μ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hρ0 x)),
        ← add_mul]
      exact mul_le_mul_of_nonneg_right (exponential_bound r t (k x) ht) (hρ0 x))
  · exact hp.add hm
  · exact ae_of_all μ (fun x => by
      exact ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul
        continuous_const).continuousAt)

#print axioms exponential_bound
#print axioms integral_continuousAt_zero

end
end UnifiedTheory.Audit.KFCausalExponentialEnergyContinuity
