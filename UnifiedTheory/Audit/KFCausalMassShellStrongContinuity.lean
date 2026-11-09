/- Strong continuity of the explicit spacetime translations. The dominating
function is 4*|f|^2, so the proof does not assume a finite shell measure. -/
import UnifiedTheory.Audit.KFCausalMassShellTranslations

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalMassShellStrongContinuity
noncomputable section
open MeasureTheory
open KFCausalRelativisticMassShell KFCausalMassShellTranslations

variable (ρ : Measure ℝ) (δ : ℝ) (f : OneParticle ρ δ)

def difference (b a : Spacetime) (x : ShellPoint) : ℂ :=
  phase δ a x * f x - phase δ b x * f x

theorem difference_bound (b a : Spacetime) (x : ShellPoint) :
    ‖difference ρ δ f b a x‖ ≤ 2*‖f x‖ := by
  have h := norm_sub_le (phase δ a x * f x) (phase δ b x * f x)
  simpa only [difference, norm_mul, phase_norm, one_mul, two_mul] using h

theorem distance_square_integral (b a : Spacetime) :
    ‖translation ρ δ a f - translation ρ δ b f‖^2 =
      ∫ x, ‖difference ρ δ f b a x‖^2 ∂shellMeasure ρ δ := by
  rw [KFCausalPositiveMultiplierEnergy.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (translation ρ δ a f) (translation ρ δ b f),
    translation_coe ρ δ a f, translation_coe ρ δ b f] with x hx ha hb
  simp only [hx, Pi.sub_apply, ha, hb, difference]

theorem distance_square_continuous (b : Spacetime) :
    Continuous (fun a => ‖translation ρ δ a f - translation ρ δ b f‖^2) := by
  simp_rw [distance_square_integral]
  apply continuous_of_dominated (bound := fun x => 4*‖f x‖^2)
  · intro a
    exact (((phase_measurable δ a).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)).sub
      ((phase_measurable δ b).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))).norm.pow 2
  · intro a
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖difference ρ δ f b a x‖)]
    have h := difference_bound ρ δ f b a x
    nlinarith [norm_nonneg (difference ρ δ f b a x), norm_nonneg (f x)]
  · exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)).const_mul 4
  · filter_upwards [] with x
    exact (((phase_continuous δ x).mul continuous_const).sub continuous_const).norm.pow 2

theorem translation_strongly_continuous : Continuous (fun a => translation ρ δ a f) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc := (Real.continuous_sqrt.comp (distance_square_continuous ρ δ f b)).continuousAt
    (x := b)
  simpa only [ContinuousAt, Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_norm, sub_self, norm_zero, abs_zero] using hc

end
end UnifiedTheory.Audit.KFCausalMassShellStrongContinuity
