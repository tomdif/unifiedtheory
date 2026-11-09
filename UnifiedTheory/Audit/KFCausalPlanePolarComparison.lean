/- Transfer an actual angular form inequality to the full plane.
Absolute integrability of the polar pullback is derived from the original
continuous integrable functions, rather than added as a new premise. -/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPlanePolarComparison
noncomputable section
open MeasureTheory Set

def polar (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1*f (p.1*Real.cos p.2,p.1*Real.sin p.2)

theorem polar_integrable (f : ℝ × ℝ → ℝ) (hc : Continuous f) (hi : Integrable f) :
    IntegrableOn (polar f) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hm : Continuous (polar f) := by unfold polar; fun_prop
  refine ⟨hm.aestronglyMeasurable,?_⟩
  change (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, ‖polar f p‖ₑ) < ⊤
  have he : (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, ‖polar f p‖ₑ) =
      ∫⁻ p : ℝ × ℝ in polarCoord.target,
        ENNReal.ofReal p.1 • ‖f (polarCoord.symm p)‖ₑ := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    change ‖p.1*f (p.1*Real.cos p.2,p.1*Real.sin p.2)‖ₑ = _
    rw [← ofReal_norm_eq_enorm, norm_mul, Real.norm_eq_abs, abs_of_pos hp.1,
      ENNReal.ofReal_mul hp.1.le, ofReal_norm_eq_enorm]
    rfl
  rw [he,lintegral_comp_polarCoord_symm (fun p => ‖f p‖ₑ)]
  exact hi.2

theorem radial_marginal_integrable (f : ℝ × ℝ → ℝ) (hc : Continuous f) (hi : Integrable f) :
    Integrable (fun R : ℝ => R*(∫ θ in -Real.pi..Real.pi,
      f (R*Real.cos θ,R*Real.sin θ))) (volume.restrict (Ioi 0)) := by
  have hp := polar_integrable f hc hi
  rw [IntegrableOn,Measure.volume_eq_prod ℝ ℝ,← Measure.prod_restrict] at hp
  have hm := hp.integral_prod_left
  apply hm.congr
  filter_upwards [] with R
  change (∫ θ in Ioo (-Real.pi) Real.pi, R*f (R*Real.cos θ,R*Real.sin θ)) = _
  rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]

theorem integral_polar_order (f : ℝ × ℝ → ℝ) (hc : Continuous f) (hi : Integrable f) :
    (∫ p, f p) = ∫ R in Ioi 0, R*(∫ θ in -Real.pi..Real.pi,
      f (R*Real.cos θ,R*Real.sin θ)) := by
  rw [← integral_comp_polarCoord_symm f]
  change (∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, polar f p) = _
  have hp := polar_integrable f hc hi
  rw [Measure.volume_eq_prod ℝ ℝ] at hp ⊢
  rw [setIntegral_prod _ hp]
  apply integral_congr_ae
  filter_upwards [] with R
  change (∫ θ in Ioo (-Real.pi) Real.pi, R*f (R*Real.cos θ,R*Real.sin θ)) = _
  rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]

theorem integral_le_of_angular (f g : ℝ × ℝ → ℝ)
    (hfc : Continuous f) (hgc : Continuous g) (hfi : Integrable f) (hgi : Integrable g)
    (ha : ∀ R : ℝ, 0 < R → (∫ θ in -Real.pi..Real.pi, f (R*Real.cos θ,R*Real.sin θ)) ≤
      ∫ θ in -Real.pi..Real.pi, g (R*Real.cos θ,R*Real.sin θ)) :
    (∫ p, f p) ≤ ∫ p, g p := by
  rw [integral_polar_order f hfc hfi,integral_polar_order g hgc hgi]
  apply integral_mono_ae (radial_marginal_integrable f hfc hfi)
    (radial_marginal_integrable g hgc hgi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
  exact mul_le_mul_of_nonneg_left (ha R hR) hR.le

#print axioms polar_integrable
#print axioms radial_marginal_integrable
#print axioms integral_polar_order
#print axioms integral_le_of_angular
end
end UnifiedTheory.Audit.KFCausalPlanePolarComparison
