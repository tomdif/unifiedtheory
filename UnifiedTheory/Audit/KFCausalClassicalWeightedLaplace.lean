/- Differentiation of the actual normalized charge average with a continuous
matter weight. This is scalar integral calculus, not an operator inequality. -/
import UnifiedTheory.Audit.KFCausalClassicalChargeLaplace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalWeightedLaplace
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargeMean

theorem mean_weighted_exp_derivative (w f : ℝ → ℝ) (hw : Continuous w) (hf : Continuous f) (a : ℝ) :
    HasDerivAt (fun u => mean (fun θ => w θ*Real.exp (u*f θ)))
      (mean (fun θ => w θ*f θ*Real.exp (a*f θ))) a := by
  let F := fun u θ => w θ*Real.exp (u*f θ)
  let F' := fun u θ => w θ*f θ*Real.exp (u*f θ)
  have hcont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) := by
    dsimp [F']
    fun_prop
  obtain ⟨B,hB⟩ := ((isCompact_Icc : IsCompact (Icc (a-1) (a+1))).prod
    (isCompact_Icc : IsCompact (Icc (0:ℝ) (2*Real.pi)))).exists_bound_of_continuousOn
    hcont.continuousOn
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := volume) (a := 0) (b := 2*Real.pi)
    (bound := fun _ => B)
    (Ioo_mem_nhds (by linarith : a-1 < a) (by linarith : a < a+1))
    (Eventually.of_forall (fun u => (show Continuous (F u) by dsimp [F]; fun_prop).aestronglyMeasurable))
    ((show Continuous (F a) by dsimp [F]; fun_prop).intervalIntegrable _ _)
    ((show Continuous (F' a) by dsimp [F']; fun_prop).aestronglyMeasurable)
    (Eventually.of_forall (fun θ hθ u hu => hB (u,θ)
      ⟨⟨hu.1.le,hu.2.le⟩, by
        rw [uIoc_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)] at hθ
        exact ⟨hθ.1.le,hθ.2⟩⟩))
    (continuous_const.intervalIntegrable _ _)
    (Eventually.of_forall (fun θ _ u _ => by
      convert (((hasDerivAt_id u).mul_const (f θ)).exp).const_mul (w θ) using 1
      dsimp [F,F']
      ring))
  exact h.2.const_mul (2*Real.pi)⁻¹

#print axioms mean_weighted_exp_derivative

end
end UnifiedTheory.Audit.KFCausalClassicalWeightedLaplace
