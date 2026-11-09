/- Differentiating the charge-orbit exponential average under its compact
integral. No differentiation of an unbounded quantum operator is used. -/
import UnifiedTheory.Audit.KFCausalClassicalChargeMean
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClassicalChargeLaplace
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean

theorem mean_exp_derivative (f : ℝ → ℝ) (hf : Continuous f) (a : ℝ) :
    HasDerivAt (fun u => mean (fun θ => Real.exp (u*f θ)))
      (mean (fun θ => f θ*Real.exp (a*f θ))) a := by
  let F := fun u θ => Real.exp (u*f θ)
  let F' := fun u θ => f θ*Real.exp (u*f θ)
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
      convert ((hasDerivAt_id u).mul_const (f θ)).exp using 1
      dsimp [F,F']
      ring))
  exact h.2.const_mul (2*Real.pi)⁻¹

theorem exponentialMean_derivative (C : ℝ) (hC : C ≠ 0) (z : Phase) :
    HasDerivAt (fun u => exponentialMean u z) (-tiltedShear C z/C) C := by
  have h := (mean_exp_derivative (fun θ => shear (rotate θ z)) (shear_continuous z) C⁻¹).comp C
    (hasDerivAt_inv hC)
  have he (u : ℝ) : mean (fun θ => Real.exp (u⁻¹*shear (rotate θ z))) = exponentialMean u z := by
    unfold exponentialMean
    congr 1
    funext θ
    rw [div_eq_mul_inv, mul_comm]
  simp only [Function.comp_def, he] at h
  convert h using 1
  have ht : tiltedShear C z = mean (fun θ => shear (rotate θ z)*
      Real.exp (C⁻¹*shear (rotate θ z)))*C⁻¹ := by
    rw [← mean_mul_const]
    unfold tiltedShear
    congr 1
    funext θ
    rw [mul_comm C⁻¹ (shear (rotate θ z))]
    ring
  rw [ht]
  field_simp

#print axioms mean_exp_derivative
#print axioms exponentialMean_derivative

end
end UnifiedTheory.Audit.KFCausalClassicalChargeLaplace
