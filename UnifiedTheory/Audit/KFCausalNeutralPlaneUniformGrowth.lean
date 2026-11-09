/- The uniform pointwise differential estimate implies finite-clock
growth control of the actual integrable centered marginal and original
transverse energy. No derivative-integral interchange is assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneIntegrability
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneUniformGrowth
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure (centeredEnergyDensity)
open UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal (centeredEnergy_plane_integral)
open UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry (scale_im_ne_zero)
open UnifiedTheory.Audit.KFCausalNeutralPlaneActualBound
open UnifiedTheory.Audit.KFCausalNeutralPlaneUniformScore
open UnifiedTheory.Audit.KFCausalNeutralPlaneIntegrability

theorem exponential_comparison (f : ℝ → ℝ) (C : ℝ)
    (hf : Differentiable ℝ f) (hbound : ∀ u, deriv f u ≤ C*f u)
    (s t : ℝ) (hst : s ≤ t) :
    f t ≤ Real.exp (C*(t-s))*f s := by
  let g := fun u : ℝ => Real.exp (-C*u)*f u
  have hd (u : ℝ) :
      HasDerivAt g (Real.exp (-C*u)*(deriv f u-C*f u)) u := by
    convert (((hasDerivAt_id u).const_mul (-C)).exp).mul (hf u).hasDerivAt using 1
    dsimp
    ring
  have hg : Antitone g := antitone_of_hasDerivAt_nonpos hd (fun u =>
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hbound u)))
  have hi := mul_le_mul_of_nonneg_left (hg hst) (Real.exp_pos (C*t)).le
  calc
    f t = Real.exp (C*t)*g t := by
      dsimp [g]
      rw [← mul_assoc,← Real.exp_add]
      simp
    _ ≤ Real.exp (C*t)*g s := hi
    _ = Real.exp (C*(t-s))*f s := by
      dsimp [g]
      rw [← mul_assoc,← Real.exp_add]
      congr 2
      ring

theorem exists_uniform_density_growth (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ε y : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (P : Polynomial ℂ) (s t x z : ℝ), s ≤ t →
        actualDensity α β ε y t P x z ≤ Real.exp (C*(t-s))*actualDensity α β ε y s P x z := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_density_bound α hα
  refine ⟨C,hC,?_⟩
  intro β ε y hε hy hy0 P s t x z hst
  exact exponential_comparison _ C
    (fun u => (actualDensity_derivative α β ε y u hα hε hy hy0 P x z).differentiableAt)
    (fun u => hbound β ε y u hε hy hy0 P x z) s t hst

theorem exists_uniform_integral_growth (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ε y : ℝ, 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (P : Polynomial ℂ) (s t : ℝ), s ≤ t →
        (∫ v : Fin 2 → ℝ, actualDensity α β ε y t P (v 0) (v 1)) ≤
          Real.exp (C*(t-s))*(∫ v : Fin 2 → ℝ, actualDensity α β ε y s P (v 0) (v 1)) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_density_growth α hα
  refine ⟨C,hC,?_⟩
  intro β ε y hβ hw hε hy hy0 P s t hst
  rw [← integral_const_mul]
  exact integral_mono (actualDensity_integrable α β ε y t hα hβ hw hε hy hy0 P)
    ((actualDensity_integrable α β ε y s hα hβ hw hε hy hy0 P).const_mul _)
    (fun v => hbound β ε y hε hy hy0 P s t (v 0) (v 1) hst)

theorem exists_uniform_centeredEnergy_growth (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ε y : ℝ, 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (P : Polynomial ℂ) (s t : ℝ), s ≤ t →
        (∫ q, centeredEnergyDensity α β (scale ε y t) P q) ≤
          Real.exp (C*(t-s))*(∫ q, centeredEnergyDensity α β (scale ε y s) P q) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_integral_growth α hα
  refine ⟨C,hC,?_⟩
  intro β ε y hβ hw hε hy hy0 P s t hst
  rw [centeredEnergy_plane_integral α β (scale ε y t) (scale_im_ne_zero ε y t hε hy hy0),
    centeredEnergy_plane_integral α β (scale ε y s) (scale_im_ne_zero ε y s hε hy hy0)]
  exact hbound β ε y hβ hw hε hy hy0 P s t hst

#print axioms exponential_comparison
#print axioms exists_uniform_density_growth
#print axioms exists_uniform_integral_growth
#print axioms exists_uniform_centeredEnergy_growth
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneUniformGrowth
