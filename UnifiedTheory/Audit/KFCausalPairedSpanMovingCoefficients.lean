/- The actual geometric kernel with coefficients that vary along the clock.
The total derivative includes the coefficient derivative; only its geometric
part satisfies the previously proved uniform relative estimate. -/
import UnifiedTheory.Audit.KFCausalPairedSpanCoefficientDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanMovingCoefficients
noncomputable section
open KFCausalPairedSpanMoments (Coefficients value value_smooth)
open KFCausalPairedSpanGrowth (rate)
open KFCausalPairedSpanCoefficientDifferential (coefficientRate joint_coefficient_derivative)
open KFCausalChargedPairCompactGeometry
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction actual_normalized_velocity)
open KFCausalNeutralPlaneClockGeometry (velocity)

variable (α β ε y : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)

include hα hβ hw hε hy in
theorem value_nonnegative (s : ℝ) (c : Coefficients) :
    0 ≤ value α β (scale ε y s) c := by
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _
    (actual_mem_region α β ε y s hα hβ.le hw hε hy)
  rw [← KFCausalPairedSpanKernel.kernel_formula α β _ c hA hB hβ]
  exact KFCausalPairedSpanKernel.kernel_nonnegative α β _ c

include hα hβ hw hε hy in
theorem moving_derivative (c : ℝ → Coefficients) (d : Coefficients) (s : ℝ)
    (hc : HasDerivAt c d s) :
    HasDerivAt (fun u => value α β (scale ε y u) (c u))
      (rate α β ε y s (c s)+coefficientRate α β (scale ε y s) (c s) d) s := by
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _
    (actual_mem_region α β ε y s hα hβ.le hw hε hy)
  have hd := ((value_smooth α β (scale ε y s) (c s) hA hB hβ).differentiableAt
    (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp_hasDerivAt s
      ((actual_normalized_velocity ε y s hε hy).prodMk hc)
  have he :
      (velocity (1-fraction ε s) (fraction ε s) (scale ε y s),d) =
      (velocity (1-fraction ε s) (fraction ε s) (scale ε y s),(0:Coefficients))+
        ((0:ℂ),d) := by simp only [Prod.mk_add_mk,add_zero,zero_add]
  rw [he,map_add,joint_coefficient_derivative α β _ (c s) d hA hB hβ] at hd
  exact hd

include hα hβ hw hε hy in
theorem moving_continuous (c : ℝ → Coefficients) (hc : Continuous c) :
    Continuous (fun s => value α β (scale ε y s) (c s)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _
    (actual_mem_region α β ε y s hα hβ.le hw hε hy)
  exact (value_smooth α β (scale ε y s) (c s) hA hB hβ).continuousAt.comp_of_eq
    (((KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).continuous.continuousAt).prodMk
      hc.continuousAt) rfl

include hα hβ hw hε hy in
theorem rate_continuous (c : ℝ → Coefficients) (hc : Continuous c) :
    Continuous (fun s => rate α β ε y s (c s)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hp := actual_mem_region α β ε y s hα hβ.le hw hε hy
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _ hp
  have hs := (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).continuous
  have hf : Continuous (fraction ε) := by
    unfold fraction
    exact Real.continuous_exp.div (continuous_const.add Real.continuous_exp)
      (fun u => by positivity)
  have hd := (value_smooth α β (scale ε y s) (c s) hA hB hβ).continuousAt_fderiv
    (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)
  have hm : ContinuousAt (fun u => (scale ε y u,c u)) s :=
    hs.continuousAt.prodMk hc.continuousAt
  have hv := (KFCausalChargedPairKernelGrowth.velocity_continuousAt α β _ hp).comp_of_eq
    (hf.continuousAt.prodMk hs.continuousAt) rfl
  exact (hd.comp_of_eq hm rfl).clm_apply (hv.prodMk continuousAt_const)

theorem exists_uniform_rate_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε y : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 →
      ∀ (c : Coefficients) (s : ℝ),
        |rate α β ε y s c| ≤ C*value α β (scale ε y s) c := by
  obtain ⟨C,hC,hbound⟩ := KFCausalPairedSpanGrowth.exists_uniform_derivative_bound α β hα hβ hw
  refine ⟨C,hC,?_⟩
  intro ε y hε hy c s
  have hd := hbound ε y hε hy c s
  rw [(KFCausalPairedSpanGrowth.actual_kernel_derivative α β ε y s c hα hβ hw hε hy).deriv,
    congrFun (KFCausalPairedSpanGrowth.actual_kernel_formula α β ε y c hα hβ hw hε hy) s] at hd
  exact hd

#print axioms value_nonnegative
#print axioms moving_derivative
#print axioms moving_continuous
#print axioms rate_continuous
#print axioms exists_uniform_rate_bound
end
end UnifiedTheory.Audit.KFCausalPairedSpanMovingCoefficients
