/- Uniform growth of the actual paired-state transverse potential kernel.
Compactness is applied to its proved positive smooth finite-moment formula,
not to an assumed derivative estimate. The bound is independent of clock
width and position, and includes the limiting real transverse scales. -/
import UnifiedTheory.Audit.KFCausalChargedPairPotentialKernel
import UnifiedTheory.Audit.KFCausalChargedPairCompactGeometry
import UnifiedTheory.Audit.KFCausalNeutralPlaneUniformGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalChargedPairKernelGrowth
noncomputable section
open Set
open KFCausalChargedPairCoordinates
open KFCausalChargedPairPotentialKernel
open KFCausalChargedPairCompactGeometry
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalNeutralPlaneClockGeometry (velocity)

def score (α β : ℝ) (p : ℝ × ℂ) : ℝ :=
  (fderiv ℝ (kernelFormula α β) p.2
    (velocity (1-p.1) p.1 p.2))/kernelFormula α β p.2

theorem normalized_clock_nonzero (t : ℝ) (r : ℂ)
    (ht : t ∈ Icc 0 1) (hA : 0 < r.re^2-r.im^2) :
    ((1-t:ℝ):ℂ)+(t:ℂ)*r^2 ≠ 0 := by
  have hp : 0 < 1-t+t*(r.re^2-r.im^2) := by
    by_cases h : t=1
    · simpa [h] using hA
    · have ht1 : t < 1 := lt_of_le_of_ne ht.2 h
      nlinarith [mul_nonneg ht.1 hA.le]
  have he : (((1-t:ℝ):ℂ)+(t:ℂ)*r^2).re = 1-t+t*(r.re^2-r.im^2) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      pow_two, Complex.mul_im]
    ring
  intro hz
  rw [hz, Complex.zero_re] at he
  linarith

theorem velocity_continuousAt (α β : ℝ) (p : ℝ × ℂ) (hp : p ∈ region α β) :
    ContinuousAt (fun q : ℝ × ℂ => velocity (1-q.1) q.1 q.2) p := by
  have hn := normalized_clock_nonzero p.1 p.2 hp.1.1
    (lt_of_lt_of_le KFCausalNeutralPlaneUniformScore.areaFloor_positive hp.1.2.2)
  unfold velocity
  fun_prop (disch := exact hn)

theorem score_continuousOn (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ContinuousOn (score α β) (region α β) := by
  intro p hp
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα p hp
  have hs := kernelFormula_smooth α β p.2 hA hB hβ
  have hc := hs.continuousAt_fderiv (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)
  have hn := (hc.comp continuousAt_snd).clm_apply (velocity_continuousAt α β p hp)
  exact (hn.div (hs.continuousAt.comp continuousAt_snd)
    (kernelFormula_positive α β p.2 hA hB hβ (region_scale_nonzero α β p hp)).ne').continuousWithinAt

theorem exists_uniform_score (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ region α β, |score α β p| ≤ C := by
  have hc := (score_continuousOn α β hα hβ).abs
  obtain ⟨M,hM⟩ := ((region_compact α β).image_of_continuousOn hc).bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro p hp
  exact (hM (mem_image_of_mem _ hp)).trans (le_max_left _ _)

theorem actual_kernel_formula (α β ε y : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (fun s => kernel α β (scale ε y s)) =
      (fun s => kernelFormula α β (scale ε y s)) := by
  funext s
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _
    (actual_mem_region α β ε y s hα hβ.le hw hε hy)
  exact kernel_formula α β _ hA hB hβ

theorem actual_kernel_positive (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    0 < kernel α β (scale ε y s) := by
  have hp := actual_mem_region α β ε y s hα hβ.le hw hε hy
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _ hp
  rw [kernel_formula α β _ hA hB hβ]
  exact kernelFormula_positive α β _ hA hB hβ (region_scale_nonzero α β _ hp)

theorem actual_kernel_derivative (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (fun u => kernel α β (scale ε y u))
      (score α β (fraction ε s,scale ε y s)*kernel α β (scale ε y s)) s := by
  have hp := actual_mem_region α β ε y s hα hβ.le hw hε hy
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _ hp
  have hn := (kernelFormula_positive α β _ hA hB hβ
    (region_scale_nonzero α β _ hp)).ne'
  have hd := ((kernelFormula_smooth α β _ hA hB hβ).differentiableAt
    (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp_hasDerivAt s
      (actual_normalized_velocity ε y s hε hy)
  rw [actual_kernel_formula α β ε y hα hβ hw hε hy]
  change HasDerivAt (fun u => kernelFormula α β (scale ε y u))
    (score α β (fraction ε s,scale ε y s)*kernel α β (scale ε y s)) s
  rw [kernel_formula α β _ hA hB hβ]
  simpa only [score, div_mul_cancel₀ _ hn] using hd

theorem actual_kernel_smooth (α β ε y : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ContDiff ℝ 1 (fun s => kernel α β (scale ε y s)) := by
  rw [actual_kernel_formula α β ε y hα hβ hw hε hy]
  apply contDiff_iff_contDiffAt.mpr
  intro s
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _
    (actual_mem_region α β ε y s hα hβ.le hw hε hy)
  exact ((kernelFormula_smooth α β _ hA hB hβ).of_le (by norm_num)).comp s
    (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).contDiffAt

theorem exists_uniform_derivative_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε y s : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 →
      |deriv (fun u => kernel α β (scale ε y u)) s| ≤ C*kernel α β (scale ε y s) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_score α β hα hβ
  refine ⟨C,hC,?_⟩
  intro ε y s hε hy
  rw [(actual_kernel_derivative α β ε y s hα hβ hw hε hy).deriv, abs_mul,
    abs_of_pos (actual_kernel_positive α β ε y s hα hβ hw hε hy)]
  exact mul_le_mul_of_nonneg_right
    (hbound _ (actual_mem_region α β ε y s hα hβ.le hw hε hy))
    (actual_kernel_positive α β ε y s hα hβ hw hε hy).le

theorem exists_uniform_growth (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε y : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 →
      ∀ s t : ℝ, s ≤ t →
        kernel α β (scale ε y t) ≤
          Real.exp (C*(t-s))*kernel α β (scale ε y s) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_derivative_bound α β hα hβ hw
  refine ⟨C,hC,?_⟩
  intro ε y hε hy s t hst
  exact KFCausalNeutralPlaneUniformGrowth.exponential_comparison _ C
    (fun u => (actual_kernel_derivative α β ε y u hα hβ hw hε hy).differentiableAt)
    (fun u => (le_abs_self _).trans (hbound ε y u hε hy)) s t hst

#print axioms normalized_clock_nonzero
#print axioms velocity_continuousAt
#print axioms score_continuousOn
#print axioms exists_uniform_score
#print axioms actual_kernel_formula
#print axioms actual_kernel_positive
#print axioms actual_kernel_derivative
#print axioms actual_kernel_smooth
#print axioms exists_uniform_derivative_bound
#print axioms exists_uniform_growth
end
end UnifiedTheory.Audit.KFCausalChargedPairKernelGrowth
