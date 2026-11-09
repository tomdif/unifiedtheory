/- A derivative estimate uniform over the unbounded width range w >= 1.
The compact parameter k=1/sqrt(w) retains a positive marginal at k=0;
no compactness of the Hilbert states themselves is claimed. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianKernel
import UnifiedTheory.Audit.KFCausalChargedPairKernelGrowth
import UnifiedTheory.Audit.KFCausalOneSidedKernelClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianKernelBound
noncomputable section
open Set MeasureTheory
open KFCausalReciprocalGaussianCoordinates
open KFCausalReciprocalGaussianKernel
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalNeutralPlaneNormalizedGeometry (fraction actual_normalized_velocity)
open KFCausalNeutralPlaneClockGeometry (velocity)
open KFCausalChargedPairCompactGeometry (widthFloor widthFloor_positive)

def region (α β : ℝ) : Set (ℝ × (ℝ × ℂ)) :=
  Icc 0 1 ×ˢ KFCausalChargedPairCompactGeometry.region α β

theorem region_compact (α β : ℝ) : IsCompact (region α β) :=
  isCompact_Icc.prod (KFCausalChargedPairCompactGeometry.region_compact α β)

theorem region_widths (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (p : ℝ × (ℝ × ℂ)) (hp : p ∈ region α β) :
    0 < narrow α β p.1 p.2.2 ∧ 0 < α*area p.2.2 := by
  obtain ⟨hA,hB⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα p.2 hp.2
  have hk : p.1^2 ≤ 1 := by nlinarith [hp.1.1,hp.1.2]
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (show 0 ≤ 8*β by positivity)) (sq_nonneg p.2.2.im)
  refine ⟨?_,hB⟩
  unfold narrow area KFCausalChargedPairCoordinates.narrowWidth at *
  nlinarith

def score (α β : ℝ) (p : ℝ × (ℝ × ℂ)) : ℝ :=
  (fderiv ℝ (kernelFormula α β) (p.1,p.2.2)
    (0,velocity (1-p.2.1) p.2.1 p.2.2))/kernelFormula α β (p.1,p.2.2)

theorem score_continuousOn (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ContinuousOn (score α β) (region α β) := by
  intro p hp
  obtain ⟨hA,hB⟩ := region_widths α β hα hβ.le p hp
  have hs := kernelFormula_smooth α β (p.1,p.2.2) hA hB hβ
  have hq : ContinuousAt (fun q : ℝ × (ℝ × ℂ) => (q.1,q.2.2)) p := by fun_prop
  have hc : ContinuousAt (fderiv ℝ (kernelFormula α β)) (p.1,p.2.2) :=
    hs.continuousAt_fderiv (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)
  have hv := (KFCausalChargedPairKernelGrowth.velocity_continuousAt α β p.2 hp.2).comp continuousAt_snd
  have hhq : ContinuousAt (fun q : ℝ × (ℝ × ℂ) =>
      fderiv ℝ (kernelFormula α β) (q.1,q.2.2)) p := hc.comp (f := fun q : ℝ × (ℝ × ℂ) => (q.1,q.2.2)) hq
  have hvq : ContinuousAt (fun q : ℝ × (ℝ × ℂ) =>
      ((0:ℝ),velocity (1-q.2.1) q.2.1 q.2.2)) p := continuousAt_const.prodMk hv
  have hn := hhq.clm_apply hvq
  exact (hn.div (hs.continuousAt.comp (f := fun q : ℝ × (ℝ × ℂ) => (q.1,q.2.2)) hq)
    (kernelFormula_positive α β p.1 p.2.2 hA hB hβ).ne').continuousWithinAt

theorem exists_uniform_score (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ region α β, |score α β p| ≤ C := by
  obtain ⟨M,hM⟩ := ((region_compact α β).image_of_continuousOn
    (score_continuousOn α β hα hβ).abs).bddAbove
  exact ⟨max M 0,le_max_right _ _,fun p hp =>
    (hM (mem_image_of_mem _ hp)).trans (le_max_left _ _)⟩

theorem actual_mem_region (α β k ε y s : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hw : 32*β ≤ α) (hk : k ∈ Icc 0 1) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (k,fraction ε s,scale ε y s) ∈ region α β :=
  ⟨hk,KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ hw hε hy⟩

theorem actual_formula (α β k ε y : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hk : k ∈ Ioc 0 1) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (fun s => kernel α β (1/k^2) (scale ε y s)) =
      (fun s => kernelFormula α β (k,scale ε y s)) := by
  funext s
  obtain ⟨hA,hB⟩ := region_widths α β hα hβ.le _
    (actual_mem_region α β k ε y s hα hβ.le hw ⟨hk.1.le,hk.2⟩ hε hy)
  exact kernel_formula α β k hk.1.ne' _ hA hB hβ

theorem actual_positive (α β k ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hk : k ∈ Ioc 0 1) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    0 < kernel α β (1/k^2) (scale ε y s) := by
  obtain ⟨hA,hB⟩ := region_widths α β hα hβ.le _
    (actual_mem_region α β k ε y s hα hβ.le hw ⟨hk.1.le,hk.2⟩ hε hy)
  rw [kernel_formula α β k hk.1.ne' _ hA hB hβ]
  exact kernelFormula_positive α β k _ hA hB hβ

theorem actual_derivative (α β k ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hk : k ∈ Ioc 0 1) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (fun t => kernel α β (1/k^2) (scale ε y t))
      (score α β (k,fraction ε s,scale ε y s)*kernel α β (1/k^2) (scale ε y s)) s := by
  obtain ⟨hA,hB⟩ := region_widths α β hα hβ.le _
    (actual_mem_region α β k ε y s hα hβ.le hw ⟨hk.1.le,hk.2⟩ hε hy)
  have hd := ((kernelFormula_smooth α β (k,scale ε y s) hA hB hβ).differentiableAt
    (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s k).prodMk (actual_normalized_velocity ε y s hε hy))
  rw [actual_formula α β k ε y hα hβ hw hk hε hy]
  change HasDerivAt (fun t => kernelFormula α β (k,scale ε y t))
    (score α β (k,fraction ε s,scale ε y s)*kernel α β (1/k^2) (scale ε y s)) s
  rw [kernel_formula α β k hk.1.ne' _ hA hB hβ]
  simpa only [score,div_mul_cancel₀ _ (kernelFormula_positive α β k _ hA hB hβ).ne'] using hd

theorem exists_uniform_derivative (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ε y s : ℝ, k ∈ Ioc 0 1 → 0 < ε →
      |y| ≤ Real.pi*ε/3 →
      |deriv (fun t => kernel α β (1/k^2) (scale ε y t)) s| ≤
        C*kernel α β (1/k^2) (scale ε y s) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_score α β hα hβ
  refine ⟨C,hC,?_⟩
  intro k ε y s hk hε hy
  rw [(actual_derivative α β k ε y s hα hβ hw hk hε hy).deriv,abs_mul,
    abs_of_pos (actual_positive α β k ε y s hα hβ hw hk hε hy)]
  exact mul_le_mul_of_nonneg_right
    (hbound _ (actual_mem_region α β k ε y s hα hβ.le hw ⟨hk.1.le,hk.2⟩ hε hy))
    (actual_positive α β k ε y s hα hβ hw hk hε hy).le

#print axioms region_compact
#print axioms region_widths
#print axioms score_continuousOn
#print axioms exists_uniform_score
#print axioms actual_mem_region
#print axioms actual_formula
#print axioms actual_positive
#print axioms actual_derivative
#print axioms exists_uniform_derivative
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianKernelBound
