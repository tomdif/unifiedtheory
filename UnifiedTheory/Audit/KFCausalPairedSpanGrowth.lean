/- Uniform transverse growth for the entire complex centered/paired span.
The coefficient unit sphere is compact. Strict positivity of the full
quadratic energy, with its cross term, controls all coefficient directions.
Homogeneity then removes the normalization. -/
import UnifiedTheory.Audit.KFCausalPairedSpanKernel
import UnifiedTheory.Audit.KFCausalChargedPairKernelGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanGrowth
noncomputable section
open Set
open KFCausalPairedSpanMoments (Coefficients value value_smooth)
open KFCausalPairedSpanKernel
open KFCausalChargedPairCompactGeometry
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction actual_normalized_velocity)
open KFCausalNeutralPlaneClockGeometry (velocity)

def coefficientRegion (α β : ℝ) : Set ((ℝ × ℂ) × Coefficients) :=
  region α β ×ˢ Metric.sphere 0 1

def score (α β : ℝ) (p : (ℝ × ℂ) × Coefficients) : ℝ :=
  (fderiv ℝ (fun z : ℂ × Coefficients => value α β z.1 z.2) (p.1.2,p.2)
    (velocity (1-p.1.1) p.1.1 p.1.2,0))/value α β p.1.2 p.2

def rate (α β ε y s : ℝ) (c : Coefficients) : ℝ :=
  fderiv ℝ (fun z : ℂ × Coefficients => value α β z.1 z.2) (scale ε y s,c)
    (velocity (1-fraction ε s) (fraction ε s) (scale ε y s),0)

theorem coefficientRegion_compact (α β : ℝ) : IsCompact (coefficientRegion α β) :=
  (region_compact α β).prod (isCompact_sphere (0:Coefficients) 1)

theorem score_continuousOn (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ContinuousOn (score α β) (coefficientRegion α β) := by
  intro p hp
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα p.1 hp.1
  have hc : p.2 ≠ 0 := by
    intro hz
    have hh := hp.2
    simp only [Metric.mem_sphere, hz, dist_self, zero_ne_one] at hh
  have hs := value_smooth α β p.1.2 p.2 hA hB hβ
  have hd := hs.continuousAt_fderiv (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)
  have hm : ContinuousAt (fun z : (ℝ × ℂ) × Coefficients => (z.1.2,z.2)) p := by fun_prop
  have hv : ContinuousAt (fun z : (ℝ × ℂ) × Coefficients =>
      (velocity (1-z.1.1) z.1.1 z.1.2,(0:Coefficients))) p :=
    ((KFCausalChargedPairKernelGrowth.velocity_continuousAt α β p.1 hp.1).comp
      continuousAt_fst).prodMk continuousAt_const
  have hnum := (hd.comp_of_eq hm rfl).clm_apply hv
  have hden := hs.continuousAt.comp_of_eq hm rfl
  have hh := hnum.div hden
    (value_positive α β p.1.2 p.2 hA hB hβ
      (region_scale_nonzero α β p.1 hp.1) hc).ne'
  exact hh.continuousWithinAt

theorem exists_normalized_score_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ coefficientRegion α β, |score α β p| ≤ C := by
  obtain ⟨M,hM⟩ := ((coefficientRegion_compact α β).image_of_continuousOn
    (score_continuousOn α β hα hβ).abs).bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro p hp
  exact (hM (mem_image_of_mem _ hp)).trans (le_max_left _ _)

theorem actual_kernel_formula (α β ε y : ℝ) (c : Coefficients)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (fun s => kernel α β (scale ε y s) c) = (fun s => value α β (scale ε y s) c) := by
  funext s
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _
    (actual_mem_region α β ε y s hα hβ.le hw hε hy)
  exact kernel_formula α β _ c hA hB hβ

theorem actual_kernel_derivative (α β ε y s : ℝ) (c : Coefficients)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (fun u => kernel α β (scale ε y u) c) (rate α β ε y s c) s := by
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _
    (actual_mem_region α β ε y s hα hβ.le hw hε hy)
  have hd := ((value_smooth α β (scale ε y s) c hA hB hβ).differentiableAt
    (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp_hasDerivAt s
      ((actual_normalized_velocity ε y s hε hy).prodMk (hasDerivAt_const s c))
  rw [actual_kernel_formula α β ε y c hα hβ hw hε hy]
  exact hd

theorem actual_kernel_smooth (α β ε y : ℝ) (c : Coefficients)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ContDiff ℝ 1 (fun s => kernel α β (scale ε y s) c) := by
  rw [actual_kernel_formula α β ε y c hα hβ hw hε hy]
  apply contDiff_iff_contDiffAt.mpr
  intro s
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _
    (actual_mem_region α β ε y s hα hβ.le hw hε hy)
  exact ((value_smooth α β (scale ε y s) c hA hB hβ).of_le (by norm_num)).comp s
    (((KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).prodMk contDiff_const).contDiffAt)

theorem normalized_derivative_bound (α β C ε y s : ℝ) (c : Coefficients)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hc : ‖c‖=1)
    (hbound : ∀ p ∈ coefficientRegion α β, |score α β p| ≤ C) :
    |deriv (fun u => kernel α β (scale ε y u) c) s| ≤ C*kernel α β (scale ε y s) c := by
  have hp := actual_mem_region α β ε y s hα hβ.le hw hε hy
  have hc0 : c ≠ 0 := by intro hz; simp only [hz, norm_zero, zero_ne_one] at hc
  obtain ⟨hA,hB⟩ := region_widths_positive α β hα _ hp
  have hpos := value_positive α β _ c hA hB hβ (region_scale_nonzero α β _ hp) hc0
  have hh := hbound ((fraction ε s,scale ε y s),c)
    ⟨hp,by simpa only [Metric.mem_sphere,dist_zero_right] using hc⟩
  change |rate α β ε y s c/value α β (scale ε y s) c| ≤ C at hh
  rw [abs_div, abs_of_pos hpos] at hh
  rw [(actual_kernel_derivative α β ε y s c hα hβ hw hε hy).deriv,
    kernel_formula α β _ c hA hB hβ]
  exact (div_le_iff₀ hpos).mp hh

theorem exists_uniform_derivative_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε y : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 →
      ∀ (c : Coefficients) (s : ℝ),
        |deriv (fun u => kernel α β (scale ε y u) c) s| ≤ C*kernel α β (scale ε y s) c := by
  obtain ⟨C,hC,hbound⟩ := exists_normalized_score_bound α β hα hβ
  refine ⟨C,hC,?_⟩
  intro ε y hε hy c s
  by_cases hz : c=0
  · simp only [hz, kernel_zero, deriv_const, abs_zero, mul_zero, le_refl]
  · have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hnC : (‖c‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    let d : Coefficients := (‖c‖:ℂ)⁻¹ • c
    have hd : ‖d‖=1 := by
      simp only [d, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_norm, inv_mul_cancel₀ hn]
    have he : c = (‖c‖:ℂ) • d := by
      simp only [d, smul_smul, mul_inv_cancel₀ hnC, one_smul]
    have hf : (fun u => kernel α β (scale ε y u) c) =
        (fun u => ‖c‖^2*kernel α β (scale ε y u) d) := by
      funext u
      conv_lhs => rw [he]
      rw [kernel_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    have hdd := actual_kernel_derivative α β ε y s d hα hβ hw hε hy
    have hds := hdd.const_mul (‖c‖^2)
    rw [← hf] at hds
    have hb := normalized_derivative_bound α β C ε y s d hα hβ hw hε hy hd hbound
    rw [hdd.deriv] at hb
    rw [hds.deriv, abs_mul, abs_of_nonneg (sq_nonneg _), congrFun hf s]
    calc
      _ ≤ ‖c‖^2*(C*kernel α β (scale ε y s) d) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = _ := by ring

theorem exists_uniform_growth (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε y : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 →
      ∀ (c : Coefficients) (s t : ℝ), s ≤ t →
        kernel α β (scale ε y t) c ≤ Real.exp (C*(t-s))*kernel α β (scale ε y s) c := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_derivative_bound α β hα hβ hw
  refine ⟨C,hC,?_⟩
  intro ε y hε hy c s t hst
  exact KFCausalNeutralPlaneUniformGrowth.exponential_comparison _ C
    (fun u => (actual_kernel_derivative α β ε y u c hα hβ hw hε hy).differentiableAt)
    (fun u => (le_abs_self _).trans (hbound ε y hε hy c u)) s t hst

#print axioms coefficientRegion_compact
#print axioms score_continuousOn
#print axioms exists_normalized_score_bound
#print axioms actual_kernel_formula
#print axioms actual_kernel_derivative
#print axioms actual_kernel_smooth
#print axioms normalized_derivative_bound
#print axioms exists_uniform_derivative_bound
#print axioms exists_uniform_growth
end
end UnifiedTheory.Audit.KFCausalPairedSpanGrowth
