/- A compact set containing every admissible charged-pair clock scale.
The narrow Gaussian width has a uniform strictly positive floor, including
the limiting real scales. This strengthens pointwise integrability. -/
import UnifiedTheory.Audit.KFCausalChargedPairCoordinates
import UnifiedTheory.Audit.KFCausalNeutralPlaneUniformScore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalChargedPairCompactGeometry
noncomputable section
open Set
open KFCausalChargedPairCoordinates
open KFCausalClockFloorRelativeShift
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalNeutralPlaneClockGeometry (scale_square_re_lower)
open KFCausalNeutralPlaneUniformScore (areaFloor areaFloor_positive)

def widthFloor (α : ℝ) : ℝ := α*Real.exp (-Real.pi/3)/4
def region (α β : ℝ) : Set (ℝ × ℂ) :=
  KFCausalNeutralPlaneUniformScore.region ∩
    {p | widthFloor α ≤ narrowWidth α β p.2}

theorem widthFloor_positive (α : ℝ) (hα : 0 < α) : 0 < widthFloor α := by
  unfold widthFloor
  positivity

theorem actual_width_floor (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    widthFloor α ≤ narrowWidth α β (scale ε y s) := by
  have hb : ‖relative ε y s‖ ≤ Real.pi/3 :=
    (relative_bound ε y s hε hy).trans ((div_le_iff₀ hε).mpr (by nlinarith))
  have hre : -Real.pi/3 ≤ (relative ε y s).re := by
    have hh := (Complex.abs_re_le_norm (relative ε y s)).trans hb
    linarith [(abs_le.mp hh).1]
  have he := Real.exp_le_exp.mpr hre
  have harea := mul_le_mul_of_nonneg_left (scale_square_re_lower ε y s hε hy) hα.le
  have him := mul_le_mul_of_nonneg_left
    (KFCausalClockFloorShearBounds.complexScale_im_square_bound (relative ε y s))
    (show 0 ≤ 8*β by positivity)
  have hwidth := mul_le_mul_of_nonneg_right hw (Real.exp_pos (relative ε y s).re).le
  have hexp := mul_le_mul_of_nonneg_left he hα.le
  change 8*β*(scale ε y s).im^2 ≤ 8*β*Real.exp (relative ε y s).re at him
  unfold widthFloor narrowWidth
  nlinarith

theorem region_compact (α β : ℝ) : IsCompact (region α β) := by
  have hc : Continuous (fun p : ℝ × ℂ => narrowWidth α β p.2) := by
    unfold narrowWidth
    fun_prop
  exact KFCausalNeutralPlaneUniformScore.region_compact.inter_right
    (isClosed_le continuous_const hc)

theorem actual_mem_region (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (fraction ε s, scale ε y s) ∈ region α β :=
  ⟨KFCausalNeutralPlaneUniformScore.actual_mem_region ε y s hε hy,
    actual_width_floor α β ε y s hα hβ hw hε hy⟩

theorem region_widths_positive (α β : ℝ) (hα : 0 < α)
    (p : ℝ × ℂ) (hp : p ∈ region α β) :
    0 < narrowWidth α β p.2 ∧ 0 < wideWidth α p.2 := by
  refine ⟨lt_of_lt_of_le (widthFloor_positive α hα) hp.2, ?_⟩
  exact mul_pos hα (lt_of_lt_of_le areaFloor_positive hp.1.2.2)

theorem region_scale_nonzero (α β : ℝ) (p : ℝ × ℂ) (hp : p ∈ region α β) :
    p.2 ≠ 0 := by
  have hA := lt_of_lt_of_le areaFloor_positive hp.1.2.2
  intro hz
  simp only [hz, Complex.zero_re, Complex.zero_im, zero_pow (by decide : 2 ≠ 0),
    sub_zero, lt_self_iff_false] at hA

#print axioms widthFloor_positive
#print axioms actual_width_floor
#print axioms region_compact
#print axioms actual_mem_region
#print axioms region_widths_positive
#print axioms region_scale_nonzero
end
end UnifiedTheory.Audit.KFCausalChargedPairCompactGeometry
