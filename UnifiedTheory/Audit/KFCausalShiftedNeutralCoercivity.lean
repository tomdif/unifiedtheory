/- Quantitative control of the shifted neutral coordinate. The inverse
imaginary scale grows at most linearly in the physical clock weight for
a fixed nonzero imaginary shift. This is a domain estimate, not a
state-uniform potential response estimate. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalShiftedNeutralCoercivity
noncomputable section
open KFCausalClockFloorRelativeShift
open KFCausalClockFloorShearBounds (complexScale)
open KFCausalComplexClockInverse (complexInverse_mem complexInverse_right)

def scaleBound (ε y : ℝ) : ℝ := Real.exp (|y|/(2*ε))
def inverseBound (ε y s : ℝ) : ℝ := scaleBound ε y*(2*Real.exp s+ε*Real.pi)/|y|

theorem scaleBound_positive (ε y : ℝ) : 0 < scaleBound ε y := Real.exp_pos _

theorem inverse_im_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    |(inverse ε y s).im| ≤ Real.pi*scaleBound ε y*|(scale ε y s).im| := by
  have hi : |(inverse ε y s).im| < Real.pi/2 :=
    complexInverse_mem ε hε _ (argument_mem ε y s hε hy)
  have hs := Real.mul_abs_le_abs_sin (x := (inverse ε y s).im/2)
    (by rw [abs_div]; norm_num; linarith [Real.pi_pos])
  have hs' : |(inverse ε y s).im| ≤ Real.pi*|Real.sin ((inverse ε y s).im/2)| := by
    rw [abs_div] at hs
    norm_num at hs
    have hm := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
    field_simp at hm
    nlinarith only [hm]
  have he : Real.exp (-(relative ε y s).re/2) ≤ scaleBound ε y := by
    apply Real.exp_le_exp.mpr
    have hr := (neg_le_abs (relative ε y s).re).trans
      ((Complex.abs_re_le_norm (relative ε y s)).trans (relative_bound ε y s hε hy))
    calc
      _ ≤ (|y|/ε)/2 := div_le_div_of_nonneg_right hr (by norm_num)
      _ = _ := by ring
  have him : |(scale ε y s).im| = Real.exp ((relative ε y s).re/2)*
      |Real.sin ((inverse ε y s).im/2)| := by
    simp only [scale,complexScale,Complex.exp_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
      relative,Complex.sub_im,Complex.ofReal_im,sub_zero,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hc : Real.exp (-(relative ε y s).re/2)*|(scale ε y s).im| =
      |Real.sin ((inverse ε y s).im/2)| := by
    rw [him,← mul_assoc,← Real.exp_add,
      show -(relative ε y s).re/2+(relative ε y s).re/2=0 by ring,Real.exp_zero,one_mul]
  calc
    _ ≤ Real.pi*|Real.sin ((inverse ε y s).im/2)| := hs'
    _ = Real.pi*(Real.exp (-(relative ε y s).re/2)*|(scale ε y s).im|) := by rw [hc]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right he (abs_nonneg _)) Real.pi_pos.le

theorem imaginary_clock_identity (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    y = 2*Real.exp s*(scale ε y s).re*(scale ε y s).im+ε*(inverse ε y s).im := by
  have hx := congrArg Complex.im (complexInverse_right ε hε _ (argument_mem ε y s hε hy))
  change (Complex.exp (inverse ε y s)+(ε:ℂ)*inverse ε y s).im = (argument ε y s).im at hx
  have hs := congrArg Complex.im (KFCausalNeutralPlaneClockGeometry.scale_square ε y s)
  simp only [argument,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add] at hx
  simp only [pow_two,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul] at hs
  nlinarith only [hx,hs]

theorem shift_bound_by_imaginary_scale (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    |y| ≤ scaleBound ε y*(2*Real.exp s+ε*Real.pi)*|(scale ε y s).im| := by
  have hr := (Complex.abs_re_le_norm (scale ε y s)).trans (scale_bound ε y s hε hy)
  have hi := inverse_im_bound ε y s hε hy
  have hx := abs_add_le (2*Real.exp s*(scale ε y s).re*(scale ε y s).im) (ε*(inverse ε y s).im)
  rw [← imaginary_clock_identity ε y s hε hy] at hx
  norm_num only [abs_mul,abs_of_pos (Real.exp_pos s),abs_of_pos hε] at hx
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*Real.exp s)) (abs_nonneg (scale ε y s).im)
  have hc := mul_le_mul_of_nonneg_left hi hε.le
  change |(scale ε y s).re| ≤ scaleBound ε y at hr
  change 2*Real.exp s*|(scale ε y s).re| *|(scale ε y s).im| ≤
    2*Real.exp s*scaleBound ε y*|(scale ε y s).im| at hb
  nlinarith only [hx,hb,hc]

theorem inverseBound_positive (ε y s : ℝ) (hε : 0 < ε) (hy : y ≠ 0) :
    0 < inverseBound ε y s := by unfold inverseBound scaleBound; positivity

theorem inverseBound_continuous (ε y : ℝ) : Continuous (inverseBound ε y) := by
  unfold inverseBound
  fun_prop

theorem inverse_scale_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    1/|(scale ε y s).im| ≤ inverseBound ε y s := by
  have hi := abs_pos.mpr (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy hy0)
  have hb := shift_bound_by_imaginary_scale ε y s hε hy
  unfold inverseBound
  apply (div_le_iff₀ hi).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (abs_pos.mpr hy0)).mpr
  simpa only [one_mul,div_mul_eq_mul_div] using hb

#print axioms scaleBound_positive
#print axioms inverse_im_bound
#print axioms imaginary_clock_identity
#print axioms shift_bound_by_imaginary_scale
#print axioms inverseBound_positive
#print axioms inverseBound_continuous
#print axioms inverse_scale_bound
end
end UnifiedTheory.Audit.KFCausalShiftedNeutralCoercivity
