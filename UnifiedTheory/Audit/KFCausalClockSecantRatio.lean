/- A bounded ratio between the physical shear weight and the positive
real interpolation coefficient. The actual inverse-clock strip supplies
the estimate for either sign of nonzero hbar. -/
import UnifiedTheory.Audit.KFCausalClockFloorShearWeight
import UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockSecantRatio
noncomputable section
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalComplexClockInverse (complexInverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument relative inverse)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (rootValue rootValue_square)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (complexClock complexDefect)

theorem strip_imaginary_bound (ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (hz : |z.im| ≤ Real.pi/3) : |((ε:ℂ)/(Complex.exp z+(ε:ℂ))).im| ≤ |z.im|/2 := by
  let v := Complex.exp z+(ε:ℂ)
  have hr : ε+Real.exp z.re/2 ≤ v.re := by
    have hc := mul_le_mul_of_nonneg_left (cos_lower_third z.im hz) (Real.exp_pos z.re).le
    simp only [v,Complex.add_re,Complex.ofReal_re,Complex.exp_re]
    linarith
  have hsq : (ε+Real.exp z.re/2)^2 ≤ v.re^2 :=
    pow_le_pow_left₀ (by positivity) hr 2
  have hn : 2*ε*Real.exp z.re ≤ Complex.normSq v := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (ε-Real.exp z.re/2),sq_nonneg v.im]
  have hp : 0 < Complex.normSq v := lt_of_lt_of_le (by positivity) hn
  have hi : |v.im| ≤ Real.exp z.re*|z.im| := by
    simp only [v,Complex.add_im,Complex.ofReal_im,add_zero,Complex.exp_im,abs_mul,
      abs_of_pos (Real.exp_pos z.re)]
    exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (Real.exp_pos z.re).le
  change |((ε:ℂ)/v).im| ≤ _
  simp only [Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,zero_sub,
    abs_neg,abs_div,abs_mul,abs_of_pos hε,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have h1 := mul_le_mul_of_nonneg_left hi hε.le
  have h2 := mul_le_mul_of_nonneg_left hn (abs_nonneg z.im)
  nlinarith

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)

include hε hb

theorem physical_imaginary_bound (s : ℝ) :
    |(physicalSymbol ε h (s,0)).im| ≤ |(displacement ε h s).im|/2 := by
  have ht : |(argument ε (-h/2) s).im| ≤ Real.pi*ε/3 := by
    simpa [argument] using half_shift_bound ε h hb
  have he := strip_imaginary_bound ε hε (complexInverse ε (argument ε (-h/2) s))
    (inverse_im_third_strip ε hε _ ht)
  simpa only [physicalSymbol,complexDefect,complexClock,displacement,relative,inverse,
    argument,Complex.sub_im,Complex.ofReal_im,sub_zero] using he

def ratio (s : ℝ) : ℝ := (rootValue ε h s)^2/(coefficient ε h s).re

include hh

theorem ratio_nonnegative (s : ℝ) : 0 ≤ ratio ε h s :=
  div_nonneg (sq_nonneg _) (coefficient_re_positive ε h s hε hh hb).le

theorem ratio_bound (s : ℝ) : ratio ε h s ≤ ε/4 := by
  have hc := coefficient_re_positive ε h s hε hh hb
  have hw := (KFCausalClockFloorShearWeight.coefficient_bounds ε hε h hb hh s).1
  have he : (rootValue ε h s)^2 = ε/(2*|h|)*|(physicalSymbol ε h (s,0)).im| := by
    rw [rootValue_square ε hε h hb hh,← abs_of_nonneg hw]
    unfold KFCausalClockFloorShearWeight.coefficient
    rw [abs_div,abs_mul,abs_mul,abs_of_pos hε]
    norm_num
    ring
  have hd : |(displacement ε h s).im|/|h| = (coefficient ε h s).re := by
    rw [← abs_neg (displacement ε h s).im,← abs_div,← coefficient_re,abs_of_pos hc]
  unfold ratio
  apply (div_le_iff₀ hc).mpr
  rw [he]
  calc
    _ ≤ ε/(2*|h|)*(|(displacement ε h s).im|/2) :=
      mul_le_mul_of_nonneg_left (physical_imaginary_bound ε h hε hb s) (by positivity)
    _ = ε/4*(coefficient ε h s).re := by rw [← hd]; ring

theorem ratio_continuous : Continuous (ratio ε h) :=
  ((KFCausalClockFloorShearWeight.rootValue_continuous ε hε h hb).pow 2).div
    (Complex.continuous_re.comp (coefficient_smooth ε h hε hb).continuous)
    (fun s => (coefficient_re_positive ε h s hε hh hb).ne')

theorem ratio_identity (s : ℝ) : ratio ε h s*(coefficient ε h s).re = (rootValue ε h s)^2 :=
  div_mul_cancel₀ _ (coefficient_re_positive ε h s hε hh hb).ne'

#print axioms strip_imaginary_bound
#print axioms physical_imaginary_bound
#print axioms ratio_nonnegative
#print axioms ratio_bound
#print axioms ratio_continuous
#print axioms ratio_identity
end
end UnifiedTheory.Audit.KFCausalClockSecantRatio
