/- The exact complex clock equation confines the physical relative scale
more tightly than a norm envelope: 1/2 <= Re(r^2) <= 1 <= |r|^2 <= 2.
In particular the physical field direction cannot degenerate. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
import UnifiedTheory.Audit.KFCausalChargedPairCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalClockFloorExactScaleRegion
noncomputable section
open KFCausalClockFloorRelativeShift
open KFCausalNeutralPlaneClockGeometry
open KFCausalChargedPairCoordinates (fieldSlope)

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s
local notation "d" => Complex.re (relative ε y s)

theorem scale_norm_square : (r).re^2+(r).im^2 = Real.exp d := by
  have he : ‖r‖^2 = Real.exp d := by
    rw [scale,KFCausalClockFloorShearBounds.complexScale,Complex.norm_exp,← Real.exp_nat_mul]
    simp only [Complex.div_ofNat_re]
    congr 1
    ring
  rw [Complex.sq_norm,Complex.normSq_apply] at he
  nlinarith

include hε hy in
theorem clock_balance : Real.exp s*((r).re^2-(r).im^2-1)+ε*d = 0 := by
  have he := KFCausalComplexClockInverse.complexInverse_right ε hε
    (argument ε y s) (argument_mem ε y s hε hy)
  change Complex.exp (inverse ε y s)+(ε:ℂ)*inverse ε y s = argument ε y s at he
  rw [← scale_square] at he
  have hr := congrArg Complex.re he
  simp only [argument,KFCausalRegularizedLongitudinalChart.chart,Complex.add_re,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,pow_two] at hr
  simp only [relative,Complex.sub_re,Complex.ofReal_re]
  nlinarith

include hε hy in
theorem relative_re_nonnegative : 0 ≤ d := by
  by_contra hn
  have hd : d < 0 := lt_of_not_ge hn
  have he : Real.exp d < 1 := (Real.exp_lt_one_iff).mpr hd
  have hs := scale_norm_square ε y s
  have hb := clock_balance ε y s hε hy
  have hA : (r).re^2-(r).im^2-1 < 0 := by nlinarith [sq_nonneg (r).im]
  have h1 := mul_neg_of_pos_of_neg (Real.exp_pos s) hA
  have h2 := mul_neg_of_pos_of_neg hε hd
  linarith

include hε hy in
theorem square_re_le_one : (r).re^2-(r).im^2 ≤ 1 := by
  have hd := mul_nonneg hε.le (relative_re_nonnegative ε y s hε hy)
  have hb := clock_balance ε y s hε hy
  have hm : Real.exp s*((r).re^2-(r).im^2-1) ≤ 0 := by linarith
  by_contra hn
  have hp := mul_pos (Real.exp_pos s) (show 0 < (r).re^2-(r).im^2-1 by linarith)
  linarith

include hε hy in
theorem norm_square_one_le : 1 ≤ (r).re^2+(r).im^2 := by
  rw [scale_norm_square]
  exact Real.one_le_exp_iff.mpr (relative_re_nonnegative ε y s hε hy)

include hε hy in
theorem square_re_half_le : (1/2:ℝ) ≤ (r).re^2-(r).im^2 := by
  have hr := scale_square_re_lower ε y s hε hy
  have he : 1 ≤ Real.exp d := Real.one_le_exp_iff.mpr (relative_re_nonnegative ε y s hε hy)
  linarith

include hε hy in
theorem norm_square_le_two : (r).re^2+(r).im^2 ≤ 2 := by
  have hr := scale_square_re_lower ε y s hε hy
  rw [← scale_norm_square] at hr
  linarith [square_re_le_one ε y s hε hy]

include hε hy in
theorem real_square_near_one : |(r).re^2-1| ≤ (r).im^2 := by
  rw [abs_le]
  constructor
  · nlinarith [norm_square_one_le ε y s hε hy]
  · nlinarith [square_re_le_one ε y s hε hy]

include hε hy in
theorem real_near_one : |(r).re-1| ≤ (r).im^2 := by
  have ha := scale_re_positive ε y s hε hy
  have he := real_square_near_one ε y s hε hy
  rw [abs_le] at he ⊢
  constructor
  · by_cases h : (r).re ≤ 1
    · have hp := mul_nonneg ha.le (sub_nonneg.mpr h)
      nlinarith
    · have hp : 0 ≤ (r).im^2 := sq_nonneg _
      linarith
  · by_cases h : 1 ≤ (r).re
    · have hp := mul_nonneg ha.le (sub_nonneg.mpr h)
      nlinarith
    · have hp : 0 ≤ (r).im^2 := sq_nonneg _
      linarith

include hε hy in
theorem imaginary_square_le_half : (r).im^2 ≤ (1/2:ℝ) := by
  have hr := scale_square_re_lower ε y s hε hy
  rw [← scale_norm_square] at hr
  nlinarith [square_re_le_one ε y s hε hy]

include hε hy in
theorem fieldSlope_bounds : (1/2:ℝ) ≤ fieldSlope r ∧ fieldSlope r ≤ 2 := by
  have hp := scale_re_positive ε y s hε hy
  have hlo := square_re_half_le ε y s hε hy
  have hhi := square_re_le_one ε y s hε hy
  have hb := imaginary_square_le_half ε y s hε hy
  have h1 : (1/2:ℝ) ≤ (r).re := by nlinarith [sq_nonneg (r).im]
  have h2 : (r).re ≤ (5/4:ℝ) := by nlinarith
  unfold fieldSlope
  constructor <;> linarith

include hε hy in
theorem field_direction_bounds : 1 ≤ (fieldSlope r)^2+(2*(r).im)^2 ∧
    (fieldSlope r)^2+(2*(r).im)^2 ≤ 6 := by
  have ha := square_re_le_one ε y s hε hy
  have hb := imaginary_square_le_half ε y s hε hy
  have hL := fieldSlope_bounds ε y s hε hy
  constructor
  · unfold fieldSlope
    by_cases h : (r).re ≤ 1
    · nlinarith [sq_nonneg (r).im,sq_nonneg ((r).re-1)]
    · have hmul := mul_nonneg (show 0 ≤ (r).re-1 by linarith) (show 0 ≤ 2*(r).re-1 by linarith)
      nlinarith
  · nlinarith [sq_nonneg (2-fieldSlope r)]

#print axioms scale_norm_square
#print axioms clock_balance
#print axioms relative_re_nonnegative
#print axioms square_re_le_one
#print axioms norm_square_one_le
#print axioms square_re_half_le
#print axioms norm_square_le_two
#print axioms real_square_near_one
#print axioms real_near_one
#print axioms imaginary_square_le_half
#print axioms fieldSlope_bounds
#print axioms field_direction_bounds
end
end UnifiedTheory.Audit.KFCausalClockFloorExactScaleRegion
