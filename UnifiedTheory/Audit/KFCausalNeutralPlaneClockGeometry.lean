/- The actual relative clock scale obeys a rational differential equation.
Its induced imaginary-plane Gaussian width has strictly positive derivative
at every nonzero admissible imaginary clock shift. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
import UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates (planeWidth)

def denominator (ε E : ℝ) (r : ℂ) : ℝ :=
  (ε+E*(r.re^2-r.im^2))^2+(2*E*r.re*r.im)^2

def velocity (ε E : ℝ) (r : ℂ) : ℂ :=
  ((E:ℂ)*r*(1-r^2)/((ε:ℂ)+(E:ℂ)*r^2))/2

def widthSlope (α ε E : ℝ) (r : ℂ) : ℝ :=
  α*E*(ε+E)*r.re^2*(r.re^2+r.im^2)/(2*r.im^2*denominator ε E r)

theorem scale_square (ε y s : ℝ) :
    (Real.exp s:ℂ)*(scale ε y s)^2 = Complex.exp (inverse ε y s) := by
  rw [scale,KFCausalClockFloorShearBounds.complexScale_square,relative,
    Complex.exp_sub,← Complex.ofReal_exp]
  field_simp [Real.exp_ne_zero s]

theorem scale_re_positive (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    0 < (scale ε y s).re := by
  have hi := abs_lt.mp (show |(inverse ε y s).im| < Real.pi/2 from
    KFCausalComplexClockInverse.complexInverse_mem ε hε _
      (argument_mem ε y s hε hy))
  change 0 < (Complex.exp ((inverse ε y s-(s:ℂ))/2)).re
  rw [Complex.exp_re,Complex.div_ofNat_re,Complex.div_ofNat_im]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  simp only [Set.mem_Ioo,Complex.sub_im,Complex.ofReal_im,sub_zero]
  constructor <;> linarith [hi.1,hi.2,Real.pi_pos]

theorem scale_im_ne_zero (ε y s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) : (scale ε y s).im ≠ 0 := by
  have hi := KFCausalNeutralPositionStripPhase.inverse_scale_im_ne_zero ε hε
    (argument ε y s) (argument_mem ε y s hε hy)
    (by simpa [argument] using hy0)
  have hs : scale ε y s =
      KFCausalClockFloorShearBounds.complexScale (inverse ε y s) *
        (Real.exp (-s/2):ℂ) := by
    unfold scale KFCausalClockFloorShearBounds.complexScale relative
    rw [show (inverse ε y s-(s:ℂ))/2 =
      inverse ε y s/2+((-s/2:ℝ):ℂ) by push_cast; ring,
      Complex.exp_add,← Complex.ofReal_exp]
  rw [hs]
  simpa only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add]
    using mul_ne_zero hi (Real.exp_ne_zero (-s/2))

theorem denominator_positive (ε E : ℝ) (r : ℂ)
    (hE : 0 < E) (ha : r.re ≠ 0) (hb : r.im ≠ 0) :
    0 < denominator ε E r := by
  unfold denominator
  have ht : 0 < (2*E*r.re*r.im)^2 := sq_pos_of_ne_zero (by positivity)
  positivity

theorem scale_velocity (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (scale ε y) (velocity ε (Real.exp s) (scale ε y s)) s := by
  have hd := KFCausalShiftedGaussianLongitudinalDifferential.scale_derivative ε y s hε hy
  have hn := KFCausalClockFloorComplexDefect.complexClock_ne_zero ε hε _
    (argument_mem ε y s hε hy)
  have he : ((ε:ℂ)+(Real.exp s:ℂ)*(scale ε y s)^2) =
      KFCausalClockFloorComplexDefect.complexClock ε (argument ε y s) := by
    rw [scale_square]
    exact add_comm _ _
  have hn' := he.symm ▸ hn
  convert hd using 1
  unfold velocity KFCausalShiftedGaussianLongitudinalDifferential.inverseClock
  rw [← he,Complex.ofReal_add]
  field_simp
  ring

theorem velocity_cross (ε E : ℝ) (r : ℂ) :
    (velocity ε E r).re*r.im-r.re*(velocity ε E r).im =
      E*(ε+E)*r.re*r.im*(r.re^2+r.im^2)/denominator ε E r := by
  unfold velocity denominator
  simp only [Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.div_re,Complex.div_im,
    Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.one_re,Complex.one_im,pow_two,Complex.normSq_apply]
  ring

theorem width_derivative (r : ℝ → ℂ) (r' : ℂ) (α β s : ℝ)
    (hr : HasDerivAt r r' s) (hb : (r s).im ≠ 0) :
    HasDerivAt (fun t => planeWidth α β (r t))
      (α*(r s).re*(r'.re*(r s).im-(r s).re*r'.im)/(2*(r s).im^3)) s := by
  have ha := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hd := ((((ha.pow 2).sub (hi.pow 2)).const_mul α).div
    ((hi.pow 2).const_mul 4) (by
      simpa using (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hb))
    )).sub_const (2*β)
  convert hd using 1
  dsimp
  field_simp
  ring

theorem actual_width_derivative (α β ε y s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    HasDerivAt (fun t => planeWidth α β (scale ε y t))
      (widthSlope α ε (Real.exp s) (scale ε y s)) s := by
  have hb := scale_im_ne_zero ε y s hε hy hy0
  have hd := width_derivative (scale ε y) _ α β s (scale_velocity ε y s hε hy) hb
  rw [velocity_cross] at hd
  convert hd using 1
  unfold widthSlope
  field_simp

theorem actual_widthSlope_positive (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    0 < widthSlope α ε (Real.exp s) (scale ε y s) := by
  have ha := (scale_re_positive ε y s hε hy).ne'
  have hb := scale_im_ne_zero ε y s hε hy hy0
  have hd := denominator_positive ε (Real.exp s) (scale ε y s) (Real.exp_pos _) ha hb
  unfold widthSlope
  positivity

theorem scale_square_re_lower (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Real.exp (relative ε y s).re/2 ≤ (scale ε y s).re^2-(scale ε y s).im^2 := by
  have hz : |(relative ε y s).im| ≤ Real.pi/3 := by
    apply (Complex.abs_im_le_norm _).trans
    apply (relative_bound ε y s hε hy).trans
    exact (div_le_iff₀ hε).mpr (by nlinarith)
  have hc := KFCausalClockInverseStripBounds.cos_lower_third _ hz
  have he := KFCausalClockFloorShearBounds.complexScale_square (relative ε y s)
  have hre := congrArg Complex.re he
  simp only [pow_two,Complex.mul_re,Complex.exp_re] at hre
  change (scale ε y s).re*(scale ε y s).re-
    (scale ε y s).im*(scale ε y s).im =
      Real.exp (relative ε y s).re*Real.cos (relative ε y s).im at hre
  nlinarith [mul_le_mul_of_nonneg_left hc (Real.exp_pos (relative ε y s).re).le]

theorem scale_square_re_positive (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    0 < (scale ε y s).re^2-(scale ε y s).im^2 := by
  exact lt_of_lt_of_le (by positivity) (scale_square_re_lower ε y s hε hy)

theorem actual_planeWidth_positive (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    0 < planeWidth α β (scale ε y s) := by
  have he := Real.exp_pos (relative ε y s).re
  have hi := KFCausalClockFloorShearBounds.complexScale_im_square_bound (relative ε y s)
  change (scale ε y s).im^2 ≤ Real.exp (relative ε y s).re at hi
  have hA := scale_square_re_lower ε y s hε hy
  have h1 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 8*β)
  have h2 := mul_le_mul_of_nonneg_right hw he.le
  have h3 := mul_le_mul_of_nonneg_left hA hα.le
  have h4 := mul_pos hα he
  apply KFCausalNeutralPlaneCoordinates.planeWidth_positive α β (scale ε y s)
    (scale_im_ne_zero ε y s hε hy hy0)
  nlinarith

#print axioms scale_square
#print axioms scale_re_positive
#print axioms scale_im_ne_zero
#print axioms denominator_positive
#print axioms scale_velocity
#print axioms velocity_cross
#print axioms width_derivative
#print axioms actual_width_derivative
#print axioms actual_widthSlope_positive
#print axioms scale_square_re_lower
#print axioms scale_square_re_positive
#print axioms actual_planeWidth_positive
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
