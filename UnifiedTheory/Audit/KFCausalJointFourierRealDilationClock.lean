/- Dilation by the actual logarithmic real-coordinate velocity removes
the real charged velocity. Its remaining real field jet is quadratic
in the imaginary clock shift, uniformly including zero shift.
These clock identities do not assert an integrated response bound. -/
import UnifiedTheory.Audit.KFCausalJointFourierDissipationClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierRealDilationClock
noncomputable section
open KFCausalClockFloorRelativeShift (scale)
open KFCausalClockFloorExactScaleRegion
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalJointClockCoolingCoercivity
open KFCausalJointFourierDissipationClock
open KFCausalChargedPairCoordinates (fieldSlope)

def realDilationRate (t : ℝ) (r : ℂ) : ℝ :=
  t*realNumerator t r/(2*denominator (1-t) t r)

theorem rate_velocity (t : ℝ) (r : ℂ) (ha : r.re ≠ 0) :
    realDilationRate t r = (velocity (1-t) t r).re/r.re := by
  rw [normalized_velocity_re]
  unfold realDilationRate
  field_simp

theorem rate_decomposition (t : ℝ) (r : ℂ) (ha : r.re ≠ 0) :
    realDilationRate t r = imaginaryRate t r+t*normalizedRealCooling t r/r.re := by
  have hc := real_cooling_identity t r
  rw [rate_velocity t r ha]
  apply (div_eq_iff ha).mpr
  rw [add_mul,div_mul_cancel₀ _ ha]
  linarith

theorem corrected_velocity (t : ℝ) (r : ℂ) (ha : r.re ≠ 0) :
    velocity (1-t) t r-(realDilationRate t r:ℂ)*r =
      Complex.I*((-t*normalizedRealCooling t r*r.im/r.re:ℝ):ℂ) := by
  have hr := rate_velocity t r ha
  have hd := rate_decomposition t r ha
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero]
    rw [hr,div_mul_cancel₀ _ ha]
    ring
  · simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,one_mul,add_zero]
    rw [imaginary_velocity,hd]
    ring

theorem corrected_field (t : ℝ) (r : ℂ) (ha : r.re ≠ 0) :
    -2*(velocity (1-t) t r).re-realDilationRate t r*fieldSlope r =
      -3*realDilationRate t r := by
  have hr := rate_velocity t r ha
  have he : realDilationRate t r*r.re = (velocity (1-t) t r).re := by
    rw [hr,div_mul_cancel₀ _ ha]
  unfold fieldSlope
  nlinarith

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s
include hε hy

theorem real_numerator_bounds (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    -4*(r).im^2 ≤ realNumerator t r ∧ realNumerator t r ≤ 4*(r).im^2 := by
  have hA := square_re_le_one ε y s hε hy
  have hR1 := norm_square_one_le ε y s hε hy
  have hR2 := norm_square_le_two ε y s hε hy
  have hb := sq_nonneg (r).im
  have hp : -4*(r).im^2 ≤ 1-(r).re^2+3*(r).im^2 ∧
      1-(r).re^2+3*(r).im^2 ≤ 4*(r).im^2 := by
    constructor <;> nlinarith
  have hq : -4*(r).im^2 ≤ ((r).re^2+(r).im^2)*(1-((r).re^2+(r).im^2)) ∧
      ((r).re^2+(r).im^2)*(1-((r).re^2+(r).im^2)) ≤ 4*(r).im^2 := by
    have hprod := mul_le_mul (show (r).re^2+(r).im^2 ≤ 2 from hR2)
      (show (r).re^2+(r).im^2-1 ≤ 2*(r).im^2 by nlinarith)
      (show 0 ≤ (r).re^2+(r).im^2-1 by linarith) (by norm_num : (0:ℝ) ≤ 2)
    have hn := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (r).re^2+(r).im^2 by positivity)
      (show 1-((r).re^2+(r).im^2) ≤ 0 by linarith)
    constructor <;> nlinarith
  have h1 := mul_le_mul_of_nonneg_left hp.1 (sub_nonneg.mpr ht.2)
  have h2 := mul_le_mul_of_nonneg_left hq.1 ht.1
  have h3 := mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr ht.2)
  have h4 := mul_le_mul_of_nonneg_left hq.2 ht.1
  unfold realNumerator
  constructor <;> nlinarith

theorem real_dilation_bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    |realDilationRate t r| ≤ 8*t*(r).im^2 := by
  have hN := real_numerator_bounds ε y s hε hy t ht
  have hD := normalized_denominator_bounds ε y s hε hy t ht
  have ht0 := ht.1
  have hd : 0 < 2*denominator (1-t) t r := by linarith [hD.1]
  have hn : |realNumerator t r| ≤ 4*(r).im^2 :=
    abs_le.mpr ⟨by nlinarith [hN.1],hN.2⟩
  unfold realDilationRate
  rw [abs_div,abs_mul,abs_of_nonneg ht.1,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have h1 := mul_le_mul_of_nonneg_left hn ht.1
  have h2 := mul_le_mul_of_nonneg_left hD.1
    (show 0 ≤ 16*t*(r).im^2 by positivity)
  nlinarith

theorem corrected_field_bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    |-3*realDilationRate t r| ≤ 24*t*(r).im^2 := by
  have hb := real_dilation_bound ε y s hε hy t ht
  rw [abs_mul]
  norm_num
  linarith

theorem actual_rate_velocity :
    realDilationRate (fraction ε s) r = (deriv (scale ε y) s).re/(r).re := by
  rw [(actual_normalized_velocity ε y s hε hy).deriv]
  exact rate_velocity _ _ (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy).ne'

theorem actual_corrected_velocity :
    deriv (scale ε y) s-(realDilationRate (fraction ε s) r:ℂ)*r =
      Complex.I*((-fraction ε s*normalizedRealCooling (fraction ε s) r*(r).im/(r).re:ℝ):ℂ) := by
  rw [(actual_normalized_velocity ε y s hε hy).deriv]
  exact corrected_velocity _ _
    (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy).ne'

theorem actual_corrected_field_bound :
    |-2*(deriv (scale ε y) s).re-realDilationRate (fraction ε s) r*fieldSlope r| ≤
      24*fraction ε s*(r).im^2 := by
  rw [(actual_normalized_velocity ε y s hε hy).deriv,
    corrected_field _ _ (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy).ne']
  exact corrected_field_bound ε y s hε hy _
    ⟨(fraction_bounds ε s hε).1.le,(fraction_bounds ε s hε).2.le⟩

theorem zero_imaginary_rate (t : ℝ) (ht : t ∈ Set.Icc 0 1) (hi : (r).im = 0) :
    realDilationRate t r = 0 := by
  have hb := real_dilation_bound ε y s hε hy t ht
  have hz : |realDilationRate t r| = 0 :=
    le_antisymm (by simpa only [hi,zero_pow (by omega : 2 ≠ 0),mul_zero] using hb)
      (abs_nonneg _)
  exact abs_eq_zero.mp hz

#print axioms rate_velocity
#print axioms rate_decomposition
#print axioms corrected_velocity
#print axioms corrected_field
#print axioms real_numerator_bounds
#print axioms real_dilation_bound
#print axioms corrected_field_bound
#print axioms actual_rate_velocity
#print axioms actual_corrected_velocity
#print axioms actual_corrected_field_bound
#print axioms zero_imaginary_rate
end
end UnifiedTheory.Audit.KFCausalJointFourierRealDilationClock
