/- The charged Fourier radius remains coercive uniformly over the whole
clock and admissible imaginary strip. Its normalized clock derivative has
only quadratic growth. These are ingredients for a Hilbert limit, not a
uniform interacting energy-response estimate. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowFourierClockDerivative
import UnifiedTheory.Audit.KFCausalShiftedGaussianPureDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowFourierClockBounds
noncomputable section
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalShiftedNarrowFourierGeometry (radius broadRadius broadRadius_nonnegative)
open KFCausalShiftedNarrowFourierClockDerivative (radiusSlope)
open KFCausalClockFloorRelativeShift (scale relative relative_bound)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock inverseClock_bound scale_derivative)
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalNeutralPlaneClockGeometry (velocity scale_velocity)

def realRadius (α : ℝ) (u : Block 2) (v : Block 4) : ℝ :=
  (Real.pi^2/α)*‖u‖^2+α*broadRadius v

theorem radius_split (α : ℝ) (r : ℂ) (u : Block 2) (v : Block 4) :
    radius ((α:ℂ)*r^2) u v =
      ((Real.pi^2/α:ℝ):ℂ)*(r^2)⁻¹*(‖u‖:ℂ)^2+(α:ℂ)*r^2*(broadRadius v:ℂ) := by
  unfold radius
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem radius_lower (α : ℝ) (hα : 0 < α) (r : ℂ) (L : ℝ)
    (hr : L ≤ (r^2).re) (hi : L ≤ ((r^2)⁻¹).re) (u : Block 2) (v : Block 4) :
    L*realRadius α u v ≤ (radius ((α:ℂ)*r^2) u v).re := by
  rw [radius_split]
  simp only [← Complex.ofReal_pow,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero]
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ Real.pi^2/α)) (sq_nonneg ‖u‖)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hα.le) (broadRadius_nonnegative v)
  unfold realRadius
  nlinarith only [h1,h2]

theorem radius_norm_bound (α : ℝ) (hα : 0 < α) (r : ℂ) (M : ℝ)
    (hr : ‖r^2‖ ≤ M) (hi : ‖(r^2)⁻¹‖ ≤ M) (u : Block 2) (v : Block 4) :
    ‖radius ((α:ℂ)*r^2) u v‖ ≤ M*realRadius α u v := by
  rw [radius_split]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,← Complex.ofReal_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.pi^2/α),abs_of_nonneg (sq_nonneg ‖u‖),
    abs_of_pos hα,abs_of_nonneg (broadRadius_nonnegative v)]
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ Real.pi^2/α)) (sq_nonneg ‖u‖)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hα.le) (broadRadius_nonnegative v)
  unfold realRadius
  nlinarith only [h1,h2]

theorem exp_strip_bounds (w : ℂ) (b : ℝ) (hw : ‖w‖ ≤ b) (hi : |w.im| ≤ Real.pi/3) :
    Real.exp (-b)/2 ≤ (Complex.exp w).re ∧ ‖Complex.exp w‖ ≤ Real.exp b := by
  have hr := abs_le.mp ((Complex.abs_re_le_norm w).trans hw)
  constructor
  · rw [Complex.exp_re]
    have he := Real.exp_le_exp.mpr hr.1
    have hc := KFCausalClockInverseStripBounds.cos_lower_third w.im hi
    nlinarith [mul_le_mul_of_nonneg_left hc (Real.exp_pos w.re).le]
  · rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hr.2

theorem scale_bounds (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (Real.exp (-Real.pi/3)/2 ≤ ((scale ε y s)^2).re ∧
      ‖(scale ε y s)^2‖ ≤ Real.exp (Real.pi/3)) ∧
    (Real.exp (-Real.pi/3)/2 ≤ (((scale ε y s)^2)⁻¹).re ∧
      ‖((scale ε y s)^2)⁻¹‖ ≤ Real.exp (Real.pi/3)) := by
  have hn : ‖relative ε y s‖ ≤ Real.pi/3 :=
    (relative_bound ε y s hε hy).trans ((div_le_iff₀ hε).mpr (by linarith))
  have hi := (Complex.abs_im_le_norm (relative ε y s)).trans hn
  have he : (scale ε y s)^2 = Complex.exp (relative ε y s) :=
    KFCausalClockFloorShearBounds.complexScale_square _
  rw [he,← Complex.exp_neg]
  constructor
  · simpa only [neg_div] using exp_strip_bounds (relative ε y s) (Real.pi/3) hn hi
  · simpa only [neg_div] using exp_strip_bounds (-relative ε y s) (Real.pi/3)
      (by simpa only [norm_neg] using hn) (by simpa only [Complex.neg_im,abs_neg] using hi)

theorem actual_radius_lower (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (u : Block 2) (v : Block 4) :
    (Real.exp (-Real.pi/3)/2)*realRadius α u v ≤
      (radius ((α:ℂ)*(scale ε y s)^2) u v).re :=
  radius_lower α hα _ _ (scale_bounds ε y s hε hy).1.1 (scale_bounds ε y s hε hy).2.1 u v

theorem actual_radius_norm_bound (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (u : Block 2) (v : Block 4) :
    ‖radius ((α:ℂ)*(scale ε y s)^2) u v‖ ≤ Real.exp (Real.pi/3)*realRadius α u v :=
  radius_norm_bound α hα _ _ (scale_bounds ε y s hε hy).1.2 (scale_bounds ε y s hε hy).2.2 u v

theorem inverse_difference_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ‖inverseClock ε y s-realInverse ε s‖ ≤ 2/ε := by
  have hr : ‖realInverse ε s‖ ≤ 1/ε := by
    simp only [realInverse,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0 < Real.exp s+ε by positivity)]
    simpa only [one_div] using one_div_le_one_div_of_le hε
      (show ε ≤ Real.exp s+ε by linarith [Real.exp_pos s])
  calc
    _ ≤ ‖inverseClock ε y s‖+‖realInverse ε s‖ := norm_sub_le _ _
    _ ≤ 1/ε+1/ε := add_le_add (inverseClock_bound ε y s hε hy) hr
    _ = _ := by ring

theorem normalized_radius_identity (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (u : Block 2) (v : Block 4) :
    realInverse ε s*radiusSlope ((α:ℂ)*(scale ε y s)^2)
      (2*(α:ℂ)*scale ε y s*velocity ε (Real.exp s) (scale ε y s)) u v =
      (inverseClock ε y s-realInverse ε s)*
        ((α:ℂ)*(scale ε y s)^2*(broadRadius v:ℂ)-
          ((Real.pi^2/α:ℝ):ℂ)*((scale ε y s)^2)⁻¹*(‖u‖:ℂ)^2) := by
  have hv := (scale_velocity ε y s hε hy).unique (scale_derivative ε y s hε hy)
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  have hr : scale ε y s ≠ 0 := fun hz => by
    have hp := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
    rw [hz] at hp
    exact lt_irrefl 0 hp
  have hc : ((Real.exp s+ε:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [hv]
  unfold radiusSlope realInverse
  push_cast
  push_cast at hc
  field_simp [ha,hr,hc]
  ring

theorem normalized_radius_bound (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (u : Block 2) (v : Block 4) :
    ‖realInverse ε s*radiusSlope ((α:ℂ)*(scale ε y s)^2)
      (2*(α:ℂ)*scale ε y s*velocity ε (Real.exp s) (scale ε y s)) u v‖ ≤
      (2/ε)*Real.exp (Real.pi/3)*realRadius α u v := by
  rw [normalized_radius_identity α ε y s hα hε hy u v,norm_mul]
  have hb : ‖(α:ℂ)*(scale ε y s)^2*(broadRadius v:ℂ)-
      ((Real.pi^2/α:ℝ):ℂ)*((scale ε y s)^2)⁻¹*(‖u‖:ℂ)^2‖ ≤
      Real.exp (Real.pi/3)*realRadius α u v := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,← Complex.ofReal_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hα,abs_of_nonneg (broadRadius_nonnegative v),
      abs_of_nonneg (by positivity : 0 ≤ Real.pi^2/α),abs_of_nonneg (sq_nonneg ‖u‖)]
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (scale_bounds ε y s hε hy).1.2 hα.le) (broadRadius_nonnegative v)
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (scale_bounds ε y s hε hy).2.2 (by positivity : 0 ≤ Real.pi^2/α)) (sq_nonneg ‖u‖)
    unfold realRadius
    nlinarith only [h1,h2]
  simpa only [mul_assoc] using mul_le_mul (inverse_difference_bound ε y s hε hy) hb
    (norm_nonneg _) (by positivity : 0 ≤ 2/ε)

#print axioms radius_split
#print axioms radius_lower
#print axioms radius_norm_bound
#print axioms exp_strip_bounds
#print axioms scale_bounds
#print axioms actual_radius_lower
#print axioms actual_radius_norm_bound
#print axioms inverse_difference_bound
#print axioms normalized_radius_identity
#print axioms normalized_radius_bound
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowFourierClockBounds
