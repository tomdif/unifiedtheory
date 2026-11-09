/- The radial defect cannot be converted into a pointwise uniform clock
estimate by bounding its wedge coefficient. That coefficient is unbounded
at every admissible nonzero shift, even with first coordinate fixed at one.
The combined imaginary radius nevertheless contracts under the actual
clock motion. Neither statement decides the integrated response bound. -/
import UnifiedTheory.Audit.KFCausalJointNeutralRadialEstimate
import UnifiedTheory.Audit.KFCausalReciprocalWedgeVelocity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalJointNeutralClockTransport
noncomputable section
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeGeometry (first second chart wedge)
open KFCausalReciprocalWedgeVelocity (radius drift shrink cooling)
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalClockFloorRelativeShift (scale)

def radialError (k α t : ℝ) (r z : ℂ) : ℝ := k*shrink t r*second α r z
def imaginaryArea (α : ℝ) (r z : ℂ) : ℝ := 4*r.im^2*first α r z
def imaginaryLoss (α t : ℝ) (r z : ℂ) : ℝ :=
  cooling (1/2) t r*((3*r.re^2-r.im^2)*first α r z+radius r*second α r z)

theorem shrink_positive (t : ℝ) (r : ℂ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hA : 0 < area r) : 0 < shrink t r := by
  have hd := normalized_denominator_positive t r ⟨ht.le,ht1⟩ hA
  have hR : 0 < radius r := by unfold radius area at *; nlinarith [sq_nonneg r.im]
  unfold shrink
  positivity

theorem radial_cross_upper (k α t J Jx : ℝ) (r z : ℂ)
    (ht : t ∈ Set.Icc 0 1) (hA : 0 < area r) (hz : z ∈ wedge α r)
    (hJx : -k*J ≤ Jx) :
    (-shrink t r*second α r z)*Jx ≤ radialError k α t r z*J := by
  have hs := KFCausalReciprocalWedgeVelocity.shrink_nonnegative t r ht hA
  have hy := hz.2
  have hc : 0 ≤ shrink t r*second α r z := mul_nonneg hs hy
  have hp := mul_le_mul_of_nonneg_left hJx hc
  unfold radialError
  nlinarith

theorem radial_error_unbounded (k α t : ℝ) (r : ℂ)
    (hk : 0 < k) (hα : α ≠ 0) (ht : 0 < t) (ht1 : t ≤ 1)
    (hA : 0 < area r) (ha : r.re ≠ 0) (hb : r.im ≠ 0) (M : ℝ) :
    ∃ z ∈ wedge α r, first α r z = 1 ∧ M < radialError k α t r z := by
  have hs := shrink_positive t r ht ht1 hA
  have hc : 0 < k*shrink t r := mul_pos hk hs
  let Y := max 0 ((M+1)/(k*shrink t r))
  have hY : 0 ≤ Y := le_max_left _ _
  have hm : (M+1)/(k*shrink t r) ≤ Y := le_max_right _ _
  have hm' : M+1 ≤ (k*shrink t r)*Y := by
    have he := (div_le_iff₀ hc).mp hm
    nlinarith
  refine ⟨chart α r 1 Y,
    KFCausalReciprocalWedgeGeometry.chart_mem_wedge α 1 Y r hα hA.ne' ha hb (by norm_num) hY,
    KFCausalReciprocalWedgeGeometry.first_chart α 1 Y r hα hA.ne' ha hb,?_⟩
  rw [radialError,KFCausalReciprocalWedgeGeometry.second_chart α 1 Y r hα hA.ne' ha hb]
  linarith

theorem actual_radial_error_unbounded (k α ε y s : ℝ)
    (hk : 0 < k) (hα : α ≠ 0) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) (M : ℝ) :
    ∃ z ∈ wedge α (scale ε y s), first α (scale ε y s) z = 1 ∧
      M < radialError k α (fraction ε s) (scale ε y s) z := by
  have ht := fraction_bounds ε s hε
  exact radial_error_unbounded k α (fraction ε s) (scale ε y s) hk hα ht.1 ht.2.le
    (KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy)
    (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy).ne'
    (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy hy0) M

theorem actual_joint_radial_cross_upper (n : ℕ) (α β ε h s : ℝ)
    (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (z : ℂ)
    (hβ : 0 < β) (hε : 0 < ε) (hh : |h| ≤ 2*Real.pi*ε/3)
    (hz : z ∈ wedge α (scale ε (-h/2) s))
    (hX : 0 < first α (scale ε (-h/2) s) z) :
    let r := scale ε (-h/2) s
    let t := fraction ε s
    let J := KFCausalJointNeutralRadialEstimate.jointArea n β w b c P r z
    (-shrink t r*second α r z)*deriv J (first α r z) ≤
      radialError (KFCausalNeutralUniformDefect.defectConstant/2) α t r z*J (first α r z) := by
  have hy : |(-h/2:ℝ)| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg]
    norm_num
    linarith
  have ht := fraction_bounds ε s hε
  apply radial_cross_upper _ _ _ _ _ _ _ ⟨ht.1.le,ht.2.le⟩
    (KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε (-h/2) s hε hy) hz
  simpa only [neg_div] using
    KFCausalJointNeutralRadialEstimate.actual_uniform_joint_area_lower n β w b c P z
      hβ ε h s hε hh (first α (scale ε (-h/2) s) z) hX

theorem imaginaryArea_derivative (r : ℝ → ℂ) (α t s : ℝ) (z : ℂ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hα : α ≠ 0) (hA : area (r s) ≠ 0) (ha : (r s).re ≠ 0) (hb : (r s).im ≠ 0)
    (hD : denominator (1-t) t (r s) ≠ 0) :
    HasDerivAt (fun u => imaginaryArea α (r u) z) (-imaginaryLoss α t (r s) z) s := by
  have hd := KFCausalReciprocalWedgeVelocity.neutralExponent_derivative r α (1/2) t s z
    hr hα hA ha hb hD
  simpa only [KFCausalReciprocalWedgeVelocity.neutralExponent,imaginaryArea,imaginaryLoss,
    show (8:ℝ)*(1/2)=4 by norm_num,neg_mul] using hd

theorem imaginaryArea_actual_derivative (α ε y s : ℝ) (z : ℂ)
    (hα : α ≠ 0) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    HasDerivAt (fun u => imaginaryArea α (scale ε y u) z)
      (-imaginaryLoss α (fraction ε s) (scale ε y s) z) s := by
  have ht := fraction_bounds ε s hε
  have hA := KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy
  exact imaginaryArea_derivative (scale ε y) α (fraction ε s) s z
    (actual_normalized_velocity ε y s hε hy) hα hA.ne'
    (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy).ne'
    (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy hy0)
    (normalized_denominator_positive _ _ ⟨ht.1.le,ht.2.le⟩ hA).ne'

theorem imaginaryArea_actual_nonpositive (α ε y s : ℝ) (z : ℂ)
    (hα : α ≠ 0) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0)
    (hz : z ∈ wedge α (scale ε y s)) :
    deriv (fun u => imaginaryArea α (scale ε y u) z) s ≤ 0 := by
  rw [(imaginaryArea_actual_derivative α ε y s z hα hε hy hy0).deriv]
  have ht := fraction_bounds ε s hε
  simpa only [imaginaryLoss,neg_mul] using
    KFCausalReciprocalWedgeVelocity.neutral_velocity_nonpositive α (1/2) (fraction ε s)
      (scale ε y s) z (by norm_num) ⟨ht.1.le,ht.2.le⟩
      (KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy) hz

#print axioms shrink_positive
#print axioms radial_cross_upper
#print axioms radial_error_unbounded
#print axioms actual_radial_error_unbounded
#print axioms actual_joint_radial_cross_upper
#print axioms imaginaryArea_derivative
#print axioms imaginaryArea_actual_derivative
#print axioms imaginaryArea_actual_nonpositive
end
end UnifiedTheory.Audit.KFCausalJointNeutralClockTransport
