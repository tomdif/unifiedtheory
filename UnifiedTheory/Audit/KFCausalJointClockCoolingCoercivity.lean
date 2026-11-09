/- A quantitative positive quadratic form for simultaneous charged and
neutral clock cooling. The exact physical scale region supplies uniform
bounds even at zero imaginary shift. This is an algebraic/differential
ingredient for the integrated response, not that integrated inequality. -/
import UnifiedTheory.Audit.KFCausalClockFloorExactScaleRegion
import UnifiedTheory.Audit.KFCausalReciprocalWedgeVelocity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointClockCoolingCoercivity
noncomputable section
open scoped ComplexConjugate
open KFCausalClockFloorRelativeShift (scale)
open KFCausalClockFloorExactScaleRegion
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeVelocity (radius)

def imaginaryRate (t : ℝ) (r : ℂ) : ℝ := t*imagNumerator t r/(2*denominator (1-t) t r)
def coefficient (t : ℝ) (r : ℂ) : ℝ := t*radius r/(2*area r*denominator (1-t) t r)
def leftCooling (t : ℝ) (r : ℂ) (X Y : ℝ) : ℝ :=
  coefficient t r*((2*area r+radius r)*X+radius r*Y)
def rightCooling (t : ℝ) (r : ℂ) (X Y : ℝ) : ℝ := leftCooling t r Y X

def leftWidth (α : ℝ) (w r : ℂ) : ℝ := α*(w*r^2).re
def rightWidth (α : ℝ) (w r : ℂ) : ℝ := α*(w*(conj r)^2).re
def leftSlope (α t : ℝ) (w r : ℂ) : ℝ := 2*α*(w*r*velocity (1-t) t r).re

theorem imaginary_velocity (t : ℝ) (r : ℂ) :
    (velocity (1-t) t r).im = imaginaryRate t r*r.im := by
  rw [normalized_velocity_im]
  unfold imaginaryRate
  ring

theorem left_width_cooling (α t : ℝ) (w r : ℂ)
    (hA : area r ≠ 0) (hD : denominator (1-t) t r ≠ 0) :
    leftSlope α t w r-2*imaginaryRate t r*leftWidth α w r =
      leftCooling t r (leftWidth α w r) (rightWidth α w r) := by
  unfold leftSlope
  simp only [Complex.mul_re,Complex.mul_im,normalized_velocity_re,normalized_velocity_im]
  unfold leftCooling coefficient imaginaryRate leftWidth rightWidth radius area realNumerator imagNumerator
  simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,pow_two]
  unfold area at hA
  field_simp
  ring

theorem rightWidth_conjugate (α : ℝ) (w r : ℂ) : rightWidth α w r = leftWidth α (conj w) r := by
  unfold rightWidth leftWidth
  simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,pow_two]
  ring

theorem cooling_quadratic_identity (t : ℝ) (r : ℂ) (X Y : ℝ)
    (hA : area r ≠ 0) (hD : denominator (1-t) t r ≠ 0) :
    X*leftCooling t r X Y+Y*rightCooling t r X Y =
      (t*radius r/denominator (1-t) t r)*(X^2+Y^2)+
      (t*(radius r)^2/(2*area r*denominator (1-t) t r))*(X+Y)^2 := by
  unfold rightCooling leftCooling coefficient
  field_simp
  ring

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s

include hε hy in
theorem normalized_denominator_bounds (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    (1/4:ℝ) ≤ denominator (1-t) t r ∧ denominator (1-t) t r ≤ 4 := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hA := square_re_half_le ε y s hε hy
  have hA1 := square_re_le_one ε y s hε hy
  have hR := norm_square_le_two ε y s hε hy
  have hR0 : 0 ≤ radius r := by unfold radius; positivity
  have hp : (1/2:ℝ) ≤ 1-t+t*area r := by
    unfold area
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hA)]
  have hR2 : (radius r)^2 ≤ 4 := by
    change (r).re^2+(r).im^2 ≤ 2 at hR
    dsimp only [radius] at hR0 ⊢
    nlinarith
  constructor
  · unfold denominator
    unfold area at hp
    nlinarith [sq_nonneg (2*t*(r).re*(r).im)]
  · have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (sub_nonneg.mpr ht.2)) (by linarith [ht.1] : 0 ≤ 1+t)
    have h2 := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hR2)
    have h3 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht.1) (sub_nonneg.mpr ht.2))
      (sub_nonneg.mpr hA1)
    have he : 4-denominator (1-t) t r =
        3*(1-t)*(1+t)+t^2*(4-(radius r)^2)+2*t*(1-t)*(1-area r) := by
      unfold denominator radius area
      ring
    have hn : 0 ≤ 4-denominator (1-t) t r := by rw [he]; exact add_nonneg (add_nonneg h1 h2) h3
    linarith

include hε hy in
theorem cooling_diagonal_lower (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    t/4 ≤ t*radius r/denominator (1-t) t r := by
  have ht0 := ht.1
  have hD := normalized_denominator_bounds ε y s hε hy t ht
  have hd : 0 < denominator (1-t) t r := by linarith [hD.1]
  have hR := norm_square_one_le ε y s hε hy
  change 1 ≤ radius r at hR
  apply (le_div_iff₀ hd).mpr
  have h1 := mul_le_mul_of_nonneg_left hD.2 (show 0 ≤ t/4 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hR ht.1
  nlinarith

include hε hy in
theorem cooling_pair_coercive (t : ℝ) (ht : t ∈ Set.Icc 0 1) (X Y : ℝ) :
    (t/4)*(X^2+Y^2) ≤ X*leftCooling t r X Y+Y*rightCooling t r X Y := by
  have hA : 0 < area r := by have := square_re_half_le ε y s hε hy; unfold area; linarith
  have hD := normalized_denominator_bounds ε y s hε hy t ht
  have hd : 0 < denominator (1-t) t r := by linarith [hD.1]
  rw [cooling_quadratic_identity t r X Y hA.ne' hd.ne']
  have hp : 0 ≤ (t*(radius r)^2/(2*area r*denominator (1-t) t r))*(X+Y)^2 := by
    have ht0 := ht.1
    positivity
  exact (mul_le_mul_of_nonneg_right (cooling_diagonal_lower ε y s hε hy t ht)
    (add_nonneg (sq_nonneg X) (sq_nonneg Y))).trans (le_add_of_nonneg_right hp)

include hε hy in
theorem actual_cooling_pair_coercive (X Y : ℝ) :
    (fraction ε s/4)*(X^2+Y^2) ≤
      X*leftCooling (fraction ε s) r X Y+Y*rightCooling (fraction ε s) r X Y :=
  cooling_pair_coercive ε y s hε hy _
    ⟨(fraction_bounds ε s hε).1.le,(fraction_bounds ε s hε).2.le⟩ X Y

include hε hy in
theorem actual_left_width_derivative (α : ℝ) (w : ℂ) :
    HasDerivAt (fun u => leftWidth α w (scale ε y u))
      (2*imaginaryRate (fraction ε s) r*leftWidth α w r+
        leftCooling (fraction ε s) r (leftWidth α w r) (rightWidth α w r)) s := by
  have hr := actual_normalized_velocity ε y s hε hy
  have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((hr.pow 2).const_mul w)).const_mul α
  have he : HasDerivAt (fun u => leftWidth α w (scale ε y u)) (leftSlope α (fraction ε s) w r) s := by
    convert hd using 1
    change 2*α*(w*r*velocity (1-fraction ε s) (fraction ε s) r).re =
      α*(w*((2:ℂ)*r^(2-1)*velocity (1-fraction ε s) (fraction ε s) r)).re
    norm_num only [Nat.reduceSub,pow_one]
    rw [show w*((2:ℂ)*r*velocity (1-fraction ε s) (fraction ε s) r) =
      2*(w*r*velocity (1-fraction ε s) (fraction ε s) r) by ring]
    simp only [Complex.mul_re]
    norm_num
    ring
  have hAp : 0 < area r := by
    have hp := square_re_half_le ε y s hε hy
    unfold area
    linarith
  have hA : area r ≠ 0 := hAp.ne'
  have hD : denominator (1-fraction ε s) (fraction ε s) r ≠ 0 :=
    (normalized_denominator_positive _ _ ⟨(fraction_bounds ε s hε).1.le,(fraction_bounds ε s hε).2.le⟩ hAp).ne'
  have hs := left_width_cooling α (fraction ε s) w r hA hD
  have hs' : leftSlope α (fraction ε s) w r =
      2*imaginaryRate (fraction ε s) r*leftWidth α w r+leftCooling (fraction ε s) r (leftWidth α w r) (rightWidth α w r) := by linarith
  rwa [hs'] at he

#print axioms imaginary_velocity
#print axioms left_width_cooling
#print axioms rightWidth_conjugate
#print axioms cooling_quadratic_identity
#print axioms normalized_denominator_bounds
#print axioms cooling_diagonal_lower
#print axioms cooling_pair_coercive
#print axioms actual_cooling_pair_coercive
#print axioms actual_left_width_derivative
end
end UnifiedTheory.Audit.KFCausalJointClockCoolingCoercivity
