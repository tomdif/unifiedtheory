/- The actual field/neutral clock jet is absorbed by the simultaneous
charged cooling form with an explicit state-independent remainder.
This retains the coupled square and is regular at zero shift and t=0.
An integrated response identity using this square remains to be proved. -/
import UnifiedTheory.Audit.KFCausalJointClockCoolingCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointClockJetAbsorption
noncomputable section
open KFCausalClockFloorRelativeShift (scale)
open KFCausalClockFloorExactScaleRegion
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeVelocity (radius)
open KFCausalJointClockCoolingCoercivity
open KFCausalChargedPairCoordinates (fieldSlope)

def normalizedVelocity (t : ℝ) (r : ℂ) : ℂ :=
  (r*(1-r^2)/(((1-t:ℝ):ℂ)+(t:ℂ)*r^2))/2

def realJet (t : ℝ) (r : ℂ) : ℝ := -2*(normalizedVelocity t r).re
def imaginaryJet (t : ℝ) (r : ℂ) : ℝ := 2*(normalizedVelocity t r).im

theorem velocity_normalized (t : ℝ) (r : ℂ) :
    velocity (1-t) t r = (t:ℂ)*normalizedVelocity t r := by
  unfold velocity normalizedVelocity
  ring

theorem normalized_norm_identity (t : ℝ) (r : ℂ) :
    ‖normalizedVelocity t r‖^2 =
      radius r*((1-area r)^2+(2*r.re*r.im)^2)/(4*denominator (1-t) t r) := by
  unfold normalizedVelocity
  simp only [norm_div,norm_mul,div_pow,mul_pow,Complex.norm_ofNat]
  rw [Complex.sq_norm,Complex.sq_norm,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,pow_two]
  simp only [div_eq_mul_inv, mul_inv_rev]
  unfold radius area denominator
  norm_num
  ring

theorem algebraic_absorption (t a b c X Y : ℝ) (ht : 0 ≤ t) (hab : a^2+b^2 ≤ 32) :
    2*c*(t*(a*X+b*Y)) ≤ (t/4)*(X^2+Y^2)+128*t*c^2 := by
  have hs1 := sq_nonneg (X/2-2*c*a)
  have hs2 := sq_nonneg (Y/2-2*c*b)
  have hb := mul_le_mul_of_nonneg_left hab (sq_nonneg c)
  have hp : 0 ≤ (X^2+Y^2)/4+128*c^2-2*c*(a*X+b*Y) := by nlinarith
  have hm := mul_nonneg ht hp
  nlinarith

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s

include hε hy in
theorem normalized_velocity_bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ‖normalizedVelocity t r‖^2 ≤ 8 := by
  have hA := square_re_half_le ε y s hε hy
  have hR := norm_square_le_two ε y s hε hy
  have hR0 : 0 ≤ radius r := by unfold radius; positivity
  have hR2 : (radius r)^2 ≤ 4 := by unfold radius at *; nlinarith
  have hN0 : 0 ≤ (1-area r)^2+(2*(r).re*(r).im)^2 := by positivity
  have hN : (1-area r)^2+(2*(r).re*(r).im)^2 ≤ 4 := by
    have he : (1-area r)^2+(2*(r).re*(r).im)^2 = 1-2*area r+(radius r)^2 := by
      unfold area radius
      ring
    rw [he]
    unfold area at *
    linarith
  have hD := normalized_denominator_bounds ε y s hε hy t ht
  have hd : 0 < 4*denominator (1-t) t r := by linarith [hD.1]
  have hp : radius r*((1-area r)^2+(2*(r).re*(r).im)^2) ≤ 8 := by
    have hx := mul_le_mul hR hN hN0 (by norm_num : (0:ℝ) ≤ 2)
    simpa only [radius, show (2:ℝ)*4 = 8 by norm_num] using hx
  rw [normalized_norm_identity]
  apply (div_le_iff₀ hd).mpr
  nlinarith [hD.1]

include hε hy in
theorem normalized_jet_bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    (realJet t r)^2+(imaginaryJet t r)^2 ≤ 32 := by
  have hv := normalized_velocity_bound ε y s hε hy t ht
  rw [Complex.sq_norm,Complex.normSq_apply] at hv
  unfold realJet imaginaryJet
  nlinarith

include hε hy in
theorem joint_jet_absorption (t : ℝ) (ht : t ∈ Set.Icc 0 1) (c X Y : ℝ) :
    2*c*(t*(realJet t r*X+imaginaryJet t r*Y)) ≤
      X*leftCooling t r X Y+Y*rightCooling t r X Y+128*t*c^2 := by
  exact (algebraic_absorption t _ _ c X Y ht.1 (normalized_jet_bound ε y s hε hy t ht)).trans
    (add_le_add (cooling_pair_coercive ε y s hε hy t ht X Y) le_rfl)

include hε hy in
theorem actual_field_direction_derivative :
    HasDerivAt (fun u => (fieldSlope (scale ε y u),2*(scale ε y u).im))
      (fraction ε s*realJet (fraction ε s) r,fraction ε s*imaginaryJet (fraction ε s) r) s := by
  have hr := actual_normalized_velocity ε y s hε hy
  have ha := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr).const_mul 2).const_sub 3
  have hb := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr).const_mul 2
  convert ha.prodMk hb using 1
  apply Prod.ext
  · change _ = -(2*(velocity (1-fraction ε s) (fraction ε s) r).re)
    rw [velocity_normalized]
    simp only [realJet,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  · change _ = 2*(velocity (1-fraction ε s) (fraction ε s) r).im
    rw [velocity_normalized]
    simp only [imaginaryJet,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring

#print axioms velocity_normalized
#print axioms normalized_norm_identity
#print axioms algebraic_absorption
#print axioms normalized_velocity_bound
#print axioms normalized_jet_bound
#print axioms joint_jet_absorption
#print axioms actual_field_direction_derivative
end
end UnifiedTheory.Audit.KFCausalJointClockJetAbsorption
