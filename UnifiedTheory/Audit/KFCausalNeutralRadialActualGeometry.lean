/- The radial obstruction can be tested at an actual admissible clock
scale. Its coherent source is chosen from that scale without approximating
the complex inverse clock. -/
import UnifiedTheory.Audit.KFCausalNeutralRadialObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralRadialActualGeometry
noncomputable section
open MeasureTheory
open KFCausalClockFloorRelativeShift (scale relative relative_bound)
open KFCausalNeutralRadialCoherentKernel (mass quartic)
open KFCausalReciprocalNeutralHolomorphic (weightedProfile)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalQuarticPlaneDomination (potential)

def geometry : ℂ := scale 1 (1/128) 0
def displacement : ℝ := 2*geometry.im
def field : ℝ := 3-2*geometry.re
def frequency : ℝ := (2/3)/displacement
def source : ℂ := 4+(frequency:ℂ)*Complex.I
def profile : ℂ → ℂ := weightedProfile 1 (exponentialProfile source 1 1)
def slice (v x : ℝ) : ℝ := potential (x+field*v)*
  ‖profile ((x:ℂ)+(displacement*v:ℝ)*Complex.I)‖^2
def marginal (η L v : ℝ) : ℝ :=
  Real.exp (2*η^2*v^2-4*v/3)*quartic (2+L*v)

theorem actual_parameters :
    KFCausalChargeGaussianGeometry.groundWidth (-1/64) = 32 ∧
      KFCausalClockFloorInvariantTrial.neutralWidth (-1/64) = 1 ∧
      |(-1/64:ℝ)| ≤ 2*Real.pi/3 ∧ |(1/128:ℝ)| ≤ Real.pi/3 := by
  norm_num [KFCausalChargeGaussianGeometry.groundWidth,KFCausalClockFloorInvariantTrial.neutralWidth]
  constructor <;> linarith [Real.two_le_pi]

theorem geometry_close : ‖geometry-1‖ ≤ 1/128 := by
  have hr := relative_bound 1 (1/128) 0 (by norm_num) (by simpa only [mul_one] using actual_parameters.2.2.2)
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/128),div_one] at hr
  have he : ‖relative 1 (1/128) 0/2‖ ≤ 1 := by
    rw [norm_div]
    norm_num
    linarith
  have hb := Complex.norm_exp_sub_one_le he
  change ‖geometry-1‖ ≤ 2*‖relative 1 (1/128) 0/2‖ at hb
  rw [norm_div] at hb
  norm_num at hb
  linarith

theorem geometry_bounds : |displacement| ≤ 1/64 ∧ |field-1| ≤ 1/64 := by
  have hi := (Complex.abs_im_le_norm (geometry-1)).trans geometry_close
  have hr := (Complex.abs_re_le_norm (geometry-1)).trans geometry_close
  simp only [Complex.sub_im,Complex.one_im,sub_zero] at hi
  simp only [Complex.sub_re,Complex.one_re] at hr
  constructor
  · unfold displacement
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  · unfold field
    rw [show 3-2*geometry.re-1 = -2*(geometry.re-1) by ring,abs_mul]
    norm_num
    linarith

theorem displacement_ne_zero : displacement ≠ 0 :=
  mul_ne_zero (by norm_num) (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero 1 (1/128) 0
    (by norm_num) (by simpa only [mul_one] using actual_parameters.2.2.2) (by norm_num))

theorem profile_norm (v x : ℝ) :
    ‖profile ((x:ℂ)+(displacement*v:ℝ)*Complex.I)‖^2 =
      Real.exp 8*Real.exp (2*displacement^2*v^2-4*v/3)*Real.exp (-2*(x-2)^2) := by
  simp only [profile,weightedProfile,exponentialProfile,Polynomial.eval_one,
    mul_one,one_mul,← Complex.exp_add,Complex.norm_exp,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  simp [source,Complex.mul_re,Complex.mul_im,pow_two]
  unfold frequency
  field_simp [displacement_ne_zero]
  ring

theorem slice_shift (v x : ℝ) :
    slice v (x+2) = (Real.exp 8*Real.exp (2*displacement^2*v^2-4*v/3))*
      (potential (x+(2+field*v))*Real.exp (-2*x^2)) := by
  rw [slice,profile_norm,show x+2-2=x by ring,show x+2+field*v=x+(2+field*v) by ring]
  ring

theorem slice_integrable (v : ℝ) : Integrable (slice v) := by
  have hi := (KFCausalNeutralRadialCoherentKernel.quartic_integrable (2+field*v)).const_mul
    (Real.exp 8*Real.exp (2*displacement^2*v^2-4*v/3))
  have he : Integrable (fun x : ℝ => slice v (x+2)) := by simpa only [slice_shift] using hi
  simpa only [add_assoc,neg_add_cancel,add_zero] using he.comp_add_right (-2)

theorem slice_integral (v : ℝ) :
    (∫ x, slice v x) = Real.exp 8*mass*marginal displacement field v := by
  rw [← integral_add_right_eq_self (slice v) 2]
  simp_rw [slice_shift]
  rw [integral_const_mul,KFCausalNeutralRadialCoherentKernel.quartic_integral]
  unfold marginal
  ring

#print axioms actual_parameters
#print axioms geometry_close
#print axioms geometry_bounds
#print axioms displacement_ne_zero
#print axioms profile_norm
#print axioms slice_shift
#print axioms slice_integrable
#print axioms slice_integral
end
end UnifiedTheory.Audit.KFCausalNeutralRadialActualGeometry
