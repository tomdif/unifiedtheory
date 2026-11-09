/- The radial witness is followed along the actual clock curve with its
coherent source fixed. The complete neutral angular energy is jointly
differentiable in clock position and radius. -/
import UnifiedTheory.Audit.KFCausalCompactAngularFDeriv
import UnifiedTheory.Audit.KFCausalJointNeutralRadialTransportObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralRadialClockFamily
noncomputable section
open MeasureTheory
open KFCausalNeutralRadialActualGeometry (geometry displacement field frequency source profile)
open KFCausalNeutralRadialCoherentKernel (quartic mass)
open KFCausalReciprocalNeutralKernel (neutral)
open KFCausalReciprocalNeutralPositiveForm (profileSum)
open KFCausalReciprocalWedgeLaplace (laplaceSum)
open KFCausalJointNeutralRadialTransportObstruction (weight)
open KFCausalJointNeutralRadialEstimate (jointSlice jointArea)
open KFCausalQuarticPlaneDomination (potential)

def actualScale (s : ℝ) : ℂ := KFCausalClockFloorRelativeShift.scale 1 (1/128) s
def slice (r : ℂ) (v x : ℝ) : ℝ := potential (x+(3-2*r.re)*v)*‖profile (neutral r v x)‖^2
def marginal (r : ℂ) (v : ℝ) : ℝ :=
  Real.exp (2*(2*r.im)^2*v^2-2*frequency*(2*r.im)*v)*quartic (2+(3-2*r.re)*v)
def angular (p : ℝ × ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, ∫ x, slice (actualScale p.1) (p.2*Real.sin θ) x)/(2*Real.pi)

theorem profile_norm (r : ℂ) (v x : ℝ) :
    ‖profile (neutral r v x)‖^2 = Real.exp 8*
      Real.exp (2*(2*r.im)^2*v^2-2*frequency*(2*r.im)*v)*Real.exp (-2*(x-2)^2) := by
  simp only [profile,KFCausalReciprocalNeutralHolomorphic.weightedProfile,
    KFCausalNeutralExponentialProfiles.exponentialProfile,Polynomial.eval_one,
    mul_one,one_mul,← Complex.exp_add,Complex.norm_exp,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  simp [neutral,source,Complex.mul_re,Complex.mul_im,pow_two]
  ring

theorem slice_shift (r : ℂ) (v x : ℝ) :
    slice r v (x+2) = (Real.exp 8*Real.exp (2*(2*r.im)^2*v^2-2*frequency*(2*r.im)*v))*
      (potential (x+(2+(3-2*r.re)*v))*Real.exp (-2*x^2)) := by
  rw [slice,profile_norm,show x+2-2=x by ring]
  rw [show x+2+(3-2*r.re)*v = x+(2+(3-2*r.re)*v) by ring]
  ring

theorem slice_integrable (r : ℂ) (v : ℝ) : Integrable (slice r v) := by
  have hi := (KFCausalNeutralRadialCoherentKernel.quartic_integrable (2+(3-2*r.re)*v)).const_mul
    (Real.exp 8*Real.exp (2*(2*r.im)^2*v^2-2*frequency*(2*r.im)*v))
  have he : Integrable (fun x : ℝ => slice r v (x+2)) := by simpa only [slice_shift] using hi
  simpa only [add_assoc,neg_add_cancel,add_zero] using he.comp_add_right (-2)

theorem slice_integral (r : ℂ) (v : ℝ) :
    (∫ x, slice r v x) = Real.exp 8*mass*marginal r v := by
  rw [← integral_add_right_eq_self (slice r v) 2]
  simp_rw [slice_shift]
  rw [integral_const_mul,KFCausalNeutralRadialCoherentKernel.quartic_integral]
  unfold marginal
  ring

theorem slice_geometry (v x : ℝ) : slice geometry v x = KFCausalNeutralRadialActualGeometry.slice v x := by
  have hz : neutral geometry v x = (x:ℂ)+(displacement*v:ℝ)*Complex.I := by
    unfold neutral displacement
    push_cast
    ring
  rw [slice,hz]
  rfl

theorem angular_formula (p : ℝ × ℝ) : angular p =
    (Real.exp 8*mass)*(∫ θ in -Real.pi..Real.pi, marginal (actualScale p.1) (p.2*Real.sin θ))/(2*Real.pi) := by
  unfold angular
  simp_rw [slice_integral]
  rw [intervalIntegral.integral_const_mul]

theorem angular_zero (ρ : ℝ) : angular (0,ρ) = KFCausalNeutralRadialActualObstruction.physicalAngular ρ := by
  unfold angular KFCausalNeutralRadialActualObstruction.physicalAngular
  change (∫ θ in -Real.pi..Real.pi, ∫ x, slice geometry (ρ*Real.sin θ) x)/(2*Real.pi) = _
  simp_rw [slice_geometry]

theorem angular_differentiable : Differentiable ℝ angular := by
  have hr : ContDiff ℝ 1 actualScale := KFCausalClockFloorRelativeShift.scale_smooth 1 (1/128)
    (by norm_num) (by simpa only [mul_one] using KFCausalNeutralRadialActualGeometry.actual_parameters.2.2.2)
  have hi : ContDiff ℝ 1 (fun s => (actualScale s).im) := Complex.imCLM.contDiff.comp hr
  have hre : ContDiff ℝ 1 (fun s => (actualScale s).re) := Complex.reCLM.contDiff.comp hr
  have hm : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => marginal (actualScale p.1.1) (p.1.2*Real.sin p.2)) := by
    have hη : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => 2*(actualScale p.1.1).im) :=
      contDiff_const.mul (hi.comp (contDiff_fst.comp contDiff_fst))
    have hL : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => 3-2*(actualScale p.1.1).re) :=
      contDiff_const.sub (contDiff_const.mul (hre.comp (contDiff_fst.comp contDiff_fst)))
    have hv : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => p.1.2*Real.sin p.2) := by fun_prop
    have he : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ =>
        2*(2*(actualScale p.1.1).im)^2*(p.1.2*Real.sin p.2)^2-
          2*frequency*(2*(actualScale p.1.1).im)*(p.1.2*Real.sin p.2)) :=
      ((contDiff_const.mul (hη.pow 2)).mul (hv.pow 2)).sub ((contDiff_const.mul hη).mul hv)
    have hx : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ =>
        2+(3-2*(actualScale p.1.1).re)*(p.1.2*Real.sin p.2)) := contDiff_const.add (hL.mul hv)
    exact he.exp.mul ((((hx.pow 4).div_const 4).add ((contDiff_const.mul (hx.pow 2)).div_const 8)).add contDiff_const)
  have hd := KFCausalCompactAngularFDeriv.integral_differentiable
    (fun p θ => marginal (actualScale p.1) (p.2*Real.sin θ)) hm
  rw [show angular = fun p => (Real.exp 8*mass)*
    (∫ θ in -Real.pi..Real.pi, marginal (actualScale p.1) (p.2*Real.sin θ))/(2*Real.pi)
    from funext angular_formula]
  simpa only [div_eq_mul_inv] using (hd.const_mul (Real.exp 8*mass)).mul_const ((2*Real.pi)⁻¹)

theorem jointSlice_factor (r z : ℂ) (v x : ℝ) :
    jointSlice 1 1 (fun _ => 1) (fun _ => source) (fun _ => 1) (fun _ => 1) r z v x =
      weight z*slice r v x := by
  unfold jointSlice profileSum laplaceSum
  simp only [Fin.sum_univ_one,Complex.ofReal_one,one_mul,mul_one,neg_mul]
  rw [mul_comm _ (Complex.exp (-z)),norm_mul,mul_pow]
  unfold weight slice profile KFCausalChargedPairCoordinates.fieldSlope
  ring

theorem jointArea_factor (s X : ℝ) (z : ℂ) :
    jointArea 1 1 (fun _ => 1) (fun _ => source) (fun _ => 1) (fun _ => 1)
      (actualScale s) z X = weight z*angular (s,Real.sqrt X) := by
  unfold jointArea KFCausalCorrectedAngularComparison.angular angular
  simp_rw [jointSlice_factor,integral_const_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

#print axioms profile_norm
#print axioms slice_shift
#print axioms slice_integrable
#print axioms slice_integral
#print axioms slice_geometry
#print axioms angular_formula
#print axioms angular_zero
#print axioms angular_differentiable
#print axioms jointSlice_factor
#print axioms jointArea_factor
end
end UnifiedTheory.Audit.KFCausalNeutralRadialClockFamily
