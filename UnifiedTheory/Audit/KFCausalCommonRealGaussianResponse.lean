/- State-independent actual clock response for arbitrary coherent finite
charged widths with one common real neutral source and P=1. This does not
assert the unrestricted source/polynomial response estimate. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianClockSplit
import UnifiedTheory.Audit.KFCausalCommonRealGaussianOriginalField
import UnifiedTheory.Audit.KFCausalReciprocalNeutralKernelDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianResponse
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalGaussianSourceJointKernel (familyForm)
open KFCausalGaussianSourceKernelDerivative (familySlope)
open KFCausalCommonRealGaussianClockSplit (clockQ clockChi familyFieldSlope)
open KFCausalJointFourierRealDilationClock (realDilationRate)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalReciprocalNeutralClockDerivative (totalEnergy totalResponse)

def jointEnergy (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (B : ℝ) (c : Fin n → ℂ) : ℝ :=
  ∫ z, positiveDensity n α β w r c (fun _ => exponentialProfile (B:ℂ) 1 1) z ∂jointMeasure

private theorem gamma_re (α : ℝ) (r : ℂ) :
    2*(gamma α r).re=α*(r.re^2-r.im^2) := by
  simp [gamma,pow_two,Complex.mul_re,Complex.mul_im]
  ring

theorem imaginary_slope_lower (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (B : ℝ) (c : Fin n → ℂ) (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i, 0 < w i) (hr : |r.im| < r.re)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i) :
    -2*jointEnergy n α β w r B c ≤
      r.im*(familySlope n α β w r Complex.I (fun _ => (B:ℂ)) c).re := by
  have he : KFCausalCommonRealGaussianImaginaryDerivative.line r.re r.im=r := by
    apply Complex.ext <;> simp [KFCausalCommonRealGaussianImaginaryDerivative.line]
  have hm : ∀ i, 8*β*r.im^2 < α*(r.re^2-r.im^2)*w i := by
    intro i
    simpa only [gamma_re] using hd i
  have hh := KFCausalCommonRealGaussianImaginaryDerivative.value_hasDerivAt n α β r.re B w c r.im hβ hm
  have hl := KFCausalCommonRealGaussianImaginaryDerivative.imaginary_lower n α β r.re B w c r.im
    hα hβ hw hr hm
  rw [hh.deriv] at hl
  simpa only [KFCausalCommonRealGaussianImaginaryDerivative.value,
    KFCausalCommonRealGaussianImaginaryDerivative.slope,he,jointEnergy] using hl

variable (n : ℕ) (α β ε y s B : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
  (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i)
local notation "r" => scale ε y s
local notation "t" => fraction ε s
include hα hβ hwidth hε hy hw

private theorem actual_geometry :
    |(r).im| < (r).re ∧ 0 < (gamma α r).re ∧
      (∀ i, 8*β*(r).im^2 < 2*(gamma α r).re*w i) ∧
      (∀ i, 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*(r).im^2) := by
  have ha := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
  have hA := KFCausalClockFloorExactScaleRegion.square_re_half_le ε y s hε hy
  have hr : |(r).im| < (r).re := by nlinarith [sq_abs (r).im,abs_nonneg (r).im]
  have hp := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr
  have hf (i : Fin n) : 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*(r).im^2 := by
    have hreg := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
    obtain ⟨hc,ha'⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hreg
    exact (KFCausalJointFourierDilationQuartic.width_floors α _ (w i) β (hw i) ha' hc).2
  refine ⟨hr,hp,?_,hf⟩
  intro i
  rw [gamma_re]
  have hi := hf i
  unfold KFCausalReciprocalGaussianCoordinates.area at hi
  nlinarith

theorem actual_kernel_bound :
    (familySlope n α β w r (deriv (scale ε y) s) (fun _ => (B:ℂ)) c).re ≤
      536*t*jointEnergy n α β w r B c := by
  obtain ⟨hr,hp,hd,hf⟩ := actual_geometry n α β ε y s w hα hβ hwidth hε hy hw
  have hwp : ∀ i, 0 < w i := fun i => lt_of_lt_of_le (by norm_num) (hw i)
  let E := jointEnergy n α β w r B c
  let Idot := (familySlope n α β w r Complex.I (fun _ => (B:ℂ)) c).re
  let F := (familyFieldSlope n α β w r B c).re
  let h := realDilationRate t r
  let q := clockQ t r
  let χ := clockChi t r
  let J := (r).im*Idot+3*χ*F
  have hEpos : 0 ≤ E := integral_nonneg
    (KFCausalReciprocalNeutralPositiveForm.positiveDensity_nonneg n α β w r c _)
  have hEq : (familyForm n α β w r (fun _ => (B:ℂ)) c).re=E := by
    rw [← KFCausalGaussianSourceJointKernel.family_integral n α β w r (fun _ => (B:ℂ)) c hβ hf,
      integral_complex_ofReal,Complex.ofReal_re]
    rfl
  have hI : -2*E ≤ (r).im*Idot := imaginary_slope_lower n α β w r B c hα hβ hwp hr hd
  have hF := KFCausalCommonRealGaussianOriginalField.original_field_bounds n α β w r B c hβ hp hwp hd
  change 0 ≤ KFCausalChargedPairCoordinates.fieldSlope r*F ∧
    KFCausalChargedPairCoordinates.fieldSlope r*F ≤ 4*E at hF
  have hL := (KFCausalClockFloorExactScaleRegion.fieldSlope_bounds ε y s hε hy).1
  have hFp : 0 ≤ F := (mul_nonneg_iff_of_pos_left (by linarith : 0 < KFCausalChargedPairCoordinates.fieldSlope r)).mp hF.1
  have hF8 : F ≤ 8*E := by
    nlinarith [mul_le_mul_of_nonneg_right hL hFp]
  have ht := KFCausalNeutralPlaneNormalizedGeometry.fraction_bounds ε s hε
  have htI : t ∈ Set.Icc 0 1 := ⟨ht.1.le,ht.2.le⟩
  have hq := KFCausalCommonRealGaussianClockSplit.clock_q_bounds ε y s hε hy t htI
  have hχ := KFCausalCommonRealGaussianClockSplit.clock_chi_bound ε y s hε hy t htI
  change 0 ≤ q ∧ q ≤ 20*t at hq
  change |χ| ≤ 1 at hχ
  have hJ : -26*E ≤ J := by
    have hx := mul_le_mul_of_nonneg_right (abs_le.mp hχ).1 hFp
    dsimp only [J]
    nlinarith
  have hR := KFCausalClockFloorExactScaleRegion.norm_square_one_le ε y s hε hy
  have hRn : KFCausalReciprocalWedgeVelocity.radius r ≠ 0 := by
    change 1 ≤ KFCausalReciprocalWedgeVelocity.radius r at hR
    linarith
  have hrate : h=q*χ := KFCausalCommonRealGaussianClockSplit.rate_eq_q_chi t r hRn
  have hh := KFCausalJointFourierRealDilationClock.real_dilation_bound ε y s hε hy t htI
  change |h| ≤ 8*t*(r).im^2 at hh
  have hb := KFCausalClockFloorExactScaleRegion.imaginary_square_le_half ε y s hε hy
  have hh4 : |h| ≤ 4*t := by nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr hb)]
  have hfirst : -4*h*E ≤ 16*t*E :=
    mul_le_mul_of_nonneg_right (by nlinarith [neg_abs_le h]) hEpos
  have hqJ := mul_le_mul_of_nonneg_left hJ hq.1
  have hqE := mul_le_mul_of_nonneg_right hq.2 hEpos
  have he := congrArg Complex.re
    (KFCausalCommonRealGaussianClockSplit.actual_family_split ε y s hε hy n α β w B c hα hβ hwidth hw)
  simp only [Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero] at he
  norm_num at he
  rw [hEq] at he
  have he' : (familySlope n α β w r (deriv (scale ε y) s) (fun _ => (B:ℂ)) c).re =
      -4*h*E-(q*(r).im)*Idot-(3*h)*F := by
    dsimp only [h,q,Idot,F]
    linear_combination he
  calc
    _ = -4*h*E-q*J := by rw [he']; dsimp only [J]; rw [hrate]; ring
    _ ≤ 536*t*E := by nlinarith

theorem actual_joint_derivative :
    HasDerivAt (fun z => jointEnergy n α β w (scale ε y z) B c)
      (familySlope n α β w r (deriv (scale ε y) s) (fun _ => (B:ℂ)) c).re s := by
  have hc := KFCausalGaussianSourceKernelDerivative.actual_integral_derivative n α β ε y s w
    (fun _ => (B:ℂ)) c hα hβ hwidth hε hy hw
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hc
  simpa only [Function.comp_apply,Complex.reCLM_apply,integral_complex_ofReal,Complex.ofReal_re,jointEnergy] using hh

theorem total_energy_eq :
    totalEnergy n ε y α β w (fun _ => (B:ℂ)) (fun _ => 1) (fun _ => c) s =
      Real.pi/4*jointEnergy n α β w r B c := by
  have he := KFCausalReciprocalNeutralActualPositive.pairing_positive_integral n α β ε y s w
    (fun _ => (B:ℂ)) c (fun _ => 1) hα hβ hwidth hε hy hw
  rw [KFCausalReciprocalNeutralKernelDerivative.pairing_totalEnergy n ε y α β w
    (fun _ => (B:ℂ)) (fun _ => 1) (fun _ => c) hε hy hα hβ hwidth hw] at he
  exact Complex.ofReal_injective he

theorem total_response_eq :
    totalResponse n ε y α β w (fun _ => (B:ℂ)) (fun _ => 1) (fun _ => c) s =
      Real.pi/4*(familySlope n α β w r (deriv (scale ε y) s) (fun _ => (B:ℂ)) c).re := by
  have he : totalEnergy n ε y α β w (fun _ => (B:ℂ)) (fun _ => 1) (fun _ => c) =
      fun z => Real.pi/4*jointEnergy n α β w (scale ε y z) B c :=
    funext (fun z => total_energy_eq n α β ε y z B w c hα hβ hwidth hε hy hw)
  have hd := KFCausalReciprocalNeutralClockDerivative.total_derivative n ε y α β w
    (fun _ => (B:ℂ)) (fun _ => 1) (fun _ => c) hε hy hα hβ hwidth hw (fun _ => contDiff_const) s
  rw [he] at hd
  exact hd.unique ((actual_joint_derivative n α β ε y s B w c hα hβ hwidth hε hy hw).const_mul (Real.pi/4))

theorem total_response_bound :
    totalResponse n ε y α β w (fun _ => (B:ℂ)) (fun _ => 1) (fun _ => c) s ≤
      536*fraction ε s*totalEnergy n ε y α β w (fun _ => (B:ℂ)) (fun _ => 1) (fun _ => c) s := by
  rw [total_response_eq n α β ε y s B w c hα hβ hwidth hε hy hw,
    total_energy_eq n α β ε y s B w c hα hβ hwidth hε hy hw]
  have he := mul_le_mul_of_nonneg_left (actual_kernel_bound n α β ε y s B w c hα hβ hwidth hε hy hw)
    (show 0 ≤ Real.pi/4 by positivity)
  nlinarith

#print axioms imaginary_slope_lower
#print axioms actual_kernel_bound
#print axioms actual_joint_derivative
#print axioms total_energy_eq
#print axioms total_response_eq
#print axioms total_response_bound
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianResponse
