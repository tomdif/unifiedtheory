/- State-independent actual clock response for arbitrary coherent finite
charged widths with one common purely imaginary neutral source and P=1. This does not
assert the unrestricted source/polynomial response estimate. -/
import UnifiedTheory.Audit.KFCausalGaussianWeightedGeneralClockSplit
import UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianWeightedImaginaryDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianWeightedResponse
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalCommonRealGaussianClockSplit (clockQ clockChi)
open KFCausalJointFourierRealDilationClock (realDilationRate)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
variable (mass2 quartic vacuum : ℝ)
local notation "familyForm" => KFCausalGaussianWeightedSourceKernelDerivative.familyForm mass2 quartic vacuum
local notation "familySlope" => KFCausalGaussianWeightedSourceKernelDerivative.familySlope mass2 quartic vacuum
local notation "familyFieldSlope" => KFCausalCommonImaginaryGaussianWeightedKernel.originalFieldSlope mass2 quartic vacuum

def jointEnergy (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (D : ℝ) (c : Fin n → ℂ) : ℝ :=
  ∫ z, KFCausalCommonImaginaryGaussianJointDensity.density mass2 quartic vacuum n α β D w r c z ∂jointMeasure

private theorem gamma_re (α : ℝ) (r : ℂ) :
    2*(gamma α r).re=α*(r.re^2-r.im^2) := by
  simp [gamma,pow_two,Complex.mul_re,Complex.mul_im]
  ring

theorem imaginary_slope_lower (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (D : ℝ) (c : Fin n → ℂ) (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i, 0 < w i) (hr : |r.im| < r.re)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    -2*jointEnergy mass2 quartic vacuum n α β w r D c ≤
      r.im*(familySlope n α β w r Complex.I (fun _ => (D:ℂ)*Complex.I) c).re := by
  have he : KFCausalCommonRealGaussianImaginaryDerivative.line r.re r.im=r := by
    apply Complex.ext <;> simp [KFCausalCommonRealGaussianImaginaryDerivative.line]
  have hm : ∀ i, 8*β*r.im^2 < α*(r.re^2-r.im^2)*w i := by
    intro i
    simpa only [gamma_re] using hd i
  have hh := KFCausalCommonImaginaryGaussianWeightedImaginaryDerivative.value_hasDerivAt mass2 quartic vacuum n α β r.re D w c r.im hα hβ hw hr hm hmass hquartic hvacuum
  have hl := KFCausalCommonImaginaryGaussianWeightedImaginaryDerivative.imaginary_lower mass2 quartic vacuum n α β r.re D w c r.im
    hα hβ hw hr hm hmass hquartic hvacuum
  rw [hh.deriv] at hl
  simpa only [KFCausalCommonImaginaryGaussianWeightedImaginaryDerivative.value,
    KFCausalCommonImaginaryGaussianWeightedImaginaryDerivative.slope,he,jointEnergy] using hl

variable (n : ℕ) (α β ε y s D : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
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

theorem actual_kernel_bound (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    (familySlope n α β w r (deriv (scale ε y) s) (fun _ => (D:ℂ)*Complex.I) c).re ≤
      536*t*jointEnergy mass2 quartic vacuum n α β w r D c := by
  obtain ⟨hr,hp,hd,hf⟩ := actual_geometry n α β ε y s w hα hβ hwidth hε hy hw
  have hwp : ∀ i, 0 < w i := fun i => lt_of_lt_of_le (by norm_num) (hw i)
  let E := jointEnergy mass2 quartic vacuum n α β w r D c
  let Idot := (familySlope n α β w r Complex.I (fun _ => (D:ℂ)*Complex.I) c).re
  let F := (familyFieldSlope n α β w r D c).re
  let h := realDilationRate t r
  let q := clockQ t r
  let χ := clockChi t r
  let J := (r).im*Idot+3*χ*F
  have hEpos : 0 ≤ E := integral_nonneg
    (fun z => KFCausalCommonImaginaryGaussianJointDensity.density_nonnegative mass2 quartic vacuum n α β D w r c z hmass hquartic hvacuum)
  have hEq : (familyForm n α β w r (fun _ => (D:ℂ)*Complex.I) c).re=E := by
    exact (congrArg Complex.re (KFCausalCommonImaginaryGaussianWeightedKernel.joint_integral_eq_family
      mass2 quartic vacuum n α β D w r c hβ hp hwp hd hmass hquartic hvacuum)).symm
  have hI : -2*E ≤ (r).im*Idot := imaginary_slope_lower mass2 quartic vacuum n α β w r D c hα hβ hwp hr hd hmass hquartic hvacuum
  have hF := KFCausalCommonImaginaryGaussianWeightedKernel.original_field_bounds mass2 quartic vacuum n α β w r D c hβ hp hwp hd hmass hquartic hvacuum
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
    (KFCausalGaussianWeightedGeneralClockSplit.actual_family_split mass2 quartic vacuum ε y s hε hy n α β w (fun _ => (D:ℂ)*Complex.I) c hα hβ hwidth hw)
  simp only [Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero] at he
  norm_num at he
  rw [hEq] at he
  have he' : (familySlope n α β w r (deriv (scale ε y) s) (fun _ => (D:ℂ)*Complex.I) c).re =
      -4*h*E-(q*(r).im)*Idot-(3*h)*F := by
    dsimp only [h,q,Idot,F,KFCausalCommonImaginaryGaussianWeightedKernel.originalFieldSlope]
    linear_combination he
  calc
    _ = -4*h*E-q*J := by rw [he']; dsimp only [J]; rw [hrate]; ring
    _ ≤ 536*t*E := by nlinarith

theorem actual_joint_derivative (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    HasDerivAt (fun z => jointEnergy mass2 quartic vacuum n α β w (scale ε y z) D c)
      (familySlope n α β w r (deriv (scale ε y) s) (fun _ => (D:ℂ)*Complex.I) c).re s := by
  have hwp : ∀ i, 0 < w i := fun i => lt_of_lt_of_le (by norm_num) (hw i)
  have he : (fun z => jointEnergy mass2 quartic vacuum n α β w (scale ε y z) D c) =
      fun z => (familyForm n α β w (scale ε y z) (fun _ => (D:ℂ)*Complex.I) c).re := by
    funext z
    obtain ⟨_,hp,hd,_⟩ := actual_geometry n α β ε y z w hα hβ hwidth hε hy hw
    exact congrArg Complex.re (KFCausalCommonImaginaryGaussianWeightedKernel.joint_integral_eq_family
      mass2 quartic vacuum n α β D w (scale ε y z) c hβ hp hwp hd hmass hquartic hvacuum)
  rw [he]
  obtain ⟨_,_,_,hf⟩ := actual_geometry n α β ε y s w hα hβ hwidth hε hy hw
  have hr := KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity ε y s hε hy
  rw [hr.deriv]
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (KFCausalGaussianWeightedSourceKernelDerivative.familyForm_derivative mass2 quartic vacuum
      hr n α β w (fun _ => (D:ℂ)*Complex.I) c
      (fun i j => (KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) r hβ (hf i) (hf j)).1)
      (fun i j => (KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) r hβ (hf i) (hf j)).2))

#print axioms imaginary_slope_lower
#print axioms actual_kernel_bound
#print axioms actual_joint_derivative
end
end UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianWeightedResponse
