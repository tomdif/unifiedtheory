/- The real shifted-defect error retains D^3(1-D), so its bound vanishes
at both defect endpoints. Every coefficient uses the actual complex
inverse and the existing closed strip. -/
import UnifiedTheory.Audit.KFCausalShiftedResponseComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTwoEndpointCorrection
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalShiftedResponseComparison (stripFactor one_le_stripFactor complex_response_bound)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar (realDefect_le_one complexDrift_difference)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem vertical_drift_bound (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    ‖complexDrift ε (complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I))‖ ≤
      (8*stripFactor/ε)*(realDefect ε hε q)^2*(1-realDefect ε hε q) := by
  have hz : ‖complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)‖ ≤ 2*realDefect ε hε q := by
    simpa using complexDefect_norm_bound ε hε ((q:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
  have hr : ‖1-complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)‖ ≤
      2*stripFactor*(1-realDefect ε hε q) := by
    simpa using complex_response_bound ε hε ((q:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
  unfold complexDrift
  rw [norm_div,norm_neg,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  calc
    _ ≤ (2*realDefect ε hε q)^2*(2*stripFactor*(1-realDefect ε hε q))/ε :=
      div_le_div_of_nonneg_right
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz 2) hr (norm_nonneg _) (sq_nonneg _)) hε.le
    _ = _ := by ring

theorem vertical_difference (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    ‖complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)-(realDefect ε hε q:ℂ)‖ ≤
      (8*stripFactor/ε)*|y| *(realDefect ε hε q)^2*(1-realDefect ε hε q) := by
  have hseg (r : ℝ) (hr : r ∈ uIcc 0 y) : |r| ≤ |y| :=
    by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
  have hb := (convex_uIcc (0:ℝ) y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (vertical_derivative ε hε q r ((hseg r hr).trans hy)).hasDerivWithinAt)
    (fun r hr => show ‖Complex.I*complexDrift ε (complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I))‖ ≤
        (8*stripFactor/ε)*(realDefect ε hε q)^2*(1-realDefect ε hε q) by
      rw [norm_mul,Complex.norm_I,one_mul]
      exact vertical_drift_bound ε hε q r ((hseg r hr).trans hy)) left_mem_uIcc right_mem_uIcc
  simp only [Complex.ofReal_zero,zero_mul,add_zero,complexDefect_real ε hε q,sub_zero,Real.norm_eq_abs] at hb
  convert hb using 1
  ring

theorem vertical_drift_difference (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    ‖complexDrift ε (complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I))-
      complexDrift ε (realDefect ε hε q:ℂ)‖ ≤
      (80*stripFactor/ε^2)*|y| *(realDefect ε hε q)^3*(1-realDefect ε hε q) := by
  have hz : ‖complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)‖ ≤ 2*realDefect ε hε q := by
    simpa using complexDefect_norm_bound ε hε ((q:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
  have hd := complexDrift_difference ε (realDefect ε hε q) _ hε
    ⟨(realDefect_positive ε hε q).le,realDefect_le_one ε hε q⟩ hz
  apply hd.trans
  have he := mul_le_mul_of_nonneg_left (vertical_difference ε hε q y hy)
    (mul_nonneg (by positivity : 0 ≤ 10/ε) (realDefect_positive ε hε q).le)
  convert he using 1
  ring

theorem vertical_remainder (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    ‖complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)-(realDefect ε hε q:ℂ)-
      (y:ℂ)*Complex.I*(drift ε (realDefect ε hε q):ℂ)‖ ≤
      (80*stripFactor/ε^2)*|y|^2*(realDefect ε hε q)^3*(1-realDefect ε hε q) := by
  let d := realDefect ε hε q
  let f : ℝ → ℂ := fun r => complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I)-(d:ℂ)-
    (r:ℂ)*Complex.I*(drift ε d:ℂ)
  have hd (r : ℝ) (hr : |r| ≤ Real.pi*ε/3) :
      HasDerivAt f (Complex.I*(complexDrift ε (complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I))-
        complexDrift ε (d:ℂ))) r := by
    have hlin := (((hasDerivAt_id r).ofReal_comp.mul_const Complex.I).mul_const (drift ε d:ℂ))
    convert ((vertical_derivative ε hε q r hr).sub_const (d:ℂ)).sub hlin using 1
    rw [complexDrift_real]
    simp only [Complex.ofReal_one,one_mul]
    ring
  have hseg (r : ℝ) (hr : r ∈ uIcc 0 y) : |r| ≤ |y| :=
    by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
  have hp : 0 ≤ (80*stripFactor/ε^2)*d^3*(1-d) :=
    mul_nonneg (mul_nonneg (by unfold stripFactor; positivity)
      (pow_nonneg (realDefect_positive ε hε q).le 3)) (sub_nonneg.mpr (realDefect_le_one ε hε q))
  have he := (convex_uIcc (0:ℝ) y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hd r ((hseg r hr).trans hy)).hasDerivWithinAt)
    (fun r hr => show ‖Complex.I*(complexDrift ε (complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I))-
        complexDrift ε (d:ℂ))‖ ≤ (80*stripFactor/ε^2)*|y| *d^3*(1-d) by
      rw [norm_mul,Complex.norm_I,one_mul]
      apply (vertical_drift_difference ε hε q r ((hseg r hr).trans hy)).trans
      nlinarith only [mul_le_mul_of_nonneg_left (hseg r hr) hp]) left_mem_uIcc right_mem_uIcc
  have h0 : f 0 = 0 := by simp [f,d,complexDefect_real ε hε q]
  rw [h0,sub_zero,sub_zero,Real.norm_eq_abs] at he
  change ‖f y‖ ≤ _
  convert he using 1
  ring

theorem physical_real_difference (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    |defect ε x.1-(physicalSymbol ε h x).re| ≤
      (20*stripFactor*h^2/ε^2)*(defect ε x.1)^3*(1-defect ε x.1) := by
  have ht := vertical_remainder ε hε (chart ε x.1) (-h/2)
    (KFCausalClockFloorShiftedDefect.shift_bound ε h hb)
  rw [KFCausalClockFloorClockShiftTaylor.real_defect_chart ε hε x] at ht
  have hr := (Complex.abs_re_le_norm
    (complexDefect ε ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I)-(defect ε x.1:ℂ)-
      ((-h/2:ℝ):ℂ)*Complex.I*(drift ε (defect ε x.1):ℂ))).trans ht
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,mul_one,add_zero] at hr
  rw [abs_sub_comm]
  convert hr using 1
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),div_pow,sq_abs]
  ring

#print axioms vertical_drift_bound
#print axioms vertical_difference
#print axioms vertical_drift_difference
#print axioms vertical_remainder
#print axioms physical_real_difference
end
end UnifiedTheory.Audit.KFCausalTwoEndpointCorrection
