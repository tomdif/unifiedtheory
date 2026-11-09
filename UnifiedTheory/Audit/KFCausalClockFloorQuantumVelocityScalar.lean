/- A quantitative comparison between the imaginary shift in the actual
ordered exponential and the classical clock-defect velocity. The error
is uniform in the clock coordinate and retains cubic defect suppression. -/
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectShift
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)

theorem realDefect_le_one (ε : ℝ) (hε : 0 < ε) (q : ℝ) : realDefect ε hε q ≤ 1 := by
  have h := KFCausalClockFloorCanonicalDefect.response_add_defect ε
    ((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm q) hε.le
  have hp := (KFCausalClockFloorCanonicalDefect.response_bounds ε
    ((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm q) hε).1
  change KFCausalClockFloorCanonicalDefect.defect ε _ ≤ 1
  linarith

theorem complexDrift_difference (ε d : ℝ) (z : ℂ) (hε : 0 < ε)
    (hd : 0 ≤ d ∧ d ≤ 1) (hz : ‖z‖ ≤ 2*d) :
    ‖complexDrift ε z-complexDrift ε (d:ℂ)‖ ≤ (10/ε)*d*‖z-(d:ℂ)‖ := by
  have hn : ‖(d:ℂ)‖ = d := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd.1]
  have hsq : d^2 ≤ d := by nlinarith [mul_nonneg hd.1 (sub_nonneg.mpr hd.2)]
  have hzsq : ‖z‖^2 ≤ (2*d)^2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hzd : ‖z‖*d ≤ 2*d^2 := by nlinarith [mul_le_mul_of_nonneg_right hz hd.1]
  have hb : ‖z^2+z*(d:ℂ)+(d:ℂ)^2-z-(d:ℂ)‖ ≤ 10*d := by
    have h1 := norm_sub_le (z^2+z*(d:ℂ)+(d:ℂ)^2-z) (d:ℂ)
    have h2 := norm_sub_le (z^2+z*(d:ℂ)+(d:ℂ)^2) z
    have h3 := norm_add_le (z^2+z*(d:ℂ)) ((d:ℂ)^2)
    have h4 := norm_add_le (z^2) (z*(d:ℂ))
    simp only [norm_pow,norm_mul,hn] at h1 h2 h3 h4
    nlinarith
  have he : complexDrift ε z-complexDrift ε (d:ℂ) =
      (z-(d:ℂ))*(z^2+z*(d:ℂ)+(d:ℂ)^2-z-(d:ℂ))/(ε:ℂ) := by
    unfold complexDrift
    ring
  rw [he,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  calc
    _ ≤ ‖z-(d:ℂ)‖*(10*d)/ε :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) hε.le
    _ = _ := by ring

theorem vertical_drift_difference (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    ‖complexDrift ε (complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I))-
      complexDrift ε (realDefect ε hε q:ℂ)‖ ≤
        (40/ε^2)*|y| *(realDefect ε hε q)^3 := by
  have hz : ‖complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)‖ ≤ 2*realDefect ε hε q := by
    simpa using complexDefect_norm_bound ε hε ((q:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
  have hd : ‖complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)-(realDefect ε hε q:ℂ)‖ ≤
      (4*|y|/ε)*(realDefect ε hε q)^2 := by
    simpa using complexDefect_vertical_difference ε hε ((q:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
  calc
    _ ≤ (10/ε)*realDefect ε hε q*
        ‖complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)-(realDefect ε hε q:ℂ)‖ :=
      complexDrift_difference ε _ _ hε ⟨(realDefect_positive ε hε q).le,realDefect_le_one ε hε q⟩ hz
    _ ≤ (10/ε)*realDefect ε hε q*((4*|y|/ε)*(realDefect ε hε q)^2) :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg (by positivity) (realDefect_positive ε hε q).le)
    _ = _ := by ring

theorem vertical_remainder (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    ‖complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I)-(realDefect ε hε q:ℂ)-
      (y:ℂ)*Complex.I*(drift ε (realDefect ε hε q):ℂ)‖ ≤
        (40/ε^2)*|y|^2*(realDefect ε hε q)^3 := by
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
  have hb (r : ℝ) (hr : r ∈ uIcc 0 y) : |r| ≤ |y| :=
    by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
  have h := (convex_uIcc (0:ℝ) y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hd r ((hb r hr).trans hy)).hasDerivWithinAt)
    (fun r hr => show ‖Complex.I*(complexDrift ε (complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I))-
        complexDrift ε (d:ℂ))‖ ≤ (40/ε^2)*|y| *d^3 by
      rw [norm_mul,Complex.norm_I,one_mul]
      exact (vertical_drift_difference ε hε q r ((hb r hr).trans hy)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb r hr) (by positivity))
          (pow_nonneg (realDefect_positive ε hε q).le 3)))
    left_mem_uIcc right_mem_uIcc
  have h0 : f 0 = 0 := by simp [f,d,complexDefect_real ε hε q]
  rw [h0,sub_zero,sub_zero,Real.norm_eq_abs] at h
  change ‖f y‖ ≤ _
  convert h using 1
  ring

def quantumVelocity (ε hbar q : ℝ) : ℝ :=
  (-2/hbar)*(complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)).im

theorem quantumVelocity_error (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
    (hh : |hbar| ≤ 2*Real.pi*ε/3) (q : ℝ) :
    |quantumVelocity ε hbar q-drift ε (realDefect ε hε q)| ≤
      (20*|hbar|/ε^2)*(realDefect ε hε q)^3 := by
  have hy : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hb := vertical_remainder ε hε q (-hbar/2) hy
  have hi := Complex.abs_im_le_norm
    (complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)-(realDefect ε hε q:ℂ)-
      ((-hbar/2:ℝ):ℂ)*Complex.I*(drift ε (realDefect ε hε q):ℂ))
  have hh' := hi.trans hb
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.mul_re,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
    zero_add,add_zero,sub_zero] at hh'
  have he : quantumVelocity ε hbar q-drift ε (realDefect ε hε q) =
      (-2/hbar)*((complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)).im-
        (-hbar/2)*drift ε (realDefect ε hε q)) := by unfold quantumVelocity; field_simp; ring
  rw [he,abs_mul]
  apply (mul_le_mul_of_nonneg_left hh' (abs_nonneg (-2/hbar))).trans
  have hn : |hbar| ≠ 0 := abs_ne_zero.mpr hne
  rw [abs_div,abs_div,abs_neg,abs_neg]
  norm_num
  field_simp
  ring_nf
  exact le_rfl

#print axioms realDefect_le_one
#print axioms complexDrift_difference
#print axioms vertical_drift_difference
#print axioms vertical_remainder
#print axioms quantumVelocity_error

end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar
