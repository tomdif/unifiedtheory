/- The imaginary translation used by the actual longitudinal exponential
changes the clock defect by O(defect^2), uniformly in the real clock
coordinate. This is a coefficient estimate; an interacting propagator
commutator estimate still requires operator-domain arguments. -/
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectShift
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect

theorem complexClock_vertical_difference (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) :
    ‖complexClock ε q - complexClock ε (q.re:ℂ)‖ ≤ 2 * |q.im| := by
  have hr : (q.re:ℂ) ∈ targetStrip ε := by
    change |(q.re:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity
  have h1 := complexInverse_right ε hε q hq
  have h0 := complexInverse_right ε hε (q.re:ℂ) hr
  have he : complexClock ε q - complexClock ε (q.re:ℂ) = q-(q.re:ℂ) -
      (ε:ℂ)*(complexInverse ε q-complexInverse ε (q.re:ℂ)) := by
    unfold complexClock
    unfold complexChart at h1 h0
    linear_combination h1-h0
  have hqre : q-(q.re:ℂ) = (q.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  have hn : ‖q-(q.re:ℂ)‖ = |q.im| := by
    rw [hqre,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hb := complexInverse_norm_bound ε hε q (q.re:ℂ) hq hr
  rw [hn] at hb
  rw [he]
  calc
    _ ≤ ‖q-(q.re:ℂ)‖ + ‖(ε:ℂ)*(complexInverse ε q-complexInverse ε (q.re:ℂ))‖ := norm_sub_le _ _
    _ = |q.im| + ε*‖complexInverse ε q-complexInverse ε (q.re:ℂ)‖ := by
      rw [hn,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
    _ ≤ |q.im| + ε*(|q.im|/ε) := by nlinarith
    _ = 2*|q.im| := by field_simp; ring

theorem complexDefect_vertical_difference (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    ‖complexDefect ε q - (realDefect ε hε q.re:ℂ)‖ ≤
      (4*|q.im|/ε) * (realDefect ε hε q.re)^2 := by
  have ht : q ∈ targetStrip ε := by change |q.im| ≤ Real.pi*ε/2; nlinarith [Real.pi_pos]
  have hC := realClock_positive ε hε q.re
  have hc := complexClock_ne_zero ε hε q ht
  have hcn : (realClock ε hε q.re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have he : complexDefect ε q - (realDefect ε hε q.re:ℂ) =
      (ε:ℂ)*((realClock ε hε q.re:ℂ)-complexClock ε q) /
        (complexClock ε q*(realClock ε hε q.re:ℂ)) := by
    rw [← complexDefect_real ε hε q.re]
    unfold complexDefect
    rw [complexClock_real ε hε q.re]
    field_simp
  have hb := complexClock_vertical_difference ε hε q ht
  rw [complexClock_real ε hε q.re, norm_sub_rev] at hb
  have hl := mul_le_mul_of_nonneg_right (complexClock_norm_lower ε hε q hq) hC.le
  have hd : (realClock ε hε q.re)^2/2 ≤ ‖complexClock ε q‖ * realClock ε hε q.re := by nlinarith
  rw [he,norm_div,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
  calc
    _ ≤ ε*(2*|q.im|)/(‖complexClock ε q‖*realClock ε hε q.re) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hε.le) (by positivity)
    _ ≤ ε*(2*|q.im|)/((realClock ε hε q.re)^2/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = _ := by
      change ε*(2*|q.im|)/((realClock ε hε q.re)^2/2) =
        (4*|q.im|/ε)*(ε/realClock ε hε q.re)^2
      field_simp
      ring

/-- The squared defect changes by a cubic quantity under vertical shift. -/
theorem complexDefect_square_difference (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    ‖complexDefect ε q ^ 2 - (realDefect ε hε q.re:ℂ)^2‖ ≤ (12*|q.im|/ε)*(realDefect ε hε q.re)^3 := by
  let z := complexDefect ε q
  let d := realDefect ε hε q.re
  have hd : 0 < d := realDefect_positive ε hε q.re
  have he : z^2-(d:ℂ)^2 = (z-(d:ℂ))*(z+(d:ℂ)) := by ring
  have hz : ‖z+(d:ℂ)‖ ≤ 3*d := by
    have h := norm_add_le z (d:ℂ)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] at h
    have hb := complexDefect_norm_bound ε hε q hq
    change ‖z‖ ≤ 2*d at hb
    linarith
  rw [he,norm_mul]
  have hb := mul_le_mul (complexDefect_vertical_difference ε hε q hq) hz
    (norm_nonneg _) (by positivity : 0 ≤ (4*|q.im|/ε)*d^2)
  convert hb using 1
  ring

/-- The imaginary part entering a squared-defect form pairing is cubic. -/
theorem complexDefect_square_im_bound (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    |(complexDefect ε q ^ 2).im| ≤ (12*|q.im|/ε)*(realDefect ε hε q.re)^3 := by
  have h := Complex.abs_im_le_norm
    (complexDefect ε q ^ 2 - (realDefect ε hε q.re:ℂ)^2)
  have hm : ((realDefect ε hε q.re:ℂ)^2).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  rw [Complex.sub_im, hm, sub_zero] at h
  exact h.trans (complexDefect_square_difference ε hε q hq)

theorem half_exponential_shift_difference (ε hbar q : ℝ) (hε : 0 < ε)
    (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    ‖complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I) - (realDefect ε hε q:ℂ)‖ ≤
      (2*|hbar|/ε)*(realDefect ε hε q)^2 := by
  have hy : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have h := complexDefect_vertical_difference ε hε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I) (by simpa using hy)
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,sub_zero,add_zero,Complex.add_im,Complex.mul_im,mul_one,
    zero_add,abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  convert h using 1
  ring

theorem half_exponential_square_difference (ε hbar q : ℝ) (hε : 0 < ε)
    (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    ‖complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)^2 - (realDefect ε hε q:ℂ)^2‖ ≤
      (6*|hbar|/ε)*(realDefect ε hε q)^3 := by
  have hy : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have h := complexDefect_square_difference ε hε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I) (by simpa using hy)
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,sub_zero,add_zero,Complex.add_im,Complex.mul_im,mul_one,
    zero_add,abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  convert h using 1
  ring

#print axioms complexClock_vertical_difference
#print axioms complexDefect_vertical_difference
#print axioms complexDefect_square_difference
#print axioms complexDefect_square_im_bound
#print axioms half_exponential_shift_difference
#print axioms half_exponential_square_difference

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectShift
