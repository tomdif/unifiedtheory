/- The actual clock part of the two-vacuum-square Gaussian quotient is
analytic and uniformly bounded on the full second contour strip. The
inverse clock is controlled by its positive real part; no transverse
Gaussian bound or mixed-operator graph is assumed or concluded here. -/
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalTwoShearClockQuotient
noncomputable section
open KFCausalComplexClockChart
open KFCausalComplexClockInverse
open KFCausalClockFloorComplexDefect (complexClock complexClock_ne_zero)

def shift (h : ℝ) (q : ℂ) : ℂ := q-(h:ℂ)*Complex.I

theorem shift_im (h : ℝ) (q : ℂ) : (shift h q).im=q.im-h := by simp [shift]

theorem shift_distance (h : ℝ) (q : ℂ) : ‖q-shift h q‖=|h| := by
  rw [shift,sub_sub_cancel,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs]

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)

include hε hb in
theorem strip_membership (q : ℂ) (hq : |q.im| ≤ |h|) :
    q ∈ targetStrip ε ∧ shift h q ∈ targetStrip ε ∧ (q.re:ℂ) ∈ targetStrip ε := by
  have hp := mul_lt_mul_of_pos_right Real.pi_gt_three hε
  have hsum : |q.im-h| ≤ 2*|h| := by
    have ha := abs_sub_le q.im 0 h
    simp only [sub_zero,zero_sub,abs_neg] at ha
    linarith
  refine ⟨?_,?_,?_⟩
  · change |q.im| ≤ Real.pi*ε/2
    linarith
  · change |(shift h q).im| ≤ Real.pi*ε/2
    rw [shift_im]
    linarith
  · change |(q.re:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity

include hε hb in
theorem inverse_increment (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖complexInverse ε q-complexInverse ε (shift h q)‖ ≤ |h|/ε := by
  have hm := strip_membership ε h hε hb q hq
  simpa only [shift_distance] using complexInverse_norm_bound ε hε q (shift h q) hm.1 hm.2.1

include hε hb in
theorem two_increment_bound (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖complexInverse ε (shift h q)-complexInverse ε q‖+
      ‖complexInverse ε q-complexInverse ε (q.re:ℂ)‖ ≤ 1/5 := by
  have hm := strip_membership ε h hε hb q hq
  have h₁ := inverse_increment ε h hε hb q hq
  have h₂ := complexInverse_norm_bound ε hε q (q.re:ℂ) hm.1 hm.2.2
  have hd : ‖q-(q.re:ℂ)‖=|q.im| := by
    have he : q-(q.re:ℂ)=(q.im:ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [hd] at h₂
  rw [norm_sub_rev] at h₁
  have hq' := (div_le_div_of_nonneg_right hq hε.le)
  have hh' : |h|/ε ≤ 1/10 := (div_le_iff₀ hε).mpr (by linarith)
  linarith

include hε in
theorem inverse_clock_bound (q : ℂ) (hq : q ∈ targetStrip ε) :
    ‖(complexClock ε q)⁻¹‖ ≤ ε⁻¹ := by
  have hr := strip_exp_re_nonnegative (complexInverse ε q)
    (show |(complexInverse ε q).im| ≤ Real.pi/2 from le_of_lt (complexInverse_mem ε hε q hq))
  have hc : ε ≤ ‖complexClock ε q‖ := by
    have hn := Complex.re_le_norm (complexClock ε q)
    simp only [complexClock,Complex.add_re,Complex.ofReal_re] at hn
    change ε ≤ ‖Complex.exp (complexInverse ε q)+(ε:ℂ)‖
    linarith
  rw [norm_inv]
  exact inv_anti₀ hε hc

def quotient (a : ℝ) (q : ℂ) : ℂ :=
  (complexClock ε q)⁻¹*
    Complex.exp (complexInverse ε q-complexInverse ε (shift h q))*
    Complex.exp (-(a:ℂ)*(shift h q)^2+(a/2:ℝ)*q^2)

include hε hb in
theorem quotient_analytic (a : ℝ) (q : ℂ) (hq : |q.im| ≤ |h|) :
    AnalyticAt ℂ (quotient ε h a) q := by
  have hm := strip_membership ε h hε hb q hq
  have hs : AnalyticAt ℂ (fun z => complexInverse ε (shift h z)) q :=
    (complexInverse_analytic ε hε (shift h q) hm.2.1).comp (by unfold shift; fun_prop)
  have hi := complexInverse_analytic ε hε q hm.1
  have hc : AnalyticAt ℂ (complexClock ε) q := hi.cexp.add analyticAt_const
  exact ((hc.inv (complexClock_ne_zero ε hε q hm.1)).mul (hi.sub hs).cexp).mul
    (by unfold shift; fun_prop)

include hε hb in
theorem quotient_gaussian_bound (a : ℝ) (ha : 0 ≤ a) (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖quotient ε h a q‖ ≤ ε⁻¹*Real.exp (|h|/ε)*
      Real.exp (-(a/2)*q.re^2+4*a*h^2) := by
  have hm := strip_membership ε h hε hb q hq
  have hc := inverse_clock_bound ε hε q hm.1
  have hs := inverse_increment ε h hε hb q hq
  have he : ‖Complex.exp (complexInverse ε q-complexInverse ε (shift h q))‖ ≤
      Real.exp (|h|/ε) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hs)
  have hq2 : (q.im-h)^2 ≤ 4*h^2 := by
    have ht : |q.im-h| ≤ 2*|h| := by
      have ht := abs_sub_le q.im 0 h
      simp only [sub_zero,zero_sub,abs_neg] at ht
      linarith
    have hh := sq_le_sq₀ (abs_nonneg (q.im-h)) (by positivity : 0 ≤ 2*|h|)
    have hh' := hh.mpr ht
    norm_num [mul_pow,sq_abs] at hh'
    exact hh'
  have hg : ‖Complex.exp (-(a:ℂ)*(shift h q)^2+(a/2:ℝ)*q^2)‖ ≤
      Real.exp (-(a/2)*q.re^2+4*a*h^2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [shift,pow_two,Complex.mul_re,Complex.mul_im]
    nlinarith [mul_le_mul_of_nonneg_left hq2 ha, mul_nonneg ha (sq_nonneg q.im)]
  rw [quotient,norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul hc he (norm_nonneg _) (inv_nonneg.mpr hε.le)) hg
    (norm_nonneg _) (by positivity)

#print axioms shift_im
#print axioms shift_distance
#print axioms strip_membership
#print axioms inverse_increment
#print axioms two_increment_bound
#print axioms inverse_clock_bound
#print axioms quotient_analytic
#print axioms quotient_gaussian_bound
end
end UnifiedTheory.Audit.KFCausalTwoShearClockQuotient
