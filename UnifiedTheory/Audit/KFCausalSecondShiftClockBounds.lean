/- Analyticity and uniform strip bounds for the clock coefficients needed
when the actual clock momentum is followed by a second matter action. -/
import UnifiedTheory.Audit.KFCausalAnalyticClockFamily
import UnifiedTheory.Audit.KFCausalGaussianClockMoment
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
import UnifiedTheory.Audit.KFCausalGaussianVacuumSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalSecondShiftClockBounds
noncomputable section
open KFCausalClockFloorComplexDefect
open KFCausalClockFloorFullGaussian (clockFactor third_strip_subset)
open KFCausalGaussianClockMoment (bound moment_bound)

def radius (ε : ℝ) : ℝ := Real.pi*ε/6

theorem shift_bound (ε h : ℝ) (hb : |h| ≤ Real.pi*ε/3) : |-h/2| ≤ radius ε := by
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  unfold radius
  linarith

theorem shifted_strip (ε h : ℝ) (hb : |h| ≤ Real.pi*ε/3) (q : ℂ)
    (hq : |q.im| ≤ radius ε) : |(q+(-h/2:ℝ)*Complex.I).im| ≤ Real.pi*ε/3 := by
  have hs := shift_bound ε h hb
  have ha := abs_add_le q.im (-h/2)
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
    Complex.ofReal_im,Complex.I_re,mul_one,mul_zero,add_zero]
  unfold radius at hq hs
  linarith

def defect (ε h : ℝ) (q : ℂ) : ℂ := complexDefect ε (q+(-h/2:ℝ)*Complex.I)
def moment (a h : ℝ) (q : ℂ) : ℂ :=
  (q+(-h/2:ℝ)*Complex.I)*clockFactor (a/2) (q+(-h/2:ℝ)*Complex.I)

theorem defect_analytic (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ Real.pi*ε/3)
    (q : ℂ) (hq : |q.im| ≤ radius ε) : AnalyticAt ℂ (defect ε h) q :=
  (complexDefect_analytic ε hε _ (third_strip_subset ε hε _ (shifted_strip ε h hb q hq))).comp
    (f := fun z : ℂ => z+(-h/2:ℝ)*Complex.I) (by fun_prop)

theorem defect_bound (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ Real.pi*ε/3)
    (q : ℂ) (hq : |q.im| ≤ radius ε) : ‖defect ε h q‖ ≤ 2 :=
  complexDefect_norm_le_two ε hε _ (shifted_strip ε h hb q hq)

theorem moment_analytic (a h : ℝ) (q : ℂ) : AnalyticAt ℂ (moment a h) q := by
  unfold moment clockFactor
  fun_prop

theorem bound_mono (a y D : ℝ) (ha : 0 < a) (hy : |y| ≤ D) : bound a y ≤ bound a D := by
  have hD : 0 ≤ D := (abs_nonneg y).trans hy
  have hs : y^2 ≤ D^2 := by nlinarith [sq_abs y,abs_nonneg y]
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ a/2))
  unfold bound
  rw [abs_of_nonneg hD]
  exact mul_le_mul (by linarith) he (Real.exp_pos _).le (by positivity)

theorem moment_bound_strip (ε a h : ℝ) (ha : 0 < a) (hb : |h| ≤ Real.pi*ε/3)
    (q : ℂ) (hq : |q.im| ≤ radius ε) : ‖moment a h q‖ ≤ bound a (Real.pi*ε/3) := by
  have ht := shifted_strip ε h hb q hq
  have he : q+(-h/2:ℝ)*Complex.I = (q.re:ℂ)+((q.im-h/2:ℝ):ℂ)*Complex.I := by
    apply Complex.ext <;> simp
    ring
  unfold moment
  rw [he]
  exact (moment_bound a q.re (q.im-h/2) ha).trans
    (bound_mono a (q.im-h/2) (Real.pi*ε/3) ha (by simpa [sub_eq_add_neg,neg_div] using ht))

#print axioms shift_bound
#print axioms shifted_strip
#print axioms defect_analytic
#print axioms defect_bound
#print axioms moment_analytic
#print axioms bound_mono
#print axioms moment_bound_strip
end
end UnifiedTheory.Audit.KFCausalSecondShiftClockBounds
