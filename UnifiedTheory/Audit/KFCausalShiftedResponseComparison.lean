/- Compare the actual shifted response with its real-clock counterpart.
The relative inverse-clock bound keeps the factor 1-D, including near
the clock floor, rather than replacing the response by a constant. -/
import UnifiedTheory.Audit.KFCausalRealShearCorrectionBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedResponseComparison
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexClockChart (targetStrip)
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chartIso)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)

def stripFactor : ℝ := Real.exp (Real.pi/3)

theorem one_le_stripFactor : 1 ≤ stripFactor := Real.one_le_exp (by positivity)

theorem inverse_exp_comparison (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    Real.exp ((chartIso ε hε).symm q.re) ≤ ‖Complex.exp (complexInverse ε q)‖ ∧
      ‖Complex.exp (complexInverse ε q)‖ ≤ stripFactor*Real.exp ((chartIso ε hε).symm q.re) := by
  have ht : q ∈ targetStrip ε := KFCausalClockFloorFullGaussian.third_strip_subset ε hε q hq
  have hr : (q.re:ℂ) ∈ targetStrip ε := by
    change |(q.re:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity
  have hb := complexInverse_norm_bound ε hε q (q.re:ℂ) ht hr
  have he : q-(q.re:ℂ) = (q.im:ℂ)*Complex.I := by apply Complex.ext <;> simp
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    complexInverse_real ε hε] at hb
  have hu := (Complex.re_le_norm (complexInverse ε q-((chartIso ε hε).symm q.re:ℂ))).trans hb
  simp only [Complex.sub_re,Complex.ofReal_re] at hu
  have hy : |q.im|/ε ≤ Real.pi/3 := (div_le_iff₀ hε).mpr (by nlinarith)
  rw [Complex.norm_exp]
  refine ⟨Real.exp_le_exp.mpr (inverse_re_ge_real ε hε q ht),?_⟩
  calc
    _ ≤ Real.exp (Real.pi/3+((chartIso ε hε).symm q.re)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add]; rfl

theorem complexClock_norm_upper (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    ‖complexClock ε q‖ ≤ stripFactor*realClock ε hε q.re := by
  have he := (inverse_exp_comparison ε hε q hq).2
  have hε' := mul_le_mul_of_nonneg_right one_le_stripFactor hε.le
  have hn := norm_add_le (Complex.exp (complexInverse ε q)) (ε:ℂ)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] at hn
  unfold complexClock realClock clock
  nlinarith

theorem real_response_eq (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    1-realDefect ε hε q = Real.exp ((chartIso ε hε).symm q)/realClock ε hε q := by
  have hc := (realClock_positive ε hε q).ne'
  change 1-ε/realClock ε hε q = _
  field_simp
  unfold realClock clock
  ring

theorem complex_response_bound (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    ‖1-complexDefect ε q‖ ≤ 2*stripFactor*(1-realDefect ε hε q.re) := by
  have hc := realClock_positive ε hε q.re
  have ht := KFCausalClockFloorFullGaussian.third_strip_subset ε hε q hq
  have hn := complexClock_ne_zero ε hε q ht
  have he : 1-complexDefect ε q = Complex.exp (complexInverse ε q)/complexClock ε q := by
    unfold complexDefect
    field_simp
    unfold complexClock
    ring
  rw [he,norm_div,real_response_eq]
  calc
    _ ≤ (stripFactor*Real.exp ((chartIso ε hε).symm q.re))/‖complexClock ε q‖ :=
      div_le_div_of_nonneg_right (inverse_exp_comparison ε hε q hq).2 (norm_nonneg _)
    _ ≤ (stripFactor*Real.exp ((chartIso ε hε).symm q.re))/(realClock ε hε q.re/2) :=
      div_le_div_of_nonneg_left (by unfold stripFactor; positivity) (half_pos hc)
        (complexClock_norm_lower ε hε q hq)
    _ = _ := by ring

#print axioms one_le_stripFactor
#print axioms inverse_exp_comparison
#print axioms complexClock_norm_upper
#print axioms real_response_eq
#print axioms complex_response_bound
end
end UnifiedTheory.Audit.KFCausalShiftedResponseComparison
