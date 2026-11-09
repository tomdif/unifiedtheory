/- Complex extension of the regulated clock chart. On the closed
vertical strip |Im z|<=pi/2 its derivative has strictly positive real
part for positive regulator. This is preparation for global inversion. -/
import UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalComplexClockChart
noncomputable section
open Set
open scoped Topology

def complexChart (ε : ℝ) (z : ℂ) : ℂ := Complex.exp z+(ε:ℂ)*z
def closedStrip : Set ℂ := {z | |z.im| ≤ Real.pi/2}
def openStrip : Set ℂ := {z | |z.im| < Real.pi/2}
def targetStrip (ε : ℝ) : Set ℂ := {q | |q.im| ≤ Real.pi*ε/2}

theorem complexChart_real (ε s : ℝ) : complexChart ε (s:ℂ) =
    (KFCausalRegularizedLongitudinalChart.chart ε s:ℂ) := by
  simp [complexChart,KFCausalRegularizedLongitudinalChart.chart,Complex.ofReal_exp]

theorem complexChart_derivative (ε : ℝ) (z : ℂ) :
    HasDerivAt (complexChart ε) (Complex.exp z+(ε:ℂ)) z := by
  simpa only [complexChart,mul_one] using
    (Complex.hasDerivAt_exp z).add ((hasDerivAt_id z).const_mul (ε:ℂ))

theorem complexChart_analytic (ε : ℝ) (z : ℂ) : AnalyticAt ℂ (complexChart ε) z := by
  unfold complexChart
  fun_prop

theorem complexChart_continuous (ε : ℝ) : Continuous (complexChart ε) := by
  exact continuous_iff_continuousAt.mpr (fun z => (complexChart_derivative ε z).continuousAt)

theorem complexChart_re (ε : ℝ) (z : ℂ) :
    (complexChart ε z).re=Real.exp z.re*Real.cos z.im+ε*z.re := by
  simp [complexChart,Complex.exp_re]

theorem complexChart_im (ε : ℝ) (z : ℂ) :
    (complexChart ε z).im=Real.exp z.re*Real.sin z.im+ε*z.im := by
  simp [complexChart,Complex.exp_im]

theorem strip_exp_re_nonnegative (z : ℂ) (hz : z ∈ closedStrip) : 0 ≤ (Complex.exp z).re := by
  rw [Complex.exp_re]
  exact mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc (abs_le.mp hz))

theorem complexChart_derivative_ne_zero (ε : ℝ) (hε : 0 < ε) (z : ℂ) (hz : z ∈ closedStrip) :
    Complex.exp z+(ε:ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hr
  linarith [strip_exp_re_nonnegative z hz]

theorem closedStrip_closed : IsClosed closedStrip :=
  isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const

theorem openStrip_open : IsOpen openStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem closedStrip_segment (w z : ℂ) (hw : w ∈ closedStrip) (hz : z ∈ closedStrip)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : w+(t:ℂ)*(z-w) ∈ closedStrip := by
  change |w.im| ≤ Real.pi/2 at hw
  change |z.im| ≤ Real.pi/2 at hz
  obtain ⟨hw₁,hw₂⟩ := abs_le.mp hw
  obtain ⟨hz₁,hz₂⟩ := abs_le.mp hz
  change |(w+(t:ℂ)*(z-w)).im| ≤ Real.pi/2
  rw [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,Complex.sub_im]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hz₁),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hw₁),
    mul_nonneg ht.1 (sub_nonneg.mpr hz₂),mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hw₂)]

#print axioms complexChart_real
#print axioms complexChart_derivative
#print axioms complexChart_analytic
#print axioms complexChart_continuous
#print axioms complexChart_re
#print axioms complexChart_im
#print axioms strip_exp_re_nonnegative
#print axioms complexChart_derivative_ne_zero
#print axioms closedStrip_closed
#print axioms openStrip_open
#print axioms closedStrip_segment

end
end UnifiedTheory.Audit.KFCausalComplexClockChart
