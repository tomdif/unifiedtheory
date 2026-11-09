/- Explicit coercivity of the degree-two semicircle moment matrix.
This uniform comparison is used for actual polynomial angular integrals,
including arbitrary real and imaginary coefficient parts. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalQuadraticSemicircleGram
noncomputable section

def half (a b c : ℝ) : ℝ :=
  Real.pi*a^2+4*a*b+Real.pi/2*b^2+Real.pi*a*c+8/3*b*c+3*Real.pi/8*c^2

def full (a b c : ℝ) : ℝ :=
  2*Real.pi*a^2+Real.pi*b^2+2*Real.pi*a*c+3*Real.pi/4*c^2

private theorem rational_coercive (a b c : ℝ) :
    (a^2+b^2+c^2)/200 ≤
      (157/50)*a^2+4*a*b+(157/100)*b^2+(157/50)*a*c+8/3*b*c+(471/400)*c^2 := by
  have he :
      (157/50)*a^2+4*a*b+(157/100)*b^2+(157/50)*a*c+8/3*b*c+(471/400)*c^2-
        (a^2+b^2+c^2)/200 =
      (627/200)*(a+(400/627)*b+(314/627)*c)^2+
        (36251/125400)*(b+(41600/36251)*c)^2+(80623/14500400)*c^2 := by ring
  have hn : 0 ≤ (627/200)*(a+(400/627)*b+(314/627)*c)^2+
      (36251/125400)*(b+(41600/36251)*c)^2+(80623/14500400)*c^2 := by positivity
  linarith

theorem half_coercive (a b c : ℝ) : (a^2+b^2+c^2)/200 ≤ half a b c := by
  have hp : 0 ≤ Real.pi-(157/50:ℝ) := by linarith [Real.pi_gt_d2]
  have hn : 0 ≤ (Real.pi-(157/50:ℝ))*((a+c/2)^2+b^2/2+c^2/8) := by positivity
  have hr := rational_coercive a b c
  unfold half
  nlinarith

theorem full_bound (a b c : ℝ) : full a b c ≤ 12*(a^2+b^2+c^2) := by
  have hp := mul_nonneg Real.pi_pos.le (sq_nonneg (a-c))
  have hq : full a b c ≤ 3*Real.pi*(a^2+b^2+c^2) := by
    unfold full
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg b),
      mul_nonneg Real.pi_pos.le (sq_nonneg c)]
  have hπ : 3*Real.pi ≤ (12:ℝ) := by linarith [Real.pi_lt_four]
  exact hq.trans (mul_le_mul_of_nonneg_right hπ (by positivity))

theorem full_le_2400_half (a b c : ℝ) : full a b c ≤ 2400*half a b c := by
  have hl := half_coercive a b c
  have hu := full_bound a b c
  linarith

#print axioms half_coercive
#print axioms full_bound
#print axioms full_le_2400_half
end
end UnifiedTheory.Audit.KFCausalQuadraticSemicircleGram
