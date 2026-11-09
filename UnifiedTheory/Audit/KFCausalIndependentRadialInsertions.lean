/- Radial quadratic and neutral linear coefficients share the real
Gaussian radius of the bare independent-width packet. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialBareMultiplier
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentInput
import UnifiedTheory.Audit.KFCausalIndependentRadialShiftedField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialInsertions
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexShearPerturbation (Space)
open KFCausalIndependentRadialHolomorphicQuotient (baselineVector)
open KFCausalIndependentRadialMomentInput (left right neutral)
open KFCausalIndependentRadialBareMultiplier (vector_norm_bound)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockFloorCoherentStrip (clockPhase)

def radialCap (A : ℝ) : ℝ := 2*(20/17:ℝ)^2/A
def neutralCap (α : ℝ) : ℝ := (20/17:ℝ)/Real.sqrt (α/32)

theorem radialCap_nonnegative (A : ℝ) (hA : 0 ≤ A) : 0 ≤ radialCap A := by
  unfold radialCap
  positivity

theorem neutralCap_nonnegative (α : ℝ) : 0 ≤ neutralCap α := by
  unfold neutralCap
  positivity

private theorem pair_bound (A R : ℝ) (hA : 0 < A) (Y : Space)
    (hy : ‖Y‖ ≤ (20/17:ℝ)*R) (i j : Fin 5) :
    ‖(Y i^2+Y j^2)/(A:ℂ)‖ ≤ radialCap A*R^2 := by
  have hi := (PiLp.norm_apply_le Y i).trans hy
  have hj := (PiLp.norm_apply_le Y j).trans hy
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA]
  calc
    _ ≤ (‖Y i‖^2+‖Y j‖^2)/A := by
      apply div_le_div_of_nonneg_right _ hA.le
      calc
        ‖Y i^2+Y j^2‖ ≤ ‖(Y i:ℂ)^2‖+‖(Y j:ℂ)^2‖ := norm_add_le _ _
        _ = ‖Y i‖^2+‖Y j‖^2 := by rw [norm_pow,norm_pow]
    _ ≤ (((20/17:ℝ)*R)^2+((20/17:ℝ)*R)^2)/A := by gcongr
    _ = _ := by unfold radialCap; ring

theorem left_bound (ε h α wL wR c : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (hα : 0 < α) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖left α wL (baselineVector ε α wL wR c q x)‖ ≤
      radialCap (α/wL)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖^2 :=
  pair_bound (α/wL) _ (div_pos hα (zero_lt_one.trans_le hL)) _
    (vector_norm_bound ε h α wL wR c hε hb hα hR q hq x) 0 2

theorem right_bound (ε h α wL wR c : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (hα : 0 < α) (hR : 1 ≤ wR)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖right α wR (baselineVector ε α wL wR c q x)‖ ≤
      radialCap (α*wR)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖^2 :=
  pair_bound (α*wR) _ (mul_pos hα (zero_lt_one.trans_le hR)) _
    (vector_norm_bound ε h α wL wR c hε hb hα hR q hq x) 1 3

theorem neutral_bound (ε h α wL wR c : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (hα : 0 < α) (hR : 1 ≤ wR)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖neutral α (baselineVector ε α wL wR c q x)‖ ≤
      neutralCap α*‖baselineVector ε α wL wR c (q.re:ℂ) x‖ := by
  have hn := (PiLp.norm_apply_le (baselineVector ε α wL wR c q x) 4).trans
    (vector_norm_bound ε h α wL wR c hε hb hα hR q hq x)
  rw [neutral,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ ((20/17:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖)/Real.sqrt (α/32) :=
      div_le_div_of_nonneg_right hn (Real.sqrt_nonneg _)
    _ = _ := by unfold neutralCap; ring

theorem phase_bound (ε h p : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖clockPhase p (complexInverse ε q)‖ ≤ Real.exp (|p| *Real.pi/3) := by
  apply KFCausalClockFloorCoherentStrip.clockPhase_bound
  apply KFCausalClockInverseStripBounds.inverse_im_third_strip ε hε
  have hp := mul_lt_mul_of_pos_right Real.pi_gt_three hε
  linarith

#print axioms radialCap_nonnegative
#print axioms neutralCap_nonnegative
#print axioms left_bound
#print axioms right_bound
#print axioms neutral_bound
#print axioms phase_bound
end
end UnifiedTheory.Audit.KFCausalIndependentRadialInsertions
