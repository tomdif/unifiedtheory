/- Scalar coefficients of the physical canonical/longitudinal commutator.
The remainder bound is uniform at fixed positive clock floor. -/
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorMomentumCoefficients
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock mobility)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response response_bounds clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative (rate)

def remainderRate (ε s : ℝ) : ℝ := mobility ε s*response ε s*(1-response ε s)/2

theorem mobility_bounds (ε s : ℝ) (hε : 0 < ε) : 0 < mobility ε s ∧ mobility ε s ≤ 1/ε := by
  refine ⟨inv_pos.mpr (clock_positive ε s hε.le),?_⟩
  simpa only [mobility,one_div] using
    inv_anti₀ hε (KFCausalClockFloorFlow.clock_above_floor ε s).le

theorem response_derivative (ε s : ℝ) (hε : 0 < ε) :
    HasDerivAt (response ε) (response ε s*(1-response ε s)) s := by
  have hc := (clock_positive ε s hε.le).ne'
  have hd := (Real.hasDerivAt_exp s).div ((Real.hasDerivAt_exp s).add_const ε) hc
  convert hd using 1
  unfold response clock
  field_simp

theorem mobility_derivative (ε s : ℝ) (hε : 0 < ε) :
    HasDerivAt (mobility ε) (-response ε s*mobility ε s) s := by
  have hc := (clock_positive ε s hε.le).ne'
  have hd := ((Real.hasDerivAt_exp s).add_const ε).inv hc
  convert hd using 1
  unfold response mobility clock
  field_simp

theorem rate_factor (ε s : ℝ) (hε : 0 < ε) : rate ε s = mobility ε s*(1-response ε s/2) := by
  have hc : Real.exp s+ε ≠ 0 := by positivity
  unfold rate mobility response clock
  field_simp [hc]

theorem rate_derivative (ε s : ℝ) (hε : 0 < ε) :
    HasDerivAt (rate ε) (-response ε s*rate ε s-remainderRate ε s) s := by
  have hd := (mobility_derivative ε s hε).mul
    ((response_derivative ε s hε).div_const 2 |>.const_sub 1)
  have he : rate ε = fun s => mobility ε s*(1-response ε s/2) := funext (fun s => rate_factor ε s hε)
  rw [he]
  convert hd using 1
  unfold remainderRate
  ring

theorem remainder_bounds (ε s : ℝ) (hε : 0 < ε) :
    0 ≤ remainderRate ε s ∧ remainderRate ε s ≤ 1/(8*ε) := by
  obtain ⟨hb,hb'⟩ := mobility_bounds ε s hε
  obtain ⟨hr,hr'⟩ := response_bounds ε s hε
  have hcomp : 0 ≤ 1-response ε s := sub_nonneg.mpr hr'.le
  have hq : response ε s*(1-response ε s) ≤ 1/4 := by
    nlinarith [sq_nonneg (response ε s-1/2)]
  refine ⟨by unfold remainderRate; positivity,?_⟩
  have he := mul_le_mul_of_nonneg_left hq hb.le
  have hf := mul_le_mul_of_nonneg_right hb' (by norm_num : (0:ℝ) ≤ 1/4)
  unfold remainderRate
  calc
    _ ≤ (1/ε)*(1/4)/2 := by nlinarith only [he,hf]
    _ = _ := by ring

theorem mobility_contDiff (ε : ℝ) (hε : 0 < ε) (n : ℕ) : ContDiff ℝ n (mobility ε) := by
  unfold mobility clock
  fun_prop (disch := intro s; positivity)

theorem response_contDiff (ε : ℝ) (hε : 0 < ε) (n : ℕ) : ContDiff ℝ n (response ε) := by
  unfold response clock
  fun_prop (disch := intro s; positivity)

theorem rate_contDiff (ε : ℝ) (hε : 0 < ε) (n : ℕ) : ContDiff ℝ n (rate ε) := by
  have he : rate ε = fun s => mobility ε s*(1-response ε s/2) := funext (fun s => rate_factor ε s hε)
  rw [he]
  exact (mobility_contDiff ε hε n).mul (contDiff_const.sub ((response_contDiff ε hε n).div_const 2))

#print axioms mobility_bounds
#print axioms response_derivative
#print axioms mobility_derivative
#print axioms rate_factor
#print axioms rate_derivative
#print axioms remainder_bounds
#print axioms mobility_contDiff
#print axioms response_contDiff
#print axioms rate_contDiff

end
end UnifiedTheory.Audit.KFCausalClockFloorMomentumCoefficients
