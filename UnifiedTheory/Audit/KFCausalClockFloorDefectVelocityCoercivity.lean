/- A uniform relative lower bound for actual quantum clock-defect
dissipation. It controls the classical dissipation without an additive
error that could accumulate over long times. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockVelocity
import UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectVelocityCoercivity
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorClockVelocity (velocity velocity_bounds velocity_positive)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response defect clock_positive response_add_defect)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)

def dissipation (ε h : ℝ) (x : Configuration) : ℝ := (2/h)*(physicalSymbol ε h x).im

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)

theorem dissipation_identity (x : Configuration) :
    dissipation ε h x = (ε/‖shiftedClock ε h x‖^2)*velocity ε h x := by
  have hd : (difference ε h x).im = -(shiftedClock ε h x).im := by simp only [difference,Complex.sub_im,Complex.ofReal_im,zero_sub]
  rw [velocity,hd,dissipation]
  change (2/h)*((ε:ℂ)/shiftedClock ε h x).im = _
  simp only [Complex.div_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,zero_div,zero_sub]
  rw [Complex.normSq_eq_norm_sq]
  ring

include hε hh in
theorem shiftedClock_norm_upper (x : Configuration) : ‖shiftedClock ε h x‖ ≤ 4*clock ε x.1 := by
  have hc := clock_positive ε x.1 hε.le
  have he : shiftedClock ε h x = (clock ε x.1:ℂ)-difference ε h x := by unfold difference; ring
  have hb : ‖shiftedClock ε h x‖ ≤ clock ε x.1+|h| := by
    rw [he]
    apply (norm_sub_le _ _).trans
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc,add_comm] using
      add_le_add_left (difference_bound ε hε h hh x) ‖(clock ε x.1:ℂ)‖
  have hπ := mul_le_mul_of_nonneg_right Real.pi_le_four hε.le
  have hC : ε ≤ clock ε x.1 := by unfold clock; linarith [Real.exp_pos x.1]
  nlinarith

include hε hh in
theorem shiftedClock_norm_positive (x : Configuration) : 0 < ‖shiftedClock ε h x‖ :=
  norm_pos_iff.mpr (complexClock_ne_zero ε hε _ (shift_mem ε hε h hh x))

include hε in
theorem classical_dissipation_identity (s : ℝ) :
    -(drift ε (defect ε s)) = (ε/(clock ε s)^2)*response ε s := by
  have hr : 1-defect ε s = response ε s := by linarith [response_add_defect ε s hε.le]
  rw [drift,neg_div,neg_neg,hr,defect]
  field_simp [hε.ne',(clock_positive ε s hε.le).ne']

include hε hne hh in
theorem dissipation_lower (x : Configuration) :
    (1/32)*(-(drift ε (defect ε x.1))) ≤ dissipation ε h x := by
  have hn := shiftedClock_norm_positive ε hε h hh x
  have hc := clock_positive ε x.1 hε.le
  have hn2 : ‖shiftedClock ε h x‖^2 ≤ 16*(clock ε x.1)^2 := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) (shiftedClock_norm_upper ε hε h hh x) 2
    simpa only [mul_pow,show (4:ℝ)^2=16 by norm_num] using hs
  have hf := div_le_div_of_nonneg_left hε.le (sq_pos_of_pos hn) hn2
  calc
    _ = (ε/(16*(clock ε x.1)^2))*((1/2)*response ε x.1) := by
      rw [classical_dissipation_identity ε hε]
      ring
    _ ≤ (ε/(16*(clock ε x.1)^2))*velocity ε h x :=
      mul_le_mul_of_nonneg_left (velocity_bounds ε hε h hne hh x).1 (by positivity)
    _ ≤ (ε/‖shiftedClock ε h x‖^2)*velocity ε h x :=
      mul_le_mul_of_nonneg_right hf (velocity_positive ε hε h hne hh x).le
    _ = _ := (dissipation_identity ε h x).symm

#print axioms dissipation_identity
#print axioms shiftedClock_norm_upper
#print axioms shiftedClock_norm_positive
#print axioms classical_dissipation_identity
#print axioms dissipation_lower
end
end UnifiedTheory.Audit.KFCausalClockFloorDefectVelocityCoercivity
