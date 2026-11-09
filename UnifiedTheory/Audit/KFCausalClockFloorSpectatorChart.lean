/- The actual clock chart and symmetric-position/neutral shear on the
four spectator coordinates. This homeomorphism supplies compact support
control for the clock-dependent partial Fourier calculation. -/
import UnifiedTheory.Audit.KFCausalPairedModeCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso chart_continuous)

def flow (t : ℝ) (x : Block 4) : Block 4 := WithLp.toLp 2
  ![x 0,Real.exp (t/2)*x 1,Real.exp (t/2)*x 2,x 3+4*scale*(Real.exp (t/2)-1)*x 2]

theorem flow_clock (t : ℝ) (x : Block 4) : flow t x 0 = x 0 := rfl

theorem flow_zero (x : Block 4) : flow 0 x = x := by
  ext i
  fin_cases i <;> simp [flow]

theorem flow_compose (t u : ℝ) (x : Block 4) : flow u (flow t x) = flow (t+u) x := by
  ext i
  fin_cases i <;> simp [flow,add_div,Real.exp_add] <;> ring

theorem flow_reverse (t : ℝ) (x : Block 4) : flow (-t) (flow t x) = x := by
  rw [flow_compose,add_neg_cancel,flow_zero]

def changeClock (q : ℝ) (x : Block 4) : Block 4 := WithLp.toLp 2 ![q,x 1,x 2,x 3]

theorem changeClock_clock (q : ℝ) (x : Block 4) : changeClock q x 0 = q := rfl

theorem changeClock_self (x : Block 4) : changeClock (x 0) x = x := by
  ext i
  fin_cases i <;> rfl

theorem changeClock_compose (q r : ℝ) (x : Block 4) : changeClock q (changeClock r x) = changeClock q x := by
  ext i
  fin_cases i <;> rfl

theorem flow_changeClock (t q : ℝ) (x : Block 4) : flow t (changeClock q x) = changeClock q (flow t x) := by
  ext i
  fin_cases i <;> rfl

def forward (ε : ℝ) (x : Block 4) : Block 4 := changeClock (chart ε (x 0)) (flow (-x 0) x)

def backward (ε : ℝ) (hε : 0 < ε) (x : Block 4) : Block 4 :=
  changeClock ((chartIso ε hε).symm (x 0)) (flow ((chartIso ε hε).symm (x 0)) x)

theorem backward_forward (ε : ℝ) (hε : 0 < ε) (x : Block 4) : backward ε hε (forward ε x) = x := by
  have hc : (chartIso ε hε).symm (chart ε (x 0)) = x 0 := (chartIso ε hε).symm_apply_apply _
  simp only [backward,forward,changeClock_clock,hc,flow_changeClock,changeClock_compose]
  have hf : flow (x 0) (flow (-x 0) x) = x := by simpa only [neg_neg] using flow_reverse (-x 0) x
  rw [hf,changeClock_self]

theorem forward_backward (ε : ℝ) (hε : 0 < ε) (x : Block 4) : forward ε (backward ε hε x) = x := by
  have hc : chart ε ((chartIso ε hε).symm (x 0)) = x 0 := (chartIso ε hε).apply_symm_apply _
  simp only [forward,backward,changeClock_clock,hc,flow_changeClock,changeClock_compose,
    flow_reverse,changeClock_self]

theorem forward_continuous (ε : ℝ) : Continuous (forward ε) := by
  have hc := chart_continuous ε
  unfold forward changeClock flow
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun x : Block 4 => chart ε (x 0))
    fun_prop
  · change Continuous (fun x : Block 4 => Real.exp (-x 0/2)*x 1)
    fun_prop
  · change Continuous (fun x : Block 4 => Real.exp (-x 0/2)*x 2)
    fun_prop
  · change Continuous (fun x : Block 4 => x 3+4*scale*(Real.exp (-x 0/2)-1)*x 2)
    fun_prop

theorem backward_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (backward ε hε) := by
  have hc : Continuous ((chartIso ε hε).symm : ℝ → ℝ) := (chartIso ε hε).symm.toHomeomorph.continuous
  unfold backward changeClock flow
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun x : Block 4 => (chartIso ε hε).symm (x 0))
    fun_prop
  · change Continuous (fun x : Block 4 => Real.exp ((chartIso ε hε).symm (x 0)/2)*x 1)
    fun_prop
  · change Continuous (fun x : Block 4 => Real.exp ((chartIso ε hε).symm (x 0)/2)*x 2)
    fun_prop
  · change Continuous (fun x : Block 4 => x 3+4*scale*(Real.exp ((chartIso ε hε).symm (x 0)/2)-1)*x 2)
    fun_prop

def homeomorph (ε : ℝ) (hε : 0 < ε) : Block 4 ≃ₜ Block 4 where
  toFun := forward ε
  invFun := backward ε hε
  left_inv := backward_forward ε hε
  right_inv := forward_backward ε hε
  continuous_toFun := forward_continuous ε
  continuous_invFun := backward_continuous ε hε

theorem backward_compact (ε : ℝ) (hε : 0 < ε) (b : Block 4 → ℂ) (hb : HasCompactSupport b) :
    HasCompactSupport (b ∘ backward ε hε) := hb.comp_homeomorph (homeomorph ε hε).symm

#print axioms flow_clock
#print axioms flow_zero
#print axioms flow_compose
#print axioms flow_reverse
#print axioms changeClock_clock
#print axioms changeClock_self
#print axioms changeClock_compose
#print axioms flow_changeClock
#print axioms backward_forward
#print axioms forward_backward
#print axioms forward_continuous
#print axioms backward_continuous
#print axioms backward_compact

end
end UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart
