/- Joint continuity, reversibility and derivatives at every time for the
already identified physical shear flow in charge coordinates. -/
import UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalChargeShearSmoothFlow
noncomputable section
open UnifiedTheory.Audit.KFCausalChargeShearJointFlow
open UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity (velocity flow_derivative_zero)
open UnifiedTheory.Audit.KFCausalChargeShearPairedFlow (pairFlow_compose)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (split)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale)

theorem flow_compose (t u : ℝ) (x : Space) : flow u (flow t x) = flow (t+u) x := by
  simp only [flow,MeasurableEquiv.apply_symm_apply,pairFlow_compose]

theorem flow_reverse (t : ℝ) (x : Space) : flow (-t) (flow t x) = x := by
  rw [flow_compose,add_neg_cancel,flow_zero]

theorem flow_continuous : Continuous (fun p : ℝ × Space => flow p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × Space => WithLp.ofLp (flow p.1 p.2)) := by
    apply continuous_pi
    intro i
    rcases i with i | i
    · change Continuous (fun p : ℝ × Space => Real.exp (-1*p.1/2)*p.2 (.inl i))
      fun_prop
    · fin_cases i
      · change Continuous (fun p : ℝ × Space => p.2 (.inr 0))
        fun_prop
      · change Continuous (fun p : ℝ × Space => Real.exp (p.1/2)*p.2 (.inr 1))
        fun_prop
      · change Continuous (fun p : ℝ × Space => Real.exp (p.1/2)*p.2 (.inr 2))
        fun_prop
      · change Continuous (fun p : ℝ × Space => p.2 (.inr 3)+4*scale*(Real.exp (p.1/2)-1)*p.2 (.inr 2))
        fun_prop
  exact (PiLp.continuous_toLp 2 _).comp hc

theorem velocity_continuous : Continuous velocity := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  rcases i with i | i
  · change Continuous (fun x : Space => -x (.inl i)/2)
    fun_prop
  · fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> fun_prop

theorem flow_derivative (t : ℝ) (x : Space) :
    HasDerivAt (fun s => flow s x) (velocity (flow t x)) t := by
  have hs : HasDerivAt (fun u => flow u (flow t x)) (velocity (flow t x)) (t-t) := by
    simpa only [sub_self] using flow_derivative_zero (flow t x)
  have hd := hs.scomp (h := fun s : ℝ => s-t) t ((hasDerivAt_id t).sub_const t)
  have he (s : ℝ) : flow (s-t) (flow t x) = flow s x := by
    rw [flow_compose]
    congr 1
    ring
  simpa only [Function.comp_def,he,one_smul] using hd

#print axioms flow_compose
#print axioms flow_reverse
#print axioms flow_continuous
#print axioms velocity_continuous
#print axioms flow_derivative
end
end UnifiedTheory.Audit.KFCausalChargeShearSmoothFlow
