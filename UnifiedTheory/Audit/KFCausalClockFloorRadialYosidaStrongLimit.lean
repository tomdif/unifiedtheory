/- Strong convergence of the actual bounded radial cutoffs on the full
maximal radial domain. The dominating L2 function is the actual operator
output; no additional radial moment or convergence premise is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaDomain
import UnifiedTheory.Audit.KFCausalDominatedRepresentedL2Limit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStrongLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol
open KFCausalClockFloorRadialYosidaDomain (operator symbol_tendsto)
open KFCausalUnitaryRealMultiplier (realPullback_graph)

theorem graph_tendsto (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (operator ε hε h).graph) :
    Tendsto (fun n : ℕ => action ε hε h ((n:ℝ)+1) (by positivity) f)
      atTop (𝓝 g) := by
  have hm : Measurable (radial ε h) :=
    (((KFCausalClockFloorRotatedAntiSymbol.chargedWeight_continuous ε hε h 0).add
      (KFCausalClockFloorRotatedAntiSymbol.chargedWeight_continuous ε hε h 1)).div_const 2).measurable
  have hg := (realPullback_graph chargeCoordinates (radial ε h) hm f g).mp hfg
  have ht := KFCausalDominatedRepresentedL2Limit.represented_tendsto
    (fun n : ℕ => chargeCoordinates (action ε hε h ((n:ℝ)+1) (by positivity) f))
    (fun n x => (symbol ε h ((n:ℝ)+1) x:ℂ)*(chargeCoordinates f) x)
    (chargeCoordinates g) (Lp.memLp (chargeCoordinates g))
    (fun x => ‖(chargeCoordinates g) x‖) (Lp.memLp (chargeCoordinates g)).norm
    (Eventually.of_forall (fun n => action_coe ε hε h ((n:ℝ)+1) (by positivity) f))
    (Eventually.of_forall (fun n => by
      filter_upwards [hg] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hx,norm_mul,norm_mul,
        Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (symbol_nonnegative ε hε h _ (by positivity) x),
        abs_of_nonneg (radial_nonnegative ε hε h x)]
      exact mul_le_mul_of_nonneg_right
        (symbol_le_radial ε hε h _ (by positivity) x) (norm_nonneg _)))
    (hg.mono (fun x hx => by
      rw [hx]
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (symbol_tendsto ε hε h x)).mul_const _))
  have ht' : Tendsto
      (fun n : ℕ => chargeCoordinates (action ε hε h ((n:ℝ)+1) (by positivity) f))
      atTop (𝓝 (chargeCoordinates g)) := by
    simpa only [Lp.toLp_coeFn] using ht
  simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using
    (chargeCoordinates.symm.continuous.tendsto (chargeCoordinates g)).comp ht'

theorem domain_tendsto (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : (operator ε hε h).domain) :
    Tendsto (fun n : ℕ => action ε hε h ((n:ℝ)+1) (by positivity) (f:Hilbert))
      atTop (𝓝 (operator ε hε h f)) :=
  graph_tendsto ε hε h f _ ((operator ε hε h).mem_graph f)

#print axioms graph_tendsto
#print axioms domain_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStrongLimit
