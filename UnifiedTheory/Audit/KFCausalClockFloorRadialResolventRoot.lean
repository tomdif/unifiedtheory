/- The radial resolvent regularizer maps every Hilbert vector into the domain
of the maximal radial square-root multiplier, with bounded square-root output
commuting with the regularizer on the square-root domain and converging
strongly to the radial square-root output. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRegularizer
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialMultiplierForm
import UnifiedTheory.Audit.KFCausalBoundedLpMultiplier

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRoot
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol (radial radial_nonnegative symbol
  symbol_nonnegative symbol_le)
open KFCausalClockFloorRadialResolventRegularizer (multiplier multiplier_nonnegative
  multiplier_le_one action action_coe sequence_tendsto)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootSymbol rootOperator)
open KFCausalClockFloorRotatedAntiSymbol (chargedWeight_continuous)
open KFCausalUnitaryRealMultiplier (realPullback_graph)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

def cutoffRootSymbol (x : Joint 2 4) : ℝ :=
  rootSymbol ε h x*multiplier ε h N x

theorem rootSymbol_nonnegative (x : Joint 2 4) : 0 ≤ rootSymbol ε h x :=
  Real.sqrt_nonneg _

include hε hN in
theorem cutoffRootSymbol_nonnegative (x : Joint 2 4) :
    0 ≤ cutoffRootSymbol ε h N x :=
  mul_nonneg (rootSymbol_nonnegative ε h x) (multiplier_nonnegative ε hε h N hN x)

include hε in
private theorem cutoffRootSymbol_sq (x : Joint 2 4) :
    cutoffRootSymbol ε h N x^2=symbol ε h N x*multiplier ε h N x := by
  unfold cutoffRootSymbol rootSymbol symbol multiplier
  rw [mul_pow,Real.sq_sqrt (radial_nonnegative ε hε h x)]
  ring

include hε hN in
theorem cutoffRootSymbol_le_sqrt (x : Joint 2 4) :
    cutoffRootSymbol ε h N x ≤ Real.sqrt N := by
  apply Real.le_sqrt_of_sq_le
  rw [cutoffRootSymbol_sq ε hε h N x]
  calc
    symbol ε h N x*multiplier ε h N x ≤ N*1 :=
      mul_le_mul (symbol_le ε hε h N hN x) (multiplier_le_one ε hε h N hN x)
        (multiplier_nonnegative ε hε h N hN x) hN.le
    _ = N := mul_one N

include hε hN in
theorem cutoffRootSymbol_le_root (x : Joint 2 4) :
    cutoffRootSymbol ε h N x ≤ rootSymbol ε h x :=
  mul_le_of_le_one_right (rootSymbol_nonnegative ε h x)
    (multiplier_le_one ε hε h N hN x)

include hε hN in
private theorem cutoffRootSymbol_continuous :
    Continuous (cutoffRootSymbol ε h N) := by
  have hr : Continuous (radial ε h) :=
    ((chargedWeight_continuous ε hε h 0).add
      (chargedWeight_continuous ε hε h 1)).div_const 2
  have hm : Continuous (multiplier ε h N) :=
    continuous_const.div (continuous_const.add hr)
      (fun x => (add_pos_of_pos_of_nonneg hN (radial_nonnegative ε hε h x)).ne')
  exact hr.sqrt.mul hm

include hε hN in
private theorem cutoffRootSymbol_measurable :
    Measurable (fun x : Joint 2 4 => (cutoffRootSymbol ε h N x:ℂ)) :=
  (Complex.continuous_ofReal.comp (cutoffRootSymbol_continuous ε hε h N hN)).measurable

include hε hN in
private theorem complex_cutoffRootSymbol_bound (x : Joint 2 4) :
    ‖(cutoffRootSymbol ε h N x:ℂ)‖ ≤ Real.sqrt N := by
  rw [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (cutoffRootSymbol_nonnegative ε hε h N hN x)]
  exact cutoffRootSymbol_le_sqrt ε hε h N hN x

def rootAction : Hilbert →L[ℂ] Hilbert :=
  (chargeCoordinates.symm : JointHilbert 2 4 →L[ℂ] Hilbert).comp
    ((KFCausalBoundedLpMultiplier.operator (fun x => (cutoffRootSymbol ε h N x:ℂ))
      (cutoffRootSymbol_measurable ε hε h N hN) (Real.sqrt N) (Real.sqrt_nonneg N)
      (complex_cutoffRootSymbol_bound ε hε h N hN)).comp
        (chargeCoordinates : Hilbert →L[ℂ] JointHilbert 2 4))

private theorem rootAction_coordinates (f : Hilbert) :
    chargeCoordinates (rootAction ε hε h N hN f)=
      KFCausalBoundedLpMultiplier.operator (fun x => (cutoffRootSymbol ε h N x:ℂ))
        (cutoffRootSymbol_measurable ε hε h N hN) (Real.sqrt N) (Real.sqrt_nonneg N)
        (complex_cutoffRootSymbol_bound ε hε h N hN) (chargeCoordinates f) :=
  chargeCoordinates.apply_symm_apply _

theorem rootAction_coe (f : Hilbert) :
    chargeCoordinates (rootAction ε hε h N hN f) =ᵐ[volume]
      fun x => (cutoffRootSymbol ε h N x:ℂ)*(chargeCoordinates f) x := by
  rw [rootAction_coordinates]
  exact KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ _

theorem rootAction_norm (f : Hilbert) :
    ‖rootAction ε hε h N hN f‖ ≤ Real.sqrt N*‖f‖ := by
  rw [← chargeCoordinates.norm_map (rootAction ε hε h N hN f),
    rootAction_coordinates,← chargeCoordinates.norm_map f]
  exact KFCausalBoundedLpMultiplier.operator_norm _ _ _ _ _ _

theorem root_graph (f : Hilbert) :
    (action ε hε h N hN f,rootAction ε hε h N hN f) ∈ (rootOperator ε hε h).graph := by
  apply (realPullback_graph chargeCoordinates (rootSymbol ε h) _ _ _).mpr
  filter_upwards [action_coe ε hε h N hN f,rootAction_coe ε hε h N hN f] with x hx hr
  rw [hr,hx,← mul_assoc,← Complex.ofReal_mul]
  rfl

theorem action_root_domain (f : Hilbert) :
    action ε hε h N hN f ∈ (rootOperator ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (root_graph ε hε h N hN f)

theorem rootAction_commute (f r : Hilbert)
    (hfr : (f,r) ∈ (rootOperator ε hε h).graph) :
    rootAction ε hε h N hN f=action ε hε h N hN r := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [rootAction_coe ε hε h N hN f,action_coe ε hε h N hN r,
    (realPullback_graph chargeCoordinates (rootSymbol ε h) _ f r).mp hfr]
      with x h1 h2 h3
  rw [h1,h2,h3]
  unfold cutoffRootSymbol
  push_cast
  ring

theorem rootAction_sequence_tendsto (f r : Hilbert)
    (hfr : (f,r) ∈ (rootOperator ε hε h).graph) :
    Tendsto (fun n : ℕ => rootAction ε hε h ((n:ℝ)+1) (by positivity) f) atTop (𝓝 r) := by
  have he : (fun n : ℕ => rootAction ε hε h ((n:ℝ)+1) (by positivity) f)=
      fun n : ℕ => action ε hε h ((n:ℝ)+1) (by positivity) r := by
    funext n
    exact rootAction_commute ε hε h ((n:ℝ)+1) (by positivity) f r hfr
  rw [he]
  exact sequence_tendsto ε hε h r

#print axioms rootSymbol_nonnegative
#print axioms cutoffRootSymbol_nonnegative
#print axioms cutoffRootSymbol_le_sqrt
#print axioms cutoffRootSymbol_le_root
#print axioms rootAction_coe
#print axioms rootAction_norm
#print axioms root_graph
#print axioms action_root_domain
#print axioms rootAction_commute
#print axioms rootAction_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRoot
