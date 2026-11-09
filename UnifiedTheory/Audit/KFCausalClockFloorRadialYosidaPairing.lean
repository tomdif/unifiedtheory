/- The actual rational radial cutoff preserves the maximal radial root
graph. Its kinetic pairing dominates its physical norm squared, with
integrability supplied by actual L2 vectors rather than extra moments. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialMultiplierForm

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaPairing
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol
open KFCausalClockFloorGrowingRadialMultiplierForm (rootSymbol rootOperator)
open KFCausalClockFloorRotatedAntiSymbol (chargedWeight_continuous)
open KFCausalUnitaryRealMultiplier (realPullback_graph)
open KFCausalAveragedEnergyGraph (l2_norm_square)

private theorem root_measurable (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Measurable (rootSymbol ε h) :=
  (((chargedWeight_continuous ε hε h 0).add
    (chargedWeight_continuous ε hε h 1)).div_const 2).sqrt.measurable

private theorem real_inner (a : ℝ) (z : ℂ) :
    (inner ℂ z ((a:ℂ)*z)).re=a*‖z‖^2 := by
  change (inner ℂ z ((a:ℂ) • z)).re=_
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change ((a:ℂ)*(‖z‖:ℂ)^2).re=a*‖z‖^2
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

theorem root_graph (f y : Hilbert) (hy : (f,y) ∈ (rootOperator ε hε h).graph) :
    (action ε hε h N hN f,action ε hε h N hN y) ∈ (rootOperator ε hε h).graph := by
  have hr := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) f y).mp hy
  apply (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) _ _).mpr
  filter_upwards [hr,action_coe ε hε h N hN f,action_coe ε hε h N hN y] with x hx hf hy
  rw [hy,hf,hx]
  ring

theorem kinetic_pairing_lower (f y : Hilbert)
    (hy : (f,y) ∈ (rootOperator ε hε h).graph) :
    ‖action ε hε h N hN f‖^2 ≤
      (inner ℂ y (action ε hε h N hN y)).re := by
  have hr := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) f y).mp hy
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (chargeCoordinates (action ε hε h N hN f)))).mp (Lp.memLp _)
  have hj := L2.integrable_inner (𝕜 := ℂ) (chargeCoordinates y)
    (chargeCoordinates (action ε hε h N hN y))
  have he := integral_re hj
  change (∫ x, (inner ℂ ((chargeCoordinates y) x)
    ((chargeCoordinates (action ε hε h N hN y)) x)).re) = _ at he
  change _ = (∫ x, inner ℂ ((chargeCoordinates y) x)
    ((chargeCoordinates (action ε hε h N hN y)) x)).re at he
  rw [← chargeCoordinates.norm_map (action ε hε h N hN f),l2_norm_square,
    ← chargeCoordinates.inner_map_map y (action ε hε h N hN y),L2.inner_def,← he]
  apply integral_mono_ae hi hj.re
  filter_upwards [hr,action_coe ε hε h N hN f,action_coe ε hε h N hN y] with x hx hf hy'
  change ‖(chargeCoordinates (action ε hε h N hN f)) x‖^2 ≤
    (inner ℂ ((chargeCoordinates y) x)
      ((chargeCoordinates (action ε hε h N hN y)) x)).re
  rw [hf,hy',real_inner,hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [rootSymbol,Real.sq_sqrt (radial_nonnegative ε hε h x)]
  have hm : symbol ε h N x^2 ≤ symbol ε h N x*radial ε h x := by
    nlinarith [symbol_nonnegative ε hε h N hN x,symbol_le_radial ε hε h N hN x]
  exact (mul_le_mul_of_nonneg_right hm (sq_nonneg ‖(chargeCoordinates f) x‖)).trans_eq (by ring)

#print axioms root_graph
#print axioms kinetic_pairing_lower
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaPairing
