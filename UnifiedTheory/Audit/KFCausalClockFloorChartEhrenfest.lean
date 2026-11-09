/- Exact unbounded chart-clock transport along the actual full quantum
evolution. Only the initial state carries the stated left-moment condition.
Neither chart nor Hamiltonian operator-domain invariance is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorChartCharacteristicMoment
import UnifiedTheory.Audit.KFCausalClockFloorChartTransportLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorChartEhrenfest
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorChartMomentDomain (moment chart_integrable_after)
open UnifiedTheory.Audit.KFCausalClockFloorChartTransportLimit (drift drift_continuous characteristic_slope_balance)
open UnifiedTheory.Audit.KFCausalClockFloorChartCharacteristicMoment (characteristic_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorChartPhaseEhrenfest (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorChartPhaseContinuity (modulation_zero)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "U" => evolution ε hε h hne hh m g k
local notation "R" => drift ε hε h hne hh m g k

def chartMoment (s t : ℝ) (w : V) : ℝ := moment ε (U s t (J w))

theorem chart_integral_balance (s a b : ℝ) (ha : s ≤ a) (hb : s ≤ b) (w : V)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w))) :
    (∫ t in a..b, R s t w) = chartMoment ε hε h hne hh m g k s b w-
      chartMoment ε hε h hne hh m g k s a w := by
  have hlim := characteristic_slope_balance ε hε h hne hh m g k s a b w
  have hi := KFCausalClockFloorChartCharacteristicMoment.moment_difference_of_slope
    ε (U s b (J w)) (U s a (J w))
    (chart_integrable_after ε hε h hne hh m g k s b hb w hw)
    (chart_integrable_after ε hε h hne hh m g k s a ha w hw)
    ((KFCausalClockFloorAveragedEvolution.evolution_norm ε hε h hne hh m g k s b (J w)).trans
      (KFCausalClockFloorAveragedEvolution.evolution_norm ε hε h hne hh m g k s a (J w)).symm)
    _ hlim
  have hr := congrArg Complex.re hi
  have hcint : (∫ t in a..b, (R s t w:ℂ)) = ((∫ t in a..b, R s t w):ℝ) := by
    exact intervalIntegral.integral_ofReal
  exact (congrArg Complex.re hcint).symm.trans hr

theorem chart_derivative (s t : ℝ) (ht : s < t) (w : V)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w))) :
    HasDerivAt (fun z => chartMoment ε hε h hne hh m g k s z w) (R s t w) t := by
  have hc := drift_continuous ε hε h hne hh m g k s w
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable s t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).add_const
    (chartMoment ε hε h hne hh m g k s s w)
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with z hz
  rw [chart_integral_balance ε hε h hne hh m g k s s z le_rfl hz.le w hw,sub_add_cancel]

theorem chart_monotone (s : ℝ) (w : V)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w))) :
    MonotoneOn (fun t => chartMoment ε hε h hne hh m g k s t w) (Set.Ici s) := by
  intro a ha b hb hab
  have hi : 0 ≤ ∫ t in a..b, R s t w :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  rw [chart_integral_balance ε hε h hne hh m g k s a b ha hb w hw] at hi
  exact sub_nonneg.mp hi

#print axioms chart_integral_balance
#print axioms chart_derivative
#print axioms chart_monotone
end
end UnifiedTheory.Audit.KFCausalClockFloorChartEhrenfest
