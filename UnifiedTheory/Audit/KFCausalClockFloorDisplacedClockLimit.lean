/- Along a proved uniformly convergent clock subsequence, the integrated
classical-coefficient quantum rates converge to increments of the limit.
No uniqueness or identification with a classical evolved measure is claimed. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLimit
noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockCompactness

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g κ s T : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
  (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
include hm hg hκ hz

theorem clockResidual_tendsto (r t : ℝ) (hr : |r-s| ≤ T) (ht : |t-s| ≤ T) :
    Tendsto (fun n => clockResidual ε a (h n) hε ha (hh n) (hb n) m g κ s p r t) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨N,hN⟩ := clockResidual_uniform_small ε a hε ha m g κ s p hm hg hκ h hh hb hz T η hη
  filter_upwards [eventually_ge_atTop N] with n hn
  simpa only [Real.dist_eq,sub_zero] using hN n hn r t hr ht

theorem clock_subsequence_balance :
    ∃ f : Window s T →ᵇ ℝ, (∀ t, f t ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ r t, dist (f r) (f t) ≤ speedConstant ε a m g κ s T p*dist r t) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n => windowPath ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s T p) f atTop ∧
        ∀ r t : Window s T, Tendsto (fun n => ∫ u in (r:ℝ)..(t:ℝ),
          comparisonRate ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p u) atTop (𝓝 (f t-f r)) := by
  obtain ⟨f,hf,hlip,φ,hφ,hlim⟩ := clock_paths_subsequence ε a hε ha m g κ s T p hm hg hκ h hh hb hz
  refine ⟨f,hf,hlip,φ,hφ,hlim,?_⟩
  intro r t
  have hw (u : Window s T) : |(u:ℝ)-s| ≤ T :=
    abs_le.mpr ⟨by linarith [u.property.1],by linarith [u.property.2]⟩
  have he := (clockResidual_tendsto ε a hε ha m g κ s T p hm hg hκ h hh hb hz r t (hw r) (hw t)).comp hφ.tendsto_atTop
  have ht := ((hlim.tendsto_at t).sub (hlim.tendsto_at r)).sub he
  have hid (n : ℕ) : windowPath ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s T p t-
      windowPath ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s T p r-
      clockResidual ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p r t =
        ∫ u in (r:ℝ)..(t:ℝ), comparisonRate ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p u := by
    simp only [windowPath,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,clockResidual]
    ring
  simpa only [Function.comp_def,hid,sub_zero] using ht

#print axioms clockResidual_tendsto
#print axioms clock_subsequence_balance

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLimit
