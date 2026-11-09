/- The actual boosted quantum clock expectation satisfies its integrated
classical-coefficient equation with an error tending uniformly to zero on
finite time windows. The coefficient is paired with quantum outputs. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockIntegral
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedOutputContinuity (comparisonRate_continuous)

def clockResidual (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (r t : ℝ) : ℝ :=
  clockExpectation ε a h hε ha hh hb m g κ s p t-clockExpectation ε a h hε ha hh hb m g κ s p r-
    ∫ u in r..t, comparisonRate ε a h hε ha hh hb m g κ s p u

theorem clockResidual_eq_integral (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (r t : ℝ) :
    clockResidual ε a h hε ha hh hb m g κ s p r t =
      ∫ u in r..t, clockRate ε a h hε ha hh hb m g κ s p u-comparisonRate ε a h hε ha hh hb m g κ s p u := by
  rw [clockResidual,← clockExpectation_integral,
    intervalIntegral.integral_sub ((clockRate_continuous ε a h hε ha hh hb m g κ s p).intervalIntegrable r t)
      ((comparisonRate_continuous ε a h hε ha hh hb m g κ s p).intervalIntegrable r t)]

private theorem between_window (s T r t u : ℝ) (hr : |r-s| ≤ T) (ht : |t-s| ≤ T)
    (hu : u ∈ Set.uIoc r t) : |u-s| ≤ T := by
  obtain ⟨hrl,hru⟩ := abs_le.mp hr
  obtain ⟨htl,htu⟩ := abs_le.mp ht
  have hlow : s-T ≤ min r t := le_min (by linarith) (by linarith)
  have hhigh : max r t ≤ s+T := max_le (by linarith) (by linarith)
  exact abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g κ s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
  (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
include hm hg hκ hz

theorem clockResidual_window_bound (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r t : ℝ, |r-s| ≤ T → |t-s| ≤ T →
      |clockResidual ε a (h n) hε ha (hh n) (hb n) m g κ s p r t| ≤
        rateConstant ε a m g κ s T p*|h n| *|t-r| := by
  filter_upwards [rate_error_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T] with n hn
  intro r t hr ht
  rw [clockResidual_eq_integral]
  simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := r) (b := t) (C := rateConstant ε a m g κ s T p*|h n|)
    (f := fun u => clockRate ε a (h n) hε ha (hh n) (hb n) m g κ s p u-
      comparisonRate ε a (h n) hε ha (hh n) (hb n) m g κ s p u)
    (fun u hu => by
      rw [Real.norm_eq_abs]
      exact hn u (between_window s T r t u hr ht hu))

theorem clockResidual_uniform_small (T η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r t : ℝ, |r-s| ≤ T → |t-s| ≤ T →
      |clockResidual ε a (h n) hε ha (hh n) (hb n) m g κ s p r t| < η := by
  have hz' : Tendsto (fun n => rateConstant ε a m g κ s T p*|h n| *(2*|T|)) atTop (𝓝 0) := by
    simpa only [abs_zero,mul_zero,zero_mul] using
      (hz.abs.const_mul (rateConstant ε a m g κ s T p)).mul_const (2*|T|)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((clockResidual_window_bound ε a hε ha m g κ s p hm hg hκ h hh hb hz T).and
    (hz'.eventually (gt_mem_nhds hη)))
  refine ⟨N,?_⟩
  intro n hn r t hr ht
  have hd : |t-r| ≤ 2*|T| := by
    have hs := abs_sub_le t s r
    rw [abs_sub_comm s r] at hs
    linarith [le_abs_self T]
  exact ((hN n hn).1 r t hr ht).trans_lt
    ((mul_le_mul_of_nonneg_left hd (mul_nonneg (rateConstant_nonnegative ε a m g κ s T p) (abs_nonneg _))).trans_lt
      (hN n hn).2)

#print axioms clockResidual_eq_integral
#print axioms clockResidual_window_bound
#print axioms clockResidual_uniform_small

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockIntegral
