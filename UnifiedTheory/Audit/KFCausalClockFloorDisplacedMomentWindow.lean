/- Higher clock moments of actual evolved boosts increase by at most a
vanishing semiclassical error, uniformly on each forward finite window. -/
import UnifiedTheory.Audit.KFCausalClockFloorPowerEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentWindow
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution evolution_initial)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw
open UnifiedTheory.Audit.KFCausalClockFloorPowerEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityScalar (errorConstant errorConstant_nonnegative)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (k : ℕ)
local notation "w" => referenceState ε a h hε ha hh hb m g κ s p
local notation "ψ₀" => boostedState ε a h hε ha hh (positionFrequency (Prod.fst p) (Prod.snd p))
local notation "U" => evolution ε hε h hh hb m g κ

def clockMoment (t : ℝ) : ℝ := moment ε hε k (U s t ψ₀)

theorem clockMoment_initial : clockMoment ε a h hε ha hh hb m g κ s p k s = initialMoment ε a k := by
  change moment ε hε k (((U s s).toContinuousLinearEquiv : _ →L[ℂ] _) ψ₀) = _
  rw [evolution_initial]
  exact boosted_initial_moment ε a h hε ha hh _ k

theorem clockMoment_derivative (t : ℝ) :
    HasDerivAt (clockMoment ε a h hε ha hh hb m g κ s p k)
      (powerRate ε hε h hh hb m g κ k s t w) t := by
  simpa only [referenceState_embedding] using powerExpectation_derivative ε hε h hh hb m g κ k s t w

theorem clockMoment_integral (r t : ℝ) :
    (∫ u in r..t, powerRate ε hε h hh hb m g κ k s u w) =
      clockMoment ε a h hε ha hh hb m g κ s p k t-clockMoment ε a h hε ha hh hb m g κ s p k r := by
  simpa only [referenceState_embedding] using powerExpectation_integral ε hε h hh hb m g κ k s r t w

omit h hε ha hh hb in
def growthConstant (T : ℝ) : ℝ := errorConstant ε k*Real.exp (2*T)*initialBudget ε a m g κ s p

omit h hε ha hh hb in
theorem growthConstant_nonnegative (T : ℝ) : 0 ≤ growthConstant ε a m g κ s p k T := by
  have := errorConstant_nonnegative ε k
  have := (initialBudget_positive ε a m g κ s p).le
  unfold growthConstant
  positivity

omit h hh hb in
theorem powerRate_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t-s| ≤ T →
      powerRate ε hε (h n) (hh n) (hb n) m g κ k s t
        (referenceState ε a (h n) hε ha (hh n) (hb n) m g κ s p) ≤ growthConstant ε a m g κ s p k T*|h n| := by
  filter_upwards [trajectory_energy_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T] with n hn
  intro t ht
  apply (powerRate_upper ε hε (h n) (hh n) (hb n) m g κ k s t _).trans
  calc
    _ ≤ (errorConstant ε k*|h n|)*(Real.exp (2*T)*initialBudget ε a m g κ s p) :=
      mul_le_mul_of_nonneg_left (hn t ht) (mul_nonneg (errorConstant_nonnegative ε k) (abs_nonneg _))
    _ = _ := by unfold growthConstant; ring

omit h hh hb in
theorem clockMoment_window_bound (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) :
    ∀ᶠ n in atTop, ∀ t ∈ Set.Icc s (s+T),
      clockMoment ε a (h n) hε ha (hh n) (hb n) m g κ s p k t ≤
        initialMoment ε a k+growthConstant ε a m g κ s p k T*|h n| *(t-s) := by
  filter_upwards [powerRate_window ε a hε ha m g κ s p k hm hg hκ h hh hb hz T] with n hn
  intro t ht
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := s) (b := t)
    (f := fun u => powerRate ε hε (h n) (hh n) (hb n) m g κ k s u
      (referenceState ε a (h n) hε ha (hh n) (hb n) m g κ s p))
    (g := fun _ => growthConstant ε a m g κ s p k T*|h n|) ht.1
    ((powerRate_continuous ε hε (h n) (hh n) (hb n) m g κ k s _).intervalIntegrable s t)
    (continuous_const.intervalIntegrable s t) (fun u hu => hn u (by
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
      linarith [hu.2,ht.2]))
  rw [clockMoment_integral ε a (h n) hε ha (hh n) (hb n) m g κ s p k s t,
    clockMoment_initial,intervalIntegral.integral_const,smul_eq_mul] at hi
  nlinarith only [hi]

omit h hh hb in
theorem clockMoment_uniform_small (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      clockMoment ε a (h n) hε ha (hh n) (hb n) m g κ s p k t < initialMoment ε a k+η := by
  have ht : Tendsto (fun n => growthConstant ε a m g κ s p k T*|h n| *|T|) atTop (𝓝 0) := by
    simpa only [abs_zero,mul_zero,zero_mul] using (hz.abs.const_mul (growthConstant ε a m g κ s p k T)).mul_const |T|
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((clockMoment_window_bound ε a hε ha m g κ s p k hm hg hκ h hh hb hz T).and
    (ht.eventually (gt_mem_nhds hη)))
  refine ⟨N,fun n hn t ht => ?_⟩
  have hbound := (hN n hn).1 t ht
  have hc : 0 ≤ growthConstant ε a m g κ s p k T*|h n| :=
    mul_nonneg (growthConstant_nonnegative ε a m g κ s p k T) (abs_nonneg _)
  have hlen : t-s ≤ |T| := by linarith [ht.2,le_abs_self T]
  have hlast := mul_le_mul_of_nonneg_left hlen hc
  linarith [(hN n hn).2]

#print axioms clockMoment_initial
#print axioms clockMoment_derivative
#print axioms clockMoment_integral
#print axioms growthConstant_nonnegative
#print axioms powerRate_window
#print axioms clockMoment_window_bound
#print axioms clockMoment_uniform_small

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentWindow
