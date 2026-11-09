/- Uniform finite-window clock-rate error and equicontinuity for actual
quantum evolutions of boosted initial states. The comparison rate still
uses quantum outputs, not an assumed classical evolved law. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedOutputContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (trajectory)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)

def rateConstant (ε a m g κ s T : ℝ) (p : Configuration) : ℝ :=
  (20/ε^2)*Real.exp (2*T)*initialBudget ε a m g κ s p

def speedConstant (ε a m g κ s T : ℝ) (p : Configuration) : ℝ :=
  (1/ε+20/ε^2)*Real.exp (2*T)*initialBudget ε a m g κ s p

theorem rateConstant_nonnegative (ε a m g κ s T : ℝ) (p : Configuration) :
    0 ≤ rateConstant ε a m g κ s T p := by
  have := (initialBudget_positive ε a m g κ s p).le
  unfold rateConstant
  positivity

theorem speedConstant_nonnegative (ε a m g κ s T : ℝ) (hε : 0 < ε) (p : Configuration) :
    0 ≤ speedConstant ε a m g κ s T p := by
  have := (initialBudget_positive ε a m g κ s p).le
  unfold speedConstant
  positivity

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g κ s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
  (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
include hm hg hκ hz

theorem rate_error_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t-s| ≤ T →
      |clockRate ε a (h n) hε ha (hh n) (hb n) m g κ s p t-
        comparisonRate ε a (h n) hε ha (hh n) (hb n) m g κ s p t| ≤ rateConstant ε a m g κ s T p*|h n| := by
  filter_upwards [trajectory_energy_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T] with n hn
  intro t ht
  apply (rate_error_bound ε a (h n) hε ha (hh n) (hb n) m g κ s p t).trans
  calc
    _ ≤ (20*|h n|/ε^2)*(Real.exp (2*T)*initialBudget ε a m g κ s p) :=
      mul_le_mul_of_nonneg_left (hn t ht) (by positivity)
    _ = _ := by unfold rateConstant; ring

theorem rate_error_uniform_small (T η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T →
      |clockRate ε a (h n) hε ha (hh n) (hb n) m g κ s p t-
        comparisonRate ε a (h n) hε ha (hh n) (hb n) m g κ s p t| < η := by
  have hz' : Tendsto (fun n => rateConstant ε a m g κ s T p*|h n|) atTop (𝓝 0) := by
    simpa only [abs_zero,mul_zero] using hz.abs.const_mul (rateConstant ε a m g κ s T p)
  have he := rate_error_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he.and (hz'.eventually (gt_mem_nhds hη)))
  exact ⟨N,fun n hn t ht => ((hN n hn).1 t ht).trans_lt (hN n hn).2⟩

theorem clockRate_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t-s| ≤ T →
      |clockRate ε a (h n) hε ha (hh n) (hb n) m g κ s p t| ≤ speedConstant ε a m g κ s T p := by
  have hsmall : ∀ᶠ n in atTop, |h n| ≤ 1 :=
    (hz.abs.eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))).mono (fun _ hn => hn.le)
  filter_upwards [trajectory_energy_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T,hsmall] with n hn hn1
  intro t ht
  have hM : 0 ≤ Real.exp (2*T)*initialBudget ε a m g κ s p :=
    mul_nonneg (Real.exp_pos _).le (initialBudget_positive ε a m g κ s p).le
  apply (clockRate_bound ε a (h n) hε ha (hh n) (hb n) m g κ s p t).trans
  calc
    _ ≤ (1/ε+20*|h n|/ε^2)*(Real.exp (2*T)*initialBudget ε a m g κ s p) :=
      mul_le_mul_of_nonneg_left (hn t ht) (by positivity)
    _ ≤ (1/ε+20/ε^2)*(Real.exp (2*T)*initialBudget ε a m g κ s p) := by
      apply mul_le_mul_of_nonneg_right _ hM
      gcongr
      linarith only [hn1]
    _ = _ := by unfold speedConstant; ring

theorem clockExpectation_window_lipschitz (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r t : ℝ, |r-s| ≤ T → |t-s| ≤ T →
      |clockExpectation ε a (h n) hε ha (hh n) (hb n) m g κ s p t-
        clockExpectation ε a (h n) hε ha (hh n) (hb n) m g κ s p r| ≤
          speedConstant ε a m g κ s T p*|t-r| := by
  filter_upwards [clockRate_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T] with n hn
  intro r t hr ht
  have hw (u : ℝ) : u ∈ Set.Icc (s-T) (s+T) ↔ |u-s| ≤ T := by
    rw [abs_le]
    constructor <;> intro hu <;> constructor <;> linarith [hu.1,hu.2]
  have hb' (u : ℝ) (hu : u ∈ Set.Icc (s-T) (s+T)) :
      ‖clockRate ε a (h n) hε ha (hh n) (hb n) m g κ s p u‖ ≤ speedConstant ε a m g κ s T p := by
    rw [Real.norm_eq_abs]
    exact hn u ((hw u).mp hu)
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ Set.Icc (s-T) (s+T)) =>
      (clockExpectation_derivative ε a (h n) hε ha (hh n) (hb n) m g κ s p u).hasDerivWithinAt)
    hb' (convex_Icc (s-T) (s+T)) ((hw r).mpr hr) ((hw t).mpr ht)

#print axioms rateConstant_nonnegative
#print axioms speedConstant_nonnegative
#print axioms rate_error_window
#print axioms rate_error_uniform_small
#print axioms clockRate_window
#print axioms clockExpectation_window_lipschitz

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow
