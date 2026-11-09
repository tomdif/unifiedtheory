/- Uniform temporal Lipschitz control of the actual neutral-momentum
characteristics on every finite time window, along each admissible small
hbar sequence. The late-index threshold works for every test frequency. -/
import UnifiedTheory.Audit.KFCausalDisplacedNeutralDynamics
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalDisplacedNeutralDynamics
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (speedBound)
open UnifiedTheory.Audit.KFCausalNeutralWeightTime (speedBound_nonneg)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)

def speedConstant (ε a m g k s T : ℝ) (p : Configuration) (v : ℝ) : ℝ :=
  speedBound (energyWeight m g k 0) 1 v*(Real.exp (2*T)*initialBudget ε a m g k s p)

theorem speedConstant_nonneg (ε a m g k s T : ℝ) (p : Configuration) (v : ℝ) :
    0 ≤ speedConstant ε a m g k s T p v :=
  mul_nonneg (speedBound_nonneg _ 1 v (by norm_num))
    (mul_nonneg (Real.exp_pos _).le (initialBudget_positive ε a m g k s p).le)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
include hz

theorem rate_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ v t : ℝ, |t-s| ≤ T →
      ‖rate ε a (h n) hε ha (hne n) (hh n) m g k s p hm hg hk v t‖ ≤
        speedConstant ε a m g k s T p v := by
  have hsmall : ∀ᶠ n in atTop, |h n| ≤ 1 :=
    (hz.abs.eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))).mono (fun _ hn => hn.le)
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm.le hg.le hk.le h hne hh hz T,hsmall]
    with n henergy hsmall
  intro v t ht
  have hb := rate_energy_bound ε a (h n) hε ha (hne n) (hh n) m g k s p hm hg hk v 1 t hsmall
  exact hb.trans (mul_le_mul_of_nonneg_left (henergy t ht)
    (speedBound_nonneg (energyWeight m g k 0) 1 v (by norm_num)))

include hm hg hk in
theorem characteristic_window_lipschitz (T : ℝ) :
    ∀ᶠ n in atTop, ∀ v r t : ℝ, |r-s| ≤ T → |t-s| ≤ T →
      ‖characteristic ε a (h n) hε ha (hne n) (hh n) m g k s p v t-
        characteristic ε a (h n) hε ha (hne n) (hh n) m g k s p v r‖ ≤
          speedConstant ε a m g k s T p v*|t-r| := by
  filter_upwards [rate_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro v r t hr ht
  have hw (z : ℝ) : z ∈ Set.Icc (s-T) (s+T) ↔ |z-s| ≤ T := by
    rw [abs_le]
    constructor <;> intro hz' <;> constructor <;> linarith [hz'.1,hz'.2]
  have hb (z : ℝ) (hz' : z ∈ Set.Icc (s-T) (s+T)) :
      ‖rate ε a (h n) hε ha (hne n) (hh n) m g k s p hm hg hk v z‖ ≤
        speedConstant ε a m g k s T p v := hn v z ((hw z).mp hz')
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Set.Icc (s-T) (s+T)) =>
      (characteristic_derivative ε a (h n) hε ha (hne n) (hh n) m g k s p hm hg hk v z).hasDerivWithinAt)
    hb (convex_Icc (s-T) (s+T)) ((hw r).mpr hr) ((hw t).mpr ht)

#print axioms speedConstant_nonneg
#print axioms rate_window
#print axioms characteristic_window_lipschitz

end
end UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl
