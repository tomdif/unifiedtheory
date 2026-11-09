/- Actual finite spacetime force measures. Their interval slices are the
previously constructed forces, and the physical energy controls both total
mass and the time marginal on every measurable set. -/
import UnifiedTheory.Audit.KFCausalSpacetimeForcePair
import UnifiedTheory.Audit.KFCausalNeutralForceConsistency

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce
open UnifiedTheory.Audit.KFCausalNeutralForceConsistency (forceBudget)
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)

def forceWindow (r : ℝ) (hr : 0 < r) (b c : ℝ) : Pair :=
  fromCurve angleMeasure h (energyWeight m g k 0)
    (outputCurve ε a h hε ha hne hh m g k s p r)
    (outputCurve_continuous ε a h hε ha hne hh m g k s p r hr) b c

theorem forceWindow_mass (r : ℝ) (hr : 0 < r) (b c : ℝ) :
    (forceWindow ε a h hε ha hne hh m g k s p r hr b c).mass =
      (forceInterval ε a h hε ha hne hh m g k s p r hr b c).mass :=
  fromCurve_mass _ _ _ _ _ b c

theorem forceWindow_slice (r : ℝ) (hr : 0 < r) (b c u v : ℝ) (hu : b ≤ u) (hv : v ≤ c) :
    ((forceWindow ε a h hε ha hne hh m g k s p r hr b c).slice u v).positive =
      (forceInterval ε a h hε ha hne hh m g k s p r hr u v).positive ∧
    ((forceWindow ε a h hε ha hne hh m g k s p r hr b c).slice u v).negative =
      (forceInterval ε a h hε ha hne hh m g k s p r hr u v).negative :=
  fromCurve_slice _ _ _ _ _ b c u v hu hv

omit h hne hh in
theorem forceWindow_mass_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, ∀ hr : 0 < r, ∀ b c : ℝ, b ≤ c → |b-s| ≤ T → |c-s| ≤ T →
      (forceWindow ε a (h n) hε ha (hne n) (hh n) m g k s p r hr b c).mass ≤
        (c-b)*forceBudget ε a m g k s T p := by
  simpa only [forceWindow_mass,forceBudget] using
    forceInterval_mass_window ε a hε ha m g k s p hm hg hk h hne hh hz T

omit h hne hh in
theorem forceWindow_time_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, ∀ hr : 0 < r, ∀ b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
      ∀ A : Set ℝ, MeasurableSet A →
        (forceWindow ε a (h n) hε ha (hne n) (hh n) m g k s p r hr b c).positive (A ×ˢ univ)+
        (forceWindow ε a (h n) hε ha (hne n) (hh n) m g k s p r hr b c).negative (A ×ˢ univ) ≤
          ENNReal.ofReal (forceBudget ε a m g k s T p)*volume (A ∩ Icc b c) := by
  filter_upwards [KFCausalNeutralStructuredResponse.force_mass_window
    ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr b c hb hc A hA
  apply fromCurve_time_bound _ _ _ _ _ b c _ _ A hA
  intro t ht
  apply hn r hr t
  rcases abs_le.mp hb with ⟨hbl,hbu⟩
  rcases abs_le.mp hc with ⟨hcl,hcu⟩
  exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩

#print axioms forceWindow_mass
#print axioms forceWindow_slice
#print axioms forceWindow_mass_window
#print axioms forceWindow_time_window
end
end UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
