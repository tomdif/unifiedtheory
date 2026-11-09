/- Actual positive force measures integrated over time. Their mass is
controlled by the physical energy, and their Fourier response has the
previously derived all-time neutral probability balance. -/
import UnifiedTheory.Audit.KFCausalNeutralOutputTimeKernel
import UnifiedTheory.Audit.KFCausalNeutralForceBalanceLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralIntegratedForce
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds (weightedLinear)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalNeutralStructuredResponse (state force_mass_window)
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow (windowBudget)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)

def outputCurve (r t : ℝ) : EnergyOutputSpace :=
  KFCausalNeutralResolventResponse.responseOutput ε hε h hne hh m g k r t
    (evolvedState ε a h hε ha hne hh m g k s p t)

theorem outputCurve_continuous (r : ℝ) (hr : 0 < r) :
    Continuous (outputCurve ε a h hε ha hne hh m g k s p r) :=
  KFCausalNeutralResolventContinuity.responseOutput_continuous ε hε h hne hh m g k r hr _
    (KFCausalClockFloorAveragedEvolution.evolution_strong_continuous ε hε h hne hh m g k s _)

def forceInterval (r : ℝ) (hr : 0 < r) (b c : ℝ) : FluxPair :=
  KFCausalNeutralOutputTimeKernel.intervalPair angleMeasure h (energyWeight m g k 0)
    (outputCurve ε a h hε ha hne hh m g k s p r)
    (outputCurve_continuous ε a h hε ha hne hh m g k s p r hr) b c

theorem forceInterval_mass (r : ℝ) (hr : 0 < r) (b c : ℝ) :
    (forceInterval ε a h hε ha hne hh m g k s p r hr b c).mass =
      ∫ t in Set.Icc b c, (state ε a h hε ha hne hh m g k s p r t).force.mass :=
  KFCausalNeutralOutputTimeKernel.intervalPair_mass angleMeasure h (energyWeight m g k 0) _ _ b c

theorem forceInterval_rate (r : ℝ) (hr : 0 < r) (b c v : ℝ) (hbc : b ≤ c) :
    Complex.I*(v:ℂ)*(forceInterval ε a h hε ha hne hh m g k s p r hr b c).fourier v =
      ∫ t in b..c, KFCausalDisplacedNeutralResolventDynamics.linearRate
        ε a h hε ha hne hh m g k s p r t v :=
  KFCausalNeutralOutputTimeKernel.intervalPair_rate angleMeasure h (energyWeight m g k 0) _ _ b c v hbc

omit h hne hh in
theorem forceInterval_mass_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, ∀ hr : 0 < r, ∀ b c : ℝ, b ≤ c → |b-s| ≤ T → |c-s| ≤ T →
      (forceInterval ε a (h n) hε ha (hne n) (hh n) m g k s p r hr b c).mass ≤
        (c-b)*(2*(1+‖weightedLinear (energyWeight m g k 0)‖^2)*windowBudget ε a m g k s T p) := by
  filter_upwards [force_mass_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr b c hbc hb hc
  apply KFCausalNeutralOutputTimeKernel.intervalPair_mass_bound angleMeasure (h n)
    (energyWeight m g k 0) _ _ b c _ hbc
  intro t ht
  apply hn r hr t
  rcases abs_le.mp hb with ⟨hbl,hbu⟩
  rcases abs_le.mp hc with ⟨hcl,hcu⟩
  exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩

omit h hne hh in
theorem forceInterval_balance_limit (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ν : ℝ → ProbabilityMeasure ℝ)
    (hc : ∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (φ n)) hε ha (hne (φ n)) (hh (φ n))
      m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrtop : Tendsto r atTop atTop)
    (b c v : ℝ) (hbc : b ≤ c) :
    Tendsto (fun n => Complex.I*(v:ℂ)*
      (forceInterval ε a (h (φ n)) hε ha (hne (φ n)) (hh (φ n)) m g k s p
        (r n) (hr n) b c).fourier v) atTop
      (𝓝 (charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v)) := by
  simp_rw [forceInterval_rate ε a _ hε ha _ _ m g k s p _ _ b c v hbc]
  exact KFCausalNeutralTemporalResponseLimit.response_integral_limit
    ε a hε ha m g k s p hm hg hk h hne hh hz φ hφ ν hc r hr hrtop v b c

#print axioms outputCurve_continuous
#print axioms forceInterval_mass
#print axioms forceInterval_rate
#print axioms forceInterval_mass_window
#print axioms forceInterval_balance_limit
end
end UnifiedTheory.Audit.KFCausalNeutralIntegratedForce
