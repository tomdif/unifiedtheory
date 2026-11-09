/- The actual model constructs one consistent spacetime force family on
the same subsequence as the neutral probability curve and weak balance.
All real subwindows converge without a further extraction. -/
import UnifiedTheory.Audit.KFCausalNeutralSpacetimeConsistency

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralConsistentSpacetimeDynamics
noncomputable section
open MeasureTheory Filter SchwartzMap BoundedContinuousFunction
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralForceConsistency (forceBudget)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeLimit (windowFamily)
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
open UnifiedTheory.Audit.KFCausalCompactTimeRestriction
open UnifiedTheory.Audit.KFCausalSpacetimeRestriction
open UnifiedTheory.Audit.KFCausalSpacetimeWindowTests
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeConsistency
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
  {K : Type*} [Countable K] (b c : K → ℝ) (hbc : ∀ i, b i ≤ c i)

local notation "W" => windowFamily ε a hε ha m g k s p h hne hh r hr b c
local notation "I" => KFCausalNeutralLocalForceLimit.family ε a hε ha m g k s p h hne hh r hr b c

include hz hbc

theorem exists_consistent_spacetime_dynamics (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hrtop : Tendsto r atTop atTop) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ t, Tendsto (fun n => snapshot ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p t) atTop (𝓝 (ν t))) ∧
      ∃ F : KFCausalConsistentForceIntervals.Family b c s (fun T => forceBudget ε a m g k s T p),
        (∀ i (q : C₀(ℝ,ℂ)), Tendsto (fun n => (I (ρ n) i).evaluate q.toBCF) atTop
          (𝓝 ((F.local i).evaluate q.toBCF))) ∧
        (∀ i (f : 𝓢(ℝ,ℂ)), (∫ x, f x ∂(ν (c i) : Measure ℝ))-
          (∫ x, f x ∂(ν (b i) : Measure ℝ)) =
          (F.local i).evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) ∧
      ∃ G : KFCausalConsistentSpacetimeWindows.Family b c s (fun T => forceBudget ε a m g k s T p),
        (∀ i, Tendsto (fun n => compactify (W (ρ n) i).positive) atTop (𝓝 (G.positive i))) ∧
        (∀ i, Tendsto (fun n => compactify (W (ρ n) i).negative) atTop (𝓝 (G.negative i))) ∧
        (∀ i (q : C₀(ℝ × ℝ,ℂ)), Tendsto (fun n => (W (ρ n) i).evaluate q.toBCF) atTop
          (𝓝 ((G.local i).evaluate q.toBCF))) ∧
        (∀ T i, |b i-s| ≤ T → |c i-s| ≤ T →
          (G.local i).mass ≤ (c i-b i)*forceBudget ε a m g k s T p) ∧
        (∀ i (χ : Spectrum →ᵇ ℂ),
          (∀ t ∈ Set.Icc (b i) (c i), χ (KFCausalCompactifiedForceMeasure.embed t) = 1) →
          (∀ x, x ∉ KFCausalLocalForceMeasure.interior → χ x = 0) →
          ∀ q : C₀(ℝ,ℂ), (F.local i).evaluate q.toBCF =
            (G.local i).evaluate (pullback (liftTest χ q))) ∧
        (∀ i (f : 𝓢(ℝ,ℂ)), ∃ χ : Spectrum →ᵇ ℂ,
          (∀ t ∈ Set.Icc (b i) (c i), χ (KFCausalCompactifiedForceMeasure.embed t) = 1) ∧
          (∀ x, x ∉ KFCausalLocalForceMeasure.interior → χ x = 0) ∧
          (∫ x, f x ∂(ν (c i) : Measure ℝ))-(∫ x, f x ∂(ν (b i) : Measure ℝ)) =
            (G.local i).evaluate (pullback (liftTest χ (derivCLM ℂ ℂ f).toZeroAtInfty))) ∧
        (∀ i u v, u ≤ v → b i ≤ u → v ≤ c i →
          Tendsto (fun n => compactify
            (forceWindow ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
              (r (ρ n)) (hr (ρ n)) u v).positive) atTop
              (𝓝 ((G.positive i).restrict (timeStrip u v))) ∧
          Tendsto (fun n => compactify
            (forceWindow ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
              (r (ρ n)) (hr (ρ n)) u v).negative) atTop
              (𝓝 ((G.negative i).restrict (timeStrip u v)))) ∧
        (∀ i u v, u ≤ v → b i ≤ u → v ≤ c i → ∀ q : C₀(ℝ × ℝ,ℂ),
          Tendsto (fun n =>
            (forceWindow ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
              (r (ρ n)) (hr (ρ n)) u v).evaluate q.toBCF) atTop
              (𝓝 ((restrictPair (G.local i) u v).evaluate q.toBCF))) := by
  obtain ⟨ρ,hρ,ν,hν,hi,hchar,hweak,F,hF,hbalance,P,N,hP,hN,hzero,hmass,hidentify,hsch⟩ :=
    KFCausalNeutralSpacetimeLimit.exists_joint_spacetime_limits
      ε a hε ha m g k s p h hne hh hz r hr b c hbc hm hg hk hrtop
  let G := consistentFamily ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
    hm.le hg.le hk.le hbc
  refine ⟨ρ,hρ,ν,hν,hi,hchar,hweak,F,hF,hbalance,G,hP,hN,hzero,hmass,hidentify,hsch,?_,?_⟩
  · exact subwindow_compact_converges ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
      hm.le hg.le hk.le
  · exact subwindow_zero_converges ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
      hm.le hg.le hk.le

#print axioms exists_consistent_spacetime_dynamics
end
end UnifiedTheory.Audit.KFCausalNeutralConsistentSpacetimeDynamics
