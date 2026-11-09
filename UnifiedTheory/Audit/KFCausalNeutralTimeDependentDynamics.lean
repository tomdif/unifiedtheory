/- The actual common semiclassical limit satisfies the time-dependent weak
equation for finite sums of separated tests, with all prior convergence data. -/
import UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralTimeDependentDynamics
noncomputable section
open MeasureTheory Filter Set SchwartzMap
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralForceConsistency (forceBudget)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce (forceInterval)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeLimit (windowFamily)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce (compactify)
open UnifiedTheory.Audit.KFCausalSpacetimeExhaustion
open UnifiedTheory.Audit.KFCausalConsistentSpacetimeWindows (Family)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalGluedSpacetimeForce
open UnifiedTheory.Audit.KFCausalNeutralGlobalForceLimit
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)

include hz

theorem exists_time_dependent_dynamics (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hrtop : Tendsto r atTop atTop) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ t, Tendsto (fun n => snapshot ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p t) atTop (𝓝 (ν t))) ∧
      ∃ G : Family (left s) (right s) s (fun T => forceBudget ε a m g k s T p),
        (∀ i, Tendsto (fun n => compactify
          (windowFamily ε a hε ha m g k s p h hne hh r hr (left s) (right s) (ρ n) i).positive)
            atTop (𝓝 (G.positive i))) ∧
        (∀ i, Tendsto (fun n => compactify
          (windowFamily ε a hε ha m g k s p h hne hh r hr (left s) (right s) (ρ n) i).negative)
            atTop (𝓝 (G.negative i))) ∧
      ∃ J : Force,
        (∀ i, J.window (left s i) (right s i) = G.local i) ∧
        (∀ J' : Force, (∀ i, J'.window (left s i) (right s i) = G.local i) →
          J'.positive = J.positive ∧ J'.negative = J.negative) ∧
        J.positive.map Prod.fst ≪ volume ∧ J.negative.map Prod.fst ≪ volume ∧
        (∀ t : ℝ, J.positive ({t} ×ˢ univ)+J.negative ({t} ×ˢ univ) = 0) ∧
        (∀ b c : ℝ, b ≤ c → ∀ q : C₀(ℝ × ℝ,ℂ),
          Tendsto (fun n =>
            (forceWindow ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
              (r (ρ n)) (hr (ρ n)) b c).evaluate q.toBCF) atTop
                (𝓝 ((J.window b c).evaluate q.toBCF))) ∧
        (∀ b c : ℝ, b ≤ c → ∀ q : C₀(ℝ,ℂ),
          Tendsto (fun n =>
            (forceInterval ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
              (r (ρ n)) (hr (ρ n)) b c).evaluate q.toBCF) atTop
                (𝓝 ((J.interval b c).evaluate q.toBCF))) ∧
        (∀ T b c : ℝ, b ≤ c → |b-s| ≤ T → |c-s| ≤ T →
          ∀ A : Set ℝ, MeasurableSet A →
            (J.window b c).positive (A ×ˢ univ)+(J.window b c).negative (A ×ˢ univ) ≤
              ENNReal.ofReal (forceBudget ε a m g k s T p)*volume (A ∩ Icc b c)) ∧
        (∀ b c : ℝ, b ≤ c → ∀ f : 𝓢(ℝ,ℂ),
          (∫ x, f x ∂(ν c : Measure ℝ))-(∫ x, f x ∂(ν b : Measure ℝ)) =
            (J.interval b c).evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) ∧
        TensorWeakEquation ν J := by
  obtain ⟨ρ,hρ,ν,hν,hi,hchar,hweak,G,hP,hN,J,hwindow,hunique,hpa,hna,
    hslice,hspace,hinterval,hbound,hbalance⟩ :=
    KFCausalNeutralGlobalSpacetimeDynamics.exists_global_spacetime_dynamics
      ε a hε ha m g k s p h hne hh hz r hr hm hg hk hrtop
  exact ⟨ρ,hρ,ν,hν,hi,hchar,hweak,G,hP,hN,J,hwindow,hunique,hpa,hna,
    hslice,hspace,hinterval,hbound,hbalance,tensor_weak_equation ν J hbalance⟩

#print axioms exists_time_dependent_dynamics
end
end UnifiedTheory.Audit.KFCausalNeutralTimeDependentDynamics
