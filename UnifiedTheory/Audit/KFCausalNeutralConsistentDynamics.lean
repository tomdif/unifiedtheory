/- The actual neutral dynamics constructs a consistent interval-force
family. Positivity, additivity, window mass control, local convergence and
the Schwartz continuity equation hold on the same subsequence. -/
import UnifiedTheory.Audit.KFCausalNeutralForceConsistency
import UnifiedTheory.Audit.KFCausalConsistentForceIntervals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralConsistentDynamics
noncomputable section
open MeasureTheory Filter SchwartzMap
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralLocalForceLimit (family)
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (compactify)
open UnifiedTheory.Audit.KFCausalConsistentForceIntervals (Family)
open UnifiedTheory.Audit.KFCausalNeutralForceConsistency
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
  (hrtop : Tendsto r atTop atTop) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)

include hz hrtop hm hg hk

theorem exists_consistent_weak_dynamics {K : Type*} [Countable K]
    (b c : K → ℝ) (hbc : ∀ i, b i ≤ c i) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ t, Tendsto (fun n => snapshot ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p t) atTop (𝓝 (ν t))) ∧
      ∃ F : Family b c s (fun T => forceBudget ε a m g k s T p),
        (∀ i, Tendsto (fun n => compactify
          (family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).positive) atTop
          (𝓝 (F.positive i))) ∧
        (∀ i, Tendsto (fun n => compactify
          (family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).negative) atTop
          (𝓝 (F.negative i))) ∧
        (∀ i (q : C₀(ℝ,ℂ)), Tendsto (fun n =>
          (family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).evaluate q.toBCF) atTop
          (𝓝 ((F.local i).evaluate q.toBCF))) ∧
        (∀ i (f : 𝓢(ℝ,ℂ)), (∫ x, f x ∂(ν (c i) : Measure ℝ))-
          (∫ x, f x ∂(ν (b i) : Measure ℝ)) =
          (F.local i).evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) := by
  obtain ⟨ρ,hρ,ν,hν,hi,hc,hw,P,N,hP,hN,hl,hf⟩ :=
    KFCausalNeutralWeakDynamics.exists_common_weak_dynamics
      ε a hε ha m g k s p h hne hh hz r hr hrtop hm hg hk b c hbc
  let F : Family b c s (fun T => forceBudget ε a m g k s T p) := {
    positive := P
    negative := N
    additive := compact_family_add ε a hε ha m g k s p h hne hh r hr b c hbc ρ P N hP hN
    mass_bound := compact_family_mass_bound ε a hε ha m g k s p h hne hh hz r hr
      b c hbc ρ hρ P N hP hN hm.le hg.le hk.le }
  exact ⟨ρ,hρ,ν,hν,hi,hc,hw,F,hP,hN,hl,hf⟩

omit hz hrtop hm hg hk in
theorem observable_increment_bound {K : Type*} {b c : K → ℝ}
    (ν : ℝ → ProbabilityMeasure ℝ)
    (F : Family b c s (fun T => forceBudget ε a m g k s T p))
    (hf : ∀ i (f : 𝓢(ℝ,ℂ)), (∫ x, f x ∂(ν (c i) : Measure ℝ))-
      (∫ x, f x ∂(ν (b i) : Measure ℝ)) =
      (F.local i).evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction)
    (T : ℝ) (i : K) (hb : |b i-s| ≤ T) (hc : |c i-s| ≤ T) (f : 𝓢(ℝ,ℂ)) :
    ‖(∫ x, f x ∂(ν (c i) : Measure ℝ))-(∫ x, f x ∂(ν (b i) : Measure ℝ))‖ ≤
      ((c i-b i)*forceBudget ε a m g k s T p)/2*
        ‖(derivCLM ℂ ℂ f).toBoundedContinuousFunction‖ := by
  rw [hf]
  exact KFCausalConsistentForceIntervals.local_test_bound F T i hb hc _

#print axioms exists_consistent_weak_dynamics
#print axioms observable_increment_bound
end
end UnifiedTheory.Audit.KFCausalNeutralConsistentDynamics
