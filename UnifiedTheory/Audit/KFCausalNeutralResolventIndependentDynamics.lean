/- Probability compactness alone selects the semiclassical subsequence.
All positive diverging resolvent scales have the same net-force limits on it. -/
import UnifiedTheory.Audit.KFCausalNeutralProbabilityDeterminesForce

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralResolventIndependentDynamics
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)
open UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl (speedConstant)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalNeutralProbabilityDeterminesForce

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))

include hz

theorem exists_resolvent_independent_dynamics (hm : 0 < m) (hg : 0 < g) (hk : 0 < k) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn
        (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p)
        (fun z => charFun (ν z.1 : Measure ℝ) z.2) atTop S) ∧
      (∀ T v b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
        ‖charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v‖ ≤
          speedConstant ε a m g k s T p v*|c-b|) ∧
      (∀ u : ℕ → ℝ, ∀ t : ℝ, Tendsto u atTop (𝓝 t) →
        Tendsto (fun n => snapshot ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
          m g k s p (u n)) atTop (𝓝 (ν t))) ∧
      ∃ J : Force, Description ε a hε ha m g k s p
        (fun n => h (ρ n)) (fun n => hne (ρ n)) (fun n => hh (ρ n)) ν J := by
  obtain ⟨ρ,hρ,ν,hν,hi,hchar,huniform,hspeed,hmoving,_⟩ :=
    KFCausalNeutralTemporalResponseLimit.exists_probability_dynamics
      ε a hε ha m g k s p hm hg hk h hne hh hz
  obtain ⟨_,_,J,hJ⟩ := exists_force_of_probability_limit ε a hε ha m g k s p
    (fun n => h (ρ n)) (fun n => hne (ρ n)) (fun n => hh (ρ n))
    (hz.comp hρ.tendsto_atTop) ν hchar hm hg hk
  exact ⟨ρ,hρ,ν,hν,hi,hchar,huniform,hspeed,hmoving,J,hJ⟩

#print axioms exists_resolvent_independent_dynamics
end
end UnifiedTheory.Audit.KFCausalNeutralResolventIndependentDynamics
