/- The actual neutral probability curve and its derived local force limits
satisfy the integrated continuity equation for every Schwartz test. This
does not identify the force as a classical functional of that marginal. -/
import UnifiedTheory.Audit.KFCausalNeutralLocalForceLimit
import UnifiedTheory.Audit.KFCausalWeakForceBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralWeakDynamics
noncomputable section
open MeasureTheory Filter SchwartzMap
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce
open UnifiedTheory.Audit.KFCausalNeutralLocalForceLimit
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum compactify)
open UnifiedTheory.Audit.KFCausalLocalForceMeasure (finitePair)
open UnifiedTheory.Audit.KFCausalVanishingForceTests (zero_test_of_compact_limits)
open UnifiedTheory.Audit.KFCausalWeakForceBalance (schwartz_balance exists_local_balance)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
  (hrtop : Tendsto r atTop atTop) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)

include hz hrtop hm hg hk

theorem exists_common_weak_dynamics {K : Type*} [Countable K]
    (b c : K → ℝ) (hbc : ∀ i, b i ≤ c i) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ t, Tendsto (fun n => snapshot ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p t) atTop (𝓝 (ν t))) ∧
      ∃ P N : K → FiniteMeasure Spectrum,
        (∀ i, Tendsto (fun n => compactify
          (family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).positive) atTop (𝓝 (P i))) ∧
        (∀ i, Tendsto (fun n => compactify
          (family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).negative) atTop (𝓝 (N i))) ∧
        (∀ i (q : C₀(ℝ,ℂ)), Tendsto (fun n =>
          (family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).evaluate q.toBCF) atTop
          (𝓝 ((finitePair (P i) (N i)).evaluate q.toBCF))) ∧
        (∀ i (f : 𝓢(ℝ,ℂ)), (∫ x, f x ∂(ν (c i) : Measure ℝ))-
          (∫ x, f x ∂(ν (b i) : Measure ℝ)) =
          (finitePair (P i) (N i)).evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) := by
  obtain ⟨ρ,hρ,ν,hν,hi,hc,hw,P,N,hP,hN,_,hf⟩ :=
    exists_joint_local_response ε a hε ha m g k s p h hne hh hz r hr b c hbc hm hg hk hrtop
  have hl (i : K) (q : C₀(ℝ,ℂ)) := zero_test_of_compact_limits
    (fun n => family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i)
    (P i) (N i) (hP i) (hN i) q
  refine ⟨ρ,hρ,ν,hν,hi,hc,hw,P,N,hP,hN,hl,?_⟩
  intro i f
  apply schwartz_balance
    (fun n => family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i)
    (finitePair (P i) (N i)) (ν (b i)) (ν (c i)) _ (hl i)
    (fun v => hf (b i) (c i) v (hbc i)) f
  obtain ⟨C,hC⟩ := family_mass_bound ε a hε ha m g k s p h hne hh hz r hr b c hbc
    hm.le hg.le hk.le i
  exact ⟨C,hρ.tendsto_atTop.eventually hC⟩

theorem exists_all_interval_weak_dynamics :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ t, Tendsto (fun n => snapshot ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p t) atTop (𝓝 (ν t))) ∧
      (∀ b c : ℝ, b ≤ c → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ J : FluxPair,
        (∀ q : C₀(ℝ,ℂ), Tendsto (fun n =>
          (forceInterval ε a (h (ρ (ψ n))) hε ha (hne (ρ (ψ n))) (hh (ρ (ψ n)))
            m g k s p (r (ρ (ψ n))) (hr (ρ (ψ n))) b c).evaluate q.toBCF) atTop
          (𝓝 (J.evaluate q.toBCF))) ∧
        (∀ f : 𝓢(ℝ,ℂ), (∫ x, f x ∂(ν c : Measure ℝ))-
          (∫ x, f x ∂(ν b : Measure ℝ)) =
          J.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction)) := by
  obtain ⟨ρ,hρ,ν,hν,hi,hc,_,_,hw,_⟩ :=
    KFCausalNeutralTemporalResponseLimit.exists_probability_dynamics
      ε a hε ha m g k s p hm hg hk h hne hh hz
  refine ⟨ρ,hρ,ν,hν,hi,hc,?_,?_⟩
  · intro t
    exact hw (fun _ => t) t tendsto_const_nhds
  · intro b c hbc
    apply exists_local_balance
      (fun n => forceInterval ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
        (r (ρ n)) (hr (ρ n)) b c) (ν b) (ν c)
    · obtain ⟨C,hC⟩ := family_mass_bound ε a hε ha m g k s p h hne hh hz r hr
        (fun _ : Unit => b) (fun _ => c) (fun _ => hbc) hm.le hg.le hk.le ()
      exact ⟨C,hρ.tendsto_atTop.eventually hC⟩
    · intro v
      exact forceInterval_balance_limit ε a hε ha m g k s p hm hg hk h hne hh hz ρ hρ ν hc
        (fun n => r (ρ n)) (fun n => hr (ρ n)) (hrtop.comp hρ.tendsto_atTop) b c v hbc

#print axioms exists_common_weak_dynamics
#print axioms exists_all_interval_weak_dynamics
end
end UnifiedTheory.Audit.KFCausalNeutralWeakDynamics
