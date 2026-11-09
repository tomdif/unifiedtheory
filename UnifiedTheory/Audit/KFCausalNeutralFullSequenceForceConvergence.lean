/- Once the probability curve converges, net force tests converge along
that whole sequence, for every diverging positive resolvent scale. -/
import UnifiedTheory.Audit.KFCausalNeutralForceClusterIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralFullSequenceForceConvergence
noncomputable section
open MeasureTheory Filter Set SchwartzMap
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce (forceWindow)
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce (forceInterval)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation (IntervalBalance)
open UnifiedTheory.Audit.KFCausalGlobalNetForceUniqueness
open UnifiedTheory.Audit.KFCausalNeutralForceClusterIdentification

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (ν : ℝ → ProbabilityMeasure ℝ)
  (hchar : ∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h n) hε ha (hne n) (hh n)
    m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
  (J : Force) (hJ : IntervalBalance ν J) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)

include hz hchar hJ hm hg hk

theorem spacetime_converges (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (b c : ℝ) (hbc : b ≤ c) (q : C₀(ℝ × ℝ,ℂ)) :
    Tendsto (fun n =>
      (forceWindow ε a (h n) hε ha (hne n) (hh n) m g k s p (r n) (hr n) b c).evaluate q.toBCF)
        atTop (𝓝 ((J.window b c).evaluate q.toBCF)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ρ,_,K,hK,hspace,_⟩ := exists_compatible_force_subsequence
    ε a hε ha m g k s p (fun n => h (ns n)) (fun n => hne (ns n)) (fun n => hh (ns n))
    (hz.comp hns) ν (fun z => (hchar z).comp hns)
    (fun n => r (ns n)) (fun n => hr (ns n)) hm hg hk (hrtop.comp hns)
  have ht := hspace b c hbc q
  rw [same_curve_same_force_action ν K J hK hJ b c q.toBCF] at ht
  exact ⟨ρ,ht⟩

theorem momentum_converges (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (b c : ℝ) (hbc : b ≤ c) (q : C₀(ℝ,ℂ)) :
    Tendsto (fun n =>
      (forceInterval ε a (h n) hε ha (hne n) (hh n) m g k s p (r n) (hr n) b c).evaluate q.toBCF)
        atTop (𝓝 ((J.interval b c).evaluate q.toBCF)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ρ,_,K,hK,_,hinterval⟩ := exists_compatible_force_subsequence
    ε a hε ha m g k s p (fun n => h (ns n)) (fun n => hne (ns n)) (fun n => hh (ns n))
    (hz.comp hns) ν (fun z => (hchar z).comp hns)
    (fun n => r (ns n)) (fun n => hr (ns n)) hm hg hk (hrtop.comp hns)
  have ht := hinterval b c hbc q
  rw [KFCausalNetForceUniqueness.evaluate_eq _ _ (interval_equivalent ν K J hK hJ b c hbc) q.toBCF] at ht
  exact ⟨ρ,ht⟩

theorem spacetime_resolvent_difference (r u : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hu : ∀ n, 0 < u n)
    (hrtop : Tendsto r atTop atTop) (hutop : Tendsto u atTop atTop)
    (b c : ℝ) (hbc : b ≤ c) (q : C₀(ℝ × ℝ,ℂ)) :
    Tendsto (fun n =>
      (forceWindow ε a (h n) hε ha (hne n) (hh n) m g k s p (r n) (hr n) b c).evaluate q.toBCF-
      (forceWindow ε a (h n) hε ha (hne n) (hh n) m g k s p (u n) (hu n) b c).evaluate q.toBCF)
        atTop (𝓝 0) := by
  simpa only [sub_self] using
    (spacetime_converges ε a hε ha m g k s p h hne hh hz ν hchar J hJ hm hg hk r hr hrtop b c hbc q).sub
    (spacetime_converges ε a hε ha m g k s p h hne hh hz ν hchar J hJ hm hg hk u hu hutop b c hbc q)

theorem momentum_resolvent_difference (r u : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hu : ∀ n, 0 < u n)
    (hrtop : Tendsto r atTop atTop) (hutop : Tendsto u atTop atTop)
    (b c : ℝ) (hbc : b ≤ c) (q : C₀(ℝ,ℂ)) :
    Tendsto (fun n =>
      (forceInterval ε a (h n) hε ha (hne n) (hh n) m g k s p (r n) (hr n) b c).evaluate q.toBCF-
      (forceInterval ε a (h n) hε ha (hne n) (hh n) m g k s p (u n) (hu n) b c).evaluate q.toBCF)
        atTop (𝓝 0) := by
  simpa only [sub_self] using
    (momentum_converges ε a hε ha m g k s p h hne hh hz ν hchar J hJ hm hg hk r hr hrtop b c hbc q).sub
    (momentum_converges ε a hε ha m g k s p h hne hh hz ν hchar J hJ hm hg hk u hu hutop b c hbc q)

#print axioms spacetime_converges
#print axioms momentum_converges
#print axioms spacetime_resolvent_difference
#print axioms momentum_resolvent_difference
end
end UnifiedTheory.Audit.KFCausalNeutralFullSequenceForceConvergence
