/- Every actual force cluster over a convergent probability sequence has
that same probability curve. The force cluster is constructed, not assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralGlobalSpacetimeDynamics
import UnifiedTheory.Audit.KFCausalGlobalNetForceUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralForceClusterIdentification
noncomputable section
open MeasureTheory Filter Set SchwartzMap
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce (forceWindow)
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce (forceInterval)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation (IntervalBalance)

theorem probability_curve_eq_of_characteristic_limits (f : ℕ → ℝ × ℝ → ℂ)
    (ν κ : ℝ → ProbabilityMeasure ℝ)
    (hν : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
    (hκ : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (charFun (κ z.1 : Measure ℝ) z.2))) : ν = κ := by
  funext t
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext v
  exact tendsto_nhds_unique (hν (t,v)) (hκ (t,v))

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (ν : ℝ → ProbabilityMeasure ℝ)
  (hchar : ∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h n) hε ha (hne n) (hh n)
    m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
  (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)

include hz hchar

theorem exists_compatible_force_subsequence (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hrtop : Tendsto r atTop atTop) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ J : Force, IntervalBalance ν J ∧
      (∀ b c : ℝ, b ≤ c → ∀ q : C₀(ℝ × ℝ,ℂ),
        Tendsto (fun n =>
          (forceWindow ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
            (r (ρ n)) (hr (ρ n)) b c).evaluate q.toBCF) atTop
              (𝓝 ((J.window b c).evaluate q.toBCF))) ∧
      (∀ b c : ℝ, b ≤ c → ∀ q : C₀(ℝ,ℂ),
        Tendsto (fun n =>
          (forceInterval ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
            (r (ρ n)) (hr (ρ n)) b c).evaluate q.toBCF) atTop
              (𝓝 ((J.interval b c).evaluate q.toBCF))) := by
  obtain ⟨ρ,hρ,κ,_,_,hκ,_,_,_,_,J,_,_,_,_,_,hspace,hinterval,_,hbalance⟩ :=
    KFCausalNeutralGlobalSpacetimeDynamics.exists_global_spacetime_dynamics
      ε a hε ha m g k s p h hne hh hz r hr hm hg hk hrtop
  have he : κ = ν := probability_curve_eq_of_characteristic_limits _ κ ν hκ
    (fun z => (hchar z).comp hρ.tendsto_atTop)
  rw [he] at hbalance
  exact ⟨ρ,hρ,J,hbalance,hspace,hinterval⟩

#print axioms probability_curve_eq_of_characteristic_limits
#print axioms exists_compatible_force_subsequence
end
end UnifiedTheory.Audit.KFCausalNeutralForceClusterIdentification
