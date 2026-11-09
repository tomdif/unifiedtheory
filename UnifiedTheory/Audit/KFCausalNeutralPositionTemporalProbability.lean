/- The actual position Born laws admit one weakly continuous limiting
probability curve on all real times. The same subsequence works for
moving observation times. Its initial law is derived, not supplied. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionTemporalCompactness
import UnifiedTheory.Audit.KFCausalTemporalProbabilityRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionTemporalProbability
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralPositionTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralPositionInitialLimit (origin initial_probability_limit)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "F" => fun n => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "M" => fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem exists_probability_curve :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = origin ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn (fun n => F (φ n))
        (fun z => charFun (ν z.1 : Measure ℝ) z.2) atTop S) ∧
      (∀ T V η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ v b c : ℝ,
        |v| ≤ V → |b-s| ≤ T → |c-s| ≤ T → |c-b| < ρ →
          ‖charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v‖ < η) ∧
      (∀ u : ℕ → ℝ, ∀ t : ℝ, Tendsto u atTop (𝓝 t) →
        Tendsto (fun n => M (φ n) (u n)) atTop (𝓝 (ν t))) := by
  obtain ⟨φ,hφ,χ,hχ,_,h0,hc,hu,ht⟩ :=
    KFCausalNeutralPositionTemporalCompactness.exists_characteristic_limit
      ε a hε ha m g k s p hm hg hk h hne hh hz
  have hp (t v : ℝ) : Tendsto (fun n => charFun (M (φ n) t : Measure ℝ) v) atTop (𝓝 (χ (t,v))) :=
    hc (t,v)
  obtain ⟨ν,hνcont,hν,hweak⟩ := KFCausalTemporalProbabilityRepresentation.represented_curve
    (fun n => M (φ n)) χ hχ h0 hp
  refine ⟨φ,hφ,ν,hνcont,?_,?_,?_,?_,?_⟩
  · exact tendsto_nhds_unique (hweak s)
      ((initial_probability_limit ε a hε ha m g k s p h hne hh hz).comp hφ.tendsto_atTop)
  · intro z
    simpa only [hν] using hc z
  · intro S hS
    simpa only [hν] using hu S hS
  · simpa only [hν] using ht
  · intro u t hut
    exact KFCausalTemporalProbabilityRepresentation.moving_time_convergence M
      (KFCausalNeutralPositionTemporalCompactness.joint_equicontinuity
        ε a hε ha m g k s p hm hg hk h hne hh hz)
      φ hφ χ hχ (fun z => hp z.1 z.2) ν hν u t hut

#print axioms exists_probability_curve

end
end UnifiedTheory.Audit.KFCausalNeutralPositionTemporalProbability
