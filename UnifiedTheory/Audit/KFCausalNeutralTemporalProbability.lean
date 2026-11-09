/- Actual neutral Born probabilities admit one subsequential, weakly
continuous limit curve on all real times. The same subsequence works at
moving times converging to any fixed time. No classical force closure or
subsequence-independent dynamics is asserted. -/
import UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness
import UnifiedTheory.Audit.KFCausalNeutralMomentumProbability
import UnifiedTheory.Audit.KFCausalTemporalProbabilityRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

namespace UnifiedTheory.Audit.KFCausalNeutralTemporalProbability
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl (speedConstant)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "F" => fun n : ℕ => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "M" => fun n : ℕ => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem exists_probability_curve :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn (fun n => F (φ n))
        (fun z => charFun (ν z.1 : Measure ℝ) z.2) atTop S) ∧
      (∀ T v b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
        ‖charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v‖ ≤
          speedConstant ε a m g k s T p v*|c-b|) ∧
      (∀ u : ℕ → ℝ, ∀ t : ℝ, Tendsto u atTop (𝓝 t) →
        Tendsto (fun n => M (φ n) (u n)) atTop (𝓝 (ν t))) := by
  obtain ⟨φ,hφ,χ,hχ,_,h0,hc,hu,hl⟩ :=
    KFCausalNeutralTemporalCompactness.exists_characteristic_limit ε a hε ha m g k s p hm hg hk h hne hh hz
  have hp (t v : ℝ) : Tendsto (fun n => charFun (M (φ n) t : Measure ℝ) v) atTop (𝓝 (χ (t,v))) := by
    simpa only [snapshot_characteristic] using hc (t,v)
  obtain ⟨ν,hνcont,hν,_⟩ := KFCausalTemporalProbabilityRepresentation.represented_curve
    (fun n => M (φ n)) χ hχ h0 hp
  refine ⟨φ,hφ,ν,hνcont,?_,?_,?_,?_⟩
  · intro z
    simpa only [hν] using hc z
  · intro S hS
    simpa only [hν] using hu S hS
  · intro T v b c hb hc'
    simpa only [hν] using hl T v b c hb hc'
  · intro u t ht
    have he : KFCausalAsymptoticCharacteristicCompactness.EventuallyLocallyEquicontinuous
        (fun n (z : ℝ × ℝ) => charFun (M n z.1 : Measure ℝ) z.2) := by
      simpa only [snapshot_characteristic] using
        KFCausalNeutralTemporalCompactness.joint_equicontinuity ε a hε ha m g k s p hm hg hk h hne hh hz
    exact KFCausalTemporalProbabilityRepresentation.moving_time_convergence M he φ hφ χ hχ
      (fun z => hp z.1 z.2) ν hν u t ht

#print axioms exists_probability_curve
end
end UnifiedTheory.Audit.KFCausalNeutralTemporalProbability
