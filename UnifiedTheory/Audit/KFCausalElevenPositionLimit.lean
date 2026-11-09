/- A common subsequence carries both the all-time position probability
curve and eleven-coordinate kernels for countably many sampling families.
Their neutral-position restrictions agree whenever sampling times converge.
This is not a full phase-space law or a closed classical evolution. -/
import UnifiedTheory.Audit.KFCausalElevenCountableCharacteristics
import UnifiedTheory.Audit.KFCausalNeutralPositionTemporalProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalElevenPositionLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates (Coefficients encode neutral_axis)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)
open UnifiedTheory.Audit.KFCausalNeutralPositionProbability (snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalNeutralPositionTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalElevenCountableCharacteristics (ClassicalKernel)
open UnifiedTheory.Audit.KFCausalNeutralPositionInitialLimit (origin)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem neutral_characteristic (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (t v : ℝ) :
    characteristic volume h (evolvedState ε a h hε ha hne hh m g k s p t) (encode (0,v)) =
      curve ε a h hε ha hne hh m g k s p (t,v) := by
  rw [neutral_axis,curve,snapshot_characteristic]
  exact (KFCausalNeutralPositionRadialCharacteristic.bare_canonical ε a h hε ha hne hh m g k s p v t).symm

variable {K : Type*} [Countable K]
variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "F" => fun n => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "M" => fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "ψ" => fun n t => evolvedState ε a (h n) hε ha (hne n) (hh n) m g k s p t
include hm hg hk hz

theorem common_sampled_limit (T : K → ℝ) (t : K → ℕ → ℝ)
    (ht : ∀ j n, t j n ∈ Set.Icc s (s+T j)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = origin ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn (fun n => F (φ n))
        (fun z => charFun (ν z.1 : Measure ℝ) z.2) atTop S) ∧
      (∀ u : ℕ → ℝ, ∀ b : ℝ, Tendsto u atTop (𝓝 b) →
        Tendsto (fun n => M (φ n) (u n)) atTop (𝓝 (ν b))) ∧
      ∃ χ : K → ClassicalKernel,
        (∀ j z, Tendsto (fun n => characteristic volume (h (φ n)) (ψ (φ n) (t j (φ n))) (encode z))
          atTop (𝓝 ((χ j).value z))) ∧
        (∀ j S, IsCompact S → TendstoUniformlyOn
          (fun n z => characteristic volume (h (φ n)) (ψ (φ n) (t j (φ n))) (encode z))
          (χ j).value atTop S) ∧
        (∀ j b, Tendsto (t j) atTop (𝓝 b) → ∀ v : ℝ,
          (χ j).value (0,v) = charFun (ν b : Measure ℝ) v) := by
  obtain ⟨α,hα,ν,hν,hi,hpos,huniform,_,_⟩ :=
    KFCausalNeutralPositionTemporalProbability.exists_probability_curve
      ε a hε ha m g k s p hm hg hk h hne hh hz
  obtain ⟨β,hβ,χ,hlim,hcompact⟩ := KFCausalElevenCountableCharacteristics.sampled_common_limit
    ε a hε ha m g k s p hm hg hk (fun n => h (α n)) (fun n => hne (α n)) (fun n => hh (α n))
    (hz.comp hα.tendsto_atTop) T (fun j n => t j (α n)) (fun j n => ht j (α n))
  let φ : ℕ → ℕ := fun n => α (β n)
  have hφ : StrictMono φ := hα.comp hβ
  have he := KFCausalNeutralPositionTemporalCompactness.joint_equicontinuity
    ε a hε ha m g k s p hm hg hk h hne hh hz
  let c : ℝ × ℝ → ℂ := fun z => charFun (ν z.1 : Measure ℝ) z.2
  have hc : Continuous c := KFCausalAsymptoticCharacteristicCompactness.continuous_limit
    F he α hα c hpos
  have hp (z : ℝ × ℝ) : Tendsto (fun n => F (φ n) z) atTop (𝓝 (c z)) :=
    (hpos z).comp hβ.tendsto_atTop
  refine ⟨φ,hφ,ν,hν,hi,hp,?_,?_,χ,hlim,hcompact,?_⟩
  · intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    exact hβ.tendsto_atTop.eventually ((Metric.tendstoUniformlyOn_iff.mp (huniform S hS)) η hη)
  · intro u b hu
    exact KFCausalTemporalProbabilityRepresentation.moving_time_convergence M he φ hφ c hc hp
      ν (fun _ _ => rfl) u b hu
  · intro j b htb v
    have htime := (htb.comp hφ.tendsto_atTop).prodMk_nhds (tendsto_const_nhds (x := v))
    have hmove := KFCausalCharacteristicCompactUniformity.moving_frequency_limit
      F he φ hφ c hp (b,v) (fun n => (t j (φ n),v)) htime
    have hneutral : Tendsto (fun n => F (φ n) (t j (φ n),v)) atTop (𝓝 ((χ j).value (0,v))) := by
      simpa only [neutral_characteristic] using hlim j (0,v)
    exact tendsto_nhds_unique hneutral hmove

#print axioms neutral_characteristic
#print axioms common_sampled_limit

end
end UnifiedTheory.Audit.KFCausalElevenPositionLimit
