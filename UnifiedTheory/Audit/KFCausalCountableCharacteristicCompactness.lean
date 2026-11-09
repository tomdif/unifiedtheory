/- One subsequence serves a countable family of frequency functions.
Local equicontinuity is only required separately for each family member. -/
import UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCountableCharacteristicCompactness
noncomputable section
open Filter Set TopologicalSpace
open scoped Topology
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness

variable {X K : Type*} [PseudoMetricSpace X] [SeparableSpace X] [Countable K]

theorem common_dense_subsequence (F : ℕ → K → X → ℂ)
    (hb : ∀ n k x, ‖F n k x‖ ≤ 1) :
    ∃ d : Set X, d.Countable ∧ Dense d ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ k x, x ∈ d → CauchySeq (fun n => F (φ n) k x) := by
  obtain ⟨d, hd, hD⟩ := TopologicalSpace.exists_countable_dense X
  letI : Countable d := hd.to_subtype
  have hk : IsCompact {g : K × d → ℂ | ∀ x, g x ∈ Metric.closedBall 0 1} :=
    isCompact_pi_infinite (fun _ => isCompact_closedBall (0 : ℂ) 1)
  have hm (n : ℕ) : (fun x : K × d => F n x.1 x.2) ∈
      {g : K × d → ℂ | ∀ x, g x ∈ Metric.closedBall 0 1} := by
    intro x
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb n x.1 x.2
  obtain ⟨g, _, φ, hφ, ht⟩ := hk.tendsto_subseq hm
  refine ⟨d, hd, hD, φ, hφ, ?_⟩
  intro k x hx
  exact ((tendsto_pi_nhds.mp ht) (k, ⟨x, hx⟩)).cauchySeq

theorem exists_common_continuous_subsequence (F : ℕ → K → X → ℂ)
    (hb : ∀ n k x, ‖F n k x‖ ≤ 1)
    (he : ∀ k, EventuallyLocallyEquicontinuous (fun n x => F n k x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : K → X → ℂ,
      (∀ k, Continuous (χ k)) ∧
      (∀ k x, Tendsto (fun n => F (φ n) k x) atTop (𝓝 (χ k x))) ∧
      ∀ k x, ‖χ k x‖ ≤ 1 := by
  classical
  obtain ⟨d, _, hD, φ, hφ, hc⟩ := common_dense_subsequence F hb
  have ht (k : K) (x : X) := cauchySeq_tendsto_of_complete
    (cauchy_of_dense (fun n x => F n k x) (he k) d hD φ hφ (hc k) x)
  choose χ hχ using ht
  refine ⟨φ, hφ, χ, ?_, hχ, ?_⟩
  · intro k
    exact continuous_limit (fun n x => F n k x) (he k) φ hφ (χ k) (hχ k)
  · intro k x
    exact le_of_tendsto' (hχ k x).norm (fun n => hb (φ n) k x)

#print axioms common_dense_subsequence
#print axioms exists_common_continuous_subsequence

end
end UnifiedTheory.Audit.KFCausalCountableCharacteristicCompactness
