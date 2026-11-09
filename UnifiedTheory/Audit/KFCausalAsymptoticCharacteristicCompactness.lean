/- A bounded family with eventual local equicontinuity has a continuous
pointwise subsequential limit. No continuity of individual terms is assumed. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness
noncomputable section
open Filter Set TopologicalSpace
open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

def EventuallyLocallyEquicontinuous (F : ℕ → X → ℂ) : Prop :=
  ∀ x ε, 0 < ε → ∃ δ, 0 < δ ∧ ∃ N, ∀ n ≥ N, ∀ y,
    dist y x < δ → dist (F n y) (F n x) < ε

theorem dense_subsequence [SeparableSpace X] (F : ℕ → X → ℂ)
    (hb : ∀ n x, ‖F n x‖ ≤ 1) :
    ∃ d : Set X, d.Countable ∧ Dense d ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ x ∈ d, CauchySeq (fun n => F (φ n) x) := by
  obtain ⟨d, hd, hD⟩ := TopologicalSpace.exists_countable_dense X
  letI : Countable d := hd.to_subtype
  have hk : IsCompact {g : d → ℂ | ∀ x, g x ∈ Metric.closedBall 0 1} :=
    isCompact_pi_infinite (fun _ => isCompact_closedBall (0 : ℂ) 1)
  have hm (n : ℕ) : (fun x : d => F n x) ∈ {g : d → ℂ | ∀ x, g x ∈ Metric.closedBall 0 1} := by
    intro x
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb n x
  obtain ⟨g, _, φ, hφ, ht⟩ := hk.tendsto_subseq hm
  refine ⟨d, hd, hD, φ, hφ, ?_⟩
  intro x hx
  exact ((tendsto_pi_nhds.mp ht) ⟨x, hx⟩).cauchySeq

theorem cauchy_of_dense (F : ℕ → X → ℂ)
    (he : EventuallyLocallyEquicontinuous F)
    (d : Set X) (hD : Dense d) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hc : ∀ x ∈ d, CauchySeq (fun n => F (φ n) x)) (x : X) :
    CauchySeq (fun n => F (φ n) x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, N, heN⟩ := he x (ε / 3) (by positivity)
  obtain ⟨y, hyd, hy⟩ := Metric.mem_closure_iff.mp (hD x) δ hδ
  have hy' : dist y x < δ := by simpa only [dist_comm] using hy
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp (hc y hyd) (ε / 3) (by positivity)
  refine ⟨max N M, ?_⟩
  intro m hm n hn
  have hmN : N ≤ φ m := (le_max_left N M).trans (hm.trans (hφ.id_le m))
  have hnN : N ≤ φ n := (le_max_left N M).trans (hn.trans (hφ.id_le n))
  have ha := heN (φ m) hmN y hy'
  have hb := hM m ((le_max_right N M).trans hm) n ((le_max_right N M).trans hn)
  have hc' := heN (φ n) hnN y hy'
  have ht := dist_triangle (F (φ m) x) (F (φ m) y) (F (φ n) x)
  have hu := dist_triangle (F (φ m) y) (F (φ n) y) (F (φ n) x)
  rw [dist_comm (F (φ m) x) (F (φ m) y)] at ht
  linarith

theorem continuous_limit (F : ℕ → X → ℂ)
    (he : EventuallyLocallyEquicontinuous F)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (f : X → ℂ)
    (hf : ∀ x, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x))) :
    Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨δ, hδ, N, heN⟩ := he x (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hl : dist (f y) (f x) ≤ ε / 2 := by
    apply le_of_tendsto ((hf y).dist (hf x))
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (heN (φ n) (hn.trans (hφ.id_le n)) y hy).le
  linarith

theorem exists_continuous_subsequence [SeparableSpace X] (F : ℕ → X → ℂ)
    (hb : ∀ n x, ‖F n x‖ ≤ 1) (he : EventuallyLocallyEquicontinuous F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ, Continuous f ∧
      (∀ x, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x))) ∧ ∀ x, ‖f x‖ ≤ 1 := by
  classical
  obtain ⟨d, _, hD, φ, hφ, hc⟩ := dense_subsequence F hb
  have ht (x : X) := cauchySeq_tendsto_of_complete (cauchy_of_dense F he d hD φ hφ hc x)
  choose f hf using ht
  refine ⟨φ, hφ, f, continuous_limit F he φ hφ f hf, hf, ?_⟩
  intro x
  exact le_of_tendsto' (hf x).norm (fun n => hb (φ n) x)

#print axioms dense_subsequence
#print axioms cauchy_of_dense
#print axioms continuous_limit
#print axioms exists_continuous_subsequence

end
end UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness
