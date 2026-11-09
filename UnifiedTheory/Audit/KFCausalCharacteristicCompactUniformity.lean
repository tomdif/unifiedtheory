/- Eventual local equicontinuity upgrades pointwise subsequential convergence
to uniform convergence on every compact frequency set. -/
import UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity
noncomputable section
open Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness

variable {X : Type*} [PseudoMetricSpace X]

theorem compact_uniform_bound (F : ℕ → X → ℂ)
    (he : EventuallyLocallyEquicontinuous F)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (f : X → ℂ)
    (hf : ∀ x, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)))
    (S : Set X) (hS : IsCompact S) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ S, dist (F (φ n) x) (f x) < ε := by
  classical
  choose δ hδ N hN using (fun x => he x (ε / 4) (by positivity))
  obtain ⟨A, hA⟩ := hS.elim_finite_subcover (fun x => Metric.ball x (δ x))
    (fun _ => Metric.isOpen_ball) (fun x _ => mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hδ x)⟩)
  have hc (x : X) : ∀ᶠ n in atTop, dist (F (φ n) x) (f x) < ε / 4 :=
    (Metric.tendsto_nhds.mp (hf x)) (ε / 4) (by positivity)
  have hall : ∀ᶠ n in atTop, ∀ x ∈ A, N x ≤ n ∧ dist (F (φ n) x) (f x) < ε / 4 := by
    apply (eventually_all_finset A).mpr
    intro x _
    exact (eventually_ge_atTop (N x)).and (hc x)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hall
  refine ⟨M, ?_⟩
  intro n hn x hx
  obtain ⟨y, hyA, hxy⟩ := mem_iUnion₂.mp (hA hx)
  have hny := hM n hn y hyA
  have hxy' : dist x y < δ y := hxy
  have hnear := hN y (φ n) (hny.1.trans (hφ.id_le n)) x hxy'
  have hlimit : dist (f x) (f y) ≤ ε / 4 := by
    apply le_of_tendsto ((hf x).dist (hf y))
    filter_upwards [eventually_ge_atTop (N y)] with j hj
    exact (hN y (φ j) (hj.trans (hφ.id_le j)) x hxy').le
  have htri := dist_triangle (F (φ n) x) (F (φ n) y) (f x)
  have htri' := dist_triangle (F (φ n) y) (f y) (f x)
  rw [dist_comm (f y) (f x)] at htri'
  linarith [hny.2]

theorem compact_uniform_convergence (F : ℕ → X → ℂ)
    (he : EventuallyLocallyEquicontinuous F)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (f : X → ℂ)
    (hf : ∀ x, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)))
    (S : Set X) (hS : IsCompact S) :
    TendstoUniformlyOn (fun n => F (φ n)) f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := compact_uniform_bound F he φ hφ f hf S hS ε hε
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  simpa only [dist_comm] using hN n hn x hx

theorem moving_frequency_limit (F : ℕ → X → ℂ)
    (he : EventuallyLocallyEquicontinuous F)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (f : X → ℂ)
    (hf : ∀ x, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)))
    (x : X) (z : ℕ → X) (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => F (φ n) (z n)) atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := he x (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop N,
    Metric.tendsto_nhds.mp hz δ hδ,
    Metric.tendsto_nhds.mp (hf x) (ε / 2) (by positivity)] with n hn hzn hfn
  have hnear := hN (φ n) (hn.trans (hφ.id_le n)) (z n) hzn
  have htri := dist_triangle (F (φ n) (z n)) (F (φ n) x) (f x)
  linarith

#print axioms compact_uniform_bound
#print axioms compact_uniform_convergence
#print axioms moving_frequency_limit

end
end UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity
