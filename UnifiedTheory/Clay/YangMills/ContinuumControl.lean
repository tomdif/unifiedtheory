/- Continuum-route interfaces and elementary survival tests. These lemmas
transfer uniform scalar estimates; they do not construct a quantum field theory. -/
import UnifiedTheory.Clay.YangMills.LocalFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ContinuumControl
noncomputable section
open Filter
open scoped Topology

abbrev Configuration (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 4)
abbrev CorrelationTest (n : ℕ) := SchwartzMap (Configuration n) ℂ

structure Hierarchy where
  correlation : (n : ℕ) → CorrelationTest n →L[ℂ] ℂ

def WeakConvergence (S : ℕ → Hierarchy) (W : Hierarchy) : Prop :=
  ∀ n f, Tendsto (fun k => (S k).correlation n f) atTop (𝓝 (W.correlation n f))

structure RegulatorScales where
  spacing : ℕ → ℝ
  radius : ℕ → ℝ
  spacing_pos : ∀ n, 0 < spacing n
  radius_pos : ∀ n, 0 < radius n
  ultraviolet_limit : Tendsto spacing atTop (𝓝 0)
  infinite_volume : Tendsto radius atTop atTop

def physicalGap (R : RegulatorScales) (latticeGap : ℕ → ℝ) (n : ℕ) : ℝ :=
  latticeGap n / R.spacing n

def UniformPhysicalGap (R : RegulatorScales) (latticeGap : ℕ → ℝ) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ n, Δ ≤ physicalGap R latticeGap n

theorem uniform_norm_bound_survives (c : ℕ → ℂ) (z : ℂ) (B : ℝ)
    (hc : Tendsto c atTop (𝓝 z)) (hb : ∀ n, ‖c n‖ ≤ B) : ‖z‖ ≤ B :=
  le_of_tendsto hc.norm (Filter.Eventually.of_forall hb)

theorem nonzero_witness_survives (c : ℕ → ℂ) (z : ℂ) (η : ℝ) (hη : 0 < η)
    (hc : Tendsto c atTop (𝓝 z)) (hb : ∀ n, η ≤ ‖c n‖) : z ≠ 0 := by
  have he : η ≤ ‖z‖ := ge_of_tendsto hc.norm (Filter.Eventually.of_forall hb)
  intro hz
  rw [hz, norm_zero] at he
  exact (not_le_of_gt hη) he

theorem exponential_bound_survives (c : ℕ → ℝ → ℂ) (w : ℝ → ℂ) (C Δ : ℝ)
    (hc : ∀ r, Tendsto (fun n => c n r) atTop (𝓝 (w r)))
    (hb : ∀ n r, 0 ≤ r → ‖c n r‖ ≤ C * Real.exp (-Δ * r)) :
    ∀ r, 0 ≤ r → ‖w r‖ ≤ C * Real.exp (-Δ * r) := by
  intro r hr
  exact uniform_norm_bound_survives (fun n => c n r) (w r) _ (hc r) (fun n => hb n r hr)

theorem positive_cutoff_gaps_can_close :
    ∃ gap : ℕ → ℝ, (∀ n, 0 < gap n) ∧ Tendsto gap atTop (𝓝 0) := by
  refine ⟨fun n => (1/2 : ℝ) ^ n, fun n => pow_pos (by norm_num) n, ?_⟩
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem collapsing_gap_has_no_uniform_floor (gap : ℕ → ℝ)
    (hg : Tendsto gap atTop (𝓝 0)) (Δ : ℝ) (hΔ : 0 < Δ) : ¬ ∀ n, Δ ≤ gap n := by
  intro h
  exact (not_le_of_gt hΔ) (ge_of_tendsto hg (Filter.Eventually.of_forall h))

end
end UnifiedTheory.Clay.YangMills.ContinuumControl
