/- A genuine common subsequence for countably many bounded correlations.
Uniform bounds and any reflection-positive kernel are inputs, not conclusions
about a continuum Yang--Mills construction. -/
import UnifiedTheory.Clay.YangMills.ContinuumControl
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CountableCorrelationCompactness
noncomputable section
open Filter
open scoped Topology BigOperators

variable {ι : Type*}

def CoordinateConvergence (c : ℕ → ι → ℂ) (w : ι → ℂ) : Prop :=
  ∀ i, Tendsto (fun k => c k i) atTop (𝓝 (w i))

theorem exists_common_subsequence [Countable ι] (c : ℕ → ι → ℂ) (B : ι → ℝ)
    (hb : ∀ k i, ‖c k i‖ ≤ B i) :
    ∃ (w : ι → ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      CoordinateConvergence (c ∘ phi) w ∧ ∀ i, ‖w i‖ ≤ B i := by
  have hc : IsCompact {w : ι → ℂ | ∀ i, w i ∈ Metric.closedBall 0 (B i)} :=
    isCompact_pi_infinite (fun i => isCompact_closedBall (0 : ℂ) (B i))
  have hm : ∀ k, c k ∈ {w : ι → ℂ | ∀ i, w i ∈ Metric.closedBall 0 (B i)} := by
    intro k i
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb k i
  obtain ⟨w, hw, phi, hphi, hconv⟩ := hc.tendsto_subseq hm
  refine ⟨w, phi, hphi, tendsto_pi_nhds.mp hconv, ?_⟩
  intro i
  simpa only [Metric.mem_closedBall, dist_zero_right] using hw i

theorem closed_constraints_survive (c : ℕ → ι → ℂ) (w : ι → ℂ)
    (hc : CoordinateConvergence c w) (C : Set (ι → ℂ)) (hC : IsClosed C)
    (hmem : ∀ k, c k ∈ C) : w ∈ C :=
  hC.mem_of_tendsto (tendsto_pi_nhds.mpr hc) (Eventually.of_forall hmem)

theorem finite_linear_relation_survives (c : ℕ → ι → ℂ) (w : ι → ℂ)
    (hc : CoordinateConvergence c w) {J : Type*} (s : Finset J)
    (index : J → ι) (a : J → ℂ) (rhs : ℂ)
    (he : ∀ k, ∑ j ∈ s, a j * c k (index j) = rhs) :
    ∑ j ∈ s, a j * w (index j) = rhs := by
  have ht : Tendsto (fun k => ∑ j ∈ s, a j * c k (index j)) atTop
      (𝓝 (∑ j ∈ s, a j * w (index j))) :=
    tendsto_finset_sum _ (fun j _ => tendsto_const_nhds.mul (hc (index j)))
  exact tendsto_nhds_unique ht (by simpa only [he] using tendsto_const_nhds)

theorem normalization_survives (c : ℕ → ι → ℂ) (w : ι → ℂ)
    (hc : CoordinateConvergence c w) (unitIndex : ι) (hn : ∀ k, c k unitIndex = 1) :
    w unitIndex = 1 :=
  tendsto_nhds_unique (hc unitIndex) (by simpa only [hn] using tendsto_const_nhds)

def gramValue {α : Type*} (pair : α → α → ι) (w : ι → ℂ)
    (n : ℕ) (index : Fin n → α) (a : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (a i) * a j * w (pair (index i) (index j))

/-- For a reflection pairing, this is precisely positivity of its finite
reflection Gram forms. The existence of that pairing and its positivity
at finite cutoff must be established separately. -/
def GramPositive {α : Type*} (pair : α → α → ι) (w : ι → ℂ) : Prop :=
  ∀ n index a, (gramValue pair w n index a).im = 0 ∧
    0 ≤ (gramValue pair w n index a).re

theorem gramValue_tendsto (c : ℕ → ι → ℂ) (w : ι → ℂ)
    (hc : CoordinateConvergence c w) {α : Type*} (pair : α → α → ι)
    (n : ℕ) (index : Fin n → α) (a : Fin n → ℂ) :
    Tendsto (fun k => gramValue pair (c k) n index a) atTop
      (𝓝 (gramValue pair w n index a)) := by
  apply tendsto_finset_sum
  intro i _
  apply tendsto_finset_sum
  intro j _
  exact tendsto_const_nhds.mul (hc (pair (index i) (index j)))

theorem gram_positive_survives (c : ℕ → ι → ℂ) (w : ι → ℂ)
    (hc : CoordinateConvergence c w) {α : Type*} (pair : α → α → ι)
    (hp : ∀ k, GramPositive pair (c k)) : GramPositive pair w := by
  intro n index a
  have ht := gramValue_tendsto c w hc pair n index a
  constructor
  · have hz : Tendsto (fun k => (gramValue pair (c k) n index a).im)
        atTop (𝓝 (0 : ℝ)) := by
      have he : (fun k => (gramValue pair (c k) n index a).im) = (fun _ : ℕ => (0 : ℝ)) :=
        funext (fun k => (hp k n index a).1)
      rw [he]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp ht) hz
  · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
      (Eventually.of_forall (fun k => (hp k n index a).2))

theorem nonzero_witness_survives (c : ℕ → ι → ℂ) (w : ι → ℂ)
    (hc : CoordinateConvergence c w) (i : ι) (eta : ℝ) (heta : 0 < eta)
    (hbound : ∀ k, eta ≤ ‖c k i‖) : w i ≠ 0 :=
  ContinuumControl.nonzero_witness_survives _ _ eta heta (hc i) hbound

theorem exists_positive_normalized_limit [Countable ι] (c : ℕ → ι → ℂ) (B : ι → ℝ)
    (hb : ∀ k i, ‖c k i‖ ≤ B i) {α : Type*} (pair : α → α → ι)
    (hp : ∀ k, GramPositive pair (c k)) (unitIndex : ι) (hn : ∀ k, c k unitIndex = 1) :
    ∃ (w : ι → ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      CoordinateConvergence (c ∘ phi) w ∧ (∀ i, ‖w i‖ ≤ B i) ∧
      GramPositive pair w ∧ w unitIndex = 1 := by
  obtain ⟨w, phi, hphi, hc, hw⟩ := exists_common_subsequence c B hb
  exact ⟨w, phi, hphi, hc, hw,
    gram_positive_survives _ w hc pair (fun k => hp (phi k)),
    normalization_survives _ w hc unitIndex (fun k => hn (phi k))⟩

end
end UnifiedTheory.Clay.YangMills.CountableCorrelationCompactness
