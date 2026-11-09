/- Sequential weak compactness from a proved continuous seminorm bound.
The bound is uniform in the regulator and a countable dense test family is
required; neither analytic input is asserted for Yang--Mills here. -/
import UnifiedTheory.Clay.YangMills.CountableCorrelationCompactness
import Mathlib.Analysis.Seminorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SeminormWeakCompactness
noncomputable section
open Filter
open scoped Topology

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℂ E] [ContinuousSMul ℂ E]

theorem dense_seminorm_approximation (p : Seminorm ℂ E) (hp : Continuous p)
    (d : ℕ → E) (hd : DenseRange d) (x : E) (eps : ℝ) (heps : 0 < eps) :
    ∃ j, p (x - d j) < eps := by
  have ho : IsOpen {y : E | p (x - y) < eps} :=
    isOpen_lt (hp.comp (continuous_const.sub continuous_id)) continuous_const
  exact hd.exists_mem_open ho ⟨x, by simpa using heps⟩

theorem cauchy_from_dense_convergence (F : ℕ → E →L[ℂ] ℂ)
    (p : Seminorm ℂ E) (hp : Continuous p) (hb : ∀ k x, ‖F k x‖ ≤ p x)
    (d : ℕ → E) (hd : DenseRange d) (w : ℕ → ℂ)
    (hc : ∀ j, Tendsto (fun k => F k (d j)) atTop (𝓝 (w j))) (x : E) :
    CauchySeq (fun k => F k x) := by
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  obtain ⟨j, hj⟩ := dense_seminorm_approximation p hp d hd x (eps / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hc j).cauchySeq (eps / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have he (k : ℕ) : dist (F k x) (F k (d j)) ≤ p (x - d j) := by
    rw [dist_eq_norm, ← map_sub]
    exact hb k _
  have ht : dist (F m x) (F n x) ≤ dist (F m x) (F m (d j)) +
      (dist (F m (d j)) (F n (d j)) + dist (F n (d j)) (F n x)) :=
    by simpa only [add_assoc] using
      dist_triangle4 (F m x) (F m (d j)) (F n (d j)) (F n x)
  have her : dist (F n (d j)) (F n x) ≤ p (x - d j) := by
    rw [dist_comm]
    exact he n
  have hmiddle := hN m hm n hn
  linarith [he m]

theorem continuous_of_seminorm_bound (L : E →ₗ[ℂ] ℂ) (p : Seminorm ℂ E)
    (hp : Continuous p) (hb : ∀ x, ‖L x‖ ≤ p x) : Continuous L := by
  apply continuous_of_continuousAt_zero L
  change Tendsto L (𝓝 0) (𝓝 (L 0))
  rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun x => norm_nonneg _) hb
  simpa using hp.tendsto 0

theorem exists_limit_of_dense_convergence (F : ℕ → E →L[ℂ] ℂ)
    (p : Seminorm ℂ E) (hp : Continuous p) (hb : ∀ k x, ‖F k x‖ ≤ p x)
    (d : ℕ → E) (hd : DenseRange d) (w : ℕ → ℂ)
    (hc : ∀ j, Tendsto (fun k => F k (d j)) atTop (𝓝 (w j))) :
    ∃ W : E →L[ℂ] ℂ, (∀ x, Tendsto (fun k => F k x) atTop (𝓝 (W x))) ∧
      ∀ x, ‖W x‖ ≤ p x := by
  have he (x : E) : ∃ z : ℂ, Tendsto (fun k => F k x) atTop (𝓝 z) :=
    cauchySeq_tendsto_of_complete (cauchy_from_dense_convergence F p hp hb d hd w hc x)
  choose z hz using he
  let L : E →ₗ[ℂ] ℂ :=
    { toFun := z
      map_add' := by
        intro x y
        exact tendsto_nhds_unique (by simpa only [map_add] using hz (x + y))
          ((hz x).add (hz y))
      map_smul' := by
        intro a x
        exact tendsto_nhds_unique (by simpa only [map_smul] using hz (a • x))
          (tendsto_const_nhds.smul (hz x)) }
  have hbound (x : E) : ‖L x‖ ≤ p x :=
    le_of_tendsto (hz x).norm (Eventually.of_forall (fun k => hb k x))
  exact ⟨⟨L, continuous_of_seminorm_bound L p hp hbound⟩, hz, hbound⟩

theorem exists_weak_subsequence (F : ℕ → E →L[ℂ] ℂ)
    (p : Seminorm ℂ E) (hp : Continuous p) (hb : ∀ k x, ‖F k x‖ ≤ p x)
    (d : ℕ → E) (hd : DenseRange d) :
    ∃ (W : E →L[ℂ] ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      (∀ x, Tendsto (fun k => F (phi k) x) atTop (𝓝 (W x))) ∧ ∀ x, ‖W x‖ ≤ p x := by
  obtain ⟨w, phi, hphi, hc, _⟩ := CountableCorrelationCompactness.exists_common_subsequence
    (fun k j => F k (d j)) (fun j => p (d j)) (fun k j => hb k (d j))
  obtain ⟨W, hW, hbound⟩ := exists_limit_of_dense_convergence (F ∘ phi) p hp
    (fun k x => hb (phi k) x) d hd w hc
  exact ⟨W, phi, hphi, hW, hbound⟩

end
end UnifiedTheory.Clay.YangMills.SeminormWeakCompactness
