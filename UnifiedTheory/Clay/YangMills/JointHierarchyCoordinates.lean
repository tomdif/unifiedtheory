/- A single subsequence for an all-orders distributional hierarchy and a
countable family of bounded coordinates. This gives compatible regulator
indices, not an identification of the two limiting objects. -/
import UnifiedTheory.Clay.YangMills.L1HierarchyCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.JointHierarchyCoordinates
noncomputable section
open Filter MeasureTheory ContinuumControl CountableCorrelationCompactness L1HierarchyCompactness
open scoped Topology NNReal ENNReal

theorem weakConvergence_subsequence (S : ℕ → Hierarchy) (W : Hierarchy)
    (hS : WeakConvergence S W) (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    WeakConvergence (S ∘ phi) W :=
  fun n f => (hS n f).comp hphi.tendsto_atTop

theorem coordinateConvergence_subsequence {ι : Type*} (c : ℕ → ι → ℂ) (w : ι → ℂ)
    (hc : CoordinateConvergence c w) (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    CoordinateConvergence (c ∘ phi) w :=
  fun i => (hc i).comp hphi.tendsto_atTop

/-- Extract additional bounded coordinates without changing an already
convergent hierarchy limit. -/
theorem exists_joint_refinement {ι : Type*} [Countable ι]
    (S : ℕ → Hierarchy) (W : Hierarchy) (hS : WeakConvergence S W)
    (c : ℕ → ι → ℂ) (C : ι → ℝ) (hc : ∀ k i, ‖c k i‖ ≤ C i) :
    ∃ (w : ι → ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence (S ∘ phi) W ∧ CoordinateConvergence (c ∘ phi) w ∧
      ∀ i, ‖w i‖ ≤ C i := by
  obtain ⟨w, phi, hphi, hw, hb⟩ := exists_common_subsequence c C hc
  exact ⟨w, phi, hphi, weakConvergence_subsequence S W hS phi hphi, hw, hb⟩

/-- Simultaneous all-orders L1 weak-* convergence and countable coordinate
convergence, with both limits taken on the displayed same strict subsequence. -/
theorem exists_l1_joint_limit {ι : Type*} [Countable ι]
    (F : (n : ℕ) → ℕ → L1Test n →L[ℂ] ℂ)
    (B : ℕ → ℝ≥0) (hB : ∀ n k, ‖F n k‖ ≤ B n)
    (c : ℕ → ι → ℂ) (C : ι → ℝ) (hc : ∀ k i, ‖c k i‖ ≤ C i) :
    ∃ (W : (n : ℕ) → L1Test n →L[ℂ] ℂ) (w : ι → ℂ) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ n x, Tendsto (fun k => F n (phi k) x) atTop (𝓝 (W n x))) ∧
      WeakConvergence (fun k => hierarchyOfL1 (fun n => F n (phi k))) (hierarchyOfL1 W) ∧
      CoordinateConvergence (c ∘ phi) w ∧ (∀ n, ‖W n‖ ≤ B n) ∧ ∀ i, ‖w i‖ ≤ C i := by
  obtain ⟨W, phi, hphi, hL1, hW, hbW⟩ := exists_l1_hierarchy_subsequence F B hB
  obtain ⟨w, psi, hpsi, hWS, hw, hbw⟩ := exists_joint_refinement
    (fun k => hierarchyOfL1 (fun n => F n (phi k))) (hierarchyOfL1 W) hW
    (c ∘ phi) C (fun k i => hc (phi k) i)
  exact ⟨W, w, phi ∘ psi, hphi.comp hpsi,
    fun n x => (hL1 n x).comp hpsi.tendsto_atTop, hWS, hw, hbW, hbw⟩

/-- Bounded measurable kernels and arbitrary bounded countable coordinates
admit a common subsequence; no dense Schwartz family is an input. -/
theorem exists_bounded_kernel_joint_limit {ι : Type*} [Countable ι]
    (K : (n : ℕ) → ℕ → Configuration n → ℂ)
    (hK : ∀ n k, Measurable (K n k)) (B : ℕ → ℝ≥0)
    (hB : ∀ n k x, ‖K n k x‖ ≤ B n)
    (c : ℕ → ι → ℂ) (C : ι → ℝ) (hc : ∀ k i, ‖c k i‖ ≤ C i) :
    ∃ (W : Hierarchy) (w : ι → ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => kernelHierarchy (fun n => K n (phi k))
          (fun n => hK n (phi k)) B (fun n => hB n (phi k))) W ∧
      CoordinateConvergence (c ∘ phi) w ∧
      (∀ n f, ‖W.correlation n f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B n) f) ∧ ∀ i, ‖w i‖ ≤ C i := by
  obtain ⟨W, phi, hphi, hW, hbW⟩ := exists_bounded_kernel_hierarchy_limit K hK B hB
  obtain ⟨w, psi, hpsi, hWS, hw, hbw⟩ := exists_joint_refinement
    (fun k => kernelHierarchy (fun n => K n (phi k))
      (fun n => hK n (phi k)) B (fun n => hB n (phi k))) W hW
    (c ∘ phi) C (fun k i => hc (phi k) i)
  exact ⟨W, w, phi ∘ psi, hphi.comp hpsi, hWS, hw, hbW, hbw⟩

end
end UnifiedTheory.Clay.YangMills.JointHierarchyCoordinates
