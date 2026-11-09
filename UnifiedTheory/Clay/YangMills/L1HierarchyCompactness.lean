/- Simultaneous weak compactness for uniformly bounded functionals on
countably many separable normed spaces. For Schwartz hierarchies dominated by
L1 bounds, separability of L1 supplies the dense sequence internally. -/
import UnifiedTheory.Clay.YangMills.BoundedKernelL1
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.L1HierarchyCompactness
noncomputable section
open MeasureTheory Filter TopologicalSpace ContinuumControl
open scoped Topology NNReal ENNReal

section SeparableSpaces
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
  [∀ n, SeparableSpace (E n)]

/-- One subsequence works for every vector in every space. No dense family
is supplied as a hypothesis: separability constructs one for each order. -/
theorem exists_common_weak_subsequence (F : (n : ℕ) → ℕ → E n →L[ℂ] ℂ)
    (B : ℕ → ℝ≥0) (hb : ∀ n k, ‖F n k‖ ≤ B n) :
    ∃ (W : (n : ℕ) → E n →L[ℂ] ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      (∀ n x, Tendsto (fun k => F n (phi k) x) atTop (𝓝 (W n x))) ∧
      ∀ n, ‖W n‖ ≤ B n := by
  let d (n : ℕ) : ℕ → E n := denseSeq (E n)
  have hd (n : ℕ) : DenseRange (d n) := denseRange_denseSeq (E n)
  let p (n : ℕ) : Seminorm ℂ (E n) := B n • normSeminorm ℂ (E n)
  have hp (n : ℕ) : Continuous (p n) := continuous_const.mul continuous_norm
  have hpb (n k : ℕ) (x : E n) : ‖F n k x‖ ≤ p n x := by
    change ‖F n k x‖ ≤ (B n : ℝ) * ‖x‖
    exact (F n k).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hb n k) (norm_nonneg x))
  obtain ⟨w, phi, hphi, hc, _⟩ := CountableCorrelationCompactness.exists_common_subsequence
    (fun k (i : ℕ × ℕ) => F i.1 k (d i.1 i.2))
    (fun i => p i.1 (d i.1 i.2)) (fun k i => hpb i.1 k (d i.1 i.2))
  have he (n : ℕ) : ∃ W : E n →L[ℂ] ℂ,
      (∀ x, Tendsto (fun k => F n (phi k) x) atTop (𝓝 (W x))) ∧
      ∀ x, ‖W x‖ ≤ p n x := by
    apply SeminormWeakCompactness.exists_limit_of_dense_convergence
      (fun k => F n (phi k)) (p n) (hp n) (fun k x => hpb n (phi k) x)
      (d n) (hd n) (fun j => w (n, j))
    intro j
    exact hc (n, j)
  choose W hW hWb using he
  refine ⟨W, phi, hphi, hW, fun n => ?_⟩
  exact (W n).opNorm_le_bound (B n).coe_nonneg (hWb n)
end SeparableSpaces

abbrev L1Test (n : ℕ) : Type := Lp ℂ 1 (volume : Measure (Configuration n))

def hierarchyOfL1 (F : (n : ℕ) → L1Test n →L[ℂ] ℂ) : Hierarchy where
  correlation n := (F n).comp (SchwartzMap.toLpCLM ℂ ℂ 1 volume)

theorem hierarchyOfL1_bound (F : (n : ℕ) → L1Test n →L[ℂ] ℂ)
    (B : ℕ → ℝ≥0) (hb : ∀ n, ‖F n‖ ≤ B n) (n : ℕ) (f : CorrelationTest n) :
    ‖(hierarchyOfL1 F).correlation n f‖ ≤
      BoundedKernelDistribution.boundSeminorm volume (B n) f := by
  change ‖F n (f.toLp 1 volume)‖ ≤ (B n : ℝ) * ‖f.toLp 1 volume‖
  exact (F n).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))

theorem exists_l1_hierarchy_subsequence (F : (n : ℕ) → ℕ → L1Test n →L[ℂ] ℂ)
    (B : ℕ → ℝ≥0) (hb : ∀ n k, ‖F n k‖ ≤ B n) :
    ∃ (W : (n : ℕ) → L1Test n →L[ℂ] ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      (∀ n x, Tendsto (fun k => F n (phi k) x) atTop (𝓝 (W n x))) ∧
      WeakConvergence (fun k => hierarchyOfL1 (fun n => F n (phi k))) (hierarchyOfL1 W) ∧
      ∀ n, ‖W n‖ ≤ B n := by
  letI : Fact ((1 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  obtain ⟨W, phi, hphi, hW, hbW⟩ := exists_common_weak_subsequence L1Test F B hb
  exact ⟨W, phi, hphi, hW, fun n f => hW n (f.toLp 1 volume), hbW⟩

/-- The actual bounded-kernel hierarchy, with the kernel interpreted in the
ordinary Bochner integral against each Schwartz test. -/
def kernelHierarchy (K : (n : ℕ) → Configuration n → ℂ)
    (hK : ∀ n, Measurable (K n)) (B : ℕ → ℝ≥0) (hb : ∀ n x, ‖K n x‖ ≤ B n) :
    Hierarchy where
  correlation n := BoundedKernelDistribution.functional volume (K n) (hK n) (B n) (hb n)

theorem kernelHierarchy_eq_l1 (K : (n : ℕ) → Configuration n → ℂ)
    (hK : ∀ n, Measurable (K n)) (B : ℕ → ℝ≥0) (hb : ∀ n x, ‖K n x‖ ≤ B n) :
    kernelHierarchy K hK B hb = hierarchyOfL1
      (fun n => BoundedKernelL1.functional volume (K n) (hK n) (B n) (hb n)) := by
  unfold kernelHierarchy hierarchyOfL1
  congr 1
  funext n
  exact (BoundedKernelL1.functional_comp_toLp volume (K n) (hK n) (B n) (hb n)).symm

/-- Uniform measurable kernel bounds suffice for a common subsequential
tempered hierarchy limit at all orders and for every Schwartz test. -/
theorem exists_bounded_kernel_hierarchy_limit
    (K : (n : ℕ) → ℕ → Configuration n → ℂ)
    (hK : ∀ n k, Measurable (K n k)) (B : ℕ → ℝ≥0)
    (hb : ∀ n k x, ‖K n k x‖ ≤ B n) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => kernelHierarchy (fun n => K n (phi k))
          (fun n => hK n (phi k)) B (fun n => hb n (phi k))) W ∧
      ∀ n f, ‖W.correlation n f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B n) f := by
  let F (n k : ℕ) : L1Test n →L[ℂ] ℂ :=
    BoundedKernelL1.functional volume (K n k) (hK n k) (B n) (hb n k)
  have hbF (n k : ℕ) : ‖F n k‖ ≤ B n :=
    BoundedKernelL1.functional_norm_le volume (K n k) (hK n k) (B n) (hb n k)
  obtain ⟨W, phi, hphi, _, hc, hW⟩ := exists_l1_hierarchy_subsequence F B hbF
  refine ⟨hierarchyOfL1 W, phi, hphi, ?_, hierarchyOfL1_bound W B hW⟩
  intro n f
  simpa only [kernelHierarchy_eq_l1] using hc n f

end
end UnifiedTheory.Clay.YangMills.L1HierarchyCompactness
