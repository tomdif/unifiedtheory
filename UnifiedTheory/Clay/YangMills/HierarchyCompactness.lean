/- A common regulator subsequence converging as a full Schwartz hierarchy,
conditional on uniform continuous-seminorm estimates and dense test families.
This supplies compactness, not the Yang--Mills analytic estimates. -/
import UnifiedTheory.Clay.YangMills.SeminormWeakCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.HierarchyCompactness
noncomputable section
open Filter ContinuumControl CountableCorrelationCompactness
open scoped Topology

def UniformSeminormBound (S : ℕ → Hierarchy)
    (p : ∀ n, Seminorm ℂ (CorrelationTest n)) : Prop :=
  ∀ k n f, ‖(S k).correlation n f‖ ≤ p n f

theorem exists_weak_hierarchy_subsequence (S : ℕ → Hierarchy)
    (p : ∀ n, Seminorm ℂ (CorrelationTest n)) (hp : ∀ n, Continuous (p n))
    (hb : UniformSeminormBound S p) (d : ∀ n, ℕ → CorrelationTest n)
    (hd : ∀ n, DenseRange (d n)) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧ WeakConvergence (S ∘ phi) W ∧
      ∀ n f, ‖W.correlation n f‖ ≤ p n f := by
  obtain ⟨w, phi, hphi, hc, _⟩ := exists_common_subsequence
    (fun k (i : ℕ × ℕ) => (S k).correlation i.1 (d i.1 i.2))
    (fun i => p i.1 (d i.1 i.2)) (fun k i => hb k i.1 (d i.1 i.2))
  have he (n : ℕ) : ∃ Wn : CorrelationTest n →L[ℂ] ℂ,
      (∀ f, Tendsto (fun k => (S (phi k)).correlation n f) atTop (𝓝 (Wn f))) ∧
      ∀ f, ‖Wn f‖ ≤ p n f :=
    SeminormWeakCompactness.exists_limit_of_dense_convergence
      (fun k => (S (phi k)).correlation n) (p n) (hp n) (fun k f => hb (phi k) n f)
      (d n) (hd n) (fun j => w (n, j)) (fun j => hc (n, j))
  choose W hW hbound using he
  exact ⟨⟨W⟩, phi, hphi, hW, hbound⟩

abbrev TestIndex := Σ n, CorrelationTest n

def evaluate (W : Hierarchy) (i : TestIndex) : ℂ := W.correlation i.1 i.2

theorem weak_coordinate_convergence (S : ℕ → Hierarchy) (W : Hierarchy)
    (hc : WeakConvergence S W) : CoordinateConvergence (fun k => evaluate (S k)) (evaluate W) :=
  fun i => hc i.1 i.2

theorem gram_positive_survives (S : ℕ → Hierarchy) (W : Hierarchy)
    (hc : WeakConvergence S W) {α : Type*} (pair : α → α → TestIndex)
    (hp : ∀ k, GramPositive pair (evaluate (S k))) : GramPositive pair (evaluate W) :=
  CountableCorrelationCompactness.gram_positive_survives _ _
    (weak_coordinate_convergence S W hc) pair hp

/-- The nonzero conclusion concerns only the chosen coordinate, which may even
be the unit coordinate. Nontrivial quantum fields require a separately identified
connected/centered correlation and its regulator-uniform positive lower bound. -/
theorem exists_positive_nonzero_hierarchy (S : ℕ → Hierarchy)
    (p : ∀ n, Seminorm ℂ (CorrelationTest n)) (hp : ∀ n, Continuous (p n))
    (hb : UniformSeminormBound S p) (d : ∀ n, ℕ → CorrelationTest n)
    (hd : ∀ n, DenseRange (d n)) {α : Type*} (pair : α → α → TestIndex)
    (hpos : ∀ k, GramPositive pair (evaluate (S k)))
    (unitIndex witnessIndex : TestIndex) (hn : ∀ k, evaluate (S k) unitIndex = 1)
    (eta : ℝ) (heta : 0 < eta) (hw : ∀ k, eta ≤ ‖evaluate (S k) witnessIndex‖) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧ WeakConvergence (S ∘ phi) W ∧
      (∀ n f, ‖W.correlation n f‖ ≤ p n f) ∧ GramPositive pair (evaluate W) ∧
      evaluate W unitIndex = 1 ∧ evaluate W witnessIndex ≠ 0 := by
  obtain ⟨W, phi, hphi, hc, hbound⟩ := exists_weak_hierarchy_subsequence S p hp hb d hd
  have hcoord := weak_coordinate_convergence (S ∘ phi) W hc
  exact ⟨W, phi, hphi, hc, hbound,
    gram_positive_survives (S ∘ phi) W hc pair (fun k => hpos (phi k)),
    normalization_survives _ _ hcoord unitIndex (fun k => hn (phi k)),
    CountableCorrelationCompactness.nonzero_witness_survives _ _ hcoord witnessIndex eta heta
      (fun k => hw (phi k))⟩

end
end UnifiedTheory.Clay.YangMills.HierarchyCompactness
