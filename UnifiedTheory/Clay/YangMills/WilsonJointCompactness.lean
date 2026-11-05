/- Actual bare Wilson distributional hierarchies and countable ordinary
Wilson Gram kernels converge on one common strict regulator subsequence.
The two objects are not thereby identified as smeared continuum fields. -/
import UnifiedTheory.Clay.YangMills.JointHierarchyCoordinates
import UnifiedTheory.Clay.YangMills.WilsonCellCompactness
import UnifiedTheory.Clay.YangMills.WilsonGramCompactness
import UnifiedTheory.Clay.YangMills.ConnectedGramLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonJointCompactness
noncomputable section
open Filter MeasureTheory ContinuumControl PeriodicLattice4
open CountableCorrelationCompactness ProbabilityGramCompactness
open PositiveKernelForm KernelHilbertCompletion ConnectedGramLimit
open scoped Topology NNReal ENNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ)
  (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
  (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ)

/-- Any countable bounded coordinates can be extracted together with the
actual cell-smeared hierarchy, preserving its bound and normalization. -/
theorem exists_hierarchy_coordinate_limit {ι : Type*} [Countable ι]
    (c : ℕ → ι → ℂ) (C : ι → ℝ) (hc : ∀ k i, ‖c k i‖ ≤ C i) :
    ∃ (W : Hierarchy) (w : ι → ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => WilsonCellHierarchy.hierarchy G (period (phi k)) (a (phi k))
          plane χ hχ B hB (beta (phi k)) (offset (phi k))) W ∧
      CoordinateConvergence (c ∘ phi) w ∧
      (∀ m f, ‖W.correlation m f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B ^ m) f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧ ∀ i, ‖w i‖ ≤ C i := by
  obtain ⟨W, phi, hphi, hW, hbW, hnW⟩ :=
    WilsonCellCompactness.exists_hierarchy_limit G period a plane χ hχ B hB beta offset
  obtain ⟨w, psi, hpsi, hWS, hw, hb⟩ := JointHierarchyCoordinates.exists_joint_refinement
    (fun k => WilsonCellHierarchy.hierarchy G (period (phi k)) (a (phi k))
      plane χ hχ B hB (beta (phi k)) (offset (phi k))) W hW
    (c ∘ phi) C (fun k i => hc (phi k) i)
  exact ⟨W, w, phi ∘ psi, hphi.comp hpsi, hWS, hw, hbW, hnW, hb⟩

/-- A joint limit for arbitrary countable bounded continuous observables under
the same Wilson laws. Every uniform connected variance floor survives on the
same subsequence. Positivity is ordinary probability Gram positivity. -/
theorem exists_hierarchy_gram_limit {ι : Type*} [Countable ι]
    (F : ∀ k, ι → RegulatedGauge.Configuration (Vertex (period k)) G → ℂ)
    (hF : ∀ k i, Continuous (F k i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hb : ∀ k i U, ‖F k i U‖ ≤ C i) (u : ι) (hu : ∀ k U, F k u U = 1) :
    ∃ (W : Hierarchy) (K : PositiveKernel ι) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => WilsonCellHierarchy.hierarchy G (period (phi k)) (a (phi k))
          plane χ hχ B hB (beta (phi k)) (offset (phi k))) W ∧
      CoordinateConvergence
        (fun k => kernel (wilsonLaw (period (phi k)) G χ (beta (phi k)) (offset (phi k)))
          (F (phi k))) K.value ∧
      (∀ m f, ‖W.correlation m f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B ^ m) f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      (∀ p, ‖K.value p‖ ≤ C p.1 * C p.2) ∧ K.value (u, u) = 1 ∧
      ∀ i eta, (∀ k, eta ≤ ∫ U, ‖F k i U - ∫ V, F k i V
        ∂wilsonLaw (period k) G χ (beta k) (offset k)‖ ^ 2
        ∂wilsonLaw (period k) G χ (beta k) (offset k)) →
        eta ≤ connectedVariance K u i := by
  letI : ∀ k, IsProbabilityMeasure (wilsonLaw (period k) G χ (beta k) (offset k)) :=
    fun k => wilsonLaw_probability (period k) G χ hχ (beta k) (offset k)
  let c (k : ℕ) := kernel (wilsonLaw (period k) G χ (beta k) (offset k)) (F k)
  obtain ⟨W, w, phi, hphi, hW, hc, hbW, hnW, hbw⟩ :=
    exists_hierarchy_coordinate_limit G period a plane χ hχ B hB beta offset c
      (fun p => C p.1 * C p.2)
      (fun k p => kernel_bound _ (F k) C hC (hb k) p)
  have hp : GramPositive (fun i j => (i, j)) w :=
    gram_positive_survives _ w hc _ (fun k => kernel_positive _ (F (phi k)) (hF (phi k)))
  let K : PositiveKernel ι := ⟨w, hp⟩
  have hn : K.value (u, u) = 1 := normalization_survives _ w hc (u, u)
    (fun k => kernel_normalized _ (F (phi k)) u (hu (phi k)))
  refine ⟨W, K, phi, hphi, hW, hc, hbW, hnW, hbw, hn, ?_⟩
  intro i eta hv
  apply connected_floor_survives _ w hc u i eta
  intro k
  change eta ≤ (kernel (wilsonLaw (period (phi k)) G χ (beta (phi k)) (offset (phi k)))
    (F (phi k)) (i, i) -
    kernel (wilsonLaw (period (phi k)) G χ (beta (phi k)) (offset (phi k)))
      (F (phi k)) (i, u) *
    kernel (wilsonLaw (period (phi k)) G χ (beta (phi k)) (offset (phi k)))
      (F (phi k)) (u, i)).re
  rw [← gram_variance_identity
    (wilsonLaw (period (phi k)) G χ (beta (phi k)) (offset (phi k)))
    (F (phi k)) (hF (phi k)) u i (hu (phi k))]
  exact hv (phi k)

/-- All countably many bounded Wilson-loop words have a positive normalized
Gram limit on the exact subsequence used by the bare Schwartz hierarchy. -/
theorem exists_hierarchy_wilson_word_limit {ι : Type*} [Countable ι]
    (order : ι → ℕ)
    (base : ∀ k i, Fin (order i) → Quiver.Symmetrify (Vertex (period k)))
    (loops : ∀ k i j, Quiver.Path (base k i j) (base k i j))
    (u : ι) (hu : order u = 0) :
    ∃ (W : Hierarchy) (K : PositiveKernel ι) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => WilsonCellHierarchy.hierarchy G (period (phi k)) (a (phi k))
          plane χ hχ B hB (beta (phi k)) (offset (phi k))) W ∧
      CoordinateConvergence
        (WilsonGramCompactness.gramCorrelation G period beta offset χ order base loops ∘ phi)
        K.value ∧
      (∀ m f, ‖W.correlation m f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B ^ m) f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      (∀ p, ‖K.value p‖ ≤ (B : ℝ) ^ (order p.1 + order p.2)) ∧ K.value (u, u) = 1 := by
  have hn (k : ℕ) (U : RegulatedGauge.Configuration (Vertex (period k)) G) :
      WilsonGramCompactness.wordProduct G period χ order base loops k u U = 1 := by
    have hz : IsEmpty (Fin (order u)) := by rw [hu]; infer_instance
    letI := hz
    simp [WilsonGramCompactness.wordProduct]
  obtain ⟨W, K, phi, hphi, hW, hc, hbW, hnW, hbK, hnK, _⟩ :=
    exists_hierarchy_gram_limit G period a plane χ hχ B hB beta offset
      (WilsonGramCompactness.wordProduct G period χ order base loops)
      (WilsonGramCompactness.wordProduct_continuous G period χ order base loops hχ)
      (fun i => (B : ℝ) ^ order i) (fun i => pow_nonneg B.coe_nonneg _)
      (WilsonGramCompactness.wordProduct_bound G period χ order base loops B B.coe_nonneg hB)
      u hn
  exact ⟨W, K, phi, hphi, hW, hc, hbW, hnW,
    fun p => by simpa only [pow_add] using hbK p, hnK⟩

end
end UnifiedTheory.Clay.YangMills.WilsonJointCompactness
