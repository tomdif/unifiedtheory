/- Exact multiplication of actual cell-smeared Wilson observables is smearing
their concatenated word against the genuine Schwartz tensor product. -/
import UnifiedTheory.Clay.YangMills.SchwartzConfigurationTensor
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTensorProduct
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 PeriodicCellSampling
open SchwartzConfigurationTensor
open scoped NNReal ENNReal

theorem point_concat_left (m n : ℕ) (x : Configuration m) (y : Configuration n) (i : Fin m) :
    point (m+n) (Fin.castAdd n i) (concat m n (x,y)) = point m i x := by
  ext μ
  exact concat_left m n (x,y) i μ

theorem point_concat_right (m n : ℕ) (x : Configuration m) (y : Configuration n) (i : Fin n) :
    point (m+n) (Fin.natAdd m i) (concat m n (x,y)) = point n i y := by
  ext μ
  exact concat_right m n (x,y) i μ

theorem sample_concat_left (m n N : ℕ) (a : ℝ) (plane : Plane)
    (x : Configuration m) (y : Configuration n) (i : Fin m) :
    sampleConfiguration (m+n) N a plane (concat m n (x,y)) (Fin.castAdd n i) =
      sampleConfiguration m N a plane x i := by
  unfold sampleConfiguration
  rw [point_concat_left]

theorem sample_concat_right (m n N : ℕ) (a : ℝ) (plane : Plane)
    (x : Configuration m) (y : Configuration n) (i : Fin n) :
    sampleConfiguration (m+n) N a plane (concat m n (x,y)) (Fin.natAdd m i) =
      sampleConfiguration n N a plane y i := by
  unfold sampleConfiguration
  rw [point_concat_right]

variable (G : Type*) [Group G] (N : ℕ) [NeZero N]

theorem word_concat (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (m n : ℕ) (x : Configuration m) (y : Configuration n)
    (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.word G N χ (m+n)
      (sampleConfiguration (m+n) N a plane (concat m n (x,y))) U =
      WilsonSmearedObservable.word G N χ m (sampleConfiguration m N a plane x) U *
      WilsonSmearedObservable.word G N χ n (sampleConfiguration n N a plane y) U := by
  unfold WilsonSmearedObservable.word
  rw [Fin.prod_univ_add]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun q => WilsonMomentBounds.loopObservable (Vertex N) G χ (loops N q) U)
      (sample_concat_left m n N a plane x y i)
  · apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun q => WilsonMomentBounds.loopObservable (Vertex N) G χ (loops N q) U)
      (sample_concat_right m n N a plane x y i)

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The finite-cutoff product/tensor dictionary is proved from the volume
factorization and Fubini product integral, rather than imposed as an input. -/
theorem observable_mul (a : ℝ) (plane : Plane) (χ : G → ℂ) (m n : ℕ)
    (f : CorrelationTest m) (g : CorrelationTest n)
    (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane χ m f U *
      WilsonSmearedObservable.observable G N a plane χ n g U =
      WilsonSmearedObservable.observable G N a plane χ (m+n) (tensor m n f g) U := by
  rw [WilsonSmearedObservable.observable_integral G N a plane χ m f U,
    WilsonSmearedObservable.observable_integral G N a plane χ n g U,
    WilsonSmearedObservable.observable_integral G N a plane χ (m+n) (tensor m n f g) U,
    ← integral_prod_mul]
  rw [← integral_concat m n]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rcases z with ⟨x,y⟩
    rw [word_concat, tensor_concat]
    ring)

theorem product_expectation_eq_hierarchy (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (beta offset : ℝ)
    (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n) :
    (∫ U, WilsonSmearedObservable.observable G N a plane χ m f U *
      WilsonSmearedObservable.observable G N a plane χ n g U
        ∂wilsonLaw N G χ beta offset) =
      (WilsonCellHierarchy.hierarchy G N a plane χ hcχ B hB beta offset).correlation
        (m+n) (tensor m n f g) := by
  simp_rw [observable_mul]
  exact WilsonSmearedObservable.expectation_eq_hierarchy G N a plane χ hcχ B hB beta offset _ _

end
end UnifiedTheory.Clay.YangMills.WilsonTensorProduct
