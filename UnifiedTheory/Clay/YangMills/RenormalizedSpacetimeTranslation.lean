/- All four translation identities for action-preserving renormalized Wilson
hierarchies. Uniform continuous seminorm estimates, not bare L1 bounds, control
the moving tests. The limit may be along any nontrivial filter refining atTop. -/
import UnifiedTheory.Clay.YangMills.RenormalizedWilsonUltrafilter
import UnifiedTheory.Clay.YangMills.ContinuumSpacetimeTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RenormalizedSpacetimeTranslation
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 LocalFields
open CellSpacetimeTranslation SchwartzTranslations PeriodicSpacetimeTranslation
open UltrafilterHierarchyCompactness
open scoped Topology NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The observable character and action character are independent. -/
theorem expectation_translation (N : ℕ) [NeZero N] (ψ χ : G → ℂ)
    (hcχ : Continuous χ) (beta offset : ℝ) (m : ℕ) (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (k : Fin 4 → ℤ) (f : CorrelationTest m) :
    (∫ U, WilsonSmearedObservable.observable G N a plane ψ m
      (translationCLM (displacement m (cellVector a k)) f) U
        ∂wilsonLaw N G χ beta offset) =
      ∫ U, WilsonSmearedObservable.observable G N a plane ψ m f U
        ∂wilsonLaw N G χ beta offset := by
  simp_rw [observable_translation G N ψ m a ha plane k f]
  exact (wilsonLaw_preserves_shift N G χ hcχ beta offset (integerVertex N k)).integral_comp
    (configurationShiftMeasurableEquiv N G (integerVertex N k)).measurableEmbedding _

theorem hierarchy_translation (N : ℕ) [NeZero N] (ψ χ : G → ℂ)
    (hcψ : Continuous ψ) (hcχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) (m : ℕ) (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (k : Fin 4 → ℤ) (f : CorrelationTest m) :
    (RenormalizedWilsonHierarchy.hierarchy G N a plane ψ χ hcχ B hB beta offset).correlation m (translationCLM (displacement m (cellVector a k)) f) =
    (RenormalizedWilsonHierarchy.hierarchy G N a plane ψ χ hcχ B hB beta offset).correlation m f := by
  rw [← RenormalizedWilsonHierarchy.expectation_eq_hierarchy G N a plane ψ χ hcψ,
    ← RenormalizedWilsonHierarchy.expectation_eq_hierarchy G N a plane ψ χ hcψ]
  exact expectation_translation G N ψ χ hcχ beta offset m a ha plane k f

/-- One actual weak limit inherits every real spacetime translation even
when the observable normalization depends on the regulator and diverges. -/
theorem limit_translation
    (l : Filter ℕ) [NeBot l] (hle : l ≤ atTop)
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0)) (plane : Plane)
    (ψ : ℕ → G → ℂ) (hcψ : ∀ k, Continuous (ψ k))
    (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℕ → ℝ≥0) (hB : ∀ k g, ‖ψ k g‖ ≤ B k) (beta offset : ℕ → ℝ)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hb : ∀ k m f, ‖(RenormalizedWilsonHierarchy.realHierarchy G (N k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation m f‖ ≤ p m f)
    (W : Hierarchy)
    (hW : WeakAlong l (fun k => RenormalizedWilsonHierarchy.realHierarchy G (N k) (a k)
      plane (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)) W)
    (m : ℕ) (v : Spacetime) (f : CorrelationTest m) :
    W.correlation m (translationCLM (displacement m v) f) = W.correlation m f := by
  let S := fun k => RenormalizedWilsonHierarchy.realHierarchy G (N k) (a k) plane
    (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)
  have hm := moving_test_limit l (fun k => (S k).correlation m) (p m) (hp m)
    (fun k f => hb k m f) (translationCLM (displacement m v) f)
    (fun k => translationCLM (displacement m
      (ContinuumSpacetimeTranslation.latticeApproximation (a k) v)) f)
    ((ContinuumSpacetimeTranslation.translated_tests_tendsto m f a ha ha0 v).mono_left hle)
    _ (hW m _)
  have he (k : ℕ) : (S k).correlation m
      (translationCLM (displacement m
        (ContinuumSpacetimeTranslation.latticeApproximation (a k) v)) f) =
      (S k).correlation m f :=
    hierarchy_translation G (N k) (CellReflectionCovariance.realPartCharacter G (ψ k)) χ
      (WilsonReflectedTensor.realPart_continuous G (ψ k) (hcψ k)) hcχ (B k)
      (WilsonReflectedTensor.realPart_bound G (ψ k) (B k) (hB k)) (beta k) (offset k)
      m (a k) (ha k).ne' plane (fun μ => ⌊v μ / a k⌋) f
  simp_rw [he] at hm
  exact tendsto_nhds_unique hm (hW m f)

end
end UnifiedTheory.Clay.YangMills.RenormalizedSpacetimeTranslation
