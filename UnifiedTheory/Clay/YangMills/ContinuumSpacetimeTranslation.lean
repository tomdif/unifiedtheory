/- All four Euclidean translation directions are symmetries of the actual
bare limiting Wilson hierarchy. This does not prove rotation covariance,
Poincare reconstruction, nontriviality, or a physical spectral gap. -/
import UnifiedTheory.Clay.YangMills.CellSpacetimeTranslation
import UnifiedTheory.Clay.YangMills.ContinuumTimeTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ContinuumSpacetimeTranslation
noncomputable section
open Filter MeasureTheory ContinuumControl PeriodicLattice4 LocalFields
open CellSpacetimeTranslation SchwartzTranslations
open scoped Topology NNReal

def latticeApproximation (a : ℝ) (v : Spacetime) : Spacetime :=
  cellVector a (fun μ => ⌊v μ / a⌋)

theorem latticeApproximation_tendsto (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k)
    (ha : Tendsto a atTop (𝓝 0)) (v : Spacetime) :
    Tendsto (fun k => latticeApproximation (a k) v) atTop (𝓝 v) := by
  have hc : Tendsto (fun k μ => ContinuumTimeTranslation.cellTime (a k) (v μ))
      atTop (𝓝 (fun μ => v μ)) :=
    tendsto_pi_nhds.mpr (fun μ =>
      ContinuumTimeTranslation.cellTime_tendsto a hpos ha (v μ))
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).tendsto (fun μ => v μ)).comp hc

theorem displacement_continuous (m : ℕ) : Continuous (displacement m) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun jμ => PiLp.continuous_apply 2 _ jμ.2))

theorem translated_tests_tendsto (m : ℕ) (f : CorrelationTest m)
    (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 0)) (v : Spacetime) :
    Tendsto (fun k => translationCLM (displacement m (latticeApproximation (a k) v)) f)
      atTop (𝓝 (translationCLM (displacement m v) f)) :=
  ((continuous_translation_tests f).tendsto (displacement m v)).comp
    (((displacement_continuous m).tendsto v).comp
      (latticeApproximation_tendsto a hpos ha v))

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem hierarchy_spacetime_translation
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ)
    (hpos : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 0))
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ) (B : ℝ≥0)
    (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ) (W : Hierarchy)
    (hW : WeakConvergence
      (fun k => WilsonCellHierarchy.hierarchy G (N k) (a k) plane χ hcχ B hB
        (beta k) (offset k)) W)
    (m : ℕ) (v : Spacetime) (f : CorrelationTest m) :
    W.correlation m (translationCLM (displacement m v) f) = W.correlation m f := by
  let S : ℕ → Hierarchy := fun k =>
    WilsonCellHierarchy.hierarchy G (N k) (a k) plane χ hcχ B hB (beta k) (offset k)
  have hm := MovingTestLimit.hierarchy_moving_limit S W hW
    (fun j => BoundedKernelDistribution.boundSeminorm volume (B ^ j))
    (fun j => BoundedKernelDistribution.boundSeminorm_continuous volume (B ^ j))
    (fun k j g => WilsonCellHierarchy.hierarchy_uniform_bound
      G (N k) (a k) plane χ hcχ B hB (beta k) (offset k) j g)
    m (translationCLM (displacement m v) f)
    (fun k => translationCLM (displacement m (latticeApproximation (a k) v)) f)
    (translated_tests_tendsto m f a hpos ha v)
  have he (k : ℕ) : (S k).correlation m
      (translationCLM (displacement m (latticeApproximation (a k) v)) f) =
      (S k).correlation m f :=
    hierarchy_translation G (N k) χ hcχ B hB (beta k) (offset k) m (a k)
      (ne_of_gt (hpos k)) plane (fun μ => ⌊v μ / a k⌋) f
  simp_rw [he] at hm
  exact tendsto_nhds_unique hm (hW m f)

end
end UnifiedTheory.Clay.YangMills.ContinuumSpacetimeTranslation
