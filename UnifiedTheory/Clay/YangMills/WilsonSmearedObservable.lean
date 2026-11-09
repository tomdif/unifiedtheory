/- Cell-smeared Wilson tests are actual continuous configuration observables.
Their expectations are exactly the previously constructed bare hierarchy. -/
import UnifiedTheory.Clay.YangMills.FiniteCellSmearing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSmearedObservable
noncomputable section
open MeasureTheory PeriodicLattice4 WilsonMomentBounds ContinuumControl
open scoped NNReal ENNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)

def word (m : ℕ) (q : Fin m → PlaquetteIndex N)
    (U : RegulatedGauge.Configuration (Vertex N) G) : ℂ :=
  ∏ j, loopObservable (Vertex N) G χ (loops N (q j)) U

theorem word_continuous (hcχ : Continuous χ) (m : ℕ) (q : Fin m → PlaquetteIndex N) :
    Continuous (word G N χ m q) :=
  continuous_finset_prod _ (fun j _ => loopObservable_continuous _ G χ hcχ (loops N (q j)))

theorem word_bound (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (m : ℕ)
    (q : Fin m → PlaquetteIndex N) (U : RegulatedGauge.Configuration (Vertex N) G) :
    ‖word G N χ m q U‖ ≤ (B : ℝ) ^ m := by
  unfold word
  rw [norm_prod]
  exact (Finset.prod_le_prod (fun j _ => norm_nonneg _)
    (fun j _ => loopObservable_bound _ G χ B hB (loops N (q j)) U)).trans (by simp)

def cellCoefficient (m : ℕ) (q : Fin m → PlaquetteIndex N) (f : CorrelationTest m) : ℂ :=
  FiniteCellSmearing.coefficient volume (PeriodicCellSampling.sampleConfiguration m N a plane) q f

def observable (m : ℕ) (f : CorrelationTest m)
    (U : RegulatedGauge.Configuration (Vertex N) G) : ℂ :=
  FiniteCellSmearing.observable volume (PeriodicCellSampling.sampleConfiguration m N a plane)
    (word G N χ m) f U

theorem observable_continuous (hcχ : Continuous χ) (m : ℕ) (f : CorrelationTest m) :
    Continuous (observable G N a plane χ m f) :=
  FiniteCellSmearing.observable_continuous _ _ _ (word_continuous G N χ hcχ m) f

theorem observable_integral (m : ℕ) (f : CorrelationTest m)
    (U : RegulatedGauge.Configuration (Vertex N) G) :
    observable G N a plane χ m f U =
      ∫ x, word G N χ m (PeriodicCellSampling.sampleConfiguration m N a plane x) U * f x :=
  FiniteCellSmearing.observable_integral _ _
    (PeriodicCellSampling.sampleConfiguration_measurable m N a plane) _ f f.integrable U

theorem observable_bound (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B)
    (m : ℕ) (f : CorrelationTest m) (U : RegulatedGauge.Configuration (Vertex N) G) :
    ‖observable G N a plane χ m f U‖ ≤
      BoundedKernelDistribution.boundSeminorm volume (B ^ m) f := by
  have h := FiniteCellSmearing.observable_bound volume _
    (PeriodicCellSampling.sampleConfiguration_measurable m N a plane)
    (word G N χ m) ((B : ℝ) ^ m) (word_bound G N χ B hB m) f f.integrable U
  change ‖observable G N a plane χ m f U‖ ≤ (B ^ m : ℝ≥0) *
    BoundedKernelDistribution.l1Seminorm volume f
  simpa only [BoundedKernelDistribution.l1Seminorm_apply, NNReal.coe_pow] using h

/-- This is an exact dictionary, not a hypothesis identifying two unrelated limits. -/
theorem expectation_eq_hierarchy (hcχ : Continuous χ) (B : ℝ≥0)
    (hB : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ) (m : ℕ) (f : CorrelationTest m) :
    (∫ U, observable G N a plane χ m f U ∂wilsonLaw N G χ β c) =
      (WilsonCellHierarchy.hierarchy G N a plane χ hcχ B hB β c).correlation m f := by
  letI := wilsonLaw_probability N G χ hcχ β c
  exact FiniteCellSmearing.expectation_identity volume _
    (PeriodicCellSampling.sampleConfiguration_measurable m N a plane)
    (wilsonLaw N G χ β c) (word G N χ m) (word_continuous G N χ hcχ m) f f.integrable

end
end UnifiedTheory.Clay.YangMills.WilsonSmearedObservable
