/- Cell-smeared bare Wilson correlations as an actual tempered hierarchy.
The uniform bounds concern bounded unrenormalized plaquette observables only. -/
import UnifiedTheory.Clay.YangMills.PeriodicCellSampling
import UnifiedTheory.Clay.YangMills.WilsonMomentBounds
import UnifiedTheory.Clay.YangMills.BoundedKernelDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCellHierarchy
noncomputable section
open MeasureTheory PeriodicLattice4 WilsonMomentBounds ContinuumControl
open scoped NNReal ENNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- An actual moment of the periodic Wilson probability measure. -/
def coefficient (N : ℕ) [NeZero N] (χ : G → ℂ) (β c : ℝ) (m : ℕ)
    (q : Fin m → PlaquetteIndex N) : ℂ :=
  moment (wilsonLaw N G χ β c) Finset.univ
    (fun j => loopObservable (Vertex N) G χ (loops N (q j)))

theorem coefficient_bound (N : ℕ) [NeZero N] (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ) (m : ℕ)
    (q : Fin m → PlaquetteIndex N) : ‖coefficient G N χ β c m q‖ ≤ (B : ℝ) ^ m := by
  simpa only [coefficient, Finset.card_univ, Fintype.card_fin] using
    wilson_moment_bound (Vertex N) G χ hcχ B B.coe_nonneg hB
      (base N) (loops N) β c Finset.univ (fun j => base N (q j))
      (fun j => loops N (q j))

def kernel (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (β c : ℝ) (m : ℕ) (x : Configuration m) : ℂ :=
  coefficient G N χ β c m (PeriodicCellSampling.sampleConfiguration m N a plane x)

theorem kernel_measurable (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (β c : ℝ) (m : ℕ) : Measurable (kernel G N a plane χ β c m) :=
  (measurable_of_countable (coefficient G N χ β c m)).comp
    (PeriodicCellSampling.sampleConfiguration_measurable m N a plane)

theorem kernel_bound (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (m : ℕ) (x : Configuration m) :
    ‖kernel G N a plane χ β c m x‖ ≤ (B : ℝ) ^ m :=
  coefficient_bound G N χ hcχ B hB β c m _

def hierarchy (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ) : Hierarchy where
  correlation m := BoundedKernelDistribution.functional volume (kernel G N a plane χ β c m)
    (kernel_measurable G N a plane χ β c m) (B ^ m)
    (by simpa only [NNReal.coe_pow] using kernel_bound G N a plane χ hcχ B hB β c m)

theorem hierarchy_apply (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (m : ℕ) (f : CorrelationTest m) :
    (hierarchy G N a plane χ hcχ B hB β c).correlation m f =
      ∫ x, kernel G N a plane χ β c m x * f x := rfl

/-- The same continuous Schwartz seminorm bounds every lattice spacing, period,
and real coupling. This bound alone does not control renormalized fields. -/
theorem hierarchy_uniform_bound (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (m : ℕ) (f : CorrelationTest m) :
    ‖(hierarchy G N a plane χ hcχ B hB β c).correlation m f‖ ≤
      BoundedKernelDistribution.boundSeminorm volume (B ^ m) f :=
  BoundedKernelDistribution.functional_bound _ _ _ _ _ f

theorem kernel_order_zero (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (β c : ℝ) (x : Configuration 0) :
    kernel G N a plane χ β c 0 x = 1 := by
  letI := wilsonLaw_probability N G χ hcχ β c
  simp [kernel, coefficient, moment]

theorem hierarchy_order_zero (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (f : CorrelationTest 0) :
    (hierarchy G N a plane χ hcχ B hB β c).correlation 0 f = ∫ x, f x := by
  rw [hierarchy_apply]
  simp only [kernel_order_zero G N a plane χ hcχ β c, one_mul]

end
end UnifiedTheory.Clay.YangMills.WilsonCellHierarchy
