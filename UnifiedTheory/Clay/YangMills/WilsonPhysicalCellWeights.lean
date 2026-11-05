/- Actual cell-integral weights for a Schwartz test on four-dimensional
spacetime. The coefficient bound is uniform in lattice spacing and volume.
This supplies smearing, not a physical renormalization trajectory. -/
import UnifiedTheory.Clay.YangMills.FiniteCellWeightBudget
import UnifiedTheory.Clay.YangMills.WilsonBlockWeightBudget
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalCellWeights
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 LocalFields

variable (n : ℕ) [NeZero n] (a : ℝ) (plane : Plane)

/-- The real component of the test is integrated over each actual periodic
sampling fiber. Fibers can be unbounded; Schwartz integrability is sufficient. -/
def weight (f : TestFunction) (p : PlaquetteIndex n) : ℝ :=
  (FiniteCellSmearing.coefficient volume (PeriodicCellSampling.sample n a plane) p f).re

theorem weight_budget (f : TestFunction) :
    (∑ p, |weight n a plane f p|) ≤ ∫ x, ‖f x‖ :=
  FiniteCellWeightBudget.coefficient_re_budget volume _
    (PeriodicCellSampling.sample_measurable n a plane) f f.integrable

omit [NeZero n] in
theorem weight_other_plane (f : TestFunction) (p : PlaquetteIndex n) (hp : p.2 ≠ plane) :
    weight n a plane f p = 0 := by
  have h (x : Spacetime) : PeriodicCellSampling.sample n a plane x ≠ p := by
    intro he
    exact hp (congrArg Prod.snd he).symm
  simp [weight, FiniteCellSmearing.coefficient, FiniteCellSmearing.cellFunction, h]

theorem independent_block_weight_budget (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f : TestFunction) :
    (∑ e : {e : Edge (Vertex n) // e ∈ S},
      ∑ p ∈ SingleLinkWilsonOscillation.affected n
        (WilsonIndependentBlocks.edgeCoord n e.val).1
        (WilsonIndependentBlocks.edgeCoord n e.val).2, |weight n a plane f p|) ≤
      ∫ x, ‖f x‖ :=
  (WilsonBlockWeightBudget.inside_weight_budget n S hS (weight n a plane f)).trans
    (weight_budget n a plane f)

variable (G : Type*) [Group G]

/-- Exact identification with the spacetime-smeared Wilson plaquette term,
before any expectation or continuum limit is taken. -/
theorem source_eq_spacetime_integral (χ : G → ℂ) (c : ℝ) (f : TestFunction)
    (U : Configuration (Vertex n) G) :
    WilsonBlockIntegration.source n G χ c (weight n a plane f) U =
      (∫ x, (WilsonIndependentBlocks.plaquetteTerm n G χ c U
        (PeriodicCellSampling.sample n a plane x) : ℂ) * f x).re := by
  exact FiniteCellWeightBudget.real_observable_integral volume _
    (PeriodicCellSampling.sample_measurable n a plane)
    (WilsonIndependentBlocks.plaquetteTerm n G χ c U) f f.integrable

theorem weight_sum (f : TestFunction) :
    (∑ p, weight n a plane f p) = (∫ x, f x).re := by
  simpa only [mul_one, Complex.ofReal_one, one_mul] using
    FiniteCellWeightBudget.real_observable_integral volume _
      (PeriodicCellSampling.sample_measurable n a plane) (fun _ => 1) f f.integrable

/-- The same budget controls the existing exact cell coefficients of every
order of the Wilson correlation hierarchy. It supplies no moment bound. -/
theorem hierarchy_coefficient_budget (m : ℕ) (f : ContinuumControl.CorrelationTest m) :
    (∑ q, ‖WilsonSmearedObservable.cellCoefficient n a plane m q f‖) ≤
      ∫ x, ‖f x‖ :=
  FiniteCellWeightBudget.coefficient_norm_budget volume _
    (PeriodicCellSampling.sampleConfiguration_measurable m n a plane) f f.integrable

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalCellWeights
