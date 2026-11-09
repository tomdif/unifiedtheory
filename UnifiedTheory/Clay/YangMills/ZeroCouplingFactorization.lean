/- Exact β=0 factorization for actual interior smeared Wilson
observables. Their two reflected halves are independent product Haar variables.
The resulting connected reflected form vanishes; this is restricted to beta=0. -/
import UnifiedTheory.Clay.YangMills.InteriorCellSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ZeroCouplingFactorization
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicHalfSplit
open PeriodicTimeReflection InteriorCellSupport ContinuumControl

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem wilsonLaw_zero (N : ℕ) [NeZero N] (χ : G → ℂ) (c : ℝ) :
    wilsonLaw N G χ 0 c = referenceMeasure G (Vertex N) := by
  have hd : gibbsDensity (Vertex N) G
      (orientedWilsonAction (Vertex N) G χ (base N) (loops N) 0 c) = fun _ => 1 := by
    funext U
    simp [gibbsDensity, orientedWilsonAction, wilsonAction]
  simp [wilsonLaw, orientedWilsonMeasure, gibbsMeasure, gibbsPartition, hd]

variable (n : ℕ) [NeZero n]

theorem reference_integral_split (H : SplitConfiguration n G → ℂ) :
    (∫ U, H (splitConfiguration n G U) ∂referenceMeasure G (Vertex (2 * n))) =
      ∫ z, H z ∂(boundaryMeasure n G).prod ((halfMeasure n G).prod (halfMeasure n G)) :=
  (splitConfiguration_preserves n G).integral_comp
    (PeriodicSiteReflection.coordinates n G).measurableEmbedding H

theorem remove_boundary_integral (H : HalfConfiguration n G × HalfConfiguration n G → ℂ) :
    (∫ z : SplitConfiguration n G, H z.2
      ∂(boundaryMeasure n G).prod ((halfMeasure n G).prod (halfMeasure n G))) =
      ∫ z, H z ∂(halfMeasure n G).prod (halfMeasure n G) := by
  simpa only [one_mul, integral_const, probReal_univ, one_smul] using
    (integral_prod_mul (μ := boundaryMeasure n G)
      (ν := (halfMeasure n G).prod (halfMeasure n G))
      (fun _ : BoundaryConfiguration n G => (1 : ℂ)) H)

theorem reference_half_mean (F : HalfConfiguration n G → ℂ) :
    (∫ U, F (splitConfiguration n G U).2.1 ∂referenceMeasure G (Vertex (2 * n))) =
      ∫ x, F x ∂halfMeasure n G := by
  rw [reference_integral_split G n (fun z => F z.2.1),
    remove_boundary_integral G n (fun z => F z.1)]
  simpa only [mul_one, integral_const, probReal_univ, one_smul] using
    (integral_prod_mul (μ := halfMeasure n G) (ν := halfMeasure n G)
      F (fun _ : HalfConfiguration n G => (1 : ℂ)))

theorem reference_half_pair (F H : HalfConfiguration n G → ℂ) :
    (∫ U, star (F (splitConfiguration n G U).2.2) * H (splitConfiguration n G U).2.1
      ∂referenceMeasure G (Vertex (2 * n))) =
      star (∫ U, F (splitConfiguration n G U).2.1 ∂referenceMeasure G (Vertex (2 * n))) *
        (∫ U, H (splitConfiguration n G U).2.1 ∂referenceMeasure G (Vertex (2 * n))) := by
  rw [reference_integral_split G n (fun z => star (F z.2.2) * H z.2.1),
    remove_boundary_integral G n (fun z => star (F z.2) * H z.1),
    reference_half_mean G n F, reference_half_mean G n H]
  simp_rw [mul_comm (star (F _)) (H _)]
  rw [integral_prod_mul H (fun x => star (F x))]
  simp only [Complex.star_def, integral_conj, mul_comm]

/-- Actual fixed smeared tests with interior cell support have exactly
factorized reflected expectation under the β=0 Wilson law. -/
theorem reflected_pair_factorizes (a : ℝ) (plane : Plane) (χ : G → ℂ) (c : ℝ)
    (m l : ℕ) (f : CorrelationTest m) (h : CorrelationTest l)
    (hf : Supported n a plane m f) (hh : Supported n a plane l h) :
    (∫ U, star (WilsonSmearedObservable.observable G (2 * n) a plane χ m f
      (reflectConfiguration (2 * n) G U)) *
      WilsonSmearedObservable.observable G (2 * n) a plane χ l h U
        ∂wilsonLaw (2 * n) G χ 0 c) =
      star (∫ U, WilsonSmearedObservable.observable G (2 * n) a plane χ m f U
        ∂wilsonLaw (2 * n) G χ 0 c) *
      (∫ U, WilsonSmearedObservable.observable G (2 * n) a plane χ l h U
        ∂wilsonLaw (2 * n) G χ 0 c) := by
  rw [wilsonLaw_zero]
  simp_rw [interior_identification n G a plane χ m f hf,
    interior_identification n G a plane χ l h hh, split_reflection]
  exact reference_half_pair G n _ _

end
end UnifiedTheory.Clay.YangMills.ZeroCouplingFactorization
