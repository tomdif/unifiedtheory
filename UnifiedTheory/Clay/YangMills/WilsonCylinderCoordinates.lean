/-
Exact coordinate, Haar and normalized Wilson-law transport between the flat
open-cylinder positive-link inventory and its spatial/temporal families.
The actual full plaquette action is identified with fullAction, including
full endpoint potentials. No influence, clustering or vacuum limit is assumed.
-/
import UnifiedTheory.Clay.YangMills.WilsonCylinderGeometry
import UnifiedTheory.Clay.YangMills.WilsonFiniteCylinder
import UnifiedTheory.Clay.YangMills.WilsonBlockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCylinderCoordinates
noncomputable section
open MeasureTheory RegulatedGauge WilsonTimeSlab WilsonCylinderGeometry WilsonFiniteCylinder

section Curry
variable {I J X : Type*} [Fintype I] [Fintype J] [MeasurableSpace X]

/-- Finite currying preserves the actual normalized product probability. -/
theorem curry_preserving (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (MeasurableEquiv.curry I J X)
      (Measure.pi (fun _ : I × J => μ))
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => μ))) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry I J X).symm
  refine ⟨(MeasurableEquiv.curry I J X).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry I J X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext U
    simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi, Function.uncurry]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : I × J => μ (s p))).symm
end Curry

variable (n L : ℕ) (G : Type*) [MeasurableSpace G]

/-- Flattened positive links and the actual spatial/temporal coordinate families are equivalent. -/
def configEquiv : (Link n L → G) ≃ᵐ (Slices n G L × TemporalLinks n G L) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Link n L => G)).trans
    ((MeasurableEquiv.curry (Fin (L + 1)) (SpatialVertex n × Fin 3) G).prodCongr
      (MeasurableEquiv.curry (Fin L) (SpatialVertex n) G))

theorem configEquiv_spatial (U : Link n L → G) (t : Fin (L + 1)) (e : SpatialVertex n × Fin 3) :
    (configEquiv n L G U).1 t e = U (Sum.inl (t, e)) := rfl

theorem configEquiv_temporal (U : Link n L → G) (t : Fin L) (x : SpatialVertex n) :
    (configEquiv n L G U).2 t x = U (Sum.inr (t, x)) := rfl

theorem configEquiv_families (U : Link n L → G) :
    configEquiv n L G U = (spatialSlice n L U, temporalSlice n L U) := rfl

variable [TopologicalSpace G]

theorem configEquiv_continuous : Continuous (configEquiv n L G) := by
  change Continuous (fun U : Link n L → G => (spatialSlice n L U, temporalSlice n L U))
  apply Continuous.prodMk
  · exact continuous_pi (fun t => continuous_pi (fun e => continuous_apply (Sum.inl (t, e))))
  · exact continuous_pi (fun t => continuous_pi (fun x => continuous_apply (Sum.inr (t, x))))

variable [NeZero n] [Group G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G]

abbrev flatHaar : Measure (Link n L → G) := Measure.pi (fun _ : Link n L => compactHaar G)

/-- The coordinate equivalence preserves all original Haar factors, including length zero. -/
theorem reference_preserving :
    MeasurePreserving (configEquiv n L G) (flatHaar n L G)
      (cylinderHaar (n := n) (G := G) L) := by
  have hs := measurePreserving_sumPiEquivProdPi (fun _ : Link n L => compactHaar G)
  have h₁ := curry_preserving (I := Fin (L + 1)) (J := SpatialVertex n × Fin 3) (compactHaar G)
  have h₂ := curry_preserving (I := Fin L) (J := SpatialVertex n) (compactHaar G)
  exact (h₁.prod h₂).comp hs

/-- The original full Wilson plaquette sum in the actual flattened link inventory. -/
def flatAction (χ : G → ℂ) (β c : ℝ) (U : Link n L → G) : ℝ :=
  β * ∑ p : Plaquette n L, (c - (χ (plaquetteProduct n L U p)).re)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
/-- The action matches every actual slice and temporal plaquette, with full endpoint potentials. -/
theorem flatAction_eq_fullAction (χ : G → ℂ) (β c : ℝ) (U : Link n L → G) :
    flatAction n L G χ β c U =
      fullAction χ β c L (configEquiv n L G U).1 (configEquiv n L G U).2 := by
  unfold flatAction
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type, spatial_plaquette_product, temporal_plaquette_product]
  rfl

omit [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
/-- Continuity follows from the proved action dictionary and continuous actual coordinates. -/
theorem flatAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    Continuous (flatAction n L G χ β c) := by
  have he := funext (flatAction_eq_fullAction n L G χ β c)
  rw [he]
  exact (fullAction_continuous χ hχ β c L).comp (configEquiv_continuous n L G)

/-- The normalized original cylinder law on flat positive-link coordinates. -/
def flatLaw (χ : G → ℂ) (β c : ℝ) : Measure (Link n L → G) :=
  CompactGibbsContinuity.law (flatHaar n L G) (flatAction n L G χ β c)

theorem flatLaw_probability (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    IsProbabilityMeasure (flatLaw n L G χ β c) :=
  CompactGibbsContinuity.law_probability _ _ (flatAction_continuous n L G χ hχ β c)

/-- Exact normalized interacting-law transport, including its partition factor. -/
theorem law_preserving (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    MeasurePreserving (configEquiv n L G) (flatLaw n L G χ β c)
      (WilsonFiniteCylinder.law (n := n) χ β c L) := by
  unfold flatLaw WilsonFiniteCylinder.law CompactGibbsContinuity.law
  have he : (fun U => Real.exp (-flatAction n L G χ β c U)) =
      fun U => Real.exp (-fullAction χ β c L
        (configEquiv n L G U).1 (configEquiv n L G U).2) := by
    funext U
    rw [flatAction_eq_fullAction]
  rw [he]
  exact WilsonBlockMarginal.weightedLaw_preserving _ _ (configEquiv n L G)
    (reference_preserving n L G) (fun z => Real.exp (-fullAction χ β c L z.1 z.2))
    (Real.continuous_exp.comp (fullAction_continuous χ hχ β c L).neg).measurable

/-- Equality for all measurable events, not only product observables. -/
theorem map_flatLaw (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    (flatLaw n L G χ β c).map (configEquiv n L G) =
      WilsonFiniteCylinder.law (n := n) χ β c L :=
  (law_preserving n L G χ hχ β c).map_eq

/-- The inverse transport recovers the actual original plaquette-action law. -/
theorem map_cylinderLaw (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    (WilsonFiniteCylinder.law (n := n) χ β c L).map (configEquiv n L G).symm =
      flatLaw n L G χ β c :=
  ((law_preserving n L G χ hχ β c).symm (configEquiv n L G)).map_eq

/-- All real observable integrals agree under the exact cylinder coordinate transport. -/
theorem integral_coordinates (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F : (Slices n G L × TemporalLinks n G L) → ℝ) :
    (∫ U, F (configEquiv n L G U) ∂flatLaw n L G χ β c) =
      ∫ z, F z ∂WilsonFiniteCylinder.law (n := n) χ β c L :=
  (law_preserving n L G χ hχ β c).integral_comp (configEquiv n L G).measurableEmbedding F

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderCoordinates
