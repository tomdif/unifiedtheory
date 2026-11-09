/- Actual site-reflection positivity of the finite periodic Wilson law.
The half/boundary Haar coordinates and action decomposition are proved in the
imported lattice modules. This theorem does not construct continuum dynamics. -/
import UnifiedTheory.Clay.YangMills.PeriodicHalfAction
import UnifiedTheory.Clay.YangMills.GibbsReflectionTransport
import UnifiedTheory.Clay.YangMills.UnitaryCharacterObservables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicSiteReflection
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicHalfSplit PeriodicHalfAction
open PeriodicTimeReflection PeriodicPlaquetteReflection

variable (n : ℕ) [NeZero n]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def coordinates : Configuration (Vertex (2 * n)) G ≃ᵐ SplitConfiguration n G := by
  letI : BorelSpace (SplitConfiguration n G) := by
    unfold SplitConfiguration
    exact Prod.borelSpace
  exact { configurationEquiv n G with
    measurable_toFun := (continuous_splitConfiguration n G).measurable
    measurable_invFun := (continuous_assemble n G).measurable }

def boundaryWeight (χ : G → ℂ) (β c : ℝ) (b : BoundaryConfiguration n G) : ℝ :=
  Real.exp (-boundaryAction n G χ β c (assemble n G (b, (1, 1))))

def halfAction (χ : G → ℂ) (β c : ℝ)
    (z : BoundaryConfiguration n G × HalfConfiguration n G) : ℝ :=
  positiveAction n G χ β c (assemble n G (z.1, (z.2, 1)))

theorem boundaryWeight_continuous (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ) :
    Continuous (boundaryWeight n G χ β c) := by
  apply Real.continuous_exp.comp
  apply Continuous.neg
  apply (continuous_boundaryAction n G χ hcχ β c).comp
  exact (continuous_assemble n G).comp (continuous_id.prodMk continuous_const)

theorem boundaryWeight_positive (χ : G → ℂ) (β c : ℝ) (b : BoundaryConfiguration n G) :
    0 < boundaryWeight n G χ β c b := Real.exp_pos _

theorem halfAction_continuous (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ) :
    Continuous (halfAction n G χ β c) :=
  (continuous_positiveAction n G χ hcχ β c).comp ((continuous_assemble n G).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))

theorem density_identification (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) :
    Real.exp (-orientedWilsonAction (Vertex (2 * n)) G χ (base (2 * n))
      (loops (2 * n)) β c U) = BoundaryReflectionGluing.weight
      (boundaryWeight n G χ β c) (halfAction n G χ β c) (coordinates n G U) := by
  have he := wilsonAction_split n G χ hχ hinv β c
    (splitConfiguration n G U).1 (splitConfiguration n G U).2.1
    (splitConfiguration n G U).2.2
  rw [show ((splitConfiguration n G U).1,
    ((splitConfiguration n G U).2.1, (splitConfiguration n G U).2.2)) =
    splitConfiguration n G U from rfl, assemble_split] at he
  rw [he]
  simp only [neg_add_rev, Real.exp_add, BoundaryReflectionGluing.weight,
    boundaryWeight, halfAction, coordinates, configurationEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  ring

/-- Exact equality of the normalized Wilson law with the boundary-gluing law
under the constructed measurable coordinate equivalence. -/
theorem wilsonLaw_to_boundary (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) :
    MeasurePreserving (coordinates n G) (wilsonLaw (2 * n) G χ β c)
      (BoundaryReflectionGluing.law (boundaryMeasure n G) (halfMeasure n G)
        (boundaryWeight n G χ β c) (halfAction n G χ β c)) :=
  GibbsReflectionTransport.gibbs_to_boundary _ _ (Vertex (2 * n)) G _ (coordinates n G)
    (splitConfiguration_preserves n G) _ (boundaryWeight_continuous n G χ hcχ β c)
    _ (halfAction_continuous n G χ hcχ β c) (density_identification n G χ hχ hinv β c)

def observable (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (U : Configuration (Vertex (2 * n)) G) : ℂ :=
  BoundaryReflectionGluing.halfObservable f (coordinates n G U)

/-- Site reflection fixes the two spatial-link boundary planes. Every continuous
observable of a closed half has a real nonnegative reflected expectation. -/
theorem reflection_positive (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ) (hf : Continuous f) :
    0 ≤ (∫ U, star (observable n G f (reflectConfiguration (2 * n) G U)) *
      observable n G f U ∂wilsonLaw (2 * n) G χ β c).re ∧
    (∫ U, star (observable n G f (reflectConfiguration (2 * n) G U)) *
      observable n G f U ∂wilsonLaw (2 * n) G χ β c).im = 0 := by
  exact GibbsReflectionTransport.reflection_positive_transport _ _ (Vertex (2 * n)) G _
    (coordinates n G) (splitConfiguration_preserves n G) (reflectConfiguration (2 * n) G)
    (split_reflection n G) _ (boundaryWeight_continuous n G χ hcχ β c)
    (boundaryWeight_positive n G χ β c) _ (halfAction_continuous n G χ hcχ β c)
    (density_identification n G χ hχ hinv β c) f hf

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem unitary_reflection_positive (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (β c : ℝ)
    (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ) (hf : Continuous f) :
    0 ≤ (∫ U, star (observable n G f (reflectConfiguration (2 * n) G U)) *
      observable n G f U ∂wilsonLaw (2 * n) G (WilsonCrossingKernel.unitaryCharacter ρ) β c).re ∧
    (∫ U, star (observable n G f (reflectConfiguration (2 * n) G U)) *
      observable n G f U ∂wilsonLaw (2 * n) G (WilsonCrossingKernel.unitaryCharacter ρ) β c).im = 0 :=
  reflection_positive n G _ (UnitaryCharacterObservables.unitaryCharacter_continuous ρ hρ)
    (UnitaryCharacterObservables.unitaryCharacter_class ρ) (unitaryCharacter_inverse_re G ρ)
    β c f hf

end
end UnifiedTheory.Clay.YangMills.PeriodicSiteReflection
