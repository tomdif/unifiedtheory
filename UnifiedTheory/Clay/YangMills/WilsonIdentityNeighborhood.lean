/- A single open link neighborhood gives an actual low-energy product event
for every periodic four-dimensional regulator. Its Haar mass is exactly
q^(4V), not a supplied estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonAverageDefect
import UnifiedTheory.Clay.YangMills.GibbsCoordinateTransport
import UnifiedTheory.Clay.YangMills.GibbsLowEnergyConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonIdentityNeighborhood
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicTimeReflection
open PeriodicPlaquetteReflection WilsonCrossingKernel UnitaryCharacterObservables UnitaryHolonomyDefect
open WilsonAverageDefect LocalGibbsComparison GibbsCoordinateTransport GibbsLowEnergyConcentration
open scoped ENNReal

variable (N : ℕ) [NeZero N] (G : Type*) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {d : Type*} [Fintype d] [DecidableEq d]

def goodEvent (V : Set G) : Set (Configuration (Vertex N) G) :=
  Set.pi Set.univ (fun _ => V)

theorem goodEvent_measurable (V : Set G) (hV : MeasurableSet V) :
    MeasurableSet (goodEvent N G V) := MeasurableSet.pi Set.countable_univ (fun _ _ => hV)

theorem edge_card : Fintype.card (Edge (Vertex N)) = 4 * Fintype.card (Vertex N) := by
  rw [Fintype.card_congr (edgeCoordinates N), Fintype.card_prod, Fintype.card_fin]
  omega

theorem goodEvent_mass (V : Set G) :
    (referenceMeasure G (Vertex N)).real (goodEvent N G V) =
      ((compactHaar G).real V) ^ (4 * Fintype.card (Vertex N)) := by
  unfold Measure.real referenceMeasure goodEvent
  rw [Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, edge_card, ENNReal.toReal_pow]

theorem goodEvent_small (ρ : G →* Matrix.unitaryGroup d ℂ) (V : Set G) (eps : ℝ)
    (hV : ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, ∀ d ∈ V,
      defect ρ (a * b * c⁻¹ * d⁻¹) ≤ eps)
    (U : Configuration (Vertex N) G) (hU : U ∈ goodEvent N G V) :
    averageDefect N G ρ U ≤ eps := by
  apply average_le_of_plaquette_le
  intro p
  unfold plaquetteDefect loops
  rw [plaquette_holonomy_eq_product N G U p.1 p.2.1.1 p.2.1.2]
  exact hV _ (hU _ (Set.mem_univ _)) _ (hU _ (Set.mem_univ _))
    _ (hU _ (Set.mem_univ _)) _ (hU _ (Set.mem_univ _))

/-- The neighborhood and its positive single-link Haar mass do not depend
on the period. -/
theorem exists_good_neighborhood (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ V : Set G, IsOpen V ∧ 0 < (compactHaar G).real V ∧
      ∀ N : ℕ, ∀ _ : NeZero N, ∀ U ∈ goodEvent N G V, averageDefect N G ρ U ≤ eps := by
  obtain ⟨V,hVo,hV1,hV⟩ := exists_identity_neighborhood ρ hρ eps heps
  refine ⟨V,hVo,?_,?_⟩
  · exact ENNReal.toReal_pos (ne_of_gt (hVo.measure_pos (μ := compactHaar G) ⟨1,hV1⟩))
      (measure_ne_top _ _)
  · intro n hn U hU
    exact goodEvent_small n G ρ V eps hV U hU

theorem law_eq_average_weight (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta : ℝ) :
    wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d) =
      weightedLaw (referenceMeasure G (Vertex N))
        (weight (averageDefect N G ρ) (6 * beta * (Fintype.card (Vertex N) : ℝ))) := by
  unfold wilsonLaw orientedWilsonMeasure
  rw [gibbs_eq_weightedLaw _ _ _ (continuous_orientedWilsonAction _ _ _
    (unitaryCharacter_continuous ρ hρ) _ _ _ _)]
  congr 1
  funext U
  rw [action_eq_average]
  unfold weight
  congr 1
  ring

/-- An explicit finite-volume estimate with no assumed low-energy event. -/
theorem average_expectation_bound (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ q : ℝ, 0 < q ∧ ∀ N : ℕ, ∀ _ : NeZero N, ∀ beta : ℝ, 0 ≤ beta →
      Real.exp (-6 * beta * eps) / q ^ 4 ≤ 1 →
      (∫ U, averageDefect N G ρ U
        ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)) ≤
      2 * eps + (2 * (Fintype.card d : ℝ)) * (Real.exp (-6 * beta * eps) / q ^ 4) := by
  obtain ⟨V,hVo,hq,hgood⟩ := exists_good_neighborhood G ρ hρ eps heps
  refine ⟨(compactHaar G).real V,hq,?_⟩
  intro n hn beta hbeta hr
  rw [law_eq_average_weight n G ρ hρ beta]
  exact volume_uniform_expectation_bound (referenceMeasure G (Vertex n))
    (averageDefect n G ρ) (average_continuous n G ρ hρ) beta hbeta eps heps.le
    (2 * (Fintype.card d : ℝ)) (by positivity) (average_le n G ρ) _ hq
    (Fintype.card (Vertex n)) Fintype.card_pos
    (goodEvent n G V) (goodEvent_measurable n G V hVo.measurableSet)
    (le_of_eq (goodEvent_mass n G V).symm) (hgood n hn) hr

end
end UnifiedTheory.Clay.YangMills.WilsonIdentityNeighborhood
