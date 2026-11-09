/- A single actual bare scalar Wilson limit has all four Euclidean
translation symmetries and its constructed OS time semigroup. This is not
rotation covariance, a physical Hamiltonian, or a nontrivial Yang--Mills theory. -/
import UnifiedTheory.Clay.YangMills.OSScalarDynamics
import UnifiedTheory.Clay.YangMills.ContinuumSpacetimeTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.TranslationOSCandidate
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 LocalFields
open ExplicitLatticeScales WilsonReflectedTensor CellReflectionCovariance
open CellSpacetimeTranslation SchwartzTranslations OSPositiveTimeKernel OSScalarDynamics
open scoped NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_candidate (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => realHierarchy G (2 * halfPeriod (phi k)) (spacing (phi k))
          plane χ hcχ B hB (beta (phi k)) (offset (phi k))) W ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      Bounded W B ∧ Stationary W ∧
      (∀ (m : ℕ) (v : Spacetime) (f : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) f) = W.correlation m f) ∧
      ∃ hp : Positive W plane, Nonempty (Evolution W plane hp) := by
  obtain ⟨W,phi,hphi,hW,hn,hb,ht,hp,hE⟩ :=
    exists_candidate_dynamics G plane χ hcχ hχ hinv B hB beta offset
  letI : ∀ k, NeZero (2 * halfPeriod (phi k)) := fun k => inferInstance
  refine ⟨W,phi,hphi,hW,hn,hb,ht,?_,hp,hE⟩
  intro m v f
  exact ContinuumSpacetimeTranslation.hierarchy_spacetime_translation G
    (fun k => 2 * halfPeriod (phi k)) (fun k => spacing (phi k))
    (fun k => spacing_pos (phi k)) (spacing_to_zero.comp hphi.tendsto_atTop)
    plane (realPartCharacter G χ) (realPart_continuous G χ hcχ)
    B (realPart_bound G χ B hB) (beta ∘ phi) (offset ∘ phi) W hW m v f

end
end UnifiedTheory.Clay.YangMills.TranslationOSCandidate
