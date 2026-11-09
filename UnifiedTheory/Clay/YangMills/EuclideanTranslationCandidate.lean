/- One actual subsequential bare hierarchy carries the properties proved here
together: normalization, a uniform Schwartz bound, all Euclidean spacetime translations,
and finite mixed-order reflection positivity on bounded positive-time slabs.
The mesh vanishes and physical volume grows along the explicit lattice scales.
This statement does not assert nontriviality, dynamics, or a Yang--Mills mass gap. -/
import UnifiedTheory.Clay.YangMills.ExplicitLatticeScales
import UnifiedTheory.Clay.YangMills.ContinuumSpacetimeTranslation
import UnifiedTheory.Clay.YangMills.BareSchwingerCandidate
import UnifiedTheory.Clay.YangMills.WilsonHierarchyReflectionPositivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.EuclideanTranslationCandidate
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open ExplicitLatticeScales CellReflectionCovariance WilsonReflectedTensor
open CellSpacetimeTranslation SchwartzTranslations LocalFields
open scoped Topology NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- A single candidate and a single strict subsequence satisfy all the stated
properties. Reflection positivity is proved from the actual Wilson laws for
every finite family, every mixture of orders, and all complex coefficients. -/
theorem exists_candidate (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => realHierarchy G (2 * halfPeriod (phi k)) (spacing (phi k))
          plane χ hcχ B hB (beta (phi k)) (offset (phi k))) W ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      (∀ m f, ‖W.correlation m f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B ^ m) f) ∧
      (∀ (m : ℕ) (v : Spacetime) (f : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) f) = W.correlation m f) ∧
      ∀ (l : ℕ) (order : Fin l → ℕ) (test : (i : Fin l) → CorrelationTest (order i))
        (coeff : Fin l → ℂ) (R : Fin l → ℝ),
        (∀ i x, test i x ≠ 0 → ∀ j,
          0 ≤ point (order i) j x 0 ∧ point (order i) j x 0 ≤ R i) →
        0 ≤ (∑ i, ∑ j, star (coeff i) * coeff j *
          W.correlation (order i + order j)
            (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).re ∧
        (∑ i, ∑ j, star (coeff i) * coeff j *
          W.correlation (order i + order j)
            (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).im = 0 := by
  obtain ⟨W, phi, hphi, hW, hn, hb, _, hrp⟩ :=
    BareSchwingerCandidate.exists_candidate G plane χ hcχ hχ hinv B hB beta offset
  letI : ∀ k, NeZero (2 * halfPeriod (phi k)) := fun k => inferInstance
  refine ⟨W, phi, hphi, hW, hn, hb, ?_, hrp⟩
  intro m v f
  exact ContinuumSpacetimeTranslation.hierarchy_spacetime_translation G
    (fun k => 2 * halfPeriod (phi k)) (fun k => spacing (phi k))
    (fun k => spacing_pos (phi k)) (spacing_to_zero.comp hphi.tendsto_atTop)
    plane (realPartCharacter G χ) (realPart_continuous G χ hcχ)
    B (realPart_bound G χ B hB) (beta ∘ phi) (offset ∘ phi) W hW m v f

end
end UnifiedTheory.Clay.YangMills.EuclideanTranslationCandidate
