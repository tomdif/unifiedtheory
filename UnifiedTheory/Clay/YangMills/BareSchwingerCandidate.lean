/- One actual subsequential bare hierarchy carries the properties proved here
together: normalization, a uniform Schwartz bound, Euclidean time translations,
and finite mixed-order reflection positivity on bounded positive-time slabs.
The mesh vanishes and physical volume grows along the explicit lattice scales.
This statement does not assert nontriviality, dynamics, or a Yang--Mills mass gap. -/
import UnifiedTheory.Clay.YangMills.ExplicitLatticeScales
import UnifiedTheory.Clay.YangMills.ContinuumTimeTranslation
import UnifiedTheory.Clay.YangMills.WilsonHierarchyReflectionPositivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.BareSchwingerCandidate
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open ExplicitLatticeScales CellReflectionCovariance WilsonReflectedTensor
open CellTranslationCovariance SchwartzTranslations
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
      (∀ (m : ℕ) (t : ℝ) (f : CorrelationTest m),
        W.correlation m (translationCLM (timeVector m t) f) = W.correlation m f) ∧
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
  letI : ∀ k, NeZero (2 * halfPeriod k) := fun k => inferInstance
  obtain ⟨W, phi, hphi, hW, hb, hn, ht⟩ :=
    ContinuumTimeTranslation.exists_time_translation_invariant_limit G
      (fun k => 2 * halfPeriod k) spacing spacing_pos spacing_to_zero
      plane (realPartCharacter G χ) (realPart_continuous G χ hcχ)
      B (realPart_bound G χ B hB) beta offset
  refine ⟨W, phi, hphi, hW, hn, hb, ht, ?_⟩
  intro l order test coeff R hs
  letI : ∀ k, NeZero (halfPeriod (phi k)) := fun k => halfPeriod_ne_zero (phi k)
  apply WilsonHierarchyReflectionPositivity.finite_form_positive G
    (fun k => halfPeriod (phi k)) (fun k => spacing (phi k))
    (fun k => ne_of_gt (spacing_pos (phi k))) (spacing_to_zero.comp hphi.tendsto_atTop)
    plane χ hcχ hχ hinv B hB (beta ∘ phi) (offset ∘ phi) W hW l order test coeff
  intro i
  exact hphi.tendsto_atTop.eventually
    (fixed_test_eventually_supported plane (order i) (test i) (R i) (hs i))

end
end UnifiedTheory.Clay.YangMills.BareSchwingerCandidate
