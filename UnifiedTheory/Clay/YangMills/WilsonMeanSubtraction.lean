/- An actual finite-cutoff identity counterterm. Translation invariance makes
the one-point plaquette expectation constant; subtracting that expectation
sets every smeared one-point function to zero under the original Wilson law.
This fixes the first moment, not higher moments, field mixing, or a positive
reflected covariance. No variance-based normalization is introduced. -/
import UnifiedTheory.Clay.YangMills.RenormalizedWilsonHierarchy
import UnifiedTheory.Clay.YangMills.WilsonReflectedTuning
import UnifiedTheory.Clay.YangMills.PeriodicSpacetimeTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonMeanSubtraction
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 ContinuumControl
open PeriodicSpacetimeTranslation WilsonMomentBounds WilsonSmearedObservable
open AffineWilsonSmearing RenormalizedWilsonHierarchy
open scoped NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

def mean (plane : Plane) (ψ χ : G → ℂ) (beta offset : ℝ) : ℂ :=
  ∫ U, loopObservable (Vertex N) G ψ (loops N (0, plane)) U
    ∂wilsonLaw N G χ beta offset

theorem mean_continuous (plane : Plane) (ψ χ : G → ℂ)
    (hψ : Continuous ψ) (hχ : Continuous χ) (offset : ℝ) :
    Continuous (fun beta => mean G N plane ψ χ beta offset) :=
  WilsonReflectedTuning.wilson_expectation_continuous G N χ hχ offset _
    ((loopObservable_continuous (Vertex N) G ψ hψ (loops N (0, plane))).comp
      continuous_snd)

theorem mean_realPart (plane : Plane) (ψ χ : G → ℂ) (beta offset : ℝ) :
    mean G N plane (CellReflectionCovariance.realPartCharacter G ψ) χ beta offset =
      ((mean G N plane (CellReflectionCovariance.realPartCharacter G ψ) χ beta offset).re : ℂ) := by
  unfold mean loopObservable wilson CellReflectionCovariance.realPartCharacter
  rw [integral_complex_ofReal]
  simp

theorem mean_translation (plane : Plane) (ψ χ : G → ℂ) (hχ : Continuous χ)
    (beta offset : ℝ) (x : Vertex N) :
    (∫ U, loopObservable (Vertex N) G ψ (loops N (x, plane)) U
      ∂wilsonLaw N G χ beta offset) = mean G N plane ψ χ beta offset := by
  have hp := wilsonLaw_preserves_shift N G χ hχ beta offset x
  have hi := hp.integral_comp (configurationShiftMeasurableEquiv N G x).measurableEmbedding
    (loopObservable (Vertex N) G ψ (loops N (0, plane)))
  have he : (fun U => loopObservable (Vertex N) G ψ (loops N (0, plane))
      (shiftConfiguration N G x U)) =
      loopObservable (Vertex N) G ψ (loops N (x, plane)) := by
    funext U
    change ψ (holonomy (Quiver.Symmetrify (Vertex N)) G
      (orientedExtension (Vertex N) G (shiftConfiguration N G x U))
      (plaquette N 0 plane.1.1 plane.1.2)) = _
    rw [plaquette_holonomy_shift]
    have hx : shiftVertex N x 0 = x := by
      unfold shiftVertex
      abel
    rw [hx]
    rfl
  rw [he] at hi
  exact hi

theorem kernel_one_constant (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hχ : Continuous χ) (beta offset : ℝ) (x : ContinuumControl.Configuration 1) :
    kernel G N a plane ψ χ beta offset 1 x = mean G N plane ψ χ beta offset := by
  simp only [kernel, coefficient, word, Fin.prod_univ_one]
  exact mean_translation G N plane ψ χ hχ beta offset _

theorem expectation_one (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hψ : Continuous ψ) (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) (f : CorrelationTest 1) :
    (∫ U, observable G N a plane ψ 1 f U ∂wilsonLaw N G χ beta offset) =
      mean G N plane ψ χ beta offset * ∫ x, f x := by
  rw [RenormalizedWilsonHierarchy.expectation_eq_hierarchy G N a plane ψ χ hψ hχ
    B hB beta offset, hierarchy_apply]
  simp_rw [kernel_one_constant G N a plane ψ χ hχ beta offset]
  exact integral_const_mul _ _

/-- The one-point subtraction is constructed from the same action law and
works simultaneously for every fixed Schwartz test, not just one chosen test. -/
theorem affine_expectation_zero (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hψ : Continuous ψ) (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) (scale : ℂ) (f : CorrelationTest 1) :
    (∫ U, observable G N a plane
      (affineCharacter ψ (mean G N plane ψ χ beta offset) scale) 1 f U
      ∂wilsonLaw N G χ beta offset) = 0 := by
  letI := wilsonLaw_probability N G χ hχ beta offset
  simp_rw [affine_smearing G N a plane]
  rw [integral_const_mul, integral_sub
    ((observable_continuous G N a plane ψ hψ 1 f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  rw [expectation_one G N a plane ψ χ hψ hχ B hB beta offset f]
  simp

/-- For a real-character field the counterterm is an actual real function
of beta, compatible with real affine renormalized hierarchies. -/
theorem real_affine_expectation_zero (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hψ : Continuous ψ) (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset scale : ℝ) (f : CorrelationTest 1) :
    (∫ U, observable G N a plane
      (affineCharacter (CellReflectionCovariance.realPartCharacter G ψ)
        ((mean G N plane (CellReflectionCovariance.realPartCharacter G ψ) χ beta offset).re : ℂ)
        (scale : ℂ)) 1 f U ∂wilsonLaw N G χ beta offset) = 0 := by
  rw [← mean_realPart G N plane ψ χ beta offset]
  exact affine_expectation_zero G N a plane _ χ
    (WilsonReflectedTensor.realPart_continuous G ψ hψ) hχ B
    (WilsonReflectedTensor.realPart_bound G ψ B hB) beta offset scale f

end
end UnifiedTheory.Clay.YangMills.WilsonMeanSubtraction
