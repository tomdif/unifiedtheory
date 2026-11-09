/- The actual reflected product of real-character smeared Wilson observables
is exactly a hierarchy evaluation on a conjugate-reflected Schwartz tensor.
The moving reflection test converges in Schwartz topology as spacing vanishes. -/
import UnifiedTheory.Clay.YangMills.WilsonTensorProduct
import UnifiedTheory.Clay.YangMills.SchwartzConfigurationConjugation
import UnifiedTheory.Clay.YangMills.AffineCellReflection
import UnifiedTheory.Clay.YangMills.MovingTestLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonReflectedTensor
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 CellReflectionCovariance
open SchwartzConfigurationTensor SchwartzConfigurationConjugation AffineCellReflection
open scoped Topology NNReal ENNReal

def reflectedTensor (m n : ℕ) (a : ℝ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) : CorrelationTest (m+n) :=
  tensor m n (conjugation m (reflectionPullback m a plane f)) g

theorem reflectedTensor_tendsto_zero (m n : ℕ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k => reflectedTensor m n (a k) plane f g) atTop
      (𝓝 (reflectedTensor m n 0 plane f g)) :=
  ((continuous_tensor_left m n g).comp (conjugation_continuous m)).tendsto
      (reflectionPullback m 0 plane f) |>.comp (reflectionPullback_tendsto_zero m plane f a ha)

variable (G : Type*) [Group G]

theorem realPart_class (χ : G → ℂ) (hχ : RegulatedGauge.ClassFunction G χ) :
    RegulatedGauge.ClassFunction G (realPartCharacter G χ) :=
  fun g x => congrArg (fun z : ℂ => (z.re : ℂ)) (hχ g x)

theorem realPart_inverse (χ : G → ℂ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) :
    ∀ g, (realPartCharacter G χ g⁻¹).re = (realPartCharacter G χ g).re :=
  hinv

theorem realPart_bound (χ : G → ℂ) (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) :
    ∀ g, ‖realPartCharacter G χ g‖ ≤ B := by
  intro g
  change ‖((χ g).re : ℂ)‖ ≤ B
  simpa only [Complex.norm_real, Real.norm_eq_abs] using (Complex.abs_re_le_norm (χ g)).trans (hB g)

theorem word_star (N : ℕ) [NeZero N] (χ : G → ℂ) (m : ℕ)
    (q : Fin m → PlaquetteIndex N) (U : RegulatedGauge.Configuration (Vertex N) G) :
    star (WilsonSmearedObservable.word G N (realPartCharacter G χ) m q U) =
      WilsonSmearedObservable.word G N (realPartCharacter G χ) m q U := by
  simp only [WilsonSmearedObservable.word, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact Complex.conj_ofReal _

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem realPart_continuous (χ : G → ℂ) (hcχ : Continuous χ) :
    Continuous (realPartCharacter G χ) :=
  Complex.continuous_ofReal.comp (Complex.continuous_re.comp hcχ)

def realHierarchy (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℝ) : Hierarchy :=
  WilsonCellHierarchy.hierarchy G N a plane (realPartCharacter G χ)
    (realPart_continuous G χ hcχ) B (realPart_bound G χ B hB) beta offset

theorem observable_conjugation (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (m : ℕ) (f : CorrelationTest m) (U : RegulatedGauge.Configuration (Vertex N) G) :
    star (WilsonSmearedObservable.observable G N a plane (realPartCharacter G χ) m f U) =
      WilsonSmearedObservable.observable G N a plane (realPartCharacter G χ) m
        (conjugation m f) U := by
  rw [WilsonSmearedObservable.observable_integral, WilsonSmearedObservable.observable_integral]
  calc
    _ = ∫ x, star (WilsonSmearedObservable.word G N (realPartCharacter G χ) m
        (PeriodicCellSampling.sampleConfiguration m N a plane x) U * f x) := by
      simp only [Complex.star_def, integral_conj]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        dsimp only
        rw [star_mul, word_star, conjugation_apply, mul_comm])

/-- Exact finite-cutoff identity, including the conjugation, coordinate tensor,
and spacing-dependent reflection. No identification hypothesis is used. -/
theorem reflected_pair_eq_hierarchy (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ z, (χ z⁻¹).re = (χ z).re)
    (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (beta offset : ℝ)
    (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n) :
    (∫ U, star (WilsonSmearedObservable.observable G N a plane (realPartCharacter G χ) m f
      (PeriodicTimeReflection.reflectConfiguration N G U)) *
      WilsonSmearedObservable.observable G N a plane (realPartCharacter G χ) n g U
        ∂wilsonLaw N G (realPartCharacter G χ) beta offset) =
      (realHierarchy G N a plane χ hcχ B hB beta offset).correlation
        (m+n) (reflectedTensor m n a plane f g) := by
  simp_rw [reflected_smearing_identity G N a ha plane χ hχ hinv,
    observable_conjugation, WilsonTensorProduct.observable_mul]
  exact WilsonSmearedObservable.expectation_eq_hierarchy G N a plane (realPartCharacter G χ)
    (realPart_continuous G χ hcχ) B (realPart_bound G χ B hB) beta offset _ _

/-- Any weak bare-hierarchy limit with vanishing lattice spacing identifies
the actual reflected-pair limits with the fixed zero-offset tensor test. -/
theorem reflected_pair_tendsto (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0) (ha0 : Tendsto a atTop (𝓝 0))
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ z, (χ z⁻¹).re = (χ z).re)
    (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (beta offset : ℕ → ℝ)
    (W : Hierarchy)
    (hW : WeakConvergence (fun k => realHierarchy G (period k) (a k) plane χ hcχ B hB
      (beta k) (offset k)) W)
    (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n) :
    Tendsto (fun k => ∫ U,
      star (WilsonSmearedObservable.observable G (period k) (a k) plane (realPartCharacter G χ) m f
        (PeriodicTimeReflection.reflectConfiguration (period k) G U)) *
      WilsonSmearedObservable.observable G (period k) (a k) plane (realPartCharacter G χ) n g U
        ∂wilsonLaw (period k) G (realPartCharacter G χ) (beta k) (offset k)) atTop
      (𝓝 (W.correlation (m+n) (reflectedTensor m n 0 plane f g))) := by
  simp_rw [reflected_pair_eq_hierarchy G _ _ (ha _) plane χ hcχ hχ hinv B hB]
  exact MovingTestLimit.hierarchy_moving_limit _ W hW
    (fun q => BoundedKernelDistribution.boundSeminorm volume (B ^ q))
    (fun q => BoundedKernelDistribution.boundSeminorm_continuous volume (B ^ q))
    (fun k q h => WilsonCellHierarchy.hierarchy_uniform_bound G (period k) (a k) plane
      (realPartCharacter G χ) (realPart_continuous G χ hcχ) B (realPart_bound G χ B hB)
      (beta k) (offset k) q h)
    (m+n) (reflectedTensor m n 0 plane f g)
    (fun k => reflectedTensor m n (a k) plane f g) (reflectedTensor_tendsto_zero m n plane f g a ha0)

end
end UnifiedTheory.Clay.YangMills.WilsonReflectedTensor
