/- Actual cell-smeared moments with separate observable and action characters.
This separation is essential for cutoff-dependent affine renormalizations:
changing the observable does not change the underlying Wilson probability law.
The finite-cutoff bounds here need not be uniform in the cutoff. -/
import UnifiedTheory.Clay.YangMills.AffineWilsonSmearing
import UnifiedTheory.Clay.YangMills.WilsonReflectedTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RenormalizedWilsonHierarchy
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 WilsonSmearedObservable
open WilsonReflectedTensor CellReflectionCovariance
open scoped NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

def coefficient (observableCharacter actionCharacter : G → ℂ) (beta offset : ℝ)
    (m : ℕ) (q : Fin m → PlaquetteIndex N) : ℂ :=
  ∫ U, word G N observableCharacter m q U
    ∂wilsonLaw N G actionCharacter beta offset

def kernel (a : ℝ) (plane : Plane) (observableCharacter actionCharacter : G → ℂ)
    (beta offset : ℝ) (m : ℕ) (x : ContinuumControl.Configuration m) : ℂ :=
  coefficient G N observableCharacter actionCharacter beta offset m
    (PeriodicCellSampling.sampleConfiguration m N a plane x)

theorem kernel_measurable (a : ℝ) (plane : Plane)
    (observableCharacter actionCharacter : G → ℂ) (beta offset : ℝ) (m : ℕ) :
    Measurable (kernel G N a plane observableCharacter actionCharacter beta offset m) :=
  (measurable_of_countable _).comp
    (PeriodicCellSampling.sampleConfiguration_measurable m N a plane)

theorem kernel_bound (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) (m : ℕ) (x : ContinuumControl.Configuration m) :
    ‖kernel G N a plane ψ χ beta offset m x‖ ≤ (B : ℝ)^m := by
  letI := wilsonLaw_probability N G χ hχ beta offset
  unfold kernel coefficient
  calc
    _ ≤ ∫ _, (B : ℝ)^m ∂wilsonLaw N G χ beta offset :=
      norm_integral_le_of_norm_le (integrable_const _)
        (Filter.Eventually.of_forall (fun U => word_bound G N ψ B hB m _ U))
    _ = _ := by simp

def hierarchy (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) : Hierarchy where
  correlation m := BoundedKernelDistribution.functional volume
    (kernel G N a plane ψ χ beta offset m)
    (kernel_measurable G N a plane ψ χ beta offset m) (B^m)
    (by simpa only [NNReal.coe_pow] using
      kernel_bound G N a plane ψ χ hχ B hB beta offset m)

theorem hierarchy_apply (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) (m : ℕ) (f : CorrelationTest m) :
    (hierarchy G N a plane ψ χ hχ B hB beta offset).correlation m f =
      ∫ x, kernel G N a plane ψ χ beta offset m x * f x := rfl

theorem expectation_eq_hierarchy (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hψ : Continuous ψ) (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) (m : ℕ) (f : CorrelationTest m) :
    (∫ U, observable G N a plane ψ m f U ∂wilsonLaw N G χ beta offset) =
      (hierarchy G N a plane ψ χ hχ B hB beta offset).correlation m f := by
  letI := wilsonLaw_probability N G χ hχ beta offset
  exact FiniteCellSmearing.expectation_identity volume _
    (PeriodicCellSampling.sampleConfiguration_measurable m N a plane)
    (wilsonLaw N G χ beta offset) (word G N ψ m) (word_continuous G N ψ hψ m)
    f f.integrable

theorem hierarchy_order_zero (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) (f : CorrelationTest 0) :
    (hierarchy G N a plane ψ χ hχ B hB beta offset).correlation 0 f = ∫ x, f x := by
  letI := wilsonLaw_probability N G χ hχ beta offset
  rw [hierarchy_apply]
  simp only [kernel, coefficient, word, Fin.prod_univ_zero, integral_const,
    probReal_univ, one_smul, one_mul]

theorem hierarchy_bound (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) (m : ℕ) (f : CorrelationTest m) :
    ‖(hierarchy G N a plane ψ χ hχ B hB beta offset).correlation m f‖ ≤
      BoundedKernelDistribution.boundSeminorm volume (B^m) f :=
  BoundedKernelDistribution.functional_bound _ _ _ _ _ f

/-- The real-valued observable may vary with the regulator while the action
character stays fixed. This includes real affine scalings of a real character. -/
def realHierarchy (a : ℝ) (plane : Plane) (ψ χ : G → ℂ)
    (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (beta offset : ℝ) : Hierarchy :=
  hierarchy G N a plane (realPartCharacter G ψ) χ hχ B (realPart_bound G ψ B hB)
    beta offset

/-- The reflected two-observable moment is a tensor evaluation of this same
hierarchy under the original action, with no change of coupling. -/
theorem reflected_pair_eq_hierarchy (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (ψ χ : G → ℂ) (hcψ : Continuous ψ) (hcχ : Continuous χ)
    (hψ : RegulatedGauge.ClassFunction G ψ) (hinv : ∀ g, (ψ g⁻¹).re = (ψ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B) (beta offset : ℝ)
    (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n) :
    (∫ U, star (observable G N a plane (realPartCharacter G ψ) m f
      (PeriodicTimeReflection.reflectConfiguration N G U)) *
      observable G N a plane (realPartCharacter G ψ) n g U
        ∂wilsonLaw N G χ beta offset) =
      (realHierarchy G N a plane ψ χ hcχ B hB beta offset).correlation
        (m+n) (reflectedTensor m n a plane f g) := by
  simp_rw [AffineCellReflection.reflected_smearing_identity G N a ha plane ψ hψ hinv,
    observable_conjugation, WilsonTensorProduct.observable_mul]
  exact expectation_eq_hierarchy G N a plane (realPartCharacter G ψ) χ
    (realPart_continuous G ψ hcψ) hcχ B (realPart_bound G ψ B hB) beta offset _ _

theorem affine_continuous (ψ : G → ℂ) (hψ : Continuous ψ) (center scale : ℂ) :
    Continuous (AffineWilsonSmearing.affineCharacter ψ center scale) :=
  continuous_const.mul (hψ.sub continuous_const)

theorem affine_class (ψ : G → ℂ) (hψ : RegulatedGauge.ClassFunction G ψ)
    (center scale : ℂ) :
    RegulatedGauge.ClassFunction G (AffineWilsonSmearing.affineCharacter ψ center scale) := by
  intro g x
  simp only [AffineWilsonSmearing.affineCharacter, hψ g x]

theorem affine_inverse (ψ : G → ℂ) (hinv : ∀ g, (ψ g⁻¹).re = (ψ g).re)
    (center scale : ℝ) :
    ∀ g, (AffineWilsonSmearing.affineCharacter ψ center scale g⁻¹).re =
      (AffineWilsonSmearing.affineCharacter ψ center scale g).re := by
  intro g
  simp only [AffineWilsonSmearing.affineCharacter, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hinv]

theorem affine_bound (ψ : G → ℂ) (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B)
    (center scale : ℂ) (g : G) :
    ‖AffineWilsonSmearing.affineCharacter ψ center scale g‖ ≤
      (‖scale‖₊ * (B + ‖center‖₊) : ℝ≥0) := by
  change ‖scale * (ψ g-center)‖ ≤ ‖scale‖ * ((B : ℝ)+‖center‖)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_sub_le _ _).trans (add_le_add (hB g) (le_refl ‖center‖))) (norm_nonneg _)

/-- Real affine insertions commute with taking the real character, so the
separately constructed hierarchy contains the intended scaled observable. -/
theorem realPart_affine (ψ : G → ℂ) (center scale : ℝ) :
    realPartCharacter G (AffineWilsonSmearing.affineCharacter ψ center scale) =
      AffineWilsonSmearing.affineCharacter (realPartCharacter G ψ) center scale := by
  funext g
  apply Complex.ext <;>
    simp [realPartCharacter, AffineWilsonSmearing.affineCharacter, Complex.mul_re,
      Complex.mul_im]

end
end UnifiedTheory.Clay.YangMills.RenormalizedWilsonHierarchy
