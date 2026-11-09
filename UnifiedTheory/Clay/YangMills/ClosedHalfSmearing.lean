/- Actual smeared Wilson observables supported on a closed lattice half.
Finite-cell support is explicit; no continuum support-identification is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable
import UnifiedTheory.Clay.YangMills.ReflectedWilsonKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ClosedHalfSmearing
noncomputable section
open MeasureTheory PeriodicLattice4 PeriodicHalfSplit PeriodicHalfAction
open PeriodicPlaquetteReflection PeriodicTimeReflection ContinuumControl

variable (n : ℕ) [NeZero n]

def ClosedWord (m : ℕ) (q : Fin m → PlaquetteIndex (2 * n)) : Prop :=
  ∀ j, BoundaryP n (q j) ∨ PositiveP n (q j)

def Supported (a : ℝ) (plane : Plane) (m : ℕ) (f : CorrelationTest m) : Prop :=
  ∀ x, f x ≠ 0 → ClosedWord n m (PeriodicCellSampling.sampleConfiguration m (2 * n) a plane x)

theorem coefficient_zero_outside (a : ℝ) (plane : Plane) (m : ℕ) (f : CorrelationTest m)
    (hf : Supported n a plane m f) (q : Fin m → PlaquetteIndex (2 * n))
    (hq : ¬ ClosedWord n m q) :
    WilsonSmearedObservable.cellCoefficient (2 * n) a plane m q f = 0 := by
  unfold WilsonSmearedObservable.cellCoefficient FiniteCellSmearing.coefficient
  have he (x : Configuration m) :
      FiniteCellSmearing.cellFunction (PeriodicCellSampling.sampleConfiguration m (2*n) a plane) q f x = 0 := by
    unfold FiniteCellSmearing.cellFunction
    split_ifs with hx
    · by_contra hnonzero
      exact hq (hx ▸ hf x hnonzero)
    · rfl
  simp_rw [he]
  exact integral_zero _ _

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem word_independent (χ : G → ℂ) (m : ℕ) (q : Fin m → PlaquetteIndex (2 * n))
    (hq : ClosedWord n m q) (b : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    WilsonSmearedObservable.word G (2*n) χ m q (assemble n G (b,(x,y))) =
      WilsonSmearedObservable.word G (2*n) χ m q (assemble n G (b,(x,z))) := by
  unfold WilsonSmearedObservable.word
  apply Finset.prod_congr rfl
  intro j _
  change χ (RegulatedGauge.holonomy _ G _ (plaquette (2*n) (q j).1 (q j).2.1.1 (q j).2.1.2)) =
    χ (RegulatedGauge.holonomy _ G _ (plaquette (2*n) (q j).1 (q j).2.1.1 (q j).2.1.2))
  simp only [plaquette_holonomy_eq_product]
  apply congrArg χ
  rcases hq j with hb | hp
  · exact boundary_plaquette_independent n G (q j) hb b x y x z
  · exact positive_plaquette_independent n G (q j) hp b x y z

theorem observable_independent (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (m : ℕ) (f : CorrelationTest m) (hf : Supported n a plane m f)
    (b : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    WilsonSmearedObservable.observable G (2*n) a plane χ m f (assemble n G (b,(x,y))) =
      WilsonSmearedObservable.observable G (2*n) a plane χ m f (assemble n G (b,(x,z))) := by
  classical
  unfold WilsonSmearedObservable.observable FiniteCellSmearing.observable
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : ClosedWord n m q
  · rw [word_independent n G χ m q hq b x y z]
  · change WilsonSmearedObservable.cellCoefficient (2*n) a plane m q f * _ =
      WilsonSmearedObservable.cellCoefficient (2*n) a plane m q f * _
    rw [coefficient_zero_outside n a plane m f hf q hq, zero_mul, zero_mul]

def halfObservable (a : ℝ) (plane : Plane) (χ : G → ℂ) (m : ℕ) (f : CorrelationTest m)
    (z : BoundaryConfiguration n G × HalfConfiguration n G) : ℂ :=
  WilsonSmearedObservable.observable G (2*n) a plane χ m f (assemble n G (z.1,(z.2,1)))

theorem halfObservable_continuous (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (m : ℕ) (f : CorrelationTest m) : Continuous (halfObservable n G a plane χ m f) :=
  (WilsonSmearedObservable.observable_continuous G (2*n) a plane χ hcχ m f).comp
    ((continuous_assemble n G).comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))

/-- The support-restricted smeared observable is exactly a closed-half function. -/
theorem half_identification (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (m : ℕ) (f : CorrelationTest m) (hf : Supported n a plane m f)
    (U : RegulatedGauge.Configuration (Vertex (2*n)) G) :
    WilsonSmearedObservable.observable G (2*n) a plane χ m f U =
      ReflectedWilsonKernel.positiveObservable n G (halfObservable n G a plane χ m f) U := by
  have he := observable_independent n G a plane χ m f hf
    (splitConfiguration n G U).1 (splitConfiguration n G U).2.1
    (splitConfiguration n G U).2.2 1
  rw [show ((splitConfiguration n G U).1,
    ((splitConfiguration n G U).2.1,(splitConfiguration n G U).2.2)) =
    splitConfiguration n G U from rfl, assemble_split] at he
  exact he

theorem reflection_positive (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (β c : ℝ) (m : ℕ) (f : CorrelationTest m) (hf : Supported n a plane m f) :
    0 ≤ (∫ U, star (WilsonSmearedObservable.observable G (2*n) a plane χ m f
      (reflectConfiguration (2*n) G U)) * WilsonSmearedObservable.observable G (2*n) a plane χ m f U
        ∂wilsonLaw (2*n) G χ β c).re ∧
    (∫ U, star (WilsonSmearedObservable.observable G (2*n) a plane χ m f
      (reflectConfiguration (2*n) G U)) * WilsonSmearedObservable.observable G (2*n) a plane χ m f U
        ∂wilsonLaw (2*n) G χ β c).im = 0 := by
  simp_rw [half_identification n G a plane χ m f hf]
  exact ReflectedWilsonKernel.positive_reflection_positive n G χ hcχ hχ hinv β c
    (halfObservable n G a plane χ m f) (halfObservable_continuous n G a plane χ hcχ m f)

end
end UnifiedTheory.Clay.YangMills.ClosedHalfSmearing
