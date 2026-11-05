/- Exact lattice-step translation covariance of the physical floor-cell
sampler and every bare smeared Wilson correlation order. Unlike reflection,
integer cell translations have no exceptional grid-boundary set. -/
import UnifiedTheory.Clay.YangMills.PeriodicSpacetimeTranslation
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable
import UnifiedTheory.Clay.YangMills.SchwartzTranslations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CellSpacetimeTranslation
noncomputable section
open MeasureTheory LocalFields PeriodicLattice4 PeriodicCellSampling
open PeriodicSpacetimeTranslation RegulatedGauge WilsonMomentBounds SchwartzTranslations
open ContinuumControl
open scoped NNReal

/-- One spacetime displacement repeated at every insertion. -/
def displacement (m : ℕ) (v : Spacetime) : ContinuumControl.Configuration m :=
  WithLp.toLp 2 (fun jμ => v jμ.2)

def cellVector (a : ℝ) (k : Fin 4 → ℤ) : Spacetime :=
  WithLp.toLp 2 (fun μ => a * k μ)

def integerVertex (N : ℕ) (k : Fin 4 → ℤ) : Vertex N :=
  fun μ => (k μ : ZMod N)

def pointTranslate (v : Spacetime) (x : Spacetime) : Spacetime := x + v

theorem point_add_displacement (m : ℕ) (v : Spacetime)
    (x : ContinuumControl.Configuration m) (j : Fin m) :
    point m j (x + displacement m v) = pointTranslate v (point m j x) := by
  ext μ
  rfl

theorem vertexSample_translate (N : ℕ) (a : ℝ) (ha : a ≠ 0)
    (k : Fin 4 → ℤ) (x : Spacetime) :
    vertexSample N a (pointTranslate (cellVector a k) x) =
      shiftVertex N (integerVertex N k) (vertexSample N a x) := by
  funext μ
  change (⌊(x μ + a * k μ) / a⌋ : ZMod N) = (⌊x μ / a⌋ : ZMod N) + k μ
  rw [add_div, mul_div_cancel_left₀ (k μ : ℝ) ha, Int.floor_add_intCast, Int.cast_add]

theorem sample_translate (N : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (k : Fin 4 → ℤ) (x : Spacetime) :
    sample N a plane (pointTranslate (cellVector a k) x) = shiftPlaquette N (integerVertex N k) (sample N a plane x) :=
  Prod.ext (vertexSample_translate N a ha k x) rfl

theorem sampleConfiguration_translate (m N : ℕ) (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (k : Fin 4 → ℤ) (x : ContinuumControl.Configuration m) :
    sampleConfiguration m N a plane (x + displacement m (cellVector a k)) =
      fun j => shiftPlaquette N (integerVertex N k) (sampleConfiguration m N a plane x j) := by
  funext j
  exact (congrArg (sample N a plane) (point_add_displacement m (cellVector a k) x j)).trans
    (sample_translate N a ha plane k (point m j x))

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

theorem word_shift (χ : G → ℂ) (m : ℕ) (q : Fin m → PlaquetteIndex N)
    (s : Vertex N) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.word G N χ m q (shiftConfiguration N G s U) =
      WilsonSmearedObservable.word G N χ m (fun j => shiftPlaquette N s (q j)) U := by
  apply Finset.prod_congr rfl
  intro j _
  change χ (holonomy (Quiver.Symmetrify (Vertex N)) G (orientedExtension (Vertex N) G
    (shiftConfiguration N G s U)) (plaquette N (q j).1 (q j).2.1.1 (q j).2.1.2)) = _
  rw [plaquette_holonomy_shift]
  rfl

theorem sampled_word_shift (χ : G → ℂ) (m : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (k : Fin 4 → ℤ) (x : ContinuumControl.Configuration m) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.word G N χ m (sampleConfiguration m N a plane x)
        (shiftConfiguration N G (integerVertex N k) U) =
      WilsonSmearedObservable.word G N χ m
        (sampleConfiguration m N a plane (x + displacement m (cellVector a k))) U := by
  rw [word_shift, sampleConfiguration_translate m N a ha plane k x]

/-- A physical test displacement by a*k is exactly the pullback by k lattice
steps, for every insertion order and every configuration. -/
theorem observable_translation (χ : G → ℂ) (m : ℕ) (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (k : Fin 4 → ℤ) (f : CorrelationTest m) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane χ m (translationCLM (displacement m (cellVector a k)) f) U =
      WilsonSmearedObservable.observable G N a plane χ m f (shiftConfiguration N G (integerVertex N k) U) := by
  rw [WilsonSmearedObservable.observable_integral, WilsonSmearedObservable.observable_integral]
  simp only [translationCLM_apply]
  rw [← integral_add_right_eq_self
    (fun x : ContinuumControl.Configuration m => WilsonSmearedObservable.word G N χ m
      (sampleConfiguration m N a plane x) U * f (x - displacement m (cellVector a k)))
    (displacement m (cellVector a k))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [add_sub_cancel_right, ← sampled_word_shift G N χ m a ha plane k x U])

/-- Actual finite Wilson expectations inherit the exact physical cell-step
translation symmetry, at every Schwartz correlation order. -/
theorem expectation_translation (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (m : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane) (k : Fin 4 → ℤ) (f : CorrelationTest m) :
    (∫ U, WilsonSmearedObservable.observable G N a plane χ m
      (translationCLM (displacement m (cellVector a k)) f) U ∂wilsonLaw N G χ β c) =
    ∫ U, WilsonSmearedObservable.observable G N a plane χ m f U ∂wilsonLaw N G χ β c := by
  simp_rw [observable_translation G N χ m a ha plane k f]
  exact (wilsonLaw_preserves_shift N G χ hcχ β c (integerVertex N k)).integral_comp
    (configurationShiftMeasurableEquiv N G (integerVertex N k)).measurableEmbedding _

theorem hierarchy_translation (χ : G → ℂ) (hcχ : Continuous χ) (B : ℝ≥0)
    (hB : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ) (m : ℕ) (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (k : Fin 4 → ℤ) (f : CorrelationTest m) :
    (WilsonCellHierarchy.hierarchy G N a plane χ hcχ B hB β c).correlation m
      (translationCLM (displacement m (cellVector a k)) f) =
    (WilsonCellHierarchy.hierarchy G N a plane χ hcχ B hB β c).correlation m f := by
  rw [← WilsonSmearedObservable.expectation_eq_hierarchy,
    ← WilsonSmearedObservable.expectation_eq_hierarchy]
  exact expectation_translation G N χ hcχ β c m a ha plane k f

end
end UnifiedTheory.Clay.YangMills.CellSpacetimeTranslation
