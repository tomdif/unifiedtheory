/- Exact lattice-step translation covariance of the physical floor-cell
sampler and every bare smeared Wilson correlation order. Unlike reflection,
integer cell translations have no exceptional grid-boundary set. -/
import UnifiedTheory.Clay.YangMills.WilsonTranslationUnitary
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable
import UnifiedTheory.Clay.YangMills.SchwartzTranslations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CellTranslationCovariance
noncomputable section
open MeasureTheory LocalFields PeriodicLattice4 PeriodicCellSampling
open PeriodicTimeTranslation RegulatedGauge WilsonMomentBounds SchwartzTranslations
open ContinuumControl
open scoped NNReal

/-- Physical time displacement, repeated at every insertion. -/
def timeVector (m : ℕ) (t : ℝ) : ContinuumControl.Configuration m :=
  WithLp.toLp 2 (fun jμ => if jμ.2 = 0 then t else 0)

def pointTranslate (t : ℝ) (x : Spacetime) : Spacetime :=
  x + WithLp.toLp 2 (fun μ => if μ = 0 then t else 0)

theorem point_add_timeVector (m : ℕ) (t : ℝ) (x : ContinuumControl.Configuration m) (j : Fin m) :
    point m j (x + timeVector m t) = pointTranslate t (point m j x) := by
  ext μ
  rfl

theorem vertexSample_translate (N : ℕ) (a : ℝ) (ha : a ≠ 0) (k : ℤ) (x : Spacetime) :
    vertexSample N a (pointTranslate (a * k) x) = shiftVertex N (k : ZMod N) (vertexSample N a x) := by
  funext μ
  by_cases hμ : μ = 0
  · subst μ
    change (⌊(x 0 + a * k) / a⌋ : ZMod N) = (⌊x 0 / a⌋ : ZMod N) + k
    rw [add_div, mul_div_cancel_left₀ (k : ℝ) ha, Int.floor_add_intCast, Int.cast_add]
  · simp [vertexSample, pointTranslate, shiftVertex, hμ]

theorem sample_translate (N : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (k : ℤ) (x : Spacetime) :
    sample N a plane (pointTranslate (a * k) x) = shiftPlaquette N (k : ZMod N) (sample N a plane x) :=
  Prod.ext (vertexSample_translate N a ha k x) rfl

theorem sampleConfiguration_translate (m N : ℕ) (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (k : ℤ) (x : ContinuumControl.Configuration m) :
    sampleConfiguration m N a plane (x + timeVector m (a * k)) =
      fun j => shiftPlaquette N (k : ZMod N) (sampleConfiguration m N a plane x j) := by
  funext j
  exact (congrArg (sample N a plane) (point_add_timeVector m (a * k) x j)).trans
    (sample_translate N a ha plane k (point m j x))

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

theorem word_shift (χ : G → ℂ) (m : ℕ) (q : Fin m → PlaquetteIndex N)
    (s : ZMod N) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.word G N χ m q (shiftConfiguration N G s U) =
      WilsonSmearedObservable.word G N χ m (fun j => shiftPlaquette N s (q j)) U := by
  apply Finset.prod_congr rfl
  intro j _
  change χ (holonomy (Quiver.Symmetrify (Vertex N)) G (orientedExtension (Vertex N) G
    (shiftConfiguration N G s U)) (plaquette N (q j).1 (q j).2.1.1 (q j).2.1.2)) = _
  rw [plaquette_holonomy_shift]
  rfl

theorem sampled_word_shift (χ : G → ℂ) (m : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (k : ℤ) (x : ContinuumControl.Configuration m) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.word G N χ m (sampleConfiguration m N a plane x)
        (shiftConfiguration N G (k : ZMod N) U) =
      WilsonSmearedObservable.word G N χ m
        (sampleConfiguration m N a plane (x + timeVector m (a * k))) U := by
  rw [word_shift, sampleConfiguration_translate m N a ha plane k x]

/-- A physical test displacement by a*k is exactly the pullback by k lattice
steps, for every insertion order and every configuration. -/
theorem observable_translation (χ : G → ℂ) (m : ℕ) (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (k : ℤ) (f : CorrelationTest m) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane χ m (translationCLM (timeVector m (a * k)) f) U =
      WilsonSmearedObservable.observable G N a plane χ m f (shiftConfiguration N G (k : ZMod N) U) := by
  rw [WilsonSmearedObservable.observable_integral, WilsonSmearedObservable.observable_integral]
  simp only [translationCLM_apply]
  rw [← integral_add_right_eq_self
    (fun x : ContinuumControl.Configuration m => WilsonSmearedObservable.word G N χ m
      (sampleConfiguration m N a plane x) U * f (x - timeVector m (a * k)))
    (timeVector m (a * k))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [add_sub_cancel_right, ← sampled_word_shift G N χ m a ha plane k x U])

/-- Actual finite Wilson expectations inherit the exact physical cell-step
translation symmetry, at every Schwartz correlation order. -/
theorem expectation_translation (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (m : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane) (k : ℤ) (f : CorrelationTest m) :
    (∫ U, WilsonSmearedObservable.observable G N a plane χ m
      (translationCLM (timeVector m (a * k)) f) U ∂wilsonLaw N G χ β c) =
    ∫ U, WilsonSmearedObservable.observable G N a plane χ m f U ∂wilsonLaw N G χ β c := by
  simp_rw [observable_translation G N χ m a ha plane k f]
  exact (wilsonLaw_preserves_shift N G χ hcχ β c (k : ZMod N)).integral_comp
    (configurationShiftMeasurableEquiv N G (k : ZMod N)).measurableEmbedding _

theorem hierarchy_translation (χ : G → ℂ) (hcχ : Continuous χ) (B : ℝ≥0)
    (hB : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ) (m : ℕ) (a : ℝ) (ha : a ≠ 0)
    (plane : Plane) (k : ℤ) (f : CorrelationTest m) :
    (WilsonCellHierarchy.hierarchy G N a plane χ hcχ B hB β c).correlation m
      (translationCLM (timeVector m (a * k)) f) =
    (WilsonCellHierarchy.hierarchy G N a plane χ hcχ B hB β c).correlation m f := by
  rw [← WilsonSmearedObservable.expectation_eq_hierarchy,
    ← WilsonSmearedObservable.expectation_eq_hierarchy]
  exact expectation_translation G N χ hcχ β c m a ha plane k f

/-- The actual smeared observable as an ordinary Wilson L2 state. -/
def smearedState (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (m : ℕ) (a : ℝ) (plane : Plane) (f : CorrelationTest m) :
    WilsonTranslationUnitary.StateSpace N G χ β c := by
  letI := wilsonLaw_probability N G χ hcχ β c
  exact ContinuousMap.toLp 2 (wilsonLaw N G χ β c) ℂ
    ⟨WilsonSmearedObservable.observable G N a plane χ m f,
      WilsonSmearedObservable.observable_continuous G N a plane χ hcχ m f⟩

theorem smearedState_ae (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (m : ℕ) (a : ℝ) (plane : Plane) (f : CorrelationTest m) :
    smearedState G N χ hcχ β c m a plane f =ᵐ[wilsonLaw N G χ β c]
      WilsonSmearedObservable.observable G N a plane χ m f := by
  letI := wilsonLaw_probability N G χ hcχ β c
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (wilsonLaw N G χ β c)
    ⟨_, WilsonSmearedObservable.observable_continuous G N a plane χ hcχ m f⟩

/-- The constructed cyclic unitary acts on the actual smeared states by the
physical Schwartz-test translation, simultaneously at every insertion. -/
theorem unitary_smearedState (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (m : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane) (k : ℤ) (f : CorrelationTest m) :
    WilsonTranslationUnitary.shiftUnitary N G χ hcχ β c (k : ZMod N)
      (smearedState G N χ hcχ β c m a plane f) =
    smearedState G N χ hcχ β c m a plane (translationCLM (timeVector m (a * k)) f) := by
  apply Lp.ext
  have hp := (wilsonLaw_preserves_shift N G χ hcχ β c (k : ZMod N)).quasiMeasurePreserving.ae
    (smearedState_ae G N χ hcχ β c m a plane f)
  filter_upwards [WilsonTranslationUnitary.shiftL2_ae N G χ hcχ β c (k : ZMod N)
      (smearedState G N χ hcχ β c m a plane f), hp,
    smearedState_ae G N χ hcχ β c m a plane (translationCLM (timeVector m (a * k)) f)]
    with U h₁ h₂ h₃
  change (WilsonTranslationUnitary.shiftL2 N G χ hcχ β c (k : ZMod N)
    (smearedState G N χ hcχ β c m a plane f)) U = _
  simp only [Function.comp_apply] at h₁ h₂
  rw [h₁, h₂, h₃, observable_translation G N χ m a ha plane k f U]

end
end UnifiedTheory.Clay.YangMills.CellTranslationCovariance
