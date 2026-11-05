/- Finite-volume gauge-invariant Wilson probability measures for compact groups.
The normalized Haar reference measure is constructed, not postulated. The graph
has finitely many edges; the gauge group need not be finite or commutative.
No reflection positivity, scaling limit, or continuum mass gap is claimed. -/
import UnifiedTheory.Clay.YangMills.RegulatedGauge
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RegulatedGauge
noncomputable section
open MeasureTheory
open scoped ENNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized on the entire compact group. -/
def compactHaar : Measure G := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)

instance compactHaar_probability : IsProbabilityMeasure (compactHaar G) where
  measure_univ := Measure.haarMeasure_self

instance compactHaar_left : (compactHaar G).IsMulLeftInvariant := by
  unfold compactHaar
  infer_instance

/-- Right invariance follows from Haar uniqueness and normalization. -/
instance compactHaar_right : (compactHaar G).IsMulRightInvariant := by
  constructor
  intro g
  have hm : IsProbabilityMeasure ((compactHaar G).map (fun x => x * g)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact ((Measure.haarMeasure_eq_iff (⊤ : TopologicalSpace.PositiveCompacts G)
    ((compactHaar G).map (fun x => x * g))).2 (by simp)).symm

variable (V : Type*) [Quiver V] [Fintype (Edge V)]

/-- Independent normalized Haar links on a finite directed graph. -/
def referenceMeasure : Measure (Configuration V G) := Measure.pi (fun _ : Edge V => compactHaar G)

instance referenceMeasure_probability : IsProbabilityMeasure (referenceMeasure G V) := by
  unfold referenceMeasure
  infer_instance

theorem gauge_preserves_reference (g : GaugeTransformation V G) :
    MeasurePreserving (gauge V G g) (referenceMeasure G V) (referenceMeasure G V) := by
  exact measurePreserving_pi (fun _ : Edge V => compactHaar G) (fun _ : Edge V => compactHaar G)
    (fun e => (measurePreserving_mul_right (compactHaar G) (g e.2.1)⁻¹).comp
      (measurePreserving_mul_left (compactHaar G) (g e.1)))

/-- An invariant density preserves the symmetries of its reference measure. -/
theorem preserves_withDensity {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {T : X → X} (hT : MeasurePreserving T μ μ) (f : X → ℝ≥0∞)
    (hf : Measurable f) (hinv : ∀ x, f (T x) = f x) :
    MeasurePreserving T (μ.withDensity f) (μ.withDensity f) := by
  refine ⟨hT.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hT.measurable hs, withDensity_apply _ (hT.measurable hs),
    withDensity_apply _ hs]
  simpa only [hinv] using hT.setLIntegral_comp_preimage hs hf

variable {P : Type*} [Fintype P]

def wilsonDensity (χ : G → ℂ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) : Configuration V G → ℝ≥0∞ :=
  fun U => ENNReal.ofReal (boltzmannWeight V G χ base loops β c U)

omit [CompactSpace G] [Fintype (Edge V)] in
theorem measurable_wilsonDensity [Countable (Edge V)]
    (χ : G → ℂ) (hχ : Continuous χ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    Measurable (wilsonDensity G V χ base loops β c) :=
  (continuous_boltzmannWeight V G χ hχ base loops β c).measurable.ennreal_ofReal

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype (Edge V)] in
theorem wilsonDensity_pos (χ : G → ℂ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) (U : Configuration V G) :
    0 < wilsonDensity G V χ base loops β c U :=
  ENNReal.ofReal_pos.mpr (boltzmannWeight_pos V G χ base loops β c U)

def wilsonPartition (χ : G → ℂ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) : ℝ≥0∞ :=
  ∫⁻ U, wilsonDensity G V χ base loops β c U ∂referenceMeasure G V

theorem wilsonPartition_pos (χ : G → ℂ) (hχ : Continuous χ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    0 < wilsonPartition G V χ base loops β c := by
  rw [wilsonPartition, lintegral_pos_iff_support (measurable_wilsonDensity G V χ hχ base loops β c)]
  have hs : Function.support (wilsonDensity G V χ base loops β c) = Set.univ := by
    ext U
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (wilsonDensity_pos G V χ base loops β c U)
  rw [hs, measure_univ]
  exact zero_lt_one

theorem integrable_boltzmannWeight (χ : G → ℂ) (hχ : Continuous χ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    Integrable (boltzmannWeight V G χ base loops β c) (referenceMeasure G V) := by
  exact (continuous_boltzmannWeight V G χ hχ base loops β c).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem wilsonPartition_ne_top (χ : G → ℂ) (hχ : Continuous χ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    wilsonPartition G V χ base loops β c ≠ ∞ := by
  unfold wilsonPartition wilsonDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_boltzmannWeight G V χ hχ base loops β c)
    (Filter.Eventually.of_forall (fun U => (boltzmannWeight_pos V G χ base loops β c U).le))]
  exact ENNReal.ofReal_ne_top

/-- The finite-volume Wilson law with an explicitly constructed partition function. -/
def wilsonMeasure (χ : G → ℂ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) : Measure (Configuration V G) :=
  (wilsonPartition G V χ base loops β c)⁻¹ •
    (referenceMeasure G V).withDensity (wilsonDensity G V χ base loops β c)

theorem wilsonMeasure_probability (χ : G → ℂ) (hχ : Continuous χ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    IsProbabilityMeasure (wilsonMeasure G V χ base loops β c) := by
  constructor
  change (wilsonPartition G V χ base loops β c)⁻¹ *
    (referenceMeasure G V).withDensity (wilsonDensity G V χ base loops β c) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (ne_of_gt (wilsonPartition_pos G V χ hχ base loops β c))
    (wilsonPartition_ne_top G V χ hχ base loops β c)

theorem gauge_preserves_wilsonMeasure (χ : G → ℂ) (hcχ : Continuous χ)
    (hiχ : ClassFunction G χ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ)
    (g : GaugeTransformation V G) :
    MeasurePreserving (gauge V G g) (wilsonMeasure G V χ base loops β c)
      (wilsonMeasure G V χ base loops β c) := by
  apply MeasurePreserving.smul_measure
  apply preserves_withDensity (gauge_preserves_reference G V g) _
    (measurable_wilsonDensity G V χ hcχ base loops β c)
  intro U
  simp only [wilsonDensity, boltzmannWeight_gauge V G χ hiχ]

end
end UnifiedTheory.Clay.YangMills.RegulatedGauge
