/- Reverse edges are the inverses of forward links, not new integration variables.
This construction extends the regulated gauge layer to ordinary oriented lattice
loops. Compactness gives a normalized finite-volume Gibbs law for every continuous
action, including the oriented Wilson action. No continuum assertions are made. -/
import UnifiedTheory.Clay.YangMills.RegulatedGaugeMeasure
import Mathlib.Combinatorics.Quiver.Symmetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RegulatedGauge
noncomputable section
open MeasureTheory
open scoped ENNReal

variable (V : Type*) [Quiver V] (G : Type*) [Group G]

/-- Extend independent forward links to formal backward edges by inversion. -/
def orientedExtension (U : Configuration V G) : Configuration (Quiver.Symmetrify V) G :=
  fun ⟨_, _, e⟩ => match e with
    | Sum.inl e => link V G U e
    | Sum.inr e => (link V G U e)⁻¹

theorem orientedExtension_reverse (U : Configuration V G)
    {a b : Quiver.Symmetrify V} (e : a ⟶ b) :
    link (Quiver.Symmetrify V) G (orientedExtension V G U) (Quiver.reverse e) =
      (link (Quiver.Symmetrify V) G (orientedExtension V G U) e)⁻¹ := by
  cases e <;> simp [link, orientedExtension, Quiver.symmetrify_reverse]

theorem orientedExtension_gauge (g : GaugeTransformation V G) (U : Configuration V G) :
    orientedExtension V G (gauge V G g U) =
      gauge (Quiver.Symmetrify V) G g (orientedExtension V G U) := by
  funext e
  rcases e with ⟨a, b, e⟩
  cases e <;> simp [orientedExtension, link, gauge, mul_assoc]

theorem oriented_holonomy_reverse (U : Configuration V G)
    {a b : Quiver.Symmetrify V} (p : Quiver.Path a b) :
    holonomy (Quiver.Symmetrify V) G (orientedExtension V G U) p.reverse =
      (holonomy (Quiver.Symmetrify V) G (orientedExtension V G U) p)⁻¹ := by
  induction p with
  | nil => simp [Quiver.Path.reverse, holonomy]
  | cons p e hp =>
    rw [Quiver.Path.reverse, holonomy_comp, hp]
    simp only [Quiver.Hom.toPath, holonomy_cons, holonomy_nil, one_mul,
      orientedExtension_reverse, mul_inv_rev]

theorem oriented_holonomy_gauge (g : GaugeTransformation V G) (U : Configuration V G)
    {a b : Quiver.Symmetrify V} (p : Quiver.Path a b) :
    holonomy (Quiver.Symmetrify V) G (orientedExtension V G (gauge V G g U)) p =
      g a * holonomy (Quiver.Symmetrify V) G (orientedExtension V G U) p * (g b)⁻¹ := by
  rw [orientedExtension_gauge, holonomy_gauge]

variable {P : Type*} [Fintype P]

/-- Wilson action evaluated on loops with backward links fixed by inversion. -/
def orientedWilsonAction (χ : G → ℂ) (base : P → Quiver.Symmetrify V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) (U : Configuration V G) : ℝ :=
  wilsonAction (Quiver.Symmetrify V) G χ base loops β c (orientedExtension V G U)

theorem orientedWilsonAction_gauge (χ : G → ℂ) (hχ : ClassFunction G χ)
    (base : P → Quiver.Symmetrify V) (loops : ∀ p, Quiver.Path (base p) (base p))
    (β c : ℝ) (g : GaugeTransformation V G) (U : Configuration V G) :
    orientedWilsonAction V G χ base loops β c (gauge V G g U) =
      orientedWilsonAction V G χ base loops β c U := by
  unfold orientedWilsonAction
  rw [orientedExtension_gauge, wilsonAction_gauge _ _ χ hχ]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_orientedExtension : Continuous (orientedExtension V G) := by
  apply continuous_pi
  rintro ⟨a, b, e⟩
  cases e with
  | inl e => exact continuous_apply _
  | inr e => exact (continuous_apply _).inv

theorem continuous_orientedWilsonAction (χ : G → ℂ) (hχ : Continuous χ)
    (base : P → Quiver.Symmetrify V) (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    Continuous (orientedWilsonAction V G χ base loops β c) :=
  (continuous_wilsonAction (Quiver.Symmetrify V) G χ hχ base loops β c).comp
    (continuous_orientedExtension V G)

variable [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Fintype (Edge V)]

def gibbsDensity (S : Configuration V G → ℝ) (U : Configuration V G) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-S U))

def gibbsPartition (S : Configuration V G → ℝ) : ℝ≥0∞ :=
  ∫⁻ U, gibbsDensity V G S U ∂referenceMeasure G V

theorem gibbsPartition_pos (S : Configuration V G → ℝ) (hS : Continuous S) :
    0 < gibbsPartition V G S := by
  have hm : Measurable (gibbsDensity V G S) :=
    (Real.continuous_exp.comp hS.neg).measurable.ennreal_ofReal
  rw [gibbsPartition, lintegral_pos_iff_support hm]
  have hs : Function.support (gibbsDensity V G S) = Set.univ := by
    ext U
    simp [gibbsDensity, Function.mem_support, Real.exp_pos]
  rw [hs, measure_univ]
  exact zero_lt_one

theorem gibbsPartition_ne_top (S : Configuration V G → ℝ) (hS : Continuous S) :
    gibbsPartition V G S ≠ ∞ := by
  have hi : Integrable (fun U => Real.exp (-S U)) (referenceMeasure G V) :=
    (Real.continuous_exp.comp hS.neg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold gibbsPartition gibbsDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun U => (Real.exp_pos (-S U)).le))]
  exact ENNReal.ofReal_ne_top

def gibbsMeasure (S : Configuration V G → ℝ) : Measure (Configuration V G) :=
  (gibbsPartition V G S)⁻¹ • (referenceMeasure G V).withDensity (gibbsDensity V G S)

theorem gibbsMeasure_probability (S : Configuration V G → ℝ) (hS : Continuous S) :
    IsProbabilityMeasure (gibbsMeasure V G S) := by
  constructor
  change (gibbsPartition V G S)⁻¹ *
    (referenceMeasure G V).withDensity (gibbsDensity V G S) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (ne_of_gt (gibbsPartition_pos V G S hS))
    (gibbsPartition_ne_top V G S hS)

theorem gauge_preserves_gibbsMeasure (S : Configuration V G → ℝ) (hS : Continuous S)
    (hinv : ∀ g U, S (gauge V G g U) = S U) (g : GaugeTransformation V G) :
    MeasurePreserving (gauge V G g) (gibbsMeasure V G S) (gibbsMeasure V G S) := by
  apply MeasurePreserving.smul_measure
  apply preserves_withDensity (gauge_preserves_reference G V g) _
    (Real.continuous_exp.comp hS.neg).measurable.ennreal_ofReal
  intro U
  exact congrArg (fun t : ℝ => ENNReal.ofReal (Real.exp (-t))) (hinv g U)

/-- A normalized Wilson law whose integration variables are forward edges only. -/
def orientedWilsonMeasure (χ : G → ℂ) (base : P → Quiver.Symmetrify V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) : Measure (Configuration V G) :=
  gibbsMeasure V G (orientedWilsonAction V G χ base loops β c)

theorem orientedWilsonMeasure_probability (χ : G → ℂ) (hχ : Continuous χ)
    (base : P → Quiver.Symmetrify V) (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    IsProbabilityMeasure (orientedWilsonMeasure V G χ base loops β c) :=
  gibbsMeasure_probability V G _ (continuous_orientedWilsonAction V G χ hχ base loops β c)

theorem gauge_preserves_orientedWilsonMeasure (χ : G → ℂ) (hcχ : Continuous χ)
    (hiχ : ClassFunction G χ) (base : P → Quiver.Symmetrify V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ)
    (g : GaugeTransformation V G) :
    MeasurePreserving (gauge V G g) (orientedWilsonMeasure V G χ base loops β c)
      (orientedWilsonMeasure V G χ base loops β c) :=
  gauge_preserves_gibbsMeasure V G _ (continuous_orientedWilsonAction V G χ hcχ base loops β c)
    (orientedWilsonAction_gauge V G χ hiχ base loops β c) g

end
end UnifiedTheory.Clay.YangMills.RegulatedGauge
