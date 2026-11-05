/- A normalized reflection-positive product-half Gibbs probability measure.
The coupling is a genuine exponential feature interaction; unitary Wilson
crossings are finite matrix-feature instances. Reflection exchanges the halves.
This file does not identify this split with the periodic four-dimensional lattice. -/
import UnifiedTheory.Clay.YangMills.WilsonReflectionForm
import UnifiedTheory.Clay.YangMills.RegulatedGaugeMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSplitMeasure
noncomputable section
open MeasureTheory WilsonCrossingKernel WilsonReflectionForm
open scoped ENNReal

variable {X D : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Fintype D]
  (μ : Measure X) [IsProbabilityMeasure μ]

def splitWeight (φ : X → D → ℝ) (A : X → ℝ) (β : ℝ) (z : X × X) : ℝ :=
  Real.exp (-A z.1 - A z.2 + β * featureKernel φ z.1 z.2)

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
theorem splitWeight_pos (φ : X → D → ℝ) (A : X → ℝ) (β : ℝ) (z : X × X) :
    0 < splitWeight φ A β z := Real.exp_pos _

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_splitWeight (φ : X → D → ℝ) (hφ : ∀ k, Continuous (fun x => φ x k))
    (A : X → ℝ) (hA : Continuous A) (β : ℝ) : Continuous (splitWeight φ A β) :=
  Real.continuous_exp.comp (((hA.comp continuous_fst).neg.sub (hA.comp continuous_snd)).add
    (continuous_const.mul (continuous_featureKernel φ hφ)))

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
theorem splitWeight_swap (φ : X → D → ℝ) (A : X → ℝ) (β : ℝ) (z : X × X) :
    splitWeight φ A β z.swap = splitWeight φ A β z := by
  unfold splitWeight
  dsimp only [Prod.swap]
  rw [featureKernel_symm φ z.2 z.1]
  congr 1
  ring

def splitDensity (φ : X → D → ℝ) (A : X → ℝ) (β : ℝ) (z : X × X) : ℝ≥0∞ :=
  ENNReal.ofReal (splitWeight φ A β z)

omit [CompactSpace X] in
theorem measurable_splitDensity (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (A : X → ℝ) (hA : Continuous A) (β : ℝ) :
    Measurable (splitDensity φ A β) :=
  (continuous_splitWeight φ hφ A hA β).measurable.ennreal_ofReal

def partition (φ : X → D → ℝ) (A : X → ℝ) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, splitDensity φ A β z ∂μ.prod μ

omit [CompactSpace X] in
theorem partition_pos (φ : X → D → ℝ) (hφ : ∀ k, Continuous (fun x => φ x k))
    (A : X → ℝ) (hA : Continuous A) (β : ℝ) : 0 < partition μ φ A β := by
  rw [partition, lintegral_pos_iff_support (measurable_splitDensity φ hφ A hA β)]
  have hs : Function.support (splitDensity φ A β) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (splitWeight_pos φ A β z))
  rw [hs, measure_univ]
  exact zero_lt_one

theorem partition_ne_top (φ : X → D → ℝ) (hφ : ∀ k, Continuous (fun x => φ x k))
    (A : X → ℝ) (hA : Continuous A) (β : ℝ) : partition μ φ A β ≠ ∞ := by
  have hi : Integrable (splitWeight φ A β) (μ.prod μ) :=
    (continuous_splitWeight φ hφ A hA β).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold partition splitDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun z => (splitWeight_pos φ A β z).le))]
  exact ENNReal.ofReal_ne_top

/-- The actual Gibbs measure, normalized by its finite positive partition function. -/
def splitMeasure (φ : X → D → ℝ) (A : X → ℝ) (β : ℝ) : Measure (X × X) :=
  (partition μ φ A β)⁻¹ • (μ.prod μ).withDensity (splitDensity φ A β)

theorem splitMeasure_probability (φ : X → D → ℝ) (hφ : ∀ k, Continuous (fun x => φ x k))
    (A : X → ℝ) (hA : Continuous A) (β : ℝ) :
    IsProbabilityMeasure (splitMeasure μ φ A β) := by
  constructor
  change (partition μ φ A β)⁻¹ *
    (μ.prod μ).withDensity (splitDensity φ A β) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (ne_of_gt (partition_pos μ φ hφ A hA β))
    (partition_ne_top μ φ hφ A hA β)

omit [CompactSpace X] in
theorem swap_preserves_splitMeasure (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (A : X → ℝ) (hA : Continuous A) (β : ℝ) :
    MeasurePreserving Prod.swap (splitMeasure μ φ A β) (splitMeasure μ φ A β) := by
  apply MeasurePreserving.smul_measure
  apply RegulatedGauge.preserves_withDensity Measure.measurePreserving_swap _
    (measurable_splitDensity φ hφ A hA β)
  intro z
  simp only [splitDensity, splitWeight_swap]

omit [CompactSpace X] [IsProbabilityMeasure μ] in
/-- Identify the measure-theoretic reflection expectation with its positive product form. -/
theorem splitMeasure_reflection_integral (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (A : X → ℝ) (hA : Continuous A) (β : ℝ)
    (f : X → ℂ) :
    (∫ z : X × X, star (f z.1) * f z.2 ∂splitMeasure μ φ A β) =
      ((partition μ φ A β)⁻¹).toReal •
        reflectionForm μ (fun x y => Real.exp (-A x - A y + β * featureKernel φ x y)) f := by
  unfold splitMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul
    (measurable_splitDensity φ hφ A hA β)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp only [splitDensity, ENNReal.toReal_ofReal (splitWeight_pos φ A β z).le]
  change (splitWeight φ A β z : ℂ) * (star (f z.1) * f z.2) =
    star (f z.1) * (splitWeight φ A β z : ℂ) * f z.2
  ring

def halfObservable (f : X → ℂ) (z : X × X) : ℂ := f z.2

/-- Swap-reflection positivity for every continuous observable depending on one half. -/
theorem splitMeasure_reflection_positive (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (A : X → ℝ) (hA : Continuous A)
    (β : ℝ) (hβ : 0 ≤ β) (f : X → ℂ) (hf : Continuous f) :
    0 ≤ (∫ z, star (halfObservable f z.swap) * halfObservable f z
      ∂splitMeasure μ φ A β).re ∧
      (∫ z, star (halfObservable f z.swap) * halfObservable f z
        ∂splitMeasure μ φ A β).im = 0 := by
  dsimp only [halfObservable, Prod.swap]
  rw [splitMeasure_reflection_integral μ φ hφ A hA β f]
  have hp := reflectionForm_split_nonneg μ φ hφ A hA f hf β hβ
  constructor
  · simpa only [Complex.smul_re, smul_eq_mul] using mul_nonneg ENNReal.toReal_nonneg hp.1
  · simp only [Complex.smul_im, hp.2, smul_zero]

variable {d G : Type*} [Fintype d] [DecidableEq d] [Group G]

/-- A normalized split law for the genuine unitary-character Wilson crossing weight. -/
def unitarySplitMeasure (ρ : G →* Matrix.unitaryGroup d ℂ) (h : X → G)
    (A : X → ℝ) (β : ℝ) : Measure (X × X) :=
  splitMeasure μ (fun x => matrixFeatures (ρ (h x) : Matrix d d ℂ)) A β

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
theorem unitarySplitWeight_eq (ρ : G →* Matrix.unitaryGroup d ℂ) (h : X → G)
    (A : X → ℝ) (β : ℝ) (z : X × X) :
    splitWeight (fun x => matrixFeatures (ρ (h x) : Matrix d d ℂ)) A β z =
      Real.exp (-A z.1) * crossingKernel ρ β (h z.1) (h z.2) * Real.exp (-A z.2) := by
  rw [crossingKernel_eq_exp_feature]
  unfold splitWeight
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
  change (Real.exp (-A z.1) * Real.exp (-A z.2)) * _ = _
  simp only [featureKernel]
  ring

theorem unitarySplitMeasure_probability (ρ : G →* Matrix.unitaryGroup d ℂ) (h : X → G)
    (hρh : Continuous (fun x => (ρ (h x) : Matrix d d ℂ)))
    (A : X → ℝ) (hA : Continuous A) (β : ℝ) :
    IsProbabilityMeasure (unitarySplitMeasure μ ρ h A β) :=
  splitMeasure_probability μ _ (continuous_unitary_features ρ h hρh) A hA β

theorem unitarySplitMeasure_reflection_positive (ρ : G →* Matrix.unitaryGroup d ℂ) (h : X → G)
    (hρh : Continuous (fun x => (ρ (h x) : Matrix d d ℂ)))
    (A : X → ℝ) (hA : Continuous A) (β : ℝ) (hβ : 0 ≤ β) (f : X → ℂ) (hf : Continuous f) :
    0 ≤ (∫ z, star (halfObservable f z.swap) * halfObservable f z
      ∂unitarySplitMeasure μ ρ h A β).re ∧
      (∫ z, star (halfObservable f z.swap) * halfObservable f z
        ∂unitarySplitMeasure μ ρ h A β).im = 0 :=
  splitMeasure_reflection_positive μ _ (continuous_unitary_features ρ h hρh) A hA β hβ f hf

end
end UnifiedTheory.Clay.YangMills.WilsonSplitMeasure
