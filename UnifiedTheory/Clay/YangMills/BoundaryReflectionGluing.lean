/- Conditional gluing across fixed reflection-boundary variables. The law is
constructed on B x (X x X); equality with a lattice law must be supplied by an
actual coordinate/action identification, not by this positivity theorem. -/
import UnifiedTheory.Clay.YangMills.WilsonSplitMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.BoundaryReflectionGluing
noncomputable section
open MeasureTheory
open scoped ENNReal

variable {B X : Type*} [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

def weight (w : B → ℝ) (A : B × X → ℝ) (z : B × (X × X)) : ℝ :=
  w z.1 * Real.exp (-A (z.1, z.2.1)) * Real.exp (-A (z.1, z.2.2))

def reflection (z : B × (X × X)) : B × (X × X) := (z.1, z.2.swap)

theorem reflection_involutive : Function.Involutive (reflection (B := B) (X := X)) := by
  intro z
  rfl

theorem weight_positive (w : B → ℝ) (hw : ∀ b, 0 < w b) (A : B × X → ℝ)
    (z : B × (X × X)) : 0 < weight w A z :=
  mul_pos (mul_pos (hw z.1) (Real.exp_pos _)) (Real.exp_pos _)

theorem weight_continuous (w : B → ℝ) (hw : Continuous w)
    (A : B × X → ℝ) (hA : Continuous A) : Continuous (weight w A) := by
  unfold weight
  fun_prop

theorem weight_reflection (w : B → ℝ) (A : B × X → ℝ) (z : B × (X × X)) :
    weight w A (reflection z) = weight w A z := by
  simp only [weight, reflection, Prod.swap]
  ring

def partition (w : B → ℝ) (A : B × X → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (weight w A z) ∂μB.prod (μX.prod μX)

theorem partition_positive (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) : 0 < partition μB μX w A := by
  rw [partition, lintegral_pos_iff_support (weight_continuous w hcw A hA).measurable.ennreal_ofReal]
  have hs : Function.support (fun z => ENNReal.ofReal (weight w A z)) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (weight_positive w hw A z)).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

theorem partition_ne_top (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) : partition μB μX w A ≠ ∞ := by
  have hi := (weight_continuous w hcw A hA).integrable_of_hasCompactSupport
    (μ := μB.prod (μX.prod μX)) (HasCompactSupport.of_compactSpace _)
  unfold partition
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun z => (weight_positive w hw A z).le))]
  exact ENNReal.ofReal_ne_top

def law (w : B → ℝ) (A : B × X → ℝ) : Measure (B × (X × X)) :=
  (partition μB μX w A)⁻¹ •
    (μB.prod (μX.prod μX)).withDensity (fun z => ENNReal.ofReal (weight w A z))

theorem law_probability (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) : IsProbabilityMeasure (law μB μX w A) := by
  constructor
  change (partition μB μX w A)⁻¹ *
    (μB.prod (μX.prod μX)).withDensity (fun z => ENNReal.ofReal (weight w A z)) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (partition_positive μB μX w hcw hw A hA).ne'
    (partition_ne_top μB μX w hcw hw A hA)

theorem reference_reflection : MeasurePreserving (reflection (B := B) (X := X))
    (μB.prod (μX.prod μX)) (μB.prod (μX.prod μX)) :=
  (MeasurePreserving.id μB).prod Measure.measurePreserving_swap

theorem law_reflection (w : B → ℝ) (hcw : Continuous w)
    (A : B × X → ℝ) (hA : Continuous A) :
    MeasurePreserving reflection (law μB μX w A) (law μB μX w A) := by
  apply MeasurePreserving.smul_measure
  exact RegulatedGauge.preserves_withDensity (reference_reflection μB μX) _
    (weight_continuous w hcw A hA).measurable.ennreal_ofReal
    (fun z => congrArg ENNReal.ofReal (weight_reflection w A z))

def halfObservable (f : B × X → ℂ) (z : B × (X × X)) : ℂ := f (z.1, z.2.2)

def amplitude (A : B × X → ℝ) (f : B × X → ℂ) (b : B) : ℂ :=
  ∫ x, (Real.exp (-A (b, x)) : ℂ) * f (b, x) ∂μX

/-- The reflected form is an integral of nonnegative squared conditional amplitudes. -/
theorem raw_reflection_identity (w : B → ℝ) (hcw : Continuous w)
    (A : B × X → ℝ) (hA : Continuous A) (f : B × X → ℂ) (hf : Continuous f) :
    (∫ z, (weight w A z : ℂ) *
      (star (halfObservable f (reflection z)) * halfObservable f z) ∂μB.prod (μX.prod μX)) =
    ∫ b, ((w b * Complex.normSq (amplitude μX A f b) : ℝ) : ℂ) ∂μB := by
  have hc : Continuous (fun z : B × (X × X) => (weight w A z : ℂ) *
      (star (halfObservable f (reflection z)) * halfObservable f z)) := by
    unfold halfObservable reflection weight
    fun_prop
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro b
  let ψ : X → ℂ := fun x => (Real.exp (-A (b,x)) : ℂ) * f (b,x)
  have he (z : X × X) : (weight w A (b,z) : ℂ) *
      (star (halfObservable f (reflection (b,z))) * halfObservable f (b,z)) =
      (w b : ℂ) * (star (ψ z.1) * ψ z.2) := by
    dsimp only [ψ, weight, halfObservable, reflection, Prod.swap]
    simp only [Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_prod_mul (fun x => star (ψ x)) ψ]
  simp only [Complex.star_def, integral_conj, Complex.ofReal_mul, amplitude, ψ,
    Complex.normSq_eq_conj_mul_self]

theorem law_reflection_identity (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (f : B × X → ℂ) (hf : Continuous f) :
    (∫ z, star (halfObservable f (reflection z)) * halfObservable f z ∂law μB μX w A) =
      ((partition μB μX w A)⁻¹).toReal •
        ∫ b, ((w b * Complex.normSq (amplitude μX A f b) : ℝ) : ℂ) ∂μB := by
  unfold law
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul
    (weight_continuous w hcw A hA).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1
  simp_rw [ENNReal.toReal_ofReal (weight_positive w hw A _).le]
  exact raw_reflection_identity μB μX w hcw A hA f hf

theorem reflection_positive (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (f : B × X → ℂ) (hf : Continuous f) :
    0 ≤ (∫ z, star (halfObservable f (reflection z)) * halfObservable f z ∂law μB μX w A).re ∧
      (∫ z, star (halfObservable f (reflection z)) * halfObservable f z ∂law μB μX w A).im = 0 := by
  rw [law_reflection_identity μB μX w hcw hw A hA f hf, integral_complex_ofReal]
  have hp : 0 ≤ ∫ b, w b * Complex.normSq (amplitude μX A f b) ∂μB :=
    integral_nonneg (fun b => mul_nonneg (hw b).le (Complex.normSq_nonneg _))
  constructor
  · simpa only [Complex.smul_re, Complex.ofReal_re, smul_eq_mul] using
      mul_nonneg ENNReal.toReal_nonneg hp
  · simp only [Complex.smul_im, Complex.ofReal_im, smul_zero]

end
end UnifiedTheory.Clay.YangMills.BoundaryReflectionGluing
