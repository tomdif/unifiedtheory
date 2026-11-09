/- Conditioning and normalized Gibbs tilting commute. All normalizers
are the actual event masses or partition integrals. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
import UnifiedTheory.Clay.YangMills.GibbsReflectionTransport
import Mathlib.Probability.ConditionalProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.GibbsConditionedLaw
noncomputable section
open MeasureTheory LocalGibbsComparison
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem cond_smul (μ : Measure X) (c : ℝ≥0∞) (hc₀ : c ≠ 0) (hctop : c ≠ ∞)
    (E : Set X) : ProbabilityTheory.cond (c • μ) E = ProbabilityTheory.cond μ E := by
  unfold ProbabilityTheory.cond
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_smul, smul_smul,
    ENNReal.mul_inv (Or.inl hc₀) (Or.inl hctop)]
  have he : (c⁻¹ * (μ E)⁻¹) * c = (μ E)⁻¹ := by
    calc
      _ = (μ E)⁻¹ * (c⁻¹ * c) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hc₀ hctop, mul_one]
  rw [he]

theorem weightedLaw_smul (μ : Measure X) (c : ℝ≥0∞) (hc₀ : c ≠ 0) (hctop : c ≠ ∞)
    (w : X → ℝ) : weightedLaw (c • μ) w = weightedLaw μ w := by
  unfold weightedLaw
  rw [integral_smul_measure, smul_eq_mul, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hctop, withDensity_smul_measure, smul_smul,
    ENNReal.mul_inv (Or.inl hc₀) (Or.inl hctop)]
  have he : (c⁻¹ * (ENNReal.ofReal (∫ x, w x ∂μ))⁻¹) * c =
      (ENNReal.ofReal (∫ x, w x ∂μ))⁻¹ := by
    calc
      _ = (ENNReal.ofReal (∫ x, w x ∂μ))⁻¹ * (c⁻¹ * c) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hc₀ hctop, mul_one]
  rw [he]

theorem weightedLaw_normalize (μ : Measure X) (w : X → ℝ) (hi : Integrable w μ)
    (hn : ∀ x, 0 ≤ w x) :
    weightedLaw μ w = ProbabilityTheory.cond
      (μ.withDensity (fun x => ENNReal.ofReal (w x))) Set.univ := by
  unfold weightedLaw ProbabilityTheory.cond
  rw [Measure.restrict_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)]

/-- The original partition cancels after conditioning, including the
case of a zero-mass event. -/
theorem conditioned_weightedLaw (μ : Measure X) (w : X → ℝ)
    (hi : Integrable w μ) (hn : ∀ x, 0 ≤ w x) (hz : 0 < ∫ x, w x ∂μ)
    (E : Set X) (hE : MeasurableSet E) :
    ProbabilityTheory.cond (weightedLaw μ w) E = weightedLaw (μ.restrict E) w := by
  have hc₀ : (ENNReal.ofReal (∫ x, w x ∂μ))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hctop : (ENNReal.ofReal (∫ x, w x ∂μ))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hz).ne'
  rw [weightedLaw, cond_smul _ _ hc₀ hctop,
    weightedLaw_normalize _ w hi.restrict hn]
  unfold ProbabilityTheory.cond
  rw [← restrict_withDensity hE, Measure.restrict_univ]
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- A normalized reference event and conditioning the final Gibbs law
produce exactly the same measure, not merely comparable integrals. -/
theorem weightedLaw_cond (μ : Measure X) [IsFiniteMeasure μ] (w : X → ℝ)
    (hi : Integrable w μ) (hn : ∀ x, 0 ≤ w x) (hz : 0 < ∫ x, w x ∂μ)
    (E : Set X) (hE : MeasurableSet E) (hp : μ E ≠ 0) :
    weightedLaw (ProbabilityTheory.cond μ E) w =
      ProbabilityTheory.cond (weightedLaw μ w) E := by
  rw [conditioned_weightedLaw μ w hi hn hz E hE, ProbabilityTheory.cond]
  exact weightedLaw_smul _ _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr hp) w

theorem weightedLaw_transport {Y : Type*} [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {T : X → Y}
    (hT : MeasurePreserving T μ ν) (he : MeasurableEmbedding T)
    (w : Y → ℝ) (hw : Measurable w) :
    MeasurePreserving T (weightedLaw μ (w ∘ T)) (weightedLaw ν w) := by
  unfold weightedLaw
  have hp := hT.integral_comp he w
  change (∫ x, (w ∘ T) x ∂μ) = ∫ y, w y ∂ν at hp
  rw [hp]
  exact (GibbsReflectionTransport.withDensity_transport hT
    (fun y => ENNReal.ofReal (w y)) hw.ennreal_ofReal).smul_measure _

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

theorem law_cond (μ : Measure X) [IsProbabilityMeasure μ]
    (A : X → ℝ) (hA : Continuous A) (E : Set X) (hE : MeasurableSet E) (hp : μ E ≠ 0) :
    CompactGibbsContinuity.law (ProbabilityTheory.cond μ E) A =
      ProbabilityTheory.cond (CompactGibbsContinuity.law μ A) E := by
  exact weightedLaw_cond μ _
    (hA.neg.rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun x => (Real.exp_pos _).le) (CompactGibbsContinuity.partition_positive μ A hA) E hE hp

end
end UnifiedTheory.Clay.YangMills.GibbsConditionedLaw
