/- A fixed nonconstant compact-group observable has a strictly positive
Haar fluctuation floor for every complex center. Haar translations preserve
that floor. This supplies the local fluctuation input, not a lattice estimate. -/
import UnifiedTheory.Clay.YangMills.UnitaryCharacterObservables
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.HaarCenteredFluctuation
noncomputable section
open MeasureTheory ProbabilityTheory RegulatedGauge

section General
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]

theorem real_variance_positive (f : X → ℝ) (hf : Continuous f) (x y : X)
    (hne : f x ≠ f y) : 0 < ProbabilityTheory.variance f μ := by
  rw [variance_eq_integral hf.measurable.aemeasurable]
  let m := ∫ z, f z ∂μ
  have he : ∃ z, f z - m ≠ 0 := by
    by_cases hx : f x - m = 0
    · exact ⟨y, fun hy => hne ((sub_eq_zero.mp hx).trans (sub_eq_zero.mp hy).symm)⟩
    · exact ⟨x, hx⟩
  obtain ⟨z, hz⟩ := he
  have hc : Continuous (fun z => (f z - m) ^ 2) := (hf.sub continuous_const).pow 2
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun z => sq_nonneg _) (pow_ne_zero 2 hz)

theorem complex_center_lower (f : X → ℂ) (hf : Continuous f) (m : ℂ) :
    ProbabilityTheory.variance (fun x => (f x).re) μ ≤ ∫ x, ‖f x - m‖ ^ 2 ∂μ := by
  have hr : Continuous (fun x => (f x).re) := Complex.continuous_re.comp hf
  have he := variance_le_expectation_sq (X := fun x => (f x).re - m.re)
    ((hr.sub continuous_const).aestronglyMeasurable (μ := μ))
  rw [variance_sub_const hr.aestronglyMeasurable m.re] at he
  apply he.trans
  apply integral_mono
    (((hr.sub continuous_const).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((hf.sub continuous_const).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro x
  have h := sq_le_sq₀ (abs_nonneg ((f x - m).re)) (norm_nonneg (f x - m))
  simpa only [Pi.pow_apply, Complex.sub_re, sq_abs] using h.mpr (Complex.abs_re_le_norm (f x - m))
end General

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def haarFluctuation (χ : G → ℂ) : ℝ :=
  ProbabilityTheory.variance (fun g => (χ g).re) (compactHaar G)

theorem haarFluctuation_pos (χ : G → ℂ) (hχ : Continuous χ) (g h : G)
    (hne : (χ g).re ≠ (χ h).re) : 0 < haarFluctuation G χ :=
  real_variance_positive (compactHaar G) (fun g => (χ g).re) (Complex.continuous_re.comp hχ) g h hne

theorem haar_center_lower (χ : G → ℂ) (hχ : Continuous χ) (a b : G) (m : ℂ) :
    haarFluctuation G χ ≤ ∫ g, ‖χ (a * g * b) - m‖ ^ 2 ∂compactHaar G := by
  have hm : MeasurePreserving (fun g => a * g * b) (compactHaar G) (compactHaar G) :=
    (measurePreserving_mul_right (compactHaar G) b).comp (measurePreserving_mul_left (compactHaar G) a)
  rw [hm.integral_comp ((measurableEmbedding_mulRight b).comp (measurableEmbedding_mulLeft a))
    (fun g => ‖χ g - m‖ ^ 2)]
  exact complex_center_lower (compactHaar G) χ hχ m

end
end UnifiedTheory.Clay.YangMills.HaarCenteredFluctuation
