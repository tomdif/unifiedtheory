/- Quantitative normalized Gibbs fluctuation bounds from an actual
contracting map and a proved pushforward domination estimate. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactGibbsContractionMoment
noncomputable section
open MeasureTheory CompactGibbsContinuity
open scoped NNReal ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The partition cancels exactly after the change-of-measure estimate. -/
theorem exponential_moment (A D : X → ℝ) (hA : Continuous A) (hD : Continuous D)
    (T : X → X) (hT : Continuous T) (C : ℝ≥0)
    (hmap : μ.map T ≤ (C : ℝ≥0∞) • μ) (γ : ℝ)
    (hgain : ∀ x, γ * D x ≤ A x - A (T x)) :
    (∫ x, Real.exp (γ * D x) ∂law μ A) ≤ (C : ℝ) := by
  letI : IsFiniteMeasure ((C : ℝ≥0∞) • μ) := μ.smul_finite ENNReal.coe_ne_top
  let w := fun x => Real.exp (-A x)
  have hw : Continuous w := hA.neg.rexp
  have hz : 0 < ∫ x, w x ∂μ := partition_positive μ A hA
  have he : Continuous (fun x => Real.exp (γ * D x)) :=
    (continuous_const.mul hD).rexp
  have hnum : (∫ x, w x * Real.exp (γ * D x) ∂μ) ≤ (C : ℝ) * ∫ x, w x ∂μ := by
    calc
      _ ≤ ∫ x, w (T x) ∂μ := by
        apply integral_mono
          ((hw.mul he).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          ((hw.comp hT).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        intro x
        dsimp [w]
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [hgain x])
      _ = ∫ x, w x ∂μ.map T :=
        (integral_map hT.measurable.aemeasurable hw.aestronglyMeasurable).symm
      _ ≤ ∫ x, w x ∂(C : ℝ≥0∞) • μ :=
        integral_mono_measure hmap (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
          (hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      _ = _ := by rw [integral_smul_measure]; rfl
  rw [law, LocalGibbsComparison.weighted_integral μ w hw.measurable
    (fun x => (Real.exp_pos _).le) hz]
  exact (div_le_iff₀ hz).mpr hnum

/-- Jensen's inequality improves the distortion factor C to log(C) in
the mean fluctuation bound. No minimum-only approximation replaces the law. -/
theorem mean_bound (A D : X → ℝ) (hA : Continuous A) (hD : Continuous D)
    (T : X → X) (hT : Continuous T) (C : ℝ≥0) (hC : 0 < (C : ℝ))
    (hmap : μ.map T ≤ (C : ℝ≥0∞) • μ) (γ : ℝ) (hγ : 0 < γ)
    (hgain : ∀ x, γ * D x ≤ A x - A (T x)) :
    (∫ x, D x ∂law μ A) ≤ Real.log C / γ := by
  letI : IsProbabilityMeasure (law μ A) := law_probability μ A hA
  have hc : Continuous (fun x => γ * D x) := continuous_const.mul hD
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun x => Set.mem_univ (γ * D x)))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := law μ A))
    (hc.rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := law μ A))
  rw [integral_const_mul] at hj
  have hb := hj.trans (exponential_moment μ A D hA hD T hT C hmap γ hgain)
  rw [← Real.exp_log hC] at hb
  exact (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using Real.exp_le_exp.mp hb)

end
end UnifiedTheory.Clay.YangMills.CompactGibbsContractionMoment
