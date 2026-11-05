/- Reversibility moves a varying row coefficient onto the source through
the original transfer. Strict positivity propagates a strict pointwise gain
to every row at finite cutoff. No uniform quantitative gain is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalSeamResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGroundRowAveraging
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalResponse WilsonAveragedResponse
open WilsonPhysicalVariance WilsonGroundHeatBath CompactDensityEntropy

variable (n : ℕ) [NeZero n]

theorem pairing (β : ℝ) (hβ : 0 ≤ β) (f g : C(Slice n, ℝ)) :
    (∫ u, f u * step n β hβ g u ∂groundLaw n β hβ) =
      ∫ u, g u * step n β hβ f u ∂groundLaw n β hβ := by
  rw [groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous,
    GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  change (∫ u, (ground n β hβ u)^2 * (f u * rowMean n β hβ g u) ∂WilsonSlabOperator.measure n) =
    ∫ u, (ground n β hβ u)^2 * (g u * rowMean n β hβ f u) ∂WilsonSlabOperator.measure n
  simp_rw [rowMean_eq_raw, ← integral_const_mul]
  have hc : Continuous (fun z : Slice n × Slice n =>
      (ground n β hβ z.1)^2 * (f z.1 * (rawTransition n β hβ z.1 z.2 * g z.2))) :=
    (((ground n β hβ).continuous.comp continuous_fst).pow 2).mul
      ((f.continuous.comp continuous_fst).mul
        ((rawTransition_continuous n β hβ).mul (g.continuous.comp continuous_snd)))
  rw [integral_integral_swap
    (hc.integrable_of_hasCompactSupport
      (μ := (WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))
      (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  filter_upwards with v
  apply integral_congr_ae
  filter_upwards with u
  calc
    _ = ((ground n β hβ u)^2 * rawTransition n β hβ u v) * (f u * g v) := by ring
    _ = _ := by rw [raw_detailed_balance]; ring

theorem step_nonneg (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, 0 ≤ f u) (u : Slice n) : 0 ≤ step n β hβ f u :=
  integral_nonneg hf

theorem step_le_const (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (C : ℝ) (hf : ∀ u, f u ≤ C) (u : Slice n) : step n β hβ f u ≤ C := by
  letI := rowLaw_probability n β hβ u
  have hh := integral_mono (continuous_integrable (rowLaw n β hβ u) _ f.continuous)
    (integrable_const C) hf
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

/-- Positive actual transition density carries a strict gain at one point into every row. -/
theorem step_lt_const (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (C : ℝ) (hf : ∀ u, f u ≤ C) (v : Slice n) (hv : f v < C) (u : Slice n) :
    step n β hβ f u < C := by
  letI : Measure.IsOpenPosMeasure (WilsonSlabOperator.measure n) := by
    unfold WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar RegulatedGauge.compactHaar
    infer_instance
  have ht : Continuous (rawTransition n β hβ u) :=
    WilsonStationaryEntropy.row_continuous n β hβ u
  have hc : Continuous (fun z => rawTransition n β hβ u z * (C - f z)) :=
    ht.mul (continuous_const.sub f.continuous)
  have hh := integral_pos_of_integrable_nonneg_nonzero hc
    (continuous_integrable (WilsonSlabOperator.measure n) _ hc)
    (fun z => mul_nonneg (rawTransition_pos n β hβ u z).le (sub_nonneg.mpr (hf z)))
    (mul_pos (rawTransition_pos n β hβ u v) (sub_pos.mpr hv)).ne'
  simp_rw [mul_sub] at hh
  rw [integral_sub ((continuous_integrable (WilsonSlabOperator.measure n) _ ht).mul_const C)
    (continuous_integrable (WilsonSlabOperator.measure n)
      (fun z => rawTransition n β hβ u z * f z) (ht.mul f.continuous)), integral_mul_const,
    rawTransition_mass, one_mul, ← rowMean_eq_raw] at hh
  exact sub_pos.mp hh

end
end UnifiedTheory.Clay.YangMills.WilsonGroundRowAveraging
