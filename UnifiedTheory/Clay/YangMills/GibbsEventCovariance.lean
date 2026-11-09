/- Exact event conditioning keeps both conditional covariances and the
between-event means. The complement probability is not assumed small. -/
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance
import UnifiedTheory.Clay.YangMills.CompactGibbsOscillation
import Mathlib.Probability.ConditionalProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.GibbsEventCovariance
noncomputable section
open MeasureTheory ProbabilityTheory GibbsCrossCovariance

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem mass_partition (E : Set X) (hE : MeasurableSet E) :
    μ.real E + μ.real Eᶜ = 1 := by
  simpa only [probReal_univ] using measureReal_add_measureReal_compl (μ := μ) hE

theorem weighted_cond_integral (E : Set X) (F : X → ℝ) :
    μ.real E * (∫ x, F x ∂cond μ E) = ∫ x in E, F x ∂μ := by
  by_cases h : μ E = 0
  · simp [ProbabilityTheory.cond, h, Measure.restrict_eq_zero.mpr h, measureReal_def]
  · rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
    exact mul_inv_cancel_left₀ (ENNReal.toReal_ne_zero.mpr ⟨h, measure_ne_top _ _⟩) _

theorem integral_split (E : Set X) (hE : MeasurableSet E) (F : X → ℝ)
    (hF : Integrable F μ) :
    (∫ x, F x ∂μ) = μ.real E * (∫ x, F x ∂cond μ E) +
      μ.real Eᶜ * (∫ x, F x ∂cond μ Eᶜ) := by
  rw [weighted_cond_integral, weighted_cond_integral]
  exact (integral_add_compl hE hF).symm

/-- This identity also covers zero-probability events and complements. -/
theorem covariance_split (E : Set X) (hE : MeasurableSet E) (F G : X → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hFG : Integrable (fun x => F x * G x) μ) :
    GibbsCrossCovariance.covariance μ F G =
      μ.real E * GibbsCrossCovariance.covariance (cond μ E) F G +
      μ.real Eᶜ * GibbsCrossCovariance.covariance (cond μ Eᶜ) F G +
      μ.real E * μ.real Eᶜ *
        ((∫ x, F x ∂cond μ E) - ∫ x, F x ∂cond μ Eᶜ) *
        ((∫ x, G x ∂cond μ E) - ∫ x, G x ∂cond μ Eᶜ) := by
  unfold GibbsCrossCovariance.covariance
  rw [integral_split μ E hE _ hFG, integral_split μ E hE F hF,
    integral_split μ E hE G hG]
  have hp := mass_partition μ E hE
  linear_combination
    -(μ.real E * (∫ x, F x ∂cond μ E) * (∫ x, G x ∂cond μ E) +
      μ.real Eᶜ * (∫ x, F x ∂cond μ Eᶜ) * (∫ x, G x ∂cond μ Eᶜ)) * hp

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

theorem conditional_mean_bound (E : Set X) (F : X → ℝ) (hF : Continuous F)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, |F x| ≤ M) :
    |∫ x, F x ∂cond μ E| ≤ M := by
  by_cases h : μ E = 0
  · simpa only [cond_eq_zero_of_meas_eq_zero h, integral_zero_measure, abs_zero] using hM
  · letI := cond_isProbabilityMeasure h
    have hi := hF.integrable_of_hasCompactSupport (μ := cond μ E)
      (HasCompactSupport.of_compactSpace _)
    calc
      |∫ x, F x ∂cond μ E| ≤ ∫ x, |F x| ∂cond μ E := abs_integral_le_integral_abs
      _ ≤ ∫ _ : X, M ∂cond μ E := integral_mono hi.abs (integrable_const _) hbound
      _ = M := by simp

theorem conditional_covariance_bound (E : Set X) (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hFb : ∀ x, |F x| ≤ M) (hGb : ∀ x, |G x| ≤ N) :
    |GibbsCrossCovariance.covariance (cond μ E) F G| ≤ M * N := by
  by_cases h : μ E = 0
  · simpa only [cond_eq_zero_of_meas_eq_zero h, GibbsCrossCovariance.covariance,
      integral_zero_measure, mul_zero, sub_self, abs_zero] using mul_nonneg hM hN
  · letI := cond_isProbabilityMeasure h
    have hh := CompactGibbsOscillation.covariance_bound (cond μ E) F G hF hG
      (-M) M (-N) N (by linarith) (by linarith)
      (fun x => abs_le.mp (hFb x)) (fun x => abs_le.mp (hGb x))
    convert hh using 1; ring

/-- For beta-scaled Wilson insertions, each absolute source is at most two.
The error includes fluctuations within the complement and its shifted means. -/
theorem bounded_source_transfer (E : Set X) (hE : MeasurableSet E) (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hFb : ∀ x, |F x| ≤ 2) (hGb : ∀ x, |G x| ≤ 2) :
    |GibbsCrossCovariance.covariance μ F G| ≤
      μ.real E * |GibbsCrossCovariance.covariance (cond μ E) F G| +
      4 * μ.real Eᶜ + 16 * μ.real E * μ.real Eᶜ := by
  have hiF := hF.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hiG := hG.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hiFG := (hF.mul hG).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  have hb := conditional_covariance_bound μ Eᶜ F G hF hG 2 2 (by norm_num) (by norm_num) hFb hGb
  have hmF : |(∫ x, F x ∂cond μ E) - ∫ x, F x ∂cond μ Eᶜ| ≤ 4 := by
    have h1 := conditional_mean_bound μ E F hF 2 (by norm_num) hFb
    have h2 := conditional_mean_bound μ Eᶜ F hF 2 (by norm_num) hFb
    exact (abs_sub _ _).trans (by linarith)
  have hmG : |(∫ x, G x ∂cond μ E) - ∫ x, G x ∂cond μ Eᶜ| ≤ 4 := by
    have h1 := conditional_mean_bound μ E G hG 2 (by norm_num) hGb
    have h2 := conditional_mean_bound μ Eᶜ G hG 2 (by norm_num) hGb
    exact (abs_sub _ _).trans (by linarith)
  rw [covariance_split μ E hE F G hiF hiG hiFG]
  calc
    _ ≤ |μ.real E * GibbsCrossCovariance.covariance (cond μ E) F G| +
        |μ.real Eᶜ * GibbsCrossCovariance.covariance (cond μ Eᶜ) F G| +
        |μ.real E * μ.real Eᶜ *
          ((∫ x, F x ∂cond μ E) - ∫ x, F x ∂cond μ Eᶜ) *
          ((∫ x, G x ∂cond μ E) - ∫ x, G x ∂cond μ Eᶜ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul, abs_of_nonneg (measureReal_nonneg : 0 ≤ μ.real E),
        abs_of_nonneg (measureReal_nonneg : 0 ≤ μ.real Eᶜ)]
      have hbad := mul_le_mul_of_nonneg_left hb (measureReal_nonneg : 0 ≤ μ.real Eᶜ)
      have hmeans := mul_le_mul hmF hmG (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
      have hmix := mul_le_mul_of_nonneg_left hmeans
        (mul_nonneg (measureReal_nonneg : 0 ≤ μ.real E) (measureReal_nonneg : 0 ≤ μ.real Eᶜ))
      nlinarith only [hbad, hmix]

end
end UnifiedTheory.Clay.YangMills.GibbsEventCovariance
