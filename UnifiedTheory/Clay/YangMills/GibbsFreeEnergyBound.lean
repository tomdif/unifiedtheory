/- A compact Gibbs energy estimate from its actual normalized measure.
Jensen and cancellation of the Boltzmann factor give E[S] <= -log Z.
Combining this with a proved low-energy event gives explicit density bounds. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
import UnifiedTheory.Clay.YangMills.GibbsLowEnergyConcentration
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsFreeEnergyBound
noncomputable section
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Exact reciprocal partition identity under the actual Gibbs probability. -/
theorem reciprocal_partition_identity (S : X → ℝ) (hS : Continuous S) :
    (∫ x, Real.exp (S x) ∂CompactGibbsContinuity.law μ S) =
      1 / (∫ x, Real.exp (-S x) ∂μ) := by
  rw [CompactGibbsContinuity.law, LocalGibbsComparison.weighted_integral μ
    (fun x => Real.exp (-S x))
    (Real.continuous_exp.comp hS.neg).measurable
    (fun _ => (Real.exp_pos _).le) (CompactGibbsContinuity.partition_positive μ S hS)]
  simp only [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simp

/-- No sign or energy-tail assumption is needed for the action estimate. -/
theorem expected_action_le_neg_log_partition (S : X → ℝ) (hS : Continuous S) :
    (∫ x, S x ∂CompactGibbsContinuity.law μ S) ≤
      -Real.log (∫ x, Real.exp (-S x) ∂μ) := by
  letI := CompactGibbsContinuity.law_probability μ S hS
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hS.integrable_of_hasCompactSupport (μ := CompactGibbsContinuity.law μ S)
      (HasCompactSupport.of_compactSpace _))
    ((Real.continuous_exp.comp hS).integrable_of_hasCompactSupport
      (μ := CompactGibbsContinuity.law μ S) (HasCompactSupport.of_compactSpace _))
  rw [reciprocal_partition_identity μ S hS] at hj
  have hlog := Real.log_le_log (Real.exp_pos _) hj
  simpa only [Real.log_exp, one_div, Real.log_inv] using hlog

theorem expected_energy_le (D : X → ℝ) (hD : Continuous D) (b : ℝ) (hb : 0 < b) :
    (∫ x, D x ∂CompactGibbsContinuity.law μ (fun x => b * D x)) ≤
      -Real.log (∫ x, Real.exp (-(b * D x)) ∂μ) / b := by
  apply (le_div_iff₀ hb).mpr
  have h := expected_action_le_neg_log_partition μ (fun x => b * D x)
    (continuous_const.mul hD)
  rw [integral_const_mul] at h
  simpa only [mul_comm] using h

/-- A positive lower mass for a low-energy event gives a normalized expectation bound. -/
theorem cap_expectation_bound (D : X → ℝ) (hD : Continuous D)
    (b : ℝ) (hb : 0 < b) (eps p : ℝ) (hp : 0 < p)
    (A : Set X) (hA : MeasurableSet A) (hpA : p ≤ μ.real A)
    (hgood : ∀ x ∈ A, D x ≤ eps) :
    (∫ x, D x ∂CompactGibbsContinuity.law μ (fun x => b * D x)) ≤
      eps - Real.log p / b := by
  have hlow := GibbsLowEnergyConcentration.partition_lower μ D hD b hb.le eps p A hA hpA hgood
  have hlog := Real.log_le_log (mul_pos hp (Real.exp_pos _)) hlow
  rw [Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have he := expected_energy_le μ D hD b hb
  have he' := (le_div_iff₀ hb).mp he
  have hz : (∫ x, GibbsLowEnergyConcentration.weight D b x ∂μ) =
      ∫ x, Real.exp (-(b * D x)) ∂μ := by
    simp only [GibbsLowEnergyConcentration.weight, neg_mul]
  rw [hz] at hlog
  apply (le_sub_iff_add_le).mpr
  apply (mul_le_mul_iff_right₀ hb).mp
  rw [mul_add, mul_div_cancel₀ _ hb.ne']
  nlinarith

/-- The same estimate in the existing Wilson weighted-law convention. -/
theorem weighted_cap_expectation_bound (D : X → ℝ) (hD : Continuous D)
    (b : ℝ) (hb : 0 < b) (eps p : ℝ) (hp : 0 < p)
    (A : Set X) (hA : MeasurableSet A) (hpA : p ≤ μ.real A)
    (hgood : ∀ x ∈ A, D x ≤ eps) :
    (∫ x, D x ∂LocalGibbsComparison.weightedLaw μ (GibbsLowEnergyConcentration.weight D b)) ≤
      eps - Real.log p / b := by
  have he : GibbsLowEnergyConcentration.weight D b = fun x => Real.exp (-(b * D x)) := by
    funext x
    simp only [GibbsLowEnergyConcentration.weight, neg_mul]
  rw [he]
  exact cap_expectation_bound μ D hD b hb eps p hp A hA hpA hgood

end
end UnifiedTheory.Clay.YangMills.GibbsFreeEnergyBound
