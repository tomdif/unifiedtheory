/- Nonnegative moments under a bounded action perturbation. Both true
partitions are included; the price depends only on the perturbation,
not the size of the reference space or the unperturbed action. -/
import UnifiedTheory.Clay.YangMills.GibbsOrderedPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.GibbsPositiveMomentComparison
noncomputable section
open MeasureTheory GibbsOrderedPerturbation

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem density_upper (A B : X → ℝ) (hA : Continuous A) (hB : Continuous B)
    (M : ℝ) (hAB : ∀ x, |A x - B x| ≤ M) (x : X) :
    normalizedWeight μ B x ≤ Real.exp (2 * M) * normalizedWeight μ A x := by
  have hF := GibbsMixedInteraction.freeEnergy_difference_bound μ A B hA hB M hAB
  rw [normalizedWeight, normalizedWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hf := (abs_le.mp hF).1
  have hx := (abs_le.mp (hAB x)).2
  linarith

theorem integral_density (A F : X → ℝ) (hA : Continuous A) :
    (∫ x, F x ∂CompactGibbsContinuity.law μ A) =
      ∫ x, normalizedWeight μ A x * F x ∂μ := by
  rw [CompactGibbsContinuity.law,
    LocalGibbsComparison.weighted_integral μ (fun x => Real.exp (-A x))
    (Real.continuous_exp.comp hA.neg).measurable
    (fun _ => (Real.exp_pos _).le) (CompactGibbsContinuity.partition_positive μ A hA)]
  simp_rw [normalizedWeight_eq μ A hA, div_mul_eq_mul_div]
  exact (integral_div _ _).symm

/-- The nonnegative test may include any continuous response weight.
No boundedness constant for that test is charged in the comparison. -/
theorem positive_moment (A B F : X → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x)
    (M : ℝ) (hAB : ∀ x, |A x - B x| ≤ M) :
    (∫ x, F x ∂CompactGibbsContinuity.law μ B) ≤
      Real.exp (2 * M) * ∫ x, F x ∂CompactGibbsContinuity.law μ A := by
  rw [integral_density μ B F hB, integral_density μ A F hA, ← integral_const_mul]
  have hc (C : X → ℝ) (hC : Continuous C) : Continuous (normalizedWeight μ C) :=
    (continuous_const.sub hC).rexp
  apply integral_mono
    (((hc B hB).mul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((continuous_const.mul ((hc A hA).mul hF)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  intro x
  simpa only [Pi.mul_apply, mul_assoc] using
    mul_le_mul_of_nonneg_right (density_upper μ A B hA hB M hAB x) (hF0 x)

end
end UnifiedTheory.Clay.YangMills.GibbsPositiveMomentComparison
