/- Exact connected-source formula for a mixed compact Gibbs free energy.
Both integrations are over the actual normalized tilted law; continuity
and the fundamental theorem of calculus are proved, not assumed. -/
import UnifiedTheory.Clay.YangMills.GibbsMixedInteraction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactConnectedRectangle
noncomputable section
open MeasureTheory CompactGibbsSource

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem expectation_continuous (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) :
    Continuous (expectation μ A F G) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (expectation_hasDerivAt μ A F G hA hF hG t).continuousAt)

theorem covariance_continuous (A F G H : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) :
    Continuous (covariance μ A F G H) :=
  (expectation_continuous μ A F (fun x => G x*H x) hA hF (hG.mul hH)).sub
    ((expectation_continuous μ A F G hA hF hG).mul
      (expectation_continuous μ A F H hA hF hH))

theorem source_difference (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) :
    (∫ t in (0 : ℝ)..1, covariance μ A F G F t) =
      expectation μ A F G 1-expectation μ A F G 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => expectation_hasDerivAt μ A F G hA hF hG t)
    ((covariance_continuous μ A F G F hA hF hG hF).intervalIntegrable 0 1)

/-- The mixed logarithmic partition increment is the integral of the
connected covariance throughout the entire two-source rectangle. -/
theorem mixed_integral (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) :
    -GibbsMixedInteraction.mixed μ A F G =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        covariance μ (action A F s) G F G t := by
  have inner (s : ℝ) :
      (∫ t in (0 : ℝ)..1, covariance μ (action A F s) G F G t) =
        expectation μ (fun x => A x-G x) F F s-expectation μ A F F s := by
    rw [source_difference μ _ G F (action_continuous A F hA hF s) hG hF]
    have h1 : action (action A F s) G 1 = action (fun x => A x-G x) F s := by
      funext x
      simp only [action, one_mul]
      ring
    have h0 : action (action A F s) G 0 = action A F s := by
      funext x
      simp only [action, zero_mul, sub_zero]
    simp only [expectation, h1, h0]
  simp_rw [inner]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => GibbsMixedInteraction.log_difference_hasDerivAt μ A F G hA hF hG s)
    (((expectation_continuous μ (fun x => A x-G x) F F (hA.sub hG) hF hF).sub
      (expectation_continuous μ A F F hA hF hF)).intervalIntegrable 0 1)]
  simp only [GibbsMixedInteraction.mixed, GibbsMixedInteraction.freeEnergy,
    partition, weight, action, one_mul, zero_mul, sub_zero]
  have he (x : X) : A x-G x-F x = A x-F x-G x := by ring
  simp_rw [he]
  ring

end
end UnifiedTheory.Clay.YangMills.CompactConnectedRectangle
