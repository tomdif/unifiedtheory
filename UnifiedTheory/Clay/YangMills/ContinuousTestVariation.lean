/-
Continuous bounded-test control extends to measurable-event variation for finite
regular measures. Closed-event approximation and inner regularity are proved
inputs from mathlib, not assumptions of a total-variation conclusion.
-/
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Regular

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.ContinuousTestVariation
noncomputable section
open MeasureTheory Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable [OpensMeasurableSpace X] [HasOuterApproxClosed X]
variable (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- A one-sided continuous-test bound passes to closed events by continuous approximations. -/
theorem closed_event_bound (C : ℝ)
    (h : ∀ (f : X → ℝ), Continuous f → (∀ x, f x ∈ Set.Icc 0 1) →
      (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ C)
    (K : Set X) (hK : IsClosed K) : μ.real K - ν.real K ≤ C := by
  have hμ := (ENNReal.tendsto_toReal (measure_ne_top μ K)).comp
    (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK μ)
  have hν := (ENNReal.tendsto_toReal (measure_ne_top ν K)).comp
    (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK ν)
  simp only [Function.comp_def, BoundedContinuousFunction.toReal_lintegral_coe_eq_integral] at hμ hν
  apply le_of_tendsto (hμ.sub hν)
  filter_upwards [] with k
  apply h (fun x => (hK.apprSeq k x : ℝ))
  · exact NNReal.continuous_coe.comp (hK.apprSeq k).continuous
  · intro x
    exact ⟨NNReal.coe_nonneg _, by exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hK k x⟩

/-- Inner regularity extends a one-sided continuous-test bound to every measurable event. -/
theorem measurable_event_bound [μ.WeaklyRegular] (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (f : X → ℝ), Continuous f → (∀ x, f x ∈ Set.Icc 0 1) →
      (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ C)
    (s : Set X) (hs : MeasurableSet s) : μ.real s - ν.real s ≤ C := by
  by_contra hn
  have hlt : ν.real s + C < μ.real s := by linarith
  have hr : ENNReal.ofReal (ν.real s + C) < μ s := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal
      (add_nonneg measureReal_nonneg hC) (measure_ne_top μ s)).mpr hlt
  obtain ⟨K, hKs, hK, hKr⟩ := hs.exists_lt_isClosed_of_ne_top (measure_ne_top μ s) hr
  have hKr' : ν.real s + C < μ.real K :=
    (ENNReal.ofReal_lt_iff_lt_toReal
      (add_nonneg measureReal_nonneg hC) (measure_ne_top μ K)).mp hKr
  have hν : ν.real K ≤ ν.real s := measureReal_mono hKs
  have hc := closed_event_bound μ ν C h K hK
  linarith

/-- The probability-TV convention is the supremum over events, without a factor of two. -/
theorem measurable_event_abs_bound [μ.WeaklyRegular] [ν.WeaklyRegular]
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (f : X → ℝ), Continuous f → (∀ x, f x ∈ Set.Icc 0 1) →
      |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ C)
    (s : Set X) (hs : MeasurableSet s) : |μ.real s - ν.real s| ≤ C := by
  apply abs_le.mpr
  constructor
  · have hn := measurable_event_bound ν μ C hC (by
      intro f hf hb
      have hh := (abs_le.mp (h f hf hb)).1
      linarith) s hs
    linarith
  · exact measurable_event_bound μ ν C hC (fun f hf hb => (abs_le.mp (h f hf hb)).2) s hs

end
end UnifiedTheory.Clay.YangMills.ContinuousTestVariation
