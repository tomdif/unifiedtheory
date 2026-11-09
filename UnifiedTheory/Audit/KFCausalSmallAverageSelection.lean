/- A small continuous average on the unit interval has a small value.
This uses the actual integral and does not presume a pointwise bound. -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSmallAverageSelection
noncomputable section
open MeasureTheory

theorem exists_lt (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) (δ : ℝ)
    (havg : (∫ r in (0:ℝ)..1, f r) < δ) :
    ∃ r ∈ Set.Icc (0:ℝ) 1, f r < δ := by
  by_contra! hn
  have hi := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (intervalIntegrable_const (c := δ)) (hf.intervalIntegrable_of_Icc zero_le_one) hn
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at hi
  exact (not_le_of_gt havg) hi

#print axioms exists_lt
end
end UnifiedTheory.Audit.KFCausalSmallAverageSelection
