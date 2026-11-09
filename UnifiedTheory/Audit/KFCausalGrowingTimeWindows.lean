/- A concrete unbounded window with square length negligible relative
to its starting exponential time. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGrowingTimeWindows
noncomputable section
open Filter
open scoped Topology

def quarterWindow (u : ℝ) : ℝ := Real.sqrt (Real.sqrt u)

theorem quarterWindow_nonneg (u : ℝ) : 0 ≤ quarterWindow u := Real.sqrt_nonneg _

theorem quarterWindow_diverges : Tendsto quarterWindow atTop atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop

theorem quarterWindow_square_ratio :
    Tendsto (fun u => quarterWindow u^2/u) atTop (𝓝 0) := by
  apply (Real.tendsto_sqrt_atTop.const_div_atTop (1:ℝ)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  rw [quarterWindow,Real.sq_sqrt (Real.sqrt_nonneg u)]
  have hs := Real.sq_sqrt hu.le
  have hn : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  apply (div_eq_div_iff hn hu.ne').mpr
  nlinarith only [hs]

#print axioms quarterWindow_nonneg
#print axioms quarterWindow_diverges
#print axioms quarterWindow_square_ratio
end
end UnifiedTheory.Audit.KFCausalGrowingTimeWindows
