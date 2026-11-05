/- The actual OS evolution is bounded self-adjoint and injective at every
finite time. This does not make its inverse bounded or establish a mass gap. -/
import UnifiedTheory.Clay.YangMills.OSScalarDynamics
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSInjectiveEvolution
noncomputable section
open Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics
open scoped NNReal Topology

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane} (D : Evolution W plane hp)

theorem selfAdjoint (t : ℝ≥0) : IsSelfAdjoint (D.operator t) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (D.symmetric t)

theorem half_null (t : ℝ≥0) (v : Hilbert (positiveKernel W plane hp))
    (hv : D.operator t v = 0) : D.operator (t/2) v = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have ht : t/2+t/2=t := by ring
  rw [D.symmetric, D.add, ht, hv, inner_zero_right]

/-- Strong continuity at zero rules out a nonzero vector annihilated at a
finite time: symmetry propagates any such null vector through all half-times. -/
theorem null_implies_zero (t : ℝ≥0) (v : Hilbert (positiveKernel W plane hp))
    (hv : D.operator t v = 0) : v = 0 := by
  have hiter (n : ℕ) : D.operator (t*(1/2 : ℝ≥0)^n) v = 0 := by
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      have hh := half_null D (t*(1/2 : ℝ≥0)^n) v ih
      simpa only [pow_succ, mul_assoc, div_eq_mul_inv, one_div, one_mul] using hh
  have ht : Tendsto (fun n : ℕ => t*(1/2 : ℝ≥0)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (1/2 : ℝ≥0) < 1 by norm_num))
  have hl : Tendsto (fun n : ℕ => D.operator (t*(1/2 : ℝ≥0)^n) v) atTop (𝓝 v) := by
    simpa only [D.zero] using ((D.strongly_continuous v).tendsto 0).comp ht
  have hz : Tendsto (fun n : ℕ => D.operator (t*(1/2 : ℝ≥0)^n) v) atTop (𝓝 0) := by
    simpa only [hiter] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (0 : Hilbert (positiveKernel W plane hp))) atTop (𝓝 0))
  exact tendsto_nhds_unique hl hz

theorem injective (t : ℝ≥0) : Function.Injective (D.operator t) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply null_implies_zero D t
  rw [map_sub, hvw, sub_self]

end
end UnifiedTheory.Clay.YangMills.OSInjectiveEvolution
