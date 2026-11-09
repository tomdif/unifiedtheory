/- Moving physical test vectors need a strong derivative only for the
test; the state may satisfy just the scalar weak differential equation. -/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMovingTestDerivative
noncomputable section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem pairing_derivative (u v : ℝ → H) (x : ℝ) (v' : H) (a : ℂ)
    (hu : ContinuousAt u x) (hv : HasDerivAt v v' x)
    (hf : HasDerivAt (fun t => inner ℂ (u t) (v x)) a x) :
    HasDerivAt (fun t => inner ℂ (u t) (v t)) (a+inner ℂ (u x) v') x := by
  have ht : Tendsto (fun h : ℝ => x+h) (𝓝[≠] 0) (𝓝 x) := by
    have hi : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa only [add_zero] using hi.const_add x
  have hc := (hu.tendsto.comp ht).inner (𝕜 := ℂ) hv.tendsto_slope_zero
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  convert hf.tendsto_slope_zero.add hc using 1
  funext h
  rw [show inner ℂ (u (x+h)) (v (x+h))-inner ℂ (u x) (v x) =
      (inner ℂ (u (x+h)) (v x)-inner ℂ (u x) (v x))+
        inner ℂ (u (x+h)) (v (x+h)-v x) by rw [inner_sub_right]; ring,smul_add]
  congr 1
  exact (inner_smul_right_eq_smul (𝕜 := ℂ) _ _ _).symm

#print axioms pairing_derivative
end
end UnifiedTheory.Audit.KFCausalMovingTestDerivative
