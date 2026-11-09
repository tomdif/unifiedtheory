/- A uniform quadratic remainder gives an actual strong derivative. -/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuadraticRemainderDerivative
open Filter Asymptotics
open scoped Topology

theorem derivative_of_quadratic_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (K : ℝ)
    (h : ∀ t, ‖f t-f 0-t • v‖ ≤ K*|t|^2) : HasDerivAt f v 0 := by
  apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
  have hb : (fun t => f (0+t)-f 0-t • v) =O[𝓝 (0:ℝ)] (fun t : ℝ => t^2) := by
    apply IsBigO.of_bound K
    exact Filter.Eventually.of_forall (fun t => by
      simpa only [zero_add,norm_pow,Real.norm_eq_abs] using h t)
  exact hb.trans_isLittleO (isLittleO_pow_id (by decide : 1 < (2:ℕ)))

#print axioms derivative_of_quadratic_remainder
end UnifiedTheory.Audit.KFCausalQuadraticRemainderDerivative
