/- Strong continuity of an isometry family suffices to differentiate
its action on a vector curve that vanishes at the differentiation point. -/
import UnifiedTheory.Audit.KFCausalStrongIsometryContinuity
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalStrongIsometryDerivative
noncomputable section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem derivative_at_zero_vector (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hc : ∀ x, Continuous (fun t => U t x)) (f : ℝ → H) (v : H) (s : ℝ)
    (hf : HasDerivAt f v s) (h0 : f s = 0) :
    HasDerivAt (fun t => U t (f t)) (U s v) s := by
  have ht := (KFCausalStrongIsometryContinuity.strong_joint_apply U hc).continuousAt.tendsto.comp
    ((tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hf.tendsto_slope)
  have hr (t r : ℝ) (x : H) : U t (r • x) = r • U t x :=
    ContinuousLinearMap.map_smul_of_tower ((U t) : H →L[ℂ] H) r x
  apply hasDerivAt_iff_tendsto_slope.mpr
  change Tendsto (fun t => (t-s)⁻¹ • (U t (f t)-U s (f s))) (𝓝[≠] s) (𝓝 (U s v))
  simpa only [Function.comp_def,id_eq,slope_def_module,h0,map_zero,sub_zero,hr] using ht

#print axioms derivative_at_zero_vector
end
end UnifiedTheory.Audit.KFCausalStrongIsometryDerivative
