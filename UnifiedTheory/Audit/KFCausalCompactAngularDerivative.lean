/- Differentiation on a compact angular interval with the dominating
bound derived from continuity, rather than supplied as a hypothesis. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralHolomorphic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCompactAngularDerivative
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem integral_hasDerivAt (F F' : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ x θ, HasDerivAt (fun t => F t θ) (F' x θ) x) (x : ℝ) :
    HasDerivAt (fun t => ∫ θ in -Real.pi..Real.pi, F t θ)
      (∫ θ in -Real.pi..Real.pi, F' x θ) x := by
  have hc := (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hF'.norm.continuousOn
    (s := Icc (x-1) (x+1) ×ˢ Icc (-Real.pi) Real.pi)
  obtain ⟨M,hM⟩ := hc.bddAbove
  have hf (t : ℝ) : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hf' (t : ℝ) : Continuous (F' t) := hF'.comp (continuous_const.prodMk continuous_id)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => M)
    (Icc_mem_nhds (by linarith : x-1<x) (by linarith : x<x+1))
    (Filter.Eventually.of_forall (fun t => (hf t).aestronglyMeasurable))
    ((hf x).intervalIntegrable _ _) (hf' x).aestronglyMeasurable _
    (intervalIntegrable_const) (Filter.Eventually.of_forall (fun θ _ t _ => hd t θ))).2
  filter_upwards [] with θ hθ t ht
  apply hM
  refine ⟨(t,θ),⟨ht,?_⟩,rfl⟩
  have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [uIoc_of_le hp] at hθ
  exact ⟨hθ.1.le,hθ.2⟩

#print axioms integral_hasDerivAt
end
end UnifiedTheory.Audit.KFCausalCompactAngularDerivative
