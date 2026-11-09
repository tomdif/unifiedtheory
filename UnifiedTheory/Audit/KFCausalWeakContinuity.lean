/- A bounded Hilbert-valued curve is weakly continuous when its pairings
against a dense family of test vectors are continuous. -/
import UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeakContinuity
noncomputable section
open Filter TopologicalSpace
open scoped Topology

variable {H E X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace X]

theorem weak_continuous_of_dense_tests (J : E → H) (hJ : DenseRange J) (u : X → H) (M : ℝ)
    (hb : ∀ t, ‖u t‖ ≤ M) (hc : ∀ v, Continuous (fun t => inner ℂ (u t) (J v))) :
    ∀ y, Continuous (fun t => inner ℂ (u t) y) := by
  intro y
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp (hJ y)
  choose w hw using hv
  have hn : Tendsto (fun n => M*‖y-v n‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero] using
      ((tendsto_const_nhds (x := y)).sub hlim).norm.const_mul M
  have hu : TendstoUniformly (fun n t => inner ℂ (u t) (v n)) (fun t => inner ℂ (u t) y) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro δ hδ
    filter_upwards [hn.eventually (gt_mem_nhds hδ)] with n hn t
    rw [dist_eq_norm,← inner_sub_right]
    exact ((norm_inner_le_norm (u t) (y-v n)).trans
      (mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _))).trans_lt hn
  apply hu.continuous
  apply Filter.Frequently.of_forall
  intro n
  rw [← hw n]
  exact hc (w n)

#print axioms weak_continuous_of_dense_tests

end
end UnifiedTheory.Audit.KFCausalWeakContinuity
