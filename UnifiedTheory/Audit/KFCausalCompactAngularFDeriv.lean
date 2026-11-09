/- Joint differentiability of an angular integral. Compactness supplies
the local derivative envelope for a C1 integrand with two real parameters. -/
import UnifiedTheory.Audit.KFCausalCompactAngularDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalCompactAngularFDeriv
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem integral_differentiable (F : (ℝ × ℝ) → ℝ → ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F)) :
    Differentiable ℝ (fun p => ∫ θ in -Real.pi..Real.pi, F p θ) := by
  let D := fun (p : ℝ × ℝ) (θ : ℝ) =>
    (fderiv ℝ (Function.uncurry F) (p,θ)).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ)
  have hc : Continuous (Function.uncurry D) :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hd (p : ℝ × ℝ) (θ : ℝ) : HasFDerivAt (fun q => F q θ) (D p θ) p := by
    exact ((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp p
      (hasFDerivAt_prodMk_left p θ)
  intro p
  have hb := ((isCompact_closedBall p (1:ℝ)).prod isCompact_Icc).image_of_continuousOn
    hc.norm.continuousOn (s := Metric.closedBall p 1 ×ˢ Icc (-Real.pi) Real.pi)
  obtain ⟨M,hM⟩ := hb.bddAbove
  have hf (q : ℝ × ℝ) : Continuous (F q) := hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hg (q : ℝ × ℝ) : Continuous (D q) := hc.comp (continuous_const.prodMk continuous_id)
  apply (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := D) (bound := fun _ => M)
    (Metric.closedBall_mem_nhds p (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun q => (hf q).aestronglyMeasurable))
    ((hf p).intervalIntegrable _ _) (hg p).aestronglyMeasurable _
    intervalIntegrable_const (Eventually.of_forall (fun θ _ q _ => hd q θ))).differentiableAt
  filter_upwards [] with θ hθ q hq
  apply hM
  refine ⟨(q,θ),⟨hq,?_⟩,rfl⟩
  rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at hθ
  exact ⟨hθ.1.le,hθ.2⟩

#print axioms integral_differentiable
end
end UnifiedTheory.Audit.KFCausalCompactAngularFDeriv
