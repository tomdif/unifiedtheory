/- Uniform physical comparison follows from a vanishing squared-error
bound, then extends from dense initial data by unitarity. -/
import UnifiedTheory.Audit.KFCausalStrongResolventFlowComparison
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDenseUnitaryUniformComparison
noncomputable section
open Filter
open scoped Topology
variable {H E ι τ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
theorem uniform_zero_of_square_bound (f : ι → τ → H) (b : ι → ℝ) (p : Filter ι) (I : Set τ)
    (hb : ∀ᶠ n in p, ∀ t ∈ I, ‖f n t‖^2 ≤ b n)
    (hl : Tendsto b p (𝓝 0)) : TendstoUniformlyOn f (fun _ => 0) p I := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [hb,hl.eventually (gt_mem_nhds (sq_pos_of_pos heps))] with n hn hbn
  intro t ht
  rw [dist_zero_left]
  have he := (hn t ht).trans_lt hbn
  nlinarith [norm_nonneg (f n t)]

theorem uniform_error_of_dense (J : E → H) (hJ : DenseRange J)
    (U V : ι → τ → H ≃ₗᵢ[ℂ] H) (p : Filter ι) (I : Set τ)
    (hd : ∀ x, TendstoUniformlyOn (fun n t => U n t (J x)-V n t (J x)) (fun _ => 0) p I)
    (x : H) : TendstoUniformlyOn (fun n t => U n t x-V n t x) (fun _ => 0) p I := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  obtain ⟨y,hxy⟩ := hJ.exists_dist_lt x (show 0 < eps/8 by positivity)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hd y)) (eps/2) (by positivity)] with n hn
  intro t ht
  have he := KFCausalStrongResolventFlowComparison.dense_comparison (U n t) (V n t) x (J y)
  have hm : ‖U n t (J y)-V n t (J y)‖ < eps/2 := by simpa only [dist_zero_left] using hn t ht
  rw [dist_eq_norm] at hxy
  rw [dist_zero_left]
  linarith

#print axioms uniform_zero_of_square_bound
#print axioms uniform_error_of_dense
end
end UnifiedTheory.Audit.KFCausalDenseUnitaryUniformComparison
