/- Strong operator convergence with a common norm bound is uniform on
compact vector sets, hence on a fixed continuous trajectory over a
compact time interval. Arbitrary moving inputs are not covered. -/
import UnifiedTheory.Audit.KFCausalCompactMovingLimit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalStrongOperatorCompactLimit
noncomputable section
open Set Filter
open scoped Topology
variable {H ι τ : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem compact_uniform (R : ι → H →L[ℂ] H) (R0 : H →L[ℂ] H) (p : Filter ι)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ n in p, ∀ x, ‖R n x-R0 x‖ ≤ C*‖x‖)
    (hl : ∀ x, Tendsto (fun n => R n x) p (𝓝 (R0 x)))
    (K : Set H) (hK : IsCompact K) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n in p, ∀ x ∈ K, ‖R n x-R0 x‖ < eps := by
  have hCp : 0 < C+1 := by linarith
  obtain ⟨F,_,hF,hcover⟩ := hK.finite_cover_balls (show 0 < eps/(3*(C+1)) by positivity)
  have hf : ∀ᶠ n in p, ∀ y ∈ F, ‖R n y-R0 y‖ < eps/3 :=
    hF.eventually_all.mpr (fun y _ => by
      simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp (hl y)) (eps/3) (by positivity))
  filter_upwards [hb,hf] with n hn hfn
  intro x hx
  obtain ⟨y,hy,hxy⟩ : ∃ y ∈ F, dist x y < eps/(3*(C+1)) := by
    simpa only [mem_iUnion,Metric.mem_ball,exists_prop] using hcover hx
  have hc : C*‖x-y‖ < eps/3 := by
    rw [dist_eq_norm] at hxy
    have hh := (lt_div_iff₀ (show 0 < 3*(C+1) by positivity)).mp hxy
    nlinarith [norm_nonneg (x-y)]
  have he : R n x-R0 x=(R n (x-y)-R0 (x-y))+(R n y-R0 y) := by
    rw [map_sub,map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith [hn (x-y),hfn y hy])

theorem moving_limit [TopologicalSpace τ]
    (R : ι → H →L[ℂ] H) (R0 : H →L[ℂ] H) (p : Filter ι)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ n in p, ∀ x, ‖R n x-R0 x‖ ≤ C*‖x‖)
    (hl : ∀ x, Tendsto (fun n => R n x) p (𝓝 (R0 x)))
    (I : Set τ) (hI : IsCompact I) (v : τ → H) (hv : ContinuousOn v I) :
    TendstoUniformlyOn (fun n t => R n (v t)) (fun t => R0 (v t)) p I := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [compact_uniform R R0 p C hC hb hl (v '' I)
    (hI.image_of_continuousOn hv) eps heps] with n hn
  intro t ht
  simpa only [dist_eq_norm,norm_sub_rev] using hn (v t) (mem_image_of_mem v ht)

#print axioms compact_uniform
#print axioms moving_limit
end
end UnifiedTheory.Audit.KFCausalStrongOperatorCompactLimit
