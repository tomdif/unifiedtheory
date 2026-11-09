/- Uniformly bounded operator families which converge strongly, uniformly
in time, converge uniformly on compact sets of vectors and on moving states. -/
import UnifiedTheory.Audit.KFCausalUniformResolventLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCompactMovingLimit
noncomputable section
open Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {ι τ : Type*}

theorem compact_uniform (A : ι → τ → V →L[ℂ] V) (p : Filter ι) (I : Set τ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in p, ∀ t ∈ I, ∀ x, ‖A n t x‖ ≤ C*‖x‖)
    (hpoint : ∀ x, TendstoUniformlyOn (fun n t => A n t x) (fun _ => x) p I)
    (K : Set V) (hK : IsCompact K) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n in p, ∀ t ∈ I, ∀ x ∈ K, ‖A n t x-x‖ < eps := by
  have hCp : 0 < C+1 := by linarith
  obtain ⟨F,_hFK,hF,hcover⟩ := hK.finite_cover_balls
    (show 0 < eps/(3*(C+1)) by positivity)
  have hfinite : ∀ᶠ n in p, ∀ y ∈ F, ∀ t ∈ I, dist y (A n t y) < eps/3 :=
    hF.eventually_all.mpr (fun y _ => (Metric.tendstoUniformlyOn_iff.mp (hpoint y)) _ (by positivity))
  filter_upwards [hbound,hfinite] with n hn hfn
  intro t ht x hx
  obtain ⟨y,hy,hxy⟩ : ∃ y ∈ F, dist x y < eps/(3*(C+1)) := by
    simpa only [mem_iUnion,Metric.mem_ball,exists_prop] using hcover hx
  have hclose : (C+1)*‖x-y‖ < eps/3 := by
    rw [dist_eq_norm] at hxy
    have hm := (lt_div_iff₀ (show 0 < 3*(C+1) by positivity)).mp hxy
    nlinarith
  have hmid : ‖A n t y-y‖ < eps/3 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hfn y hy t ht
  have he : A n t x-x = A n t (x-y)+(A n t y-y)+(y-x) := by
    rw [map_sub]
    abel
  have hnorm : ‖A n t x-x‖ ≤ (C+1)*‖x-y‖+‖A n t y-y‖ := by
    rw [he]
    calc
      _ ≤ (‖A n t (x-y)‖+‖A n t y-y‖)+‖y-x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (C*‖x-y‖+‖A n t y-y‖)+‖y-x‖ :=
        add_le_add (add_le_add (hn t ht _) le_rfl) le_rfl
      _ = _ := by rw [norm_sub_rev y x]; ring
  linarith

theorem moving_limit [TopologicalSpace τ]
    (A : ι → τ → V →L[ℂ] V) (p : Filter ι) (I : Set τ) (hI : IsCompact I)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in p, ∀ t ∈ I, ∀ x, ‖A n t x‖ ≤ C*‖x‖)
    (hpoint : ∀ x, TendstoUniformlyOn (fun n t => A n t x) (fun _ => x) p I)
    (u : τ → V) (hu : ContinuousOn u I) :
    TendstoUniformlyOn (fun n t => A n t (u t)) u p I := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [compact_uniform A p I C hC hbound hpoint (u '' I)
    (hI.image_of_continuousOn hu) eps heps] with n hn
  intro t ht
  simpa only [dist_eq_norm,norm_sub_rev] using hn t ht (u t) (mem_image_of_mem u ht)

theorem varying_limit [TopologicalSpace τ]
    (A : ι → τ → V →L[ℂ] V) (p : Filter ι) (I : Set τ) (hI : IsCompact I)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in p, ∀ t ∈ I, ∀ x, ‖A n t x‖ ≤ C*‖x‖)
    (hpoint : ∀ x, TendstoUniformlyOn (fun n t => A n t x) (fun _ => x) p I)
    (w : ι → τ → V) (u : τ → V) (hu : ContinuousOn u I)
    (hw : TendstoUniformlyOn w u p I) :
    TendstoUniformlyOn (fun n t => A n t (w n t)) u p I := by
  have hm := moving_limit A p I hI C hC hbound hpoint u hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have hCp : 0 < C+1 := by linarith
  filter_upwards [hbound,
    (Metric.tendstoUniformlyOn_iff.mp hw) (eps/(2*(C+1))) (by positivity),
    (Metric.tendstoUniformlyOn_iff.mp hm) (eps/2) (by positivity)] with n hn hwn hmn
  intro t ht
  have hclose : C*‖w n t-u t‖ < eps/2 := by
    have hh := hwn t ht
    rw [dist_eq_norm,norm_sub_rev] at hh
    have hh' := (lt_div_iff₀ (show 0 < 2*(C+1) by positivity)).mp hh
    nlinarith [norm_nonneg (w n t-u t)]
  have hdiff : dist (A n t (u t)) (A n t (w n t)) < eps/2 := by
    rw [dist_eq_norm,norm_sub_rev,← map_sub]
    exact (hn t ht _).trans_lt hclose
  exact (dist_triangle (u t) (A n t (u t)) (A n t (w n t))).trans_lt
    (by linarith [hmn t ht])

#print axioms compact_uniform
#print axioms moving_limit
#print axioms varying_limit
end
end UnifiedTheory.Audit.KFCausalCompactMovingLimit
