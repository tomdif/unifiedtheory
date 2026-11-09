/- Strong convergence from uniform scaled-resolvent bounds and an exact
left inverse on a dense operator domain. No symmetry in the original
Hilbert norm is required. -/
import UnifiedTheory.Audit.KFCausalMassResolventStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDenseResolventConvergence
noncomputable section
open Filter
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem domain_error (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (c : ℂ) (b C : ℝ)
    (hb : 0 < b) (hbound : ∀ f, ‖b • R f‖ ≤ C*‖f‖)
    (hleft : ∀ x : T.domain, R (b • (x:V)-c • T x) = x) (x : T.domain) :
    ‖b • R (x:V)-(x:V)‖ ≤ b⁻¹*C*‖c • T x‖ := by
  have he := hleft x
  rw [map_sub,ContinuousLinearMap.map_smul_of_tower] at he
  have hh : b • R (x:V)-(x:V) = R (c • T x) := by
    apply sub_eq_iff_eq_add.mpr
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  rw [hh,mul_assoc]
  apply (le_inv_mul_iff₀ hb).mpr
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hb] using hbound (c • T x)

theorem dense_error (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (c : ℂ) (b C : ℝ)
    (hb : 0 < b) (hbound : ∀ f, ‖b • R f‖ ≤ C*‖f‖)
    (hleft : ∀ x : T.domain, R (b • (x:V)-c • T x) = x) (f : V) (x : T.domain) :
    ‖b • R f-f‖ ≤ (C+1)*‖f-(x:V)‖+b⁻¹*C*‖c • T x‖ := by
  have he : b • R f-f = b • R (f-(x:V))+(b • R (x:V)-(x:V))+((x:V)-f) := by
    rw [map_sub,smul_sub]
    abel
  rw [he]
  calc
    _ ≤ (‖b • R (f-(x:V))‖+‖b • R (x:V)-(x:V)‖)+‖(x:V)-f‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (C*‖f-(x:V)‖+b⁻¹*C*‖c • T x‖)+‖(x:V)-f‖ :=
      add_le_add (add_le_add (hbound _) (domain_error T R c b C hb hbound hleft x)) le_rfl
    _ = _ := by rw [norm_sub_rev (x:V) f]; ring

theorem scaled_strong_limit (T : V →ₗ.[ℂ] V) (R : ℝ → V →L[ℂ] V) (c : ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hdense : Dense (T.domain : Set V))
    (hbound : ∀ b, 0 < b → ∀ f, ‖b • R b f‖ ≤ C*‖f‖)
    (hleft : ∀ b, 0 < b → ∀ x : T.domain, R b (b • (x:V)-c • T x) = x) (f : V) :
    Tendsto (fun b : ℝ => b • R b f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have hCp : 0 < C+1 := by linarith
  obtain ⟨x,hx,hfx⟩ := hdense.exists_dist_lt f (show 0 < δ/(4*(C+1)) by positivity)
  let y : T.domain := ⟨x,hx⟩
  refine ⟨max 1 (4*C*‖c • T y‖/δ),?_⟩
  intro b hb
  have hb1 : 1 ≤ b := (le_max_left _ _).trans hb
  have hbp : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hbm : 4*C*‖c • T y‖/δ ≤ b := (le_max_right _ _).trans hb
  have hlast : b⁻¹*C*‖c • T y‖ ≤ δ/4 := by
    rw [mul_assoc]
    apply (inv_mul_le_iff₀ hbp).mpr
    have hm := (div_le_iff₀ hδ).mp hbm
    nlinarith
  rw [dist_eq_norm] at hfx ⊢
  have hfirst : (C+1)*‖f-(y:V)‖ < δ/4 := by
    change ‖f-(y:V)‖ < δ/(4*(C+1)) at hfx
    have hm := mul_lt_mul_of_pos_left hfx hCp
    have he : (C+1)*(δ/(4*(C+1))) = δ/4 := by field_simp
    exact hm.trans_eq he
  have he := dense_error T (R b) c b C hbp (hbound b hbp) (hleft b hbp) f y
  linarith

theorem generator_on_domain (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (c : ℂ) (b : ℝ)
    (hleft : ∀ x : T.domain, R (b • (x:V)-c • T x) = x) (x : T.domain) :
    (b • (b • R-1)) (x:V) = b • R (c • T x) := by
  have he := hleft x
  rw [map_sub,ContinuousLinearMap.map_smul_of_tower] at he
  change b • (b • R (x:V)-(x:V)) = b • R (c • T x)
  congr 1
  apply sub_eq_iff_eq_add.mpr
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem generator_strong_limit (T : V →ₗ.[ℂ] V) (R : ℝ → V →L[ℂ] V) (c : ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hdense : Dense (T.domain : Set V))
    (hbound : ∀ b, 0 < b → ∀ f, ‖b • R b f‖ ≤ C*‖f‖)
    (hleft : ∀ b, 0 < b → ∀ x : T.domain, R b (b • (x:V)-c • T x) = x) (x : T.domain) :
    Tendsto (fun b : ℝ => (b • (b • R b-1)) (x:V)) atTop (𝓝 (c • T x)) := by
  apply (scaled_strong_limit T R c C hC hdense hbound hleft (c • T x)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
  exact (generator_on_domain T (R b) c b (hleft b hb) x).symm

#print axioms generator_on_domain
#print axioms generator_strong_limit
#print axioms domain_error
#print axioms dense_error
#print axioms scaled_strong_limit
end
end UnifiedTheory.Audit.KFCausalDenseResolventConvergence
