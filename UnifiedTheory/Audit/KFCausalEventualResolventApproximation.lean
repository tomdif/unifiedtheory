/- Eventual resolvent bounds suffice for strong approximation on a dense
domain. The spectral threshold may be positive, as for bounded perturbations. -/
import UnifiedTheory.Audit.KFCausalDenseResolventConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEventualResolventApproximation
noncomputable section
open Filter
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem scaled_bound_from_gap (R : V →L[ℂ] V) (b w K : ℝ)
    (hb : 0 < b) (hgap : w < b) (hhalf : 2*w ≤ b) (hK : 0 ≤ K)
    (hr : ∀ f, ‖R f‖ ≤ K/(b-w)*‖f‖) (f : V) : ‖b • R f‖ ≤ (2*K)*‖f‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hb]
  have hratio : b*(K/(b-w)) ≤ 2*K := by
    rw [← mul_div_assoc,div_le_iff₀ (sub_pos.mpr hgap)]
    nlinarith only [mul_nonneg hK (show 0 ≤ b-2*w by linarith only [hhalf])]
  exact (mul_le_mul_of_nonneg_left (hr f) hb.le).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hratio (norm_nonneg f))

theorem scaled_strong_limit (T : V →ₗ.[ℂ] V) (R : ℝ → V →L[ℂ] V) (C q : ℝ)
    (hC : 0 ≤ C) (hdense : Dense (T.domain : Set V))
    (hbound : ∀ b, q < b → 0 < b → ∀ f, ‖b • R b f‖ ≤ C*‖f‖)
    (hleft : ∀ b, q < b → 0 < b → ∀ x : T.domain, R b (b • (x:V)-T x) = x) (f : V) :
    Tendsto (fun b : ℝ => b • R b f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have hCp : 0 < C+1 := by linarith
  obtain ⟨x,hx,hfx⟩ := hdense.exists_dist_lt f (show 0 < δ/(4*(C+1)) by positivity)
  let y : T.domain := ⟨x,hx⟩
  refine ⟨max (q+1) (max 1 (4*C*‖T y‖/δ)),?_⟩
  intro b hb
  have hbq : q < b := lt_of_lt_of_le (by linarith : q < q+1) ((le_max_left _ _).trans hb)
  have hbm := (le_max_right _ _).trans hb
  have hb1 : 1 ≤ b := (le_max_left _ _).trans hbm
  have hbp : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hbl : 4*C*‖T y‖/δ ≤ b := (le_max_right _ _).trans hbm
  have hlast : b⁻¹*C*‖T y‖ ≤ δ/4 := by
    rw [mul_assoc]
    apply (inv_mul_le_iff₀ hbp).mpr
    have hm := (div_le_iff₀ hδ).mp hbl
    nlinarith
  rw [dist_eq_norm] at hfx ⊢
  have hfirst : (C+1)*‖f-(y:V)‖ < δ/4 := by
    change ‖f-(y:V)‖ < δ/(4*(C+1)) at hfx
    have hm := mul_lt_mul_of_pos_left hfx hCp
    have he : (C+1)*(δ/(4*(C+1))) = δ/4 := by field_simp
    exact hm.trans_eq he
  have hl (z : T.domain) : R b (b • (z:V)-(1:ℂ) • T z) = z := by
    simpa only [one_smul] using hleft b hbq hbp z
  have he := KFCausalDenseResolventConvergence.dense_error T (R b) 1 b C hbp
    (hbound b hbq hbp) hl f y
  simp only [one_smul] at he
  linarith

theorem generator_strong_limit (T : V →ₗ.[ℂ] V) (R : ℝ → V →L[ℂ] V) (q : ℝ)
    (hleft : ∀ b, q < b → ∀ x : T.domain, R b (b • (x:V)-T x) = x)
    (hlim : ∀ f, Tendsto (fun b : ℝ => b • R b f) atTop (𝓝 f)) (x : T.domain) :
    Tendsto (fun b : ℝ => (b • (b • R b-1)) (x:V)) atTop (𝓝 (T x)) := by
  apply (hlim (T x)).congr'
  filter_upwards [eventually_gt_atTop q] with b hb
  have hl (z : T.domain) : R b (b • (z:V)-(1:ℂ) • T z) = z := by
    simpa only [one_smul] using hleft b hb z
  simpa only [one_smul] using (KFCausalDenseResolventConvergence.generator_on_domain T (R b) 1 b hl x).symm

theorem compact_uniform_scaling (R : ℝ → ℝ → V →L[ℂ] V) (K q : ℝ → ℝ)
    (hK : Continuous K) (hq : Continuous q)
    (hbound : ∀ b t, 0 < b → 2*q t < b → ∀ f, ‖b • R b t f‖ ≤ (2*K t)*‖f‖)
    (l r : ℝ) :
    ∃ b₀ K₀ : ℝ, 0 < b₀ ∧ 0 ≤ K₀ ∧ ∀ b, b₀ ≤ b → ∀ t ∈ Set.Icc l r,
      q t < b ∧ ∀ f : V, ‖b • R b t f‖ ≤ K₀*‖f‖ := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Set.Icc l r)).bddAbove_image hK.continuousOn
  obtain ⟨N,hN⟩ := (isCompact_Icc : IsCompact (Set.Icc l r)).bddAbove_image hq.continuousOn
  refine ⟨2*(|N|+1),2*(|M|+1),by positivity,by positivity,?_⟩
  intro b hb t ht
  have hkt : K t ≤ M := hM (Set.mem_image_of_mem _ ht)
  have hqt : q t ≤ N := hN (Set.mem_image_of_mem _ ht)
  have hbp : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hlarge : 2*q t < b := by linarith [le_abs_self N]
  refine ⟨by linarith [le_abs_self N],?_⟩
  intro f
  exact (hbound b t hbp hlarge f).trans
    (mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (norm_nonneg _))

#print axioms scaled_bound_from_gap
#print axioms scaled_strong_limit
#print axioms generator_strong_limit
#print axioms compact_uniform_scaling
end
end UnifiedTheory.Audit.KFCausalEventualResolventApproximation
