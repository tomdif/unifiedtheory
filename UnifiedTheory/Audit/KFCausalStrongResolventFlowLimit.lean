/- Strong convergence of shifted resolvents implies convergence of the
corresponding unitary groups, uniformly on bounded time intervals for
every fixed physical input. All derivative hypotheses are explicit. -/
import UnifiedTheory.Audit.KFCausalStrongOperatorCompactLimit
import UnifiedTheory.Audit.KFCausalStrongResolventFlowComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalStrongResolventFlowLimit
noncomputable section
open Set Filter
open scoped Topology
open KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem uniform_on_double_resolvent (U : ι → StrongUnitaryGroup H) (V : StrongUnitaryGroup H)
    (R : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (c : ℂ) (p : Filter ι)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ n in p, ∀ x, ‖R n x-S x‖ ≤ C*‖x‖)
    (hl : ∀ x, Tendsto (fun n => R n x) p (𝓝 (S x)))
    (hU : ∀ᶠ n in p, ∀ f t, HasDerivAt (fun u => (U n).action u (R n f))
      (c • (U n).action t (f-R n f)) t)
    (hV : ∀ f t, HasDerivAt (fun u => V.action u (S f)) (c • V.action t (f-S f)) t)
    (hc : ∀ t x, S (V.action t x)=V.action t (S x)) (x : H) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun n t => (U n).action t (S (S x)))
      (fun t => V.action t (S (S x))) p (Icc (-L) L) := by
  have hm₁ := KFCausalStrongOperatorCompactLimit.moving_limit R S p C hC hb hl
    (Icc (-L) L) isCompact_Icc (fun t => V.action t x) (V.continuous_orbit x).continuousOn
  have hm₂ := KFCausalStrongOperatorCompactLimit.moving_limit R S p C hC hb hl
    (Icc (-L) L) isCompact_Icc (fun t => V.action t (S x)) (V.continuous_orbit (S x)).continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  let δ := eps/(2*(2+‖c‖*L))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hU,(Metric.tendstoUniformlyOn_iff.mp hm₁) δ hδ,
    (Metric.tendstoUniformlyOn_iff.mp hm₂) δ hδ] with n hn h₁ h₂
  intro t ht
  have he := KFCausalStrongResolventFlowComparison.double_resolvent_bound (U n) V (R n) S c hn hV hc
    x L δ t hL hδ.le (abs_le.mpr ht)
    (fun s hs => by simpa only [dist_eq_norm,norm_sub_rev] using (h₁ s hs).le)
    (fun s hs => by simpa only [dist_eq_norm,norm_sub_rev] using (h₂ s hs).le)
  have hδval : (2+‖c‖*L)*δ=eps/2 := by
    dsimp [δ]
    have hp : 0 < 2+‖c‖*L := by positivity
    field_simp
  rw [dist_eq_norm,norm_sub_rev]
  exact he.trans_lt (hδval.trans_lt (by linarith))

theorem uniform_limit (U : ι → StrongUnitaryGroup H) (V : StrongUnitaryGroup H)
    (R : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (c : ℂ) (p : Filter ι)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ n in p, ∀ x, ‖R n x-S x‖ ≤ C*‖x‖)
    (hl : ∀ x, Tendsto (fun n => R n x) p (𝓝 (S x)))
    (hU : ∀ᶠ n in p, ∀ f t, HasDerivAt (fun u => (U n).action u (R n f))
      (c • (U n).action t (f-R n f)) t)
    (hV : ∀ f t, HasDerivAt (fun u => V.action u (S f)) (c • V.action t (f-S f)) t)
    (hc : ∀ t x, S (V.action t x)=V.action t (S x)) (hS : DenseRange S)
    (x : H) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun n t => (U n).action t x) (fun t => V.action t x) p (Icc (-L) L) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  obtain ⟨y,hxy⟩ := (hS.comp hS S.continuous).exists_dist_lt x (show 0 < eps/8 by positivity)
  have hy := uniform_on_double_resolvent U V R S c p C hC hb hl hU hV hc y L hL
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hy) (eps/2) (by positivity)] with n hn
  intro t ht
  have hd := KFCausalStrongResolventFlowComparison.dense_comparison ((U n).action t) (V.action t) x (S (S y))
  have hm : ‖(U n).action t (S (S y))-V.action t (S (S y))‖ < eps/2 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hn t ht
  change dist x (S (S y)) < eps/8 at hxy
  rw [dist_eq_norm] at hxy
  rw [dist_eq_norm,norm_sub_rev]
  linarith

#print axioms uniform_on_double_resolvent
#print axioms uniform_limit
end
end UnifiedTheory.Audit.KFCausalStrongResolventFlowLimit
