/- Passage from bounded approximate equations to the transported mass
equation. Only the mass-applied state is differentiated in the limit. -/
import UnifiedTheory.Audit.KFCausalCompactMovingLimit
import UnifiedTheory.Audit.KFCausalResolventDomainTrajectories
import UnifiedTheory.Audit.KFCausalQuasiResolventVelocity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTransportedMassLimit
noncomputable section
open Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem mass_equation_from_graph (T : V →ₗ.[ℂ] V) (M S S' H R A : V →L[ℂ] V)
    (b : ℝ) (hA : A = b • (b • R-1))
    (hR : ∀ f, (R f,b • R f-f) ∈ T.graph)
    (hM : ∀ z : T.domain, M (S (T z)+S' z) = H (S z)) (x : V) :
    M (S (A x)+S' (b • R x)) = H (S (b • R x)) := by
  have hg := KFCausalQuasiResolventVelocity.smoothed_graph T R A b hA hR x
  obtain ⟨z,hz,hgz⟩ := T.mem_graph_iff.mp hg
  simpa only [hgz,hz] using hM z

theorem bounded_apply {ι τ : Type*} (A : τ → V →L[ℂ] V) (p : Filter ι)
    (I : Set τ) (C : ℝ) (hC : 0 ≤ C) (hA : ∀ t ∈ I, ‖A t‖ ≤ C)
    (w : ι → τ → V) (u : τ → V) (hw : TendstoUniformlyOn w u p I) :
    TendstoUniformlyOn (fun n t => A t (w n t)) (fun t => A t (u t)) p I := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have hCp : 0 < C+1 := by linarith
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hw) (eps/(C+1)) (by positivity)] with n hn
  intro t ht
  have he : ‖u t-w n t‖*(C+1) < eps := by
    have hh := hn t ht
    rw [dist_eq_norm] at hh
    exact (lt_div_iff₀ hCp).mp hh
  rw [dist_eq_norm,← map_sub]
  have hb := ((A t).le_opNorm (u t-w n t)).trans
    (mul_le_mul_of_nonneg_right (hA t ht) (norm_nonneg _))
  nlinarith [norm_nonneg (u t-w n t)]

theorem continuous_apply {ι τ : Type*} [TopologicalSpace τ]
    (A : τ → V →L[ℂ] V) (p : Filter ι) (I : Set τ) (hI : IsCompact I)
    (hA : ContinuousOn A I) (w : ι → τ → V) (u : τ → V)
    (hw : TendstoUniformlyOn w u p I) :
    TendstoUniformlyOn (fun n t => A t (w n t)) (fun t => A t (u t)) p I := by
  obtain ⟨C,hC⟩ := hI.exists_bound_of_continuousOn hA
  exact bounded_apply A p I (max C 0) (le_max_right _ _)
    (fun t ht => (hC t ht).trans (le_max_left _ _)) w u hw

theorem approximate_mass_derivative (M : V →L[ℂ] V) (S : ℝ → V →L[ℂ] V)
    (S' A E H : V →L[ℂ] V) (w : ℝ → V) (I : Set ℝ) (t : ℝ)
    (hS : HasDerivAt S S' t) (hw : HasDerivWithinAt w (A (w t)) I t)
    (hg : M (S t (A (w t))+S' (E (w t))) = H (S t (E (w t)))) :
    HasDerivWithinAt (fun z => M (S z (w z)))
      (H (S t (E (w t)))+M (S' (w t-E (w t)))) I t := by
  have hd := KFCausalResolventDomainTrajectories.operator_apply_within S w S' (A (w t)) I t hS hw
  have hm := (M.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  have he : M (S' (w t)+S t (A (w t))) =
      H (S t (E (w t)))+M (S' (w t-E (w t))) := by
    rw [map_add] at hg
    rw [map_add,map_sub,map_sub,← hg]
    abel
  exact hm.congr_deriv he

theorem mass_derivative_limit [CompleteSpace V]
    (M : V →L[ℂ] V) (S S' H : ℝ → V →L[ℂ] V)
    (A E : ℕ → ℝ → V →L[ℂ] V) (w : ℕ → ℝ → V) (u : ℝ → V) (l r : ℝ)
    (hS : ∀ t, HasDerivAt S (S' t) t)
    (hS' : ContinuousOn S' (Icc l r)) (hH : ContinuousOn H (Icc l r))
    (hw : ∀ n t, t ∈ Icc l r → HasDerivWithinAt (w n) (A n t (w n t)) (Icc l r) t)
    (hg : ∀ n t, t ∈ Icc l r →
      M (S t (A n t (w n t))+S' t (E n t (w n t))) = H t (S t (E n t (w n t))))
    (hlim : TendstoUniformlyOn w u atTop (Icc l r))
    (hsm : TendstoUniformlyOn (fun n t => E n t (w n t)) u atTop (Icc l r))
    (t : ℝ) (ht : t ∈ Ioo l r) :
    HasDerivAt (fun z => M (S z (u z))) (H t (S t (u t))) t := by
  have hSc : ContinuousOn S (Icc l r) := fun z _ => (hS z).continuousAt.continuousWithinAt
  have hfirst := continuous_apply (fun z => H z*S z) atTop (Icc l r) isCompact_Icc
    (hH.mul hSc) (fun n z => E n z (w n z)) u hsm
  have hsecond := continuous_apply (fun z => M*S' z) atTop (Icc l r) isCompact_Icc
    (continuousOn_const.mul hS') (fun n z => w n z-E n z (w n z)) (fun z => u z-u z)
    (hlim.sub hsm)
  have hdlim : TendstoUniformlyOn
      (fun n z => H z (S z (E n z (w n z)))+M (S' z (w n z-E n z (w n z))))
      (fun z => H z (S z (u z))) atTop (Icc l r) := by
    have hsum := hfirst.add hsecond
    change TendstoUniformlyOn
      (fun n z => (H z*S z) (E n z (w n z))+(M*S' z) (w n z-E n z (w n z)))
      (fun z => (H z*S z) (u z)+(M*S' z) (u z-u z)) atTop (Icc l r) at hsum
    simpa only [ContinuousLinearMap.mul_apply,sub_self,map_zero,add_zero] using hsum
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hdlim.mono Ioo_subset_Icc_self)
  · exact Eventually.of_forall (fun n z hz =>
      (approximate_mass_derivative M S (S' z) (A n z) (E n z) (H z) (w n) (Icc l r) z
        (hS z) (hw n z (Ioo_subset_Icc_self hz)) (hg n z (Ioo_subset_Icc_self hz))).hasDerivAt
        (Icc_mem_nhds hz.1 hz.2))
  · intro z hz
    exact (M.continuous.tendsto _).comp
      (((S z).continuous.tendsto _).comp (hlim.tendsto_at (Ioo_subset_Icc_self hz)))
  · exact ht

#print axioms mass_equation_from_graph
#print axioms bounded_apply
#print axioms continuous_apply
#print axioms approximate_mass_derivative
#print axioms mass_derivative_limit
end
end UnifiedTheory.Audit.KFCausalTransportedMassLimit
