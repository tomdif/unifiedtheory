/- Construct domain-preserving approximate trajectories through a bounded
equation for their resolvent coordinates. No domain preservation is assumed. -/
import UnifiedTheory.Audit.KFCausalBoundedLinearIntervalFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalResolventDomainTrajectories
noncomputable section
open Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem operator_apply_within (R : ℝ → V →L[ℂ] V) (z : ℝ → V)
    (R' : V →L[ℂ] V) (z' : V) (I : Set ℝ) (t : ℝ)
    (hR : HasDerivAt R R' t) (hz : HasDerivWithinAt z z' I t) :
    HasDerivWithinAt (fun u => R u (z u)) (R' (z t)+R t z') I t := by
  have hr : HasDerivAt (fun u => (R u).restrictScalars ℝ) (R'.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hR
  exact hr.hasDerivWithinAt.clm_apply hz

theorem reconstructed_derivative (R A D : ℝ → V →L[ℂ] V) (z : ℝ → V)
    (I : Set ℝ) (t : ℝ) (hR : HasDerivAt R (R t*D t) t)
    (hz : HasDerivWithinAt z ((A t-D t) (z t)) I t) (hc : R t*A t = A t*R t) :
    HasDerivWithinAt (fun u => R u (z u)) (A t (R t (z t))) I t := by
  have hd := operator_apply_within R z (R t*D t) ((A t-D t) (z t)) I t hR hz
  have he := congrArg (fun L : V →L[ℂ] V => L (z t)) hc
  simp only [ContinuousLinearMap.mul_apply] at he
  convert hd using 1
  simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.sub_apply,map_sub,he]
  abel

theorem solution_unique (A : ℝ → V →L[ℂ] V) (l r : ℝ)
    (hA : ContinuousOn A (Icc l r)) (u v : ℝ → V)
    (hcU : ContinuousOn u (Icc l r)) (hcV : ContinuousOn v (Icc l r))
    (hu : ∀ t ∈ Icc l r, HasDerivWithinAt u (A t (u t)) (Icc l r) t)
    (hv : ∀ t ∈ Icc l r, HasDerivWithinAt v (A t (v t)) (Icc l r) t)
    (hi : u l = v l) : ∀ t ∈ Icc l r, u t = v t := by
  obtain ⟨N,hN⟩ := (isCompact_Icc : IsCompact (Icc l r)).exists_bound_of_continuousOn hA
  have he := KFCausalBoundedLinearIntervalFlow.interval_norm_bound
    (fun t => u t-v t) (fun t => A t (u t)-A t (v t)) l r N 0 (hcU.sub hcV)
    (fun t ht => (hu t ht).sub (hv t ht)) (by simp only [hi,sub_self,norm_zero,le_refl])
    (fun t ht => by
      change ‖A t (u t)-A t (v t)‖ ≤ N*‖u t-v t‖
      rw [← map_sub]
      exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hN t ht) (norm_nonneg _)))
  intro t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using he t ht))

variable [CompleteSpace V]

theorem exists_graph_solution (G : ℝ → V →ₗ.[ℂ] V) (A R D : ℝ → V →L[ℂ] V)
    (lam l r : ℝ) (hlr : l ≤ r) (hA : ContinuousOn A (Icc l r)) (hD : ContinuousOn D (Icc l r))
    (hR : ∀ t ∈ Icc l r, HasDerivAt R (R t*D t) t)
    (hcomm : ∀ t ∈ Icc l r, R t*A t = A t*R t)
    (hgraph : ∀ t ∈ Icc l r, ∀ f, (R t f,lam • R t f-f) ∈ (G t).graph)
    (hleft : ∀ x y, (x,y) ∈ (G l).graph → R l (lam • x-y) = x)
    (x y : V) (hxy : (x,y) ∈ (G l).graph) :
    ∃ w z : ℝ → V, w l = x ∧ z l = lam • x-y ∧
      ContinuousOn w (Icc l r) ∧ ContinuousOn z (Icc l r) ∧
      (∀ t ∈ Icc l r, w t = R t (z t)) ∧ ∀ t ∈ Icc l r,
        HasDerivWithinAt w (A t (w t)) (Icc l r) t ∧
        HasDerivWithinAt z ((A t-D t) (z t)) (Icc l r) t ∧
        (w t,lam • w t-z t) ∈ (G t).graph := by
  obtain ⟨z,hi,hc,hz⟩ := KFCausalBoundedLinearIntervalFlow.exists_interval_solution
    (fun t => A t-D t) l r hlr (hA.sub hD) (lam • x-y)
  have hRc : ContinuousOn R (Icc l r) := fun t ht => (hR t ht).continuousAt.continuousWithinAt
  refine ⟨fun t => R t (z t),z,?_,hi,hRc.clm_apply hc,hc,fun _ _ => rfl,?_⟩
  · change R l (z l) = x
    rw [hi]
    exact hleft x y hxy
  · intro t ht
    exact ⟨reconstructed_derivative R A D z (Icc l r) t (hR t ht) (hz t ht) (hcomm t ht),
      hz t ht,hgraph t ht (z t)⟩

theorem every_solution_graph (G : ℝ → V →ₗ.[ℂ] V) (A R D : ℝ → V →L[ℂ] V)
    (lam l r : ℝ) (hlr : l ≤ r) (hA : ContinuousOn A (Icc l r)) (hD : ContinuousOn D (Icc l r))
    (hR : ∀ t ∈ Icc l r, HasDerivAt R (R t*D t) t)
    (hcomm : ∀ t ∈ Icc l r, R t*A t = A t*R t)
    (hgraph : ∀ t ∈ Icc l r, ∀ f, (R t f,lam • R t f-f) ∈ (G t).graph)
    (hleft : ∀ x y, (x,y) ∈ (G l).graph → R l (lam • x-y) = x)
    (w : ℝ → V) (y : V) (hi : (w l,y) ∈ (G l).graph)
    (hc : ContinuousOn w (Icc l r))
    (hw : ∀ t ∈ Icc l r, HasDerivWithinAt w (A t (w t)) (Icc l r) t) :
    ∃ z : ℝ → V, z l = lam • w l-y ∧ ContinuousOn z (Icc l r) ∧ ∀ t ∈ Icc l r,
      w t = R t (z t) ∧ HasDerivWithinAt z ((A t-D t) (z t)) (Icc l r) t ∧
      (w t,lam • w t-z t) ∈ (G t).graph := by
  obtain ⟨u,z,hu,hz,huc,hzc,hur,hug⟩ := exists_graph_solution G A R D lam l r hlr hA hD
    hR hcomm hgraph hleft (w l) y hi
  have he := solution_unique A l r hA w u hc huc hw (fun t ht => (hug t ht).1) hu.symm
  refine ⟨z,hz,hzc,?_⟩
  intro t ht
  exact ⟨(he t ht).trans (hur t ht),(hug t ht).2.1,by simpa only [he t ht] using (hug t ht).2.2⟩

#print axioms operator_apply_within
#print axioms reconstructed_derivative
#print axioms solution_unique
#print axioms exists_graph_solution
#print axioms every_solution_graph
end
end UnifiedTheory.Audit.KFCausalResolventDomainTrajectories
