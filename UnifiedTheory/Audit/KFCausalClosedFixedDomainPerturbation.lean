/- Invertible bounded output changes and bounded additive terms preserve
a closed operator's domain and closed graph. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClosedFixedDomainPerturbation
noncomputable section
open Set
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def transform (T : V →ₗ.[ℂ] V) (A B : V →L[ℂ] V) : V →ₗ.[ℂ] V where
  domain := T.domain
  toFun := A.toLinearMap.comp T.toFun+B.toLinearMap.comp T.domain.subtype

theorem transform_apply (T : V →ₗ.[ℂ] V) (A B : V →L[ℂ] V) (x : T.domain) :
    transform T A B x = A (T x)+B (x:V) := rfl

theorem graph_iff (T : V →ₗ.[ℂ] V) (A B Z : V →L[ℂ] V)
    (hl : ∀ v, Z (A v) = v) (hr : ∀ v, A (Z v) = v) (x y : V) :
    (x,y) ∈ (transform T A B).graph ↔ (x,Z (y-B x)) ∈ T.graph := by
  constructor
  · intro hp
    obtain ⟨u,hx,hy⟩ := ((transform T A B).mem_graph_iff).mp hp
    change (u:V) = x at hx
    change A (T u)+B (u:V) = y at hy
    subst x
    apply T.mem_graph_iff.mpr
    refine ⟨u,rfl,?_⟩
    rw [← hy,add_sub_cancel_right,hl]
  · intro hp
    obtain ⟨u,hx,hy⟩ := (T.mem_graph_iff).mp hp
    change (u:V) = x at hx
    change T u = Z (y-B x) at hy
    subst x
    apply (transform T A B).mem_graph_iff.mpr
    refine ⟨u,rfl,?_⟩
    change A (T u)+B (u:V) = y
    rw [hy,hr,sub_add_cancel]

theorem transform_closed (T : V →ₗ.[ℂ] V) (hT : T.IsClosed) (A B Z : V →L[ℂ] V)
    (hl : ∀ v, Z (A v) = v) (hr : ∀ v, A (Z v) = v) :
    (transform T A B).IsClosed := by
  have he : ((transform T A B).graph : Set (V × V)) =
      (fun p : V × V => (p.1,Z (p.2-B p.1))) ⁻¹' (T.graph : Set (V × V)) := by
    ext p
    exact graph_iff T A B Z hl hr p.1 p.2
  change IsClosed ((transform T A B).graph : Set (V × V))
  rw [he]
  exact hT.preimage (continuous_fst.prodMk (Z.continuous.comp
    (continuous_snd.sub (B.continuous.comp continuous_fst))))

theorem shifted_action (T : V →ₗ.[ℂ] V) (R C : V →L[ℂ] V)
    (c : ℂ) (a : ℝ) (w : T.domain) :
    transform T (c • R) (c • (a • (R-1))+C) w =
      c • R (T w+a • (w:V))-c • (a • (w:V))+C w := by
  rw [transform_apply]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,map_add,
    ContinuousLinearMap.map_smul_of_tower,smul_add,smul_sub]
  abel

theorem transported_shifted_action (S R C D : V →L[ℂ] V)
    (hi : ∀ v, S (R v) = v) (hc : ∀ v, S (C v) = -D v)
    (c : ℂ) (a : ℝ) (w v : V) :
    S (c • R (v+a • w)-c • (a • w)+C w)+D w =
      c • (v+a • w-a • S w) := by
  simp only [map_add,map_sub,map_smul,ContinuousLinearMap.map_smul_of_tower,
    hi,hc,smul_sub]
  abel

#print axioms shifted_action
#print axioms transported_shifted_action
#print axioms transform_apply
#print axioms graph_iff
#print axioms transform_closed
end
end UnifiedTheory.Audit.KFCausalClosedFixedDomainPerturbation
