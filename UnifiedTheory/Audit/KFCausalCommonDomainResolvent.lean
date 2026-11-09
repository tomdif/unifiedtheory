/- Bounded graph outputs and the derivative identity for resolvents of
operators with a fixed domain and differentiable bounded coefficients. -/
import UnifiedTheory.Audit.KFCausalClosedFixedDomainPerturbation
import UnifiedTheory.Audit.KFCausalMassFormOperator
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCommonDomainResolvent
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClosedFixedDomainPerturbation
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem transform_graph (T : V →ₗ.[ℂ] V) (A B : V →L[ℂ] V)
    (x y : V) (hxy : (x,y) ∈ T.graph) : (x,A y+B x) ∈ (transform T A B).graph := by
  obtain ⟨u,hx,hy⟩ := T.mem_graph_iff.mp hxy
  exact (transform T A B).mem_graph_iff.mpr ⟨u,hx,by
    change A (T u)+B (u:V) = A y+B x
    rw [hy,hx]⟩

theorem transform_output_unique (T : V →ₗ.[ℂ] V) (A B : V →L[ℂ] V)
    (x y z : V) (hxy : (x,y) ∈ T.graph) (hxz : (x,z) ∈ (transform T A B).graph) :
    A y+B x = z := by
  have h₁ := (KFCausalMassFormOperator.graph_domain_iff (transform T A B) x (A y+B x)).mp
    (transform_graph T A B x y hxy)
  have h₂ := (KFCausalMassFormOperator.graph_domain_iff (transform T A B) x z).mp hxz
  exact h₁.2.symm.trans h₂.2

theorem graph_output (T : V →ₗ.[ℂ] V) (A B Z R H : V →L[ℂ] V) (lam : ℝ)
    (hZl : ∀ x, Z (A x) = x) (hZr : ∀ x, A (Z x) = x)
    (hH : H = Z*((lam • R-1)-B*R))
    (hg : ∀ f, (R f,lam • R f-f) ∈ (transform T A B).graph) (f : V) :
    (R f,H f) ∈ T.graph := by
  have he := (graph_iff T A B Z hZl hZr (R f) (lam • R f-f)).mp (hg f)
  simpa only [hH,ContinuousLinearMap.mul_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply] using he

theorem reference_left (T : V →ₗ.[ℂ] V) (A B R : V →L[ℂ] V) (lam : ℝ)
    (hl : ∀ x y, (x,y) ∈ (transform T A B).graph → R (lam • x-y) = x)
    (x y : V) (hxy : (x,y) ∈ T.graph) : R (lam • x-(A y+B x)) = x :=
  hl x (A y+B x) (transform_graph T A B x y hxy)

theorem resolvent_difference (T : V →ₗ.[ℂ] V) (A B C D R Q H : V →L[ℂ] V) (lam : ℝ)
    (hl : ∀ x y, (x,y) ∈ T.graph → R (lam • x-(A y+B x)) = x)
    (hg : ∀ f, (Q f,H f) ∈ T.graph)
    (hr : ∀ f, (Q f,lam • Q f-f) ∈ (transform T C D).graph) :
    R-Q = R*((A-C)*H+(B-D)*Q) := by
  ext f
  have hq := transform_output_unique T C D (Q f) (H f) (lam • Q f-f) (hg f) (hr f)
  have he : lam • Q f-(A (H f)+B (Q f)) =
      f-((A-C) (H f)+(B-D) (Q f)) := by
    have hf : lam • Q f-(C (H f)+D (Q f)) = f := by rw [hq]; abel
    calc
      _ = (lam • Q f-(C (H f)+D (Q f)))-((A-C) (H f)+(B-D) (Q f)) := by
        simp only [ContinuousLinearMap.sub_apply]
        abel
      _ = _ := by rw [hf]
  have hh := hl (Q f) (H f) (hg f)
  rw [he,map_sub] at hh
  change R f-Q f = R ((A-C) (H f)+(B-D) (Q f))
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hh).trans (add_comm _ _))

theorem derivative_factorization (R A B : ℝ → V →L[ℂ] V)
    (H R' A' B' : V →L[ℂ] V) (t : ℝ)
    (hR : HasDerivAt R R' t) (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t)
    (he : ∀ᶠ u in 𝓝 t, R u-R t = R u*((A u-A t)*H+(B u-B t)*R t)) :
    R' = R t*(A'*H+B'*R t) := by
  have hh := hR.mul (((hA.sub_const (A t)).mul_const H).add ((hB.sub_const (B t)).mul_const (R t)))
  have eqd := (hR.sub_const (R t)).unique (hh.congr_of_eventuallyEq he)
  simpa only [Pi.add_apply,sub_self,zero_mul,zero_add,mul_zero] using eqd

theorem factored_derivative (R : ℝ → V →L[ℂ] V) (R' D : V →L[ℂ] V) (t : ℝ)
    (hR : HasDerivAt R R' t) (he : R' = R t*D) : HasDerivAt R (R t*D) t := he ▸ hR

#print axioms transform_graph
#print axioms transform_output_unique
#print axioms graph_output
#print axioms reference_left
#print axioms resolvent_difference
#print axioms derivative_factorization
#print axioms factored_derivative
end
end UnifiedTheory.Audit.KFCausalCommonDomainResolvent
