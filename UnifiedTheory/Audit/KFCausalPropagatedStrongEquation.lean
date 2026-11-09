/- Transfer domain membership through inverse coordinates and embeddings.
A cocycle with an exact initial derivative then has that strong derivative
at every time where the propagated state belongs to the operator domain. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPropagatedStrongEquation
noncomputable section
open Set
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inverse_coordinate_domain (D E : Submodule ℂ V) (S R : V →L[ℂ] V)
    (hS : ∀ x, S x ∈ E ↔ x ∈ D) (hR : ∀ x, S (R x) = x)
    (x : V) (hx : R x ∈ D) : x ∈ E := by
  simpa only [hR] using (hS (R x)).mpr hx

theorem embedding_domain (L : V →ₗ.[ℂ] V) (T : H →ₗ.[ℂ] H) (J : V →L[ℂ] H)
    (hJ : ∀ x y, (x,y) ∈ L.graph → (J x,J y) ∈ T.graph) (x : L.domain) : J x ∈ T.domain :=
  LinearPMap.mem_domain_of_mem_graph (hJ x (L x) (L.mem_graph x))

theorem lifted_domain_of_output_range (L : V →ₗ.[ℂ] V) (T : H →ₗ.[ℂ] H)
    (J : V →L[ℂ] H) (lift : T.domain → V)
    (hgraph : ∀ x y, (x,y) ∈ L.graph ↔ (J x,J y) ∈ T.graph)
    (hlift : ∀ x, J (lift x) = (x:H))
    (x : T.domain) (hout : T x ∈ range J) : lift x ∈ L.domain := by
  obtain ⟨y,hy⟩ := hout
  apply LinearPMap.mem_domain_of_mem_graph (y := y)
  apply (hgraph (lift x) y).mpr
  rw [hlift,hy]
  exact T.mem_graph x

theorem embedded_domain_dense (L : V →ₗ.[ℂ] V) (J : V →L[ℂ] H)
    (hL : Dense (L.domain : Set V)) (hJ : DenseRange J) :
    DenseRange (fun x : L.domain => J x) :=
  hJ.comp hL.denseRange_val J.continuous

theorem at_propagated_domain (U : ℝ → ℝ → H →L[ℂ] H) (T : ℝ → H →ₗ.[ℂ] H) (c : ℂ)
    (hcomp : ∀ s r t, U r t*U s r = U s t)
    (hinit : ∀ t, ∀ x : (T t).domain, HasDerivAt (fun r => U t r x) (c • T t x) t)
    (s t : ℝ) (x : H) (hx : U s t x ∈ (T t).domain) :
    HasDerivAt (fun r => U s r x) (c • T t ⟨U s t x,hx⟩) t := by
  have he : (fun r => U t r (U s t x)) = fun r => U s r x := by
    funext r
    exact congrArg (fun B : H →L[ℂ] H => B x) (hcomp s t r)
  simpa only [he] using hinit t ⟨U s t x,hx⟩

#print axioms inverse_coordinate_domain
#print axioms embedding_domain
#print axioms lifted_domain_of_output_range
#print axioms embedded_domain_dense
#print axioms at_propagated_domain
end
end UnifiedTheory.Audit.KFCausalPropagatedStrongEquation
