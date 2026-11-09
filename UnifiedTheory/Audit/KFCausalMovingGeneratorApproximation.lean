/- Bounded generator approximations under a differentiable coordinate
change. The connection term cancels the derivative of that change. -/
import UnifiedTheory.Audit.KFCausalHilbertStateEvolution
import UnifiedTheory.Audit.KFCausalMassFormOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMovingGeneratorApproximation
noncomputable section
open Filter
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def transformed (S R C A : V →L[ℂ] V) : V →L[ℂ] V := R*(A*S)+C

theorem transported_action (S R C D A : V →L[ℂ] V)
    (hi : ∀ v, S (R v) = v) (hc : ∀ v, S (C v) = -D v) (w : V) :
    S (transformed S R C A w)+D w = A (S w) := by
  change S (R (A (S w))+C w)+D w = _
  rw [map_add,hi,hc]
  abel

theorem transported_derivative (S R C A D : ℝ → V →L[ℂ] V)
    (hS : ∀ t, HasDerivAt S (D t) t) (hi : ∀ t v, S t (R t v) = v)
    (hc : ∀ t v, S t (C t v) = -D t v) (w : ℝ → V) (t : ℝ)
    (hw : HasDerivAt w (transformed (S t) (R t) (C t) (A t) (w t)) t) :
    HasDerivAt (fun r => S r (w r)) (A t (S t (w t))) t := by
  have hd := KFCausalHilbertStateEvolution.operator_apply_derivative S w (D t)
    (transformed (S t) (R t) (C t) (A t) (w t)) t (hS t) hw
  exact hd.congr_deriv ((add_comm _ _).trans (transported_action _ _ _ _ _ (hi t) (hc t) (w t)))

theorem transformed_limit (S R C : V →L[ℂ] V) (A : ℝ → V →L[ℂ] V) (w v : V)
    (hl : Tendsto (fun b => A b (S w)) atTop (𝓝 v)) :
    Tendsto (fun b => transformed S R C (A b) w) atTop (𝓝 (R v+C w)) :=
  (R.continuous.continuousAt.tendsto.comp hl).add_const (C w)

theorem limit_identification (S R C D : V →L[ℂ] V)
    (hi : ∀ v, S (R v) = v) (hr : ∀ v, R (S v) = v)
    (hc : ∀ v, S (C v) = -D v) (w g v : V) (he : S g+D w = v) :
    R v+C w = g := by
  apply Function.LeftInverse.injective hr
  rw [map_add,hi,hc]
  rw [← sub_eq_add_neg]
  exact (eq_sub_iff_add_eq.mpr he).symm

theorem transformed_graph_limit (T : V →ₗ.[ℂ] V) (S R C D : V →L[ℂ] V)
    (A : ℝ → V →L[ℂ] V) (c : ℂ)
    (hi : ∀ v, S (R v) = v) (hr : ∀ v, R (S v) = v)
    (hc : ∀ v, S (C v) = -D v)
    (hl : ∀ x : T.domain, Tendsto (fun b => A b (x:V)) atTop (𝓝 (c • T x)))
    (w z g : V) (hg : (S w,z) ∈ T.graph) (he : S g+D w = c • z) :
    Tendsto (fun b => transformed S R C (A b) w) atTop (𝓝 g) := by
  obtain ⟨hx,hval⟩ := (KFCausalMassFormOperator.graph_domain_iff T (S w) z).mp hg
  have hp : Tendsto (fun b => A b (S w)) atTop (𝓝 (c • z)) := by
    simpa only [hval] using hl ⟨S w,hx⟩
  have ht := transformed_limit S R C A w (c • z) hp
  have hv := limit_identification S R C D hi hr hc w g (c • z) he
  exact hv ▸ ht

#print axioms transformed_graph_limit
#print axioms transported_action
#print axioms transported_derivative
#print axioms transformed_limit
#print axioms limit_identification
end
end UnifiedTheory.Audit.KFCausalMovingGeneratorApproximation
