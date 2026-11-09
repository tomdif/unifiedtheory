/- Closed graph constructions for bounded lifts and closed operator actions. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClosedGraphLift
noncomputable section
open Filter Topology
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem intertwining_continuous (J : V →L[ℂ] H) (hJ : Function.Injective J)
    (U : H →L[ℂ] H) (f : V →ₗ[ℂ] V) (he : ∀ x, J (f x) = U (J x)) :
    Continuous f := by
  apply f.continuous_of_seq_closed_graph
  intro u x y hu hf
  apply hJ
  have hy := (J.continuous.tendsto y).comp hf
  have hx := ((U.continuous.comp J.continuous).tendsto x).comp hu
  have heq : (fun n => J (f (u n))) = fun n => U (J (u n)) := funext (fun n => he (u n))
  exact (tendsto_nhds_unique (by simpa only [Function.comp_def,heq] using hy) hx).trans (he x).symm

theorem exists_bounded_lift (J : V →L[ℂ] H) (hJ : Function.Injective J)
    (U : H →L[ℂ] H) (f : V →ₗ[ℂ] V) (he : ∀ x, J (f x) = U (J x)) :
    ∃ F : V →L[ℂ] V, ∀ x, F x = f x :=
  ⟨⟨f,intertwining_continuous J hJ U f he⟩,fun _ => rfl⟩

theorem closed_action (T : V →ₗ.[ℂ] V) (hT : T.IsClosed) (P : V →L[ℂ] V)
    (hP : ∀ x, P x ∈ T.domain) :
    ∃ B : V →L[ℂ] V, ∀ x, (P x,B x) ∈ T.graph := by
  let f : V →ₗ[ℂ] V := T.toFun.comp (P.toLinearMap.codRestrict T.domain hP)
  have hg (x : V) : (P x,f x) ∈ T.graph := T.mem_graph ⟨P x,hP x⟩
  have hc : Continuous f := by
    apply f.continuous_of_seq_closed_graph
    intro u x y hu hf
    have hp := (P.continuous.tendsto x).comp hu
    have hm : (P x,y) ∈ T.graph := hT.mem_of_tendsto (hp.prodMk_nhds hf)
      (Eventually.of_forall (fun n => hg (u n)))
    exact T.mem_graph_snd_inj' hm (hg x) rfl
  exact ⟨⟨f,hc⟩,hg⟩

#print axioms intertwining_continuous
#print axioms exists_bounded_lift
#print axioms closed_action
end
end UnifiedTheory.Audit.KFCausalClosedGraphLift
