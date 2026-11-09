/- Resolvent regularization preserves the actual operator domain and
commutes there with its generator. This is not a domain-preserving flow theorem. -/
import UnifiedTheory.Audit.KFCausalMassFormOperator
import UnifiedTheory.Audit.KFCausalDenseResolventConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPartialResolventGraphRegularization
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem resolvent_commutation (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (b : ℝ)
    (hl : ∀ x : T.domain, R (b • (x:V)-T x) = x) (x : T.domain) :
    R (T x) = b • R (x:V)-(x:V) := by
  have he := hl x
  rw [map_sub,ContinuousLinearMap.map_smul_of_tower] at he
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp he).symm)

theorem scaled_graph (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (b : ℝ)
    (hg : ∀ f, (R f,b • R f-f) ∈ T.graph)
    (hl : ∀ x : T.domain, R (b • (x:V)-T x) = x) (x : T.domain) :
    (b • R (x:V),b • R (T x)) ∈ T.graph := by
  have he := resolvent_commutation T R b hl x
  have hg' := T.graph.smul_mem (b:ℂ) (hg (x:V))
  simpa only [Prod.smul_mk,Complex.coe_smul,← he] using hg'

theorem regularization_graph (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (b : ℝ)
    (hg : ∀ f, (R f,b • R f-f) ∈ T.graph)
    (hl : ∀ x : T.domain, R (b • (x:V)-T x) = x) (x : T.domain) :
    ((b • (b • R-1)) (x:V),(b • (b • R-1)) (T x)) ∈ T.graph := by
  have he := T.graph.sub_mem (scaled_graph T R b hg hl x) (T.mem_graph x)
  have hh := T.graph.smul_mem (b:ℂ) he
  simpa only [Prod.smul_mk,Complex.coe_smul,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply] using hh

theorem regularization_on_domain (T : V →ₗ.[ℂ] V) (R : V →L[ℂ] V) (b : ℝ)
    (hl : ∀ x : T.domain, R (b • (x:V)-T x) = x) (x : T.domain) :
    (b • (b • R-1)) (x:V) = b • R (T x) := by
  change b • (b • R (x:V)-(x:V)) = _
  exact congrArg (fun z : V => b • z) (resolvent_commutation T R b hl x).symm

#print axioms resolvent_commutation
#print axioms scaled_graph
#print axioms regularization_graph
#print axioms regularization_on_domain
end
end UnifiedTheory.Audit.KFCausalPartialResolventGraphRegularization
