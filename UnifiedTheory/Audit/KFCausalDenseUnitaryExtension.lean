/- A complex-linear equivalence preserving the norm of a dense embedding
extends to an actual unitary operator on the physical Hilbert space.
Continuity of trajectories on the dense domain extends by uniform
approximation, using the isometry bound. -/
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDenseUnitaryExtension
noncomputable section
open Filter
open scoped Topology

variable {E H : Type*} [AddCommGroup E] [Module ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def extension (J : E →ₗ[ℂ] H) (hJ : DenseRange J) (f : E ≃ₗ[ℂ] E)
    (hn : ∀ x, ‖J (f x)‖ = ‖J x‖) : H ≃ₗᵢ[ℂ] H :=
  f.extendOfIsometry J J hJ hJ hn

theorem extension_embedding (J : E →ₗ[ℂ] H) (hJ : DenseRange J) (f : E ≃ₗ[ℂ] E)
    (hn : ∀ x, ‖J (f x)‖ = ‖J x‖) (x : E) : extension J hJ f hn (J x) = J (f x) :=
  f.extendOfIsometry_eq J J hJ hJ hn x

theorem extension_unitary (J : E →ₗ[ℂ] H) (hJ : DenseRange J) (f : E ≃ₗ[ℂ] E)
    (hn : ∀ x, ‖J (f x)‖ = ‖J x‖) :
    (extension J hJ f hn : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H) :=
  (Unitary.linearIsometryEquiv.symm (extension J hJ f hn)).property

omit [CompleteSpace H] in
theorem equal_on_dense (J : E →ₗ[ℂ] H) (hJ : DenseRange J) (P Q : H →L[ℂ] H)
    (he : ∀ x, P (J x) = Q (J x)) : P = Q := by
  exact ContinuousLinearMap.ext (congrFun (hJ.equalizer P.continuous Q.continuous (funext he)))

omit [AddCommGroup E] [Module ℂ E] [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem continuous_of_dense_isometries {X : Type*} [TopologicalSpace X]
    (J : E → H) (hJ : DenseRange J) (F : X → H → H)
    (hF : ∀ t, Isometry (F t)) (hc : ∀ v, Continuous (fun t => F t (J v))) (x : H) :
    Continuous (fun t => F t x) := by
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp (hJ x)
  choose w hw using hv
  have hn : Tendsto (fun n => dist x (v n)) atTop (𝓝 0) := by
    simpa only [dist_self] using (tendsto_const_nhds (x := x)).dist hlim
  have hu : TendstoUniformly (fun n t => F t (v n)) (fun t => F t x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro δ hδ
    filter_upwards [hn.eventually (gt_mem_nhds hδ)] with n hn t
    simpa only [(hF t).dist_eq] using hn
  apply hu.continuous
  apply Filter.Frequently.of_forall
  intro n
  rw [← hw n]
  exact hc (w n)

theorem extension_strong_continuous {X : Type*} [TopologicalSpace X]
    (J : E →ₗ[ℂ] H) (hJ : DenseRange J) (f : X → E ≃ₗ[ℂ] E)
    (hn : ∀ t x, ‖J (f t x)‖ = ‖J x‖) (hc : ∀ v, Continuous (fun t => J (f t v))) (x : H) :
    Continuous (fun t => extension J hJ (f t) (hn t) x) := by
  apply continuous_of_dense_isometries J hJ _ (fun t => (extension J hJ (f t) (hn t)).isometry) _ x
  intro v
  simpa only [extension_embedding] using hc v

#print axioms extension
#print axioms extension_embedding
#print axioms extension_unitary
#print axioms equal_on_dense
#print axioms continuous_of_dense_isometries
#print axioms extension_strong_continuous

end
end UnifiedTheory.Audit.KFCausalDenseUnitaryExtension
