/- Continuous changes of output coordinates transport the closure of a
core graph. Forward and backward transports identify the input domains. -/
import UnifiedTheory.Audit.KFCausalSeparatedGraphClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGraphTransport
noncomputable section
open UnifiedTheory.Audit.KFCausalSeparatedGraphClosure

variable {V H K : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem closure_transport (I : V →ₗ[ℂ] H) (O P : V →ₗ[ℂ] K) (T : K →L[ℂ] K)
    (ht : ∀ v, T (O v) = P v) (z : H × K)
    (hz : z ∈ (graphRange I O).topologicalClosure) :
    (z.1,T z.2) ∈ (graphRange I P).topologicalClosure := by
  have hc : IsClosed {w : H × K | (w.1,T w.2) ∈ (graphRange I P).topologicalClosure} :=
    (graphRange I P).isClosed_topologicalClosure.preimage
      (continuous_fst.prodMk (T.continuous.comp continuous_snd))
  apply closure_minimal (t := {w : H × K | (w.1,T w.2) ∈ (graphRange I P).topologicalClosure})
    ?_ hc hz
  rintro _ ⟨v,rfl⟩
  change (I v,T (O v)) ∈ (graphRange I P).topologicalClosure
  rw [ht]
  exact (graphRange I P).le_topologicalClosure ⟨v,rfl⟩

theorem closed_domain_le (I : V →ₗ[ℂ] H) (O P : V →ₗ[ℂ] K) (T : K →L[ℂ] K)
    (ht : ∀ v, T (O v) = P v) : (closedOperator I O).domain ≤ (closedOperator I P).domain := by
  rintro x ⟨z,hz,hx⟩
  exact ⟨(z.1,T z.2),closure_transport I O P T ht z hz,hx⟩

theorem closed_domain_eq (I : V →ₗ[ℂ] H) (O P : V →ₗ[ℂ] K) (T S : K →L[ℂ] K)
    (ht : ∀ v, T (O v) = P v) (hs : ∀ v, S (P v) = O v) :
    (closedOperator I O).domain = (closedOperator I P).domain :=
  le_antisymm (closed_domain_le I O P T ht) (closed_domain_le I P O S hs)

#print axioms closure_transport
#print axioms closed_domain_eq

end
end UnifiedTheory.Audit.KFCausalGraphTransport
