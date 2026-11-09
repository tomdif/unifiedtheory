/- The range of a squared resolvent is a core for its closed operator:
both the initial vectors and their Hamiltonian outputs are approximated. -/
import UnifiedTheory.Audit.KFCausalPositiveResolventBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalResolventGraphCore
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalPositiveResolventBounds
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem double_resolvent_graph_closure (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (hl : ∀ x : T.domain, R (T x+a • (x:H)) = x)
    (hd : DenseRange R) (hc : T.IsClosed) :
    closure (range (fun f : H => (R (R f),R f-a • R (R f)))) = (T.graph : Set (H × H)) := by
  apply Subset.antisymm
  · apply closure_minimal _ hc
    rintro _ ⟨f,rfl⟩
    obtain ⟨hx,hxv⟩ := hr (R f)
    exact (T.mem_graph_iff).mpr ⟨⟨R (R f),hx⟩,rfl,hxv⟩
  · intro p hp
    obtain ⟨x,rfl⟩ := (T.mem_graph_iff').mp hp
    let B := fun f : H => (R f,f-a • R f)
    have hB : Continuous B := R.continuous.prodMk (continuous_id.sub (R.continuous.const_smul a))
    have hm := mem_closure_image hB.continuousAt (hd (T x+a • (x:H)))
    have he : B (T x+a • (x:H)) = ((x:H),T x) := by
      dsimp only [B]
      rw [hl x,add_sub_cancel_right]
    rw [he] at hm
    simpa only [← Set.range_comp,Function.comp_def,B] using hm

#print axioms double_resolvent_graph_closure
end
end UnifiedTheory.Audit.KFCausalResolventGraphCore
