/- Positive self-adjoint representation of a densely and injectively
embedded Hilbert form space, including the variational domain criterion. -/
import UnifiedTheory.Audit.KFCausalResolventHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFormHamiltonian
noncomputable section
open UnifiedTheory.Audit.KFCausalFormResolvent
open UnifiedTheory.Audit.KFCausalResolventHamiltonian

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hamiltonian (J : E →L[ℂ] H) (hi : Function.Injective J) (hd : DenseRange J) : H →ₗ.[ℂ] H :=
  inverseShift (resolvent J) (resolvent_injective J hi hd)

theorem hamiltonian_selfAdjoint (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) : IsSelfAdjoint (hamiltonian J hi hd) :=
  inverseShift_selfAdjoint _ _ (resolvent_dense J hi hd) (resolvent_symmetric J)

theorem hamiltonian_positive (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) (hc : ∀ u, ‖J u‖ ≤ ‖u‖)
    (x : (hamiltonian J hi hd).domain) :
    0 ≤ (inner ℂ (hamiltonian J hi hd x) (x : H)).re := by
  obtain ⟨_, u, rfl⟩ := x
  change 0 ≤ (inner ℂ
    (inverseShift (resolvent J) (resolvent_injective J hi hd)
      (rangeVector (resolvent J) (resolvent_injective J hi hd) u)) (resolvent J u)).re
  have hn : inner ℂ (resolvent J u) (resolvent J u) = ((‖resolvent J u‖^2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (resolvent J u))
  rw [inverseShift_apply_range, inner_sub_left, Complex.sub_re, resolvent_inner,
    Complex.ofReal_re, hn, Complex.ofReal_re]
  change 0 ≤ ‖J.adjoint u‖^2 - ‖J (J.adjoint u)‖^2
  nlinarith [hc (J.adjoint u), norm_nonneg (J (J.adjoint u))]

def formLift (J : E →L[ℂ] H) (hi : Function.Injective J) (hd : DenseRange J)
    (x : (hamiltonian J hi hd).domain) : E :=
  J.adjoint (hamiltonian J hi hd x + (x:H))

theorem embedding_formLift (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) (x : (hamiltonian J hi hd).domain) : J (formLift J hi hd x) = x :=
  inverseShift_resolvent (resolvent J) (resolvent_injective J hi hd) x

theorem hamiltonian_form_pairing (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) (x : (hamiltonian J hi hd).domain) (v : E) :
    inner ℂ (formLift J hi hd x) v - inner ℂ (x:H) (J v) =
      inner ℂ (hamiltonian J hi hd x) (J v) := by
  rw [formLift, J.adjoint_inner_left, inner_add_left, add_sub_cancel_right]

theorem formLift_range_vector (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) (x : H) :
    formLift J hi hd (rangeVector (resolvent J) (resolvent_injective J hi hd) x) =
      J.adjoint x := by
  change J.adjoint (inverseShift (resolvent J) (resolvent_injective J hi hd)
    (rangeVector (resolvent J) (resolvent_injective J hi hd) x) + resolvent J x) = _
  rw [inverseShift_apply_range, sub_add_cancel]

theorem operator_domain_form_dense (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) : DenseRange (formLift J hi hd) := by
  have ha : DenseRange J.adjoint := by
    change Dense (J.adjoint.range : Set E)
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    rw [ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.adjoint_adjoint]
    exact LinearMap.ker_eq_bot.mpr hi
  apply ha.mono
  rintro _ ⟨x,rfl⟩
  exact ⟨rangeVector (resolvent J) (resolvent_injective J hi hd) x,
    formLift_range_vector J hi hd x⟩

theorem variational_lift (J : E →L[ℂ] H) (u : E) (y : H)
    (hq : ∀ v, inner ℂ u v - inner ℂ (J u) (J v) = inner ℂ y (J v)) :
    u = J.adjoint (y + J u) := by
  apply ext_inner_right ℂ
  intro v
  rw [J.adjoint_inner_left, inner_add_left, ← hq v]
  exact (sub_add_cancel _ _).symm

theorem variational_mem_domain (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) (u : E) (y : H)
    (hq : ∀ v, inner ℂ u v - inner ℂ (J u) (J v) = inner ℂ y (J v)) :
    J u ∈ (hamiltonian J hi hd).domain := by
  refine ⟨y + J u, ?_⟩
  change J (J.adjoint (y + J u)) = J u
  rw [← variational_lift J u y hq]

theorem variational_value (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) (u : E) (y : H)
    (hq : ∀ v, inner ℂ u v - inner ℂ (J u) (J v) = inner ℂ y (J v)) :
    hamiltonian J hi hd ⟨J u, variational_mem_domain J hi hd u y hq⟩ = y := by
  have h := inverseShift_resolvent (resolvent J) (resolvent_injective J hi hd)
    (⟨J u, variational_mem_domain J hi hd u y hq⟩ : (hamiltonian J hi hd).domain)
  have hr : resolvent J (y + J u) = J u := by
    change J (J.adjoint (y + J u)) = J u
    rw [← variational_lift J u y hq]
  have he := resolvent_injective J hi hd (h.trans hr.symm)
  exact add_right_cancel he

#print axioms hamiltonian_selfAdjoint
#print axioms hamiltonian_positive
#print axioms embedding_formLift
#print axioms hamiltonian_form_pairing
#print axioms operator_domain_form_dense
#print axioms variational_mem_domain
#print axioms variational_value

end
end UnifiedTheory.Audit.KFCausalFormHamiltonian
