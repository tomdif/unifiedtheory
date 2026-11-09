/- Inverting a bounded injective symmetric resolvent on its actual range.
Self-adjointness is proved by identifying the adjoint domain. -/
import UnifiedTheory.Audit.KFCausalFormResolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalResolventHamiltonian
noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def inverseShift (R : H →L[ℂ] H) (hi : Function.Injective R) : H →ₗ.[ℂ] H where
  domain := R.range
  toFun := (LinearEquiv.ofInjective R.toLinearMap hi).symm.toLinearMap - R.range.subtype

def rangeVector (R : H →L[ℂ] H) (hi : Function.Injective R) (x : H) :
    (inverseShift R hi).domain := ⟨R x, ⟨x, rfl⟩⟩

theorem inverseShift_apply_range (R : H →L[ℂ] H) (hi : Function.Injective R) (x : H) :
    inverseShift R hi (rangeVector R hi x) = x - R x := by
  change (LinearEquiv.ofInjective R.toLinearMap hi).symm
    ((LinearEquiv.ofInjective R.toLinearMap hi) x) - R x = _
  rw [LinearEquiv.symm_apply_apply]

theorem inverseShift_resolvent (R : H →L[ℂ] H) (hi : Function.Injective R)
    (x : (inverseShift R hi).domain) : R (inverseShift R hi x + (x : H)) = x := by
  change R ((LinearEquiv.ofInjective R.toLinearMap hi).symm x - (x:H) + (x:H)) = x
  rw [sub_add_cancel]
  exact LinearEquiv.ofInjective_symm_apply R.toLinearMap x

theorem inverseShift_dense (R : H →L[ℂ] H) (hi : Function.Injective R)
    (hd : DenseRange R) : Dense ((inverseShift R hi).domain : Set H) := hd

theorem inverseShift_symmetric (R : H →L[ℂ] H) (hi : Function.Injective R)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) :
    (inverseShift R hi).IsFormalAdjoint (inverseShift R hi) := by
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
  change inner ℂ (inverseShift R hi (rangeVector R hi x)) (R y) =
    inner ℂ (R x) (inverseShift R hi (rangeVector R hi y))
  rw [inverseShift_apply_range, inverseShift_apply_range, inner_sub_left, inner_sub_right,
    hs x y]

variable [CompleteSpace H]

theorem adjoint_resolvent_identity (R : H →L[ℂ] H) (hi : Function.Injective R)
    (hd : DenseRange R) (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y))
    (y : (inverseShift R hi).adjoint.domain) :
    R ((inverseShift R hi).adjoint y + (y : H)) = y := by
  apply ext_inner_right ℂ
  intro u
  have hpair := LinearPMap.adjoint_isFormalAdjoint
    (inverseShift_dense R hi hd) y (rangeVector R hi u)
  change inner ℂ ((inverseShift R hi).adjoint y) (R u) =
    inner ℂ (y : H) (inverseShift R hi (rangeVector R hi u)) at hpair
  rw [inverseShift_apply_range, inner_sub_right] at hpair
  rw [hs, inner_add_left, hpair]
  exact sub_add_cancel _ _

theorem inverseShift_selfAdjoint (R : H →L[ℂ] H) (hi : Function.Injective R)
    (hd : DenseRange R) (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) :
    IsSelfAdjoint (inverseShift R hi) := by
  have hf : inverseShift R hi ≤ (inverseShift R hi).adjoint :=
    (inverseShift_symmetric R hi hs).le_adjoint (inverseShift_dense R hi hd)
  have hb : (inverseShift R hi).adjoint.domain ≤ (inverseShift R hi).domain := by
    intro y hy
    exact ⟨(inverseShift R hi).adjoint ⟨y,hy⟩ + y,
      adjoint_resolvent_identity R hi hd hs ⟨y,hy⟩⟩
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hf (le_antisymm hf.1 hb)).symm

theorem inverseShift_closed (R : H →L[ℂ] H) (hi : Function.Injective R)
    (hd : DenseRange R) (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) :
    (inverseShift R hi).IsClosed := (inverseShift_selfAdjoint R hi hd hs).isClosed

#print axioms inverseShift_apply_range
#print axioms inverseShift_resolvent
#print axioms adjoint_resolvent_identity
#print axioms inverseShift_selfAdjoint
#print axioms inverseShift_closed

end
end UnifiedTheory.Audit.KFCausalResolventHamiltonian
