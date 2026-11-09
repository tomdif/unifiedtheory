/- A self-adjoint operator constructed from a coercive form on a densely
embedded Hilbert form space. The resolvent and full operator domain are
constructed explicitly; no representing operator is assumed. -/
import UnifiedTheory.Audit.KFCausalCoerciveInverse
import UnifiedTheory.Audit.KFCausalFormResolvent

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalCoerciveFormHamiltonian
noncomputable section
open KFCausalCoerciveInverse
variable {V X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable (J : V →L[ℂ] X) (hi : Function.Injective J) (hd : DenseRange J)
  (A : V →L[ℂ] V) (ha : IsUnit A) (hs : A.toLinearMap.IsSymmetric)

include ha hs in
theorem inverse_symmetric (u v : V) :
    inner ℂ (Ring.inverse A u) v = inner ℂ u (Ring.inverse A v) := by
  have he := hs (Ring.inverse A u) (Ring.inverse A v)
  change inner ℂ (A (Ring.inverse A u)) (Ring.inverse A v) =
    inner ℂ (Ring.inverse A u) (A (Ring.inverse A v)) at he
  rw [inverse_apply_right A ha, inverse_apply_right A ha] at he
  exact he.symm

include ha in
theorem inverse_injective : Function.Injective (Ring.inverse A : V →L[ℂ] V) :=
  (show Function.LeftInverse A (Ring.inverse A : V →L[ℂ] V)
    from inverse_apply_right A ha).injective

def resolvent : X →L[ℂ] X := J.comp ((Ring.inverse A).comp J.adjoint)

include ha hs in
theorem resolvent_symmetric (x y : X) :
    inner ℂ (resolvent J A x) y = inner ℂ x (resolvent J A y) := by
  change inner ℂ (J (Ring.inverse A (J.adjoint x))) y =
    inner ℂ x (J (Ring.inverse A (J.adjoint y)))
  rw [← J.adjoint_inner_right, inverse_symmetric A ha hs, J.adjoint_inner_left]

include hi hd ha in
theorem resolvent_injective : Function.Injective (resolvent J A) :=
  hi.comp ((inverse_injective A ha).comp (KFCausalFormResolvent.adjoint_injective J hd))

include hi hd ha hs in
theorem resolvent_dense : DenseRange (resolvent J A) := by
  have hh : (resolvent J A).toLinearMap.IsSymmetric := resolvent_symmetric J A ha hs
  change Dense ((resolvent J A).range : Set X)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  rw [hh.orthogonal_range, LinearMap.ker_eq_bot.mpr (resolvent_injective J hi hd A ha)]

def hamiltonian (a : ℝ) : X →ₗ.[ℂ] X where
  domain := (resolvent J A).range
  toFun := (LinearEquiv.ofInjective (resolvent J A).toLinearMap
    (resolvent_injective J hi hd A ha)).symm.toLinearMap -
    (a : ℂ) • (resolvent J A).range.subtype

def rangeVector (a : ℝ) (x : X) : (hamiltonian J hi hd A ha a).domain :=
  ⟨resolvent J A x, ⟨x, rfl⟩⟩

theorem hamiltonian_apply_range (a : ℝ) (x : X) :
    hamiltonian J hi hd A ha a (rangeVector J hi hd A ha a x) =
      x - (a : ℂ) • resolvent J A x := by
  change (LinearEquiv.ofInjective (resolvent J A).toLinearMap
    (resolvent_injective J hi hd A ha)).symm
      ((LinearEquiv.ofInjective (resolvent J A).toLinearMap
        (resolvent_injective J hi hd A ha)) x) - (a : ℂ) • resolvent J A x = _
  rw [LinearEquiv.symm_apply_apply]

theorem hamiltonian_resolvent (a : ℝ) (x : (hamiltonian J hi hd A ha a).domain) :
    resolvent J A (hamiltonian J hi hd A ha a x + (a : ℂ) • (x : X)) = x := by
  change resolvent J A ((LinearEquiv.ofInjective (resolvent J A).toLinearMap
    (resolvent_injective J hi hd A ha)).symm x - (a : ℂ) • (x : X) +
      (a : ℂ) • (x : X)) = x
  rw [sub_add_cancel]
  exact LinearEquiv.ofInjective_symm_apply (resolvent J A).toLinearMap x

include hs in
theorem hamiltonian_symmetric (a : ℝ) :
    (hamiltonian J hi hd A ha a).IsFormalAdjoint (hamiltonian J hi hd A ha a) := by
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
  change inner ℂ (hamiltonian J hi hd A ha a (rangeVector J hi hd A ha a x))
      (resolvent J A y) = inner ℂ (resolvent J A x)
      (hamiltonian J hi hd A ha a (rangeVector J hi hd A ha a y))
  rw [hamiltonian_apply_range, hamiltonian_apply_range, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, resolvent_symmetric J A ha hs]
  rw [resolvent_symmetric J A ha hs x y]

include hs in
theorem hamiltonian_selfAdjoint (a : ℝ) : IsSelfAdjoint (hamiltonian J hi hd A ha a) := by
  let T := hamiltonian J hi hd A ha a
  have hdT : Dense (T.domain : Set X) := resolvent_dense J hi hd A ha hs
  have hf : T ≤ T.adjoint := (hamiltonian_symmetric J hi hd A ha hs a).le_adjoint hdT
  have he (y : T.adjoint.domain) :
      resolvent J A (T.adjoint y + (a : ℂ) • (y : X)) = y := by
    apply ext_inner_right ℂ
    intro u
    have hp := LinearPMap.adjoint_isFormalAdjoint hdT y (rangeVector J hi hd A ha a u)
    change inner ℂ (T.adjoint y) (resolvent J A u) =
      inner ℂ (y : X) (hamiltonian J hi hd A ha a (rangeVector J hi hd A ha a u)) at hp
    rw [hamiltonian_apply_range, inner_sub_right, inner_smul_right] at hp
    rw [resolvent_symmetric J A ha hs, inner_add_left, inner_smul_left,
      Complex.conj_ofReal, hp]
    ring
  have hb : T.adjoint.domain ≤ T.domain := by
    intro y hy
    exact ⟨T.adjoint ⟨y,hy⟩ + (a : ℂ) • y, he ⟨y,hy⟩⟩
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hf (le_antisymm hf.1 hb)).symm

theorem variational_graph (a : ℝ) (u : V) (y : X) :
    (J u, y) ∈ (hamiltonian J hi hd A ha a).graph ↔
      ∀ v : V, inner ℂ (A u) v - (a : ℂ)*inner ℂ (J u) (J v) = inner ℂ y (J v) := by
  constructor
  · intro hg
    obtain ⟨x, hx, hy⟩ := (hamiltonian J hi hd A ha a).mem_graph_iff.mp hg
    have hr := hamiltonian_resolvent J hi hd A ha a x
    rw [hy, hx] at hr
    have hu : Ring.inverse A (J.adjoint (y + (a : ℂ) • J u)) = u := hi hr
    have hA := congrArg A hu
    rw [inverse_apply_right A ha] at hA
    intro v
    rw [← hA, J.adjoint_inner_left, inner_add_left, inner_smul_left, Complex.conj_ofReal]
    ring
  · intro hv
    have hA : A u = J.adjoint (y + (a : ℂ) • J u) := by
      apply ext_inner_right ℂ
      intro v
      rw [J.adjoint_inner_left, inner_add_left, inner_smul_left, Complex.conj_ofReal]
      linear_combination hv v
    have hr : resolvent J A (y + (a : ℂ) • J u) = J u := by
      change J (Ring.inverse A (J.adjoint (y + (a : ℂ) • J u))) = J u
      rw [← hA, inverse_apply_left A ha]
    refine (hamiltonian J hi hd A ha a).mem_graph_iff.mpr
      ⟨rangeVector J hi hd A ha a (y + (a : ℂ) • J u), hr, ?_⟩
    rw [hamiltonian_apply_range, hr]
    abel

end
end UnifiedTheory.Audit.KFCausalCoerciveFormHamiltonian
