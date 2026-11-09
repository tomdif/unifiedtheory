/- A densely defined nonnegative self-adjoint partial operator constructed
from the actual OS Laplace resolvent, with its exact domain and inverse laws.
This is a bare-sector operator construction, not a physical Yang--Mills gap. -/
import UnifiedTheory.Clay.YangMills.OSLaplaceResolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSLaplaceHamiltonian
noncomputable section
open ContinuumControl PeriodicLattice4 OSPositiveTimeKernel OSScalarDynamics OSLaplaceResolvent
open UnifiedTheory.Audit.KFCausalResolventHamiltonian

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane} (D : Evolution W plane hp)

/-- Positivity and the norm bound improve the contraction estimate to the
quadratic inequality needed for the inverse-shift operator's nonnegativity. -/
theorem resolvent_firm (x : State (hp := hp)) :
    ‖resolvent D x‖^2 ≤ (inner ℂ x (resolvent D x)).re := by
  have hn := resolvent_positive D (x-resolvent D x)
  have hu : (inner ℂ (resolvent D x) (resolvent D (resolvent D x))).re ≤
      ‖resolvent D x‖^2 := by
    apply (re_inner_le_norm (𝕜 := ℂ) _ _).trans
    nlinarith [resolvent_contraction D (resolvent D x), norm_nonneg (resolvent D x)]
  have he : inner ℂ x (resolvent D (resolvent D x)) =
      inner ℂ (resolvent D x) (resolvent D x) :=
    (resolvent_symmetric D x (resolvent D x)).symm
  simp only [map_sub, inner_sub_left, inner_sub_right, he, Complex.sub_re] at hn
  have hs : (inner ℂ (resolvent D x) (resolvent D x)).re = ‖resolvent D x‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hs] at hn
  linarith

def hamiltonian : State (hp := hp) →ₗ.[ℂ] State (hp := hp) :=
  inverseShift (resolvent D) (resolvent_injective D)

@[simp] theorem domain : (hamiltonian D).domain = (resolvent D).range := rfl

def rangePoint (x : State (hp := hp)) : (hamiltonian D).domain :=
  rangeVector (resolvent D) (resolvent_injective D) x

@[simp] theorem rangePoint_value (x : State (hp := hp)) :
    (rangePoint D x : State (hp := hp)) = resolvent D x := rfl

@[simp] theorem apply_range (x : State (hp := hp)) :
    hamiltonian D (rangePoint D x) = x-resolvent D x :=
  inverseShift_apply_range (resolvent D) (resolvent_injective D) x

theorem resolvent_left (x : (hamiltonian D).domain) :
    resolvent D (hamiltonian D x + (x : State (hp := hp))) = x :=
  inverseShift_resolvent (resolvent D) (resolvent_injective D) x

theorem resolvent_right (x : State (hp := hp)) :
    hamiltonian D (rangePoint D x) + (rangePoint D x : State (hp := hp)) = x := by
  rw [apply_range, rangePoint_value, sub_add_cancel]

theorem dense_domain : Dense ((hamiltonian D).domain : Set (State (hp := hp))) :=
  resolvent_dense D

theorem selfAdjoint : IsSelfAdjoint (hamiltonian D) :=
  inverseShift_selfAdjoint (resolvent D) (resolvent_injective D)
    (resolvent_dense D) (resolvent_symmetric D)

theorem closed : (hamiltonian D).IsClosed :=
  inverseShift_closed (resolvent D) (resolvent_injective D)
    (resolvent_dense D) (resolvent_symmetric D)

theorem nonnegative (x : (hamiltonian D).domain) :
    0 ≤ (inner ℂ (x : State (hp := hp)) (hamiltonian D x)).re := by
  obtain ⟨x,hx⟩ := x
  obtain ⟨y,rfl⟩ := hx
  change 0 ≤ (inner ℂ (resolvent D y) (hamiltonian D (rangePoint D y))).re
  rw [apply_range, inner_sub_right, Complex.sub_re, resolvent_symmetric]
  have hs : (inner ℂ (resolvent D y) (resolvent D y)).re = ‖resolvent D y‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hs]
  exact sub_nonneg.mpr (resolvent_firm D y)

theorem graph_iff (x y : State (hp := hp)) :
    (x,y) ∈ (hamiltonian D).graph ↔ resolvent D (y+x)=x :=
  UnifiedTheory.Audit.KFCausalInverseResolventGraph.inverseShift_graph_iff
    (resolvent D) (resolvent_injective D) x y

end
end UnifiedTheory.Clay.YangMills.OSLaplaceHamiltonian
