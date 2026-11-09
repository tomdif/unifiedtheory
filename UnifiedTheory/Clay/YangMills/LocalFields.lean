/- Initial semantic interfaces for continuum local fields. These are
requirements on a candidate, not a construction or a complete Wightman axiom set.
See the requirements ledger for Poincare, spectrum, gauge and UV obligations. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.LocalFields
noncomputable section

abbrev Spacetime := EuclideanSpace ℝ (Fin 4)
abbrev TestFunction := SchwartzMap Spacetime ℂ

def minkowskiSquare (x : Spacetime) : ℝ := x 0 ^ 2 - ∑ i : Fin 3, x i.succ ^ 2

theorem minkowskiSquare_neg (x : Spacetime) : minkowskiSquare (-x) = minkowskiSquare x := by
  simp [minkowskiSquare]

theorem minkowskiSquare_sub_comm (x y : Spacetime) :
    minkowskiSquare (x - y) = minkowskiSquare (y - x) := by
  simpa only [neg_sub] using (minkowskiSquare_neg (x - y)).symm

def SpacelikeSeparated (f g : TestFunction) : Prop :=
  ∀ x ∈ tsupport f, ∀ y ∈ tsupport g, minkowskiSquare (x - y) < 0

theorem spacelikeSeparated_symm (f g : TestFunction) (h : SpacelikeSeparated f g) :
    SpacelikeSeparated g f := by
  intro x hx y hy
  rw [minkowskiSquare_sub_comm]
  exact h y hy x hx

variable (Label H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure FieldSystem where
  domain : Submodule ℂ H
  domain_dense : Dense (domain : Set H)
  vacuum : domain
  vacuum_norm : ‖(vacuum : H)‖ = 1
  field : Label → TestFunction →ₗ[ℂ] domain →ₗ[ℂ] domain

variable {Label H}

def WeakTempered (S : FieldSystem Label H) : Prop :=
  ∀ a (u v : S.domain), Continuous (fun f : TestFunction => inner ℂ (u : H) (S.field a f v : H))

def Locality (S : FieldSystem Label H) : Prop :=
  ∀ a b (f g : TestFunction), SpacelikeSeparated f g →
    ∀ u : S.domain, S.field a f (S.field b g u) = S.field b g (S.field a f u)

def wordState (S : FieldSystem Label H) : List (Label × TestFunction) → S.domain
  | [] => S.vacuum
  | (a, f) :: w => S.field a f (wordState S w)

def Cyclic (S : FieldSystem Label H) : Prop :=
  Dense (Submodule.span ℂ (Set.range (fun w => (wordState S w : H))) : Set H)

def Nontrivial (S : FieldSystem Label H) : Prop :=
  ∃ w, (wordState S w : H) ∉ Submodule.span ℂ ({(S.vacuum : H)} : Set H)

def vacuumCorrelation (S : FieldSystem Label H) (w : List (Label × TestFunction)) : ℂ :=
  inner ℂ (S.vacuum : H) (wordState S w : H)

theorem zero_fields_not_nontrivial (S : FieldSystem Label H)
    (hz : ∀ a f, S.field a f = 0) : ¬ Nontrivial S := by
  rintro ⟨w, hw⟩
  cases w with
  | nil => exact hw (Submodule.mem_span_singleton_self (S.vacuum : H))
  | cons af w =>
    apply hw
    simp only [wordState, hz, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    exact (Submodule.span ℂ ({(S.vacuum : H)} : Set H)).zero_mem

structure LocalFieldRequirements (S : FieldSystem Label H) : Prop where
  weak_tempered : WeakTempered S
  locality : Locality S
  cyclicity : Cyclic S
  nontriviality : Nontrivial S

end
end UnifiedTheory.Clay.YangMills.LocalFields
