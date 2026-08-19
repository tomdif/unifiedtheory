/-
  Audit/KFCausalCSpecDiffeomorphismInvariantObservables.lean

  Generic quotient construction for physical, label/diffeomorphism-invariant
  observables.

  The mathematical point is simple but important: an observable is physical when
  it is constant on representatives related by the chosen physical equivalence
  relation.  Such observables descend to the quotient of states by that
  relation, so they do not depend on labels, coordinates, or gauge choices.

  Zero sorry.  Zero custom axioms.
-/

import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecDiffeomorphismInvariantObservables

open scoped BigOperators

/-- An observable is invariant when it is constant on physical equivalence
classes.  The setoid can represent relabeling, diffeomorphism, gauge
equivalence, or any other physical-identification relation. -/
def RelInvariant {State Value : Type*} [Setoid State]
    (O : State → Value) : Prop :=
  ∀ ⦃x y : State⦄, x ≈ y → O x = O y

/-- An invariant observable descends to the physical quotient. -/
def quotientObservable {State Value : Type*} [Setoid State]
    (O : State → Value) (hO : RelInvariant O) :
    Quotient (inferInstance : Setoid State) → Value :=
  Quotient.lift O (by
    intro x y hxy
    exact hO hxy)

/-- Evaluating the descended observable on a representative recovers the
original representative-level value. -/
theorem quotientObservable_mk {State Value : Type*} [Setoid State]
    (O : State → Value) (hO : RelInvariant O) (x : State) :
    quotientObservable O hO (Quotient.mk _ x) = O x := rfl

/-- Pairing invariant observables gives another invariant observable. -/
theorem pair_invariant {State Value₁ Value₂ : Type*} [Setoid State]
    (O₁ : State → Value₁) (O₂ : State → Value₂)
    (h₁ : RelInvariant O₁) (h₂ : RelInvariant O₂) :
    RelInvariant (fun x => (O₁ x, O₂ x)) := by
  intro x y hxy
  simp [h₁ hxy, h₂ hxy]

/-- Finite signatures of invariant observables are invariant componentwise. -/
def finiteSignature {Index State Value : Type*}
    (O : Index → State → Value) : State → Index → Value :=
  fun x i => O i x

theorem finiteSignature_invariant {Index State Value : Type*} [Setoid State]
    (O : Index → State → Value)
    (hO : ∀ i, RelInvariant (O i)) :
    RelInvariant (finiteSignature O) := by
  intro x y hxy
  funext i
  exact hO i hxy

/-- Real-valued invariant observables are closed under addition. -/
theorem add_invariant {State : Type*} [Setoid State]
    (O₁ O₂ : State → ℝ)
    (h₁ : RelInvariant O₁) (h₂ : RelInvariant O₂) :
    RelInvariant (fun x => O₁ x + O₂ x) := by
  intro x y hxy
  simp [h₁ hxy, h₂ hxy]

/-- Real-valued invariant observables are closed under multiplication. -/
theorem mul_invariant {State : Type*} [Setoid State]
    (O₁ O₂ : State → ℝ)
    (h₁ : RelInvariant O₁) (h₂ : RelInvariant O₂) :
    RelInvariant (fun x => O₁ x * O₂ x) := by
  intro x y hxy
  simp [h₁ hxy, h₂ hxy]

/-- Real-valued invariant observables are closed under scalar rescaling. -/
theorem smul_invariant {State : Type*} [Setoid State]
    (a : ℝ) (O : State → ℝ) (hO : RelInvariant O) :
    RelInvariant (fun x => a * O x) := by
  intro x y hxy
  simp [hO hxy]

/-- A family of physical observables indexed by `Index`, all invariant under
the physical equivalence relation on `State`. -/
structure InvariantObservableFamily (State Index : Type*) [Setoid State] where
  value : Index → State → ℝ
  invariant : ∀ i, RelInvariant (value i)

namespace InvariantObservableFamily

/-- The descended family of observables on the physical quotient. -/
def quotientFamily {State Index : Type*} [Setoid State]
    (F : InvariantObservableFamily State Index) :
    Index → Quotient (inferInstance : Setoid State) → ℝ :=
  fun i => quotientObservable (F.value i) (F.invariant i)

/-- Bridge proposition: the invariant observable family has been constructed
on the physical quotient. -/
def DiffeomorphismInvariantObservablesConstructed
    {State Index : Type*} [Setoid State]
    (F : InvariantObservableFamily State Index) : Prop :=
  ∃ Q : Index → Quotient (inferInstance : Setoid State) → ℝ,
    ∀ i x, Q i (Quotient.mk _ x) = F.value i x

/-- Any representative-level invariant family constructs physical quotient
observables. -/
theorem constructs_diffeomorphismInvariantObservables
    {State Index : Type*} [Setoid State]
    (F : InvariantObservableFamily State Index) :
    F.DiffeomorphismInvariantObservablesConstructed := by
  refine ⟨F.quotientFamily, ?_⟩
  intro i x
  rfl

/-- Componentwise signatures of an invariant family are themselves invariant,
so the whole finite diagnostic vector is a physical observable. -/
theorem finiteSignature_constructs
    {State Index : Type*} [Setoid State]
    (F : InvariantObservableFamily State Index) :
    RelInvariant (finiteSignature F.value) :=
  finiteSignature_invariant F.value F.invariant

#print axioms quotientObservable_mk
#print axioms pair_invariant
#print axioms finiteSignature_invariant
#print axioms add_invariant
#print axioms mul_invariant
#print axioms smul_invariant
#print axioms InvariantObservableFamily.constructs_diffeomorphismInvariantObservables
#print axioms InvariantObservableFamily.finiteSignature_constructs

end InvariantObservableFamily

end UnifiedTheory.Audit.KFCausalCSpecDiffeomorphismInvariantObservables
