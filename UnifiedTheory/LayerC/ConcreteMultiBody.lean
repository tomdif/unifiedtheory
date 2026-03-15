/-
  LayerC/ConcreteMultiBody.lean — Concrete many-body defect instance

  Constructs an explicit ComposableDefectBlock and certifies
  particle-like many-body behavior: conjugation, annihilation,
  charge additivity, neutrality, and screening.

  ALL PROVEN. No sorry. No axioms beyond Lean core.
-/
import UnifiedTheory.LayerB.FarField
import UnifiedTheory.LayerC.ConcreteModel

namespace UnifiedTheory.LayerC

open UnifiedTheory.LayerA
open UnifiedTheory.LayerB

/-! ### Composable defect block -/

def composeDefects (d₁ d₂ : ConcreteDefect) : ConcreteDefect :=
  ⟨d₁.κ + d₂.κ, d₁.δ + d₂.δ⟩

def conjugateDefect (d : ConcreteDefect) : ConcreteDefect :=
  ⟨-d.κ, -d.δ⟩

/-- All-stable predicate (every defect including vacuum is stable). -/
def allStable (_ : ConcreteDefect) : Prop := True

private lemma source_eq (d : ConcreteDefect) :
    proj₁ (concreteToBF d).Kpart = d.κ := by
  simp [proj₁, concreteToBF]

private lemma bias_eq (d : ConcreteDefect) :
    (concreteToNull d).bias = d.κ := by
  simp [concreteToNull]

noncomputable def concreteComposable : ComposableDefectBlock FieldSpace where
  Defect := ConcreteDefect
  Stable := allStable
  toBF := concreteToBF
  toNull := concreteToNull
  sourceMeas := ⟨proj₁⟩
  biasScale := 1
  sourceMatchesBias := fun d _ => by
    change proj₁ (concreteToBF d).Kpart = 1 * (concreteToNull d).bias
    rw [source_eq, bias_eq, one_mul]
  dressingNeutral := fun d _ => by
    change proj₁ (concreteToBF d).Ppart = 0
    simp [proj₁, concreteToBF]
  compose := composeDefects
  compose_stable := fun _ _ _ _ => trivial
  compose_K_additive := fun d₁ d₂ => by
    change proj₁ (concreteToBF (composeDefects d₁ d₂)).Kpart =
      proj₁ (concreteToBF d₁).Kpart + proj₁ (concreteToBF d₂).Kpart
    simp [source_eq, composeDefects]
  compose_bias_additive := fun d₁ d₂ => by
    simp [concreteToNull, composeDefects]
  conjugate := conjugateDefect
  conjugate_stable := fun _ _ => trivial
  conjugate_K_neg := fun d => by
    change proj₁ (concreteToBF (conjugateDefect d)).Kpart =
      -(proj₁ (concreteToBF d).Kpart)
    simp [source_eq, conjugateDefect]
  conjugate_bias_neg := fun d => by
    simp [concreteToNull, conjugateDefect]

/-! ### Charge computation helper -/

private lemma charge_concrete (d : ConcreteDefect) :
    charge concreteComposable d = d.κ := by
  show proj₁ (concreteToBF d).Kpart = d.κ
  exact source_eq d

/-! ### Particle-like defects -/

def electron : ConcreteDefect := ⟨1, 0⟩
def positron : ConcreteDefect := ⟨-1, 0⟩
def proton : ConcreteDefect := ⟨3, 0⟩
def neutron : ConcreteDefect := ⟨0, 1⟩

theorem electron_charge : charge concreteComposable electron = 1 :=
  charge_concrete electron

theorem positron_charge : charge concreteComposable positron = -1 :=
  charge_concrete positron

theorem neutron_charge : charge concreteComposable neutron = 0 :=
  charge_concrete neutron

theorem positron_is_conjugate :
    concreteComposable.conjugate electron = positron := by
  show conjugateDefect electron = positron
  simp [conjugateDefect, electron, positron]

theorem neutron_neutral : IsNeutral concreteComposable neutron :=
  neutron_charge

/-! ### e⁺e⁻ bound state -/

theorem epem_zero_charge :
    charge concreteComposable (concreteComposable.compose electron positron) = 0 := by
  rw [charge_additive, electron_charge, positron_charge, add_neg_cancel]

theorem epem_neutral :
    IsNeutral concreteComposable (concreteComposable.compose electron positron) :=
  epem_zero_charge

/-! ### Three-body system -/

theorem three_body_charge :
    charge concreteComposable
      (concreteComposable.compose
        (concreteComposable.compose proton electron) electron) = 5 := by
  have : charge concreteComposable proton = 3 := charge_concrete proton
  have : charge concreteComposable electron = 1 := charge_concrete electron
  rw [charge_additive, charge_additive]; linarith

/-! ### Screening -/

theorem screening_example :
    FarFieldEquiv concreteComposable electron
      (concreteComposable.compose electron
        (concreteComposable.compose neutron
          (concreteComposable.conjugate neutron))) := by
  show charge concreteComposable electron =
    charge concreteComposable (concreteComposable.compose electron
      (concreteComposable.compose neutron (concreteComposable.conjugate neutron)))
  rw [charge_additive, charge_additive, charge_conjugate]
  simp [charge_concrete, electron, neutron]

/-! ### Summary -/

/-- **Concrete many-body realization.**
    Particle-like defects with conjugation, annihilation,
    charge additivity, neutrality, and screening — all certified. -/
theorem concrete_many_body :
    concreteComposable.conjugate electron = positron
    ∧ IsNeutral concreteComposable (concreteComposable.compose electron positron)
    ∧ charge concreteComposable
        (concreteComposable.compose
          (concreteComposable.compose proton electron) electron) = 5
    ∧ IsNeutral concreteComposable neutron :=
  ⟨positron_is_conjugate, epem_neutral, three_body_charge, neutron_neutral⟩

end UnifiedTheory.LayerC
