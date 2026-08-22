/-
  Audit/KFHopfQuotientInverse.lean

  A noncomputable inverse for the set-level algebraic Hopf quotient.

  `KFHopfSurjectivity` proves that the normalized phase quotient maps
  bijectively to the unit Bloch sphere.  This file packages that theorem as an
  explicit inverse function from unit Bloch coordinates to normalized phase
  classes and proves the two inverse laws.

  The inverse is noncomputable because it is built from the surjectivity
  witness by choice.  The theorem remains set-level/algebraic: no quotient
  topology, local trivialization, principal-bundle structure, Chern class, or
  continuum spin-bundle claim is made here.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfSurjectivity

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitSpinorCoords

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient

/-- The inverse phase class associated to a unit Bloch point. -/
noncomputable def phaseClassOfUnitBloch
    (B : UnitBlochCoords) : UnitPhaseSpinorQuotient :=
  Classical.choose (quotientUnitBloch_surjective B)

/-- The chosen inverse really lands over the given unit Bloch point. -/
theorem quotientUnitBloch_phaseClassOfUnitBloch
    (B : UnitBlochCoords) :
    quotientUnitBloch (phaseClassOfUnitBloch B) = B :=
  Classical.choose_spec (quotientUnitBloch_surjective B)

/-- The inverse returns the original quotient phase class after projecting to
the Bloch sphere. -/
theorem phaseClassOfUnitBloch_quotientUnitBloch
    (q : UnitPhaseSpinorQuotient) :
    phaseClassOfUnitBloch (quotientUnitBloch q) = q := by
  apply quotientUnitBloch_injective
  exact quotientUnitBloch_phaseClassOfUnitBloch (quotientUnitBloch q)

/-- Equality of unit Bloch points is equivalent to equality of their chosen
phase classes. -/
theorem phaseClassOfUnitBloch_eq_iff
    (B C : UnitBlochCoords) :
    phaseClassOfUnitBloch B = phaseClassOfUnitBloch C ↔ B = C := by
  constructor
  · intro h
    calc
      B = quotientUnitBloch (phaseClassOfUnitBloch B) :=
        (quotientUnitBloch_phaseClassOfUnitBloch B).symm
      _ = quotientUnitBloch (phaseClassOfUnitBloch C) :=
        congrArg quotientUnitBloch h
      _ = C :=
        quotientUnitBloch_phaseClassOfUnitBloch C
  · intro h
    exact congrArg phaseClassOfUnitBloch h

/-- The inverse map from Bloch points to phase classes is injective. -/
theorem phaseClassOfUnitBloch_injective :
    Function.Injective phaseClassOfUnitBloch := by
  intro B C h
  exact (phaseClassOfUnitBloch_eq_iff B C).mp h

/-- Bundled inverse-law statement for the algebraic Hopf quotient. -/
theorem unit_hopf_quotient_inverse_laws :
    (∀ B : UnitBlochCoords,
      quotientUnitBloch (phaseClassOfUnitBloch B) = B) ∧
    (∀ q : UnitPhaseSpinorQuotient,
      phaseClassOfUnitBloch (quotientUnitBloch q) = q) := by
  exact
    ⟨quotientUnitBloch_phaseClassOfUnitBloch,
      phaseClassOfUnitBloch_quotientUnitBloch⟩

#print axioms UnitSpinorCoords.phaseClassOfUnitBloch
#print axioms UnitSpinorCoords.quotientUnitBloch_phaseClassOfUnitBloch
#print axioms UnitSpinorCoords.phaseClassOfUnitBloch_quotientUnitBloch
#print axioms UnitSpinorCoords.phaseClassOfUnitBloch_eq_iff
#print axioms UnitSpinorCoords.unit_hopf_quotient_inverse_laws

end UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitSpinorCoords
