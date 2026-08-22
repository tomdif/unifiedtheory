/-
  Audit/KFRecoveredCSpecHopfBornPhaseClassReconstruction.lean

  Reconstruct the recovered Hopf phase class from local Pauli Born data.

  `KFRecoveredCSpecHopfBornTomography` reconstructs the local quotient Bloch
  observable from Pauli Born expectations.  `KFHopfQuotientInverse` packages the
  algebraic Hopf quotient bijection as an inverse from unit Bloch points to
  normalized phase classes.  This file composes them:

  * the phase class reconstructed from Pauli Born expectations is exactly the
    recovered phase class;
  * this reconstructed phase class is invariant under local stagewise `U(1)`
    gauge rotation.

  This is still finite local projective-qubit tomography, not detector
  dynamics, continuum QFT, spin/statistics, Standard Model recovery, quotient
  topology, or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfQuotientInverse
import UnifiedTheory.Audit.KFRecoveredCSpecHopfBornPhaseClassSeparation

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

variable {site : Type*}

/-- The recovered phase class reconstructed from the three local Pauli Born
expectations. -/
noncomputable def reconstructedPhaseClassAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    UnitSpinorCoords.UnitPhaseSpinorQuotient :=
  UnitSpinorCoords.phaseClassOfUnitBloch (I.reconstructedBlochAt n x)

/-- Pauli Born tomography reconstructs the exact recovered Hopf phase class. -/
theorem reconstructedPhaseClassAt_eq_phaseClassAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.reconstructedPhaseClassAt n x = I.phaseClassAt n x := by
  unfold reconstructedPhaseClassAt
  rw [reconstructedBlochAt_eq_quotientBlochAt]
  exact UnitSpinorCoords.phaseClassOfUnitBloch_quotientUnitBloch (I.phaseClassAt n x)

/-- Local stagewise `U(1)` gauge rotation leaves the reconstructed phase class
unchanged. -/
theorem phaseRotate_reconstructedPhaseClassAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).reconstructedPhaseClassAt n x =
      I.reconstructedPhaseClassAt n x := by
  rw [
    reconstructedPhaseClassAt_eq_phaseClassAt,
    reconstructedPhaseClassAt_eq_phaseClassAt,
    phaseRotate_phaseClassAt_eq]

/-- Bundled local projective tomography theorem: Pauli Born data reconstructs
the recovered normalized phase class, and this reconstruction is locally
`U(1)` gauge-invariant. -/
theorem recoveredStage_local_pauli_born_projective_tomography
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.reconstructedPhaseClassAt n x = I.phaseClassAt n x ∧
    ∀ P : ℕ → UnitPhaseField site,
      (I.phaseRotate P).reconstructedPhaseClassAt n x =
        I.reconstructedPhaseClassAt n x := by
  exact
    ⟨reconstructedPhaseClassAt_eq_phaseClassAt I n x,
      fun P => phaseRotate_reconstructedPhaseClassAt_eq I P n x⟩

#print axioms RecoveredStageHopfFiberInterface.reconstructedPhaseClassAt
#print axioms RecoveredStageHopfFiberInterface.reconstructedPhaseClassAt_eq_phaseClassAt
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_reconstructedPhaseClassAt_eq
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_local_pauli_born_projective_tomography

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
