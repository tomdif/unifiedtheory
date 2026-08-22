/-
  Audit/KFRecoveredCSpecHopfFiber.lean

  Local Hopf quantum fibers over recovered-stage sites.

  `KFHopfSpinorBlochBridge` proves the algebraic Hopf map for one two-component
  spinor.  This file lifts that result to a per-site, per-stage interface:
  a recovered finite site can carry a normalized local spinor, its downstairs
  Bloch observable has unit norm, and local common `U(1)` phase choices are
  invisible to the Bloch coordinates.

  This is still not a full QFT/Standard Model limit.  It is the finite local
  quantum-fiber attachment that Gate 5 needs before continuum dynamics,
  propagators, spin/statistics, gauge-field action, and parameter recovery can
  be stated without hiding the fiber architecture.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfSpinorBlochBridge

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

open UnifiedTheory.Audit.KFHopfSpinorBlochBridge

/-- A normalized two-component Hopf spinor assigned to every site.  The site
type is deliberately abstract: in Gate 5 applications it is the finite recovered
CSpec cell type at a stage, but the Hopf/Bloch algebra itself only needs a site
index. -/
structure LocalHopfSpinorField (site : Type*) where
  a : site → Real
  b : site → Real
  c : site → Real
  d : site → Real
  normalized :
    ∀ x,
      spinorNormSq (a x) (b x) (c x) (d x) = 1

/-- A sitewise unit complex phase `p + iq`. -/
structure UnitPhaseField (site : Type*) where
  p : site → Real
  q : site → Real
  unit : ∀ x, p x ^ 2 + q x ^ 2 = 1

namespace LocalHopfSpinorField

variable {site : Type*}

/-- The repo qubit spinor at one site. -/
noncomputable def spinor (F : LocalHopfSpinorField site) (x : site) :
    Fin 2 → Complex :=
  spinorOfCoords (F.a x) (F.b x) (F.c x) (F.d x)

/-- First local Bloch observable. -/
def blochX (F : LocalHopfSpinorField site) (x : site) : Real :=
  hopfX (F.a x) (F.b x) (F.c x) (F.d x)

/-- Second local Bloch observable. -/
def blochY (F : LocalHopfSpinorField site) (x : site) : Real :=
  hopfY (F.a x) (F.b x) (F.c x) (F.d x)

/-- Third local Bloch observable. -/
def blochZ (F : LocalHopfSpinorField site) (x : site) : Real :=
  hopfZ (F.a x) (F.b x) (F.c x) (F.d x)

/-- Squared norm of the local Bloch observable. -/
def observableNormSq (F : LocalHopfSpinorField site) (x : site) : Real :=
  blochNormSq (F.a x) (F.b x) (F.c x) (F.d x)

/-- Local Born/Bloch normalization: a normalized Hopf spinor gives a unit
Bloch observable at every site. -/
theorem observableNormSq_eq_one
    (F : LocalHopfSpinorField site) (x : site) :
    F.observableNormSq x = 1 := by
  exact hopf_unit_spinor_unit_bloch
    (F.a x) (F.b x) (F.c x) (F.d x) (F.normalized x)

/-- The local Bloch observables agree with the repo's `WignerHardQubit`
Bloch vector at every site. -/
theorem repo_blochVector_eq_hopf_at
    (F : LocalHopfSpinorField site) (x : site) :
    UnifiedTheory.LayerB.WignerHardQubit.blochVector (F.spinor x) 0 =
        F.blochX x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector (F.spinor x) 1 =
        F.blochY x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector (F.spinor x) 2 =
        F.blochZ x := by
  simpa [spinor, blochX, blochY, blochZ] using
    repo_blochVector_eq_hopf (F.a x) (F.b x) (F.c x) (F.d x)

/-- Rotate every local spinor by the same sitewise unit phase on both complex
components. -/
def phaseRotate
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) :
    LocalHopfSpinorField site where
  a x := phaseRe (P.p x) (P.q x) (F.a x) (F.b x)
  b x := phaseIm (P.p x) (P.q x) (F.a x) (F.b x)
  c x := phaseRe (P.p x) (P.q x) (F.c x) (F.d x)
  d x := phaseIm (P.p x) (P.q x) (F.c x) (F.d x)
  normalized x := by
    rw [phase_preserves_spinorNormSq
      (P.p x) (P.q x) (F.a x) (F.b x) (F.c x) (F.d x) (P.unit x),
      F.normalized x]

/-- A local phase rotation leaves all Hopf/Bloch coordinates unchanged. -/
theorem phaseRotate_hopfPhaseInvariant
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) (x : site) :
    hopfPhaseInvariant
      (P.p x) (P.q x) (F.a x) (F.b x) (F.c x) (F.d x) := by
  exact hopf_phase_invariant
    (P.p x) (P.q x) (F.a x) (F.b x) (F.c x) (F.d x) (P.unit x)

theorem phaseRotate_blochX_eq
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) (x : site) :
    (F.phaseRotate P).blochX x = F.blochX x := by
  simpa [phaseRotate, blochX] using
    (phaseRotate_hopfPhaseInvariant F P x).1

theorem phaseRotate_blochY_eq
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) (x : site) :
    (F.phaseRotate P).blochY x = F.blochY x := by
  simpa [phaseRotate, blochY] using
    (phaseRotate_hopfPhaseInvariant F P x).2.1

theorem phaseRotate_blochZ_eq
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) (x : site) :
    (F.phaseRotate P).blochZ x = F.blochZ x := by
  simpa [phaseRotate, blochZ] using
    (phaseRotate_hopfPhaseInvariant F P x).2.2

/-- Local gauge covariance in repo coordinates: after a sitewise phase
rotation, the repo Bloch vector still reads the original physical observables. -/
theorem phaseRotate_repo_blochVector_eq
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) (x : site) :
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((F.phaseRotate P).spinor x) 0 = F.blochX x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((F.phaseRotate P).spinor x) 1 = F.blochY x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((F.phaseRotate P).spinor x) 2 = F.blochZ x := by
  have hrepo := repo_blochVector_eq_hopf_at (F.phaseRotate P) x
  exact
    ⟨hrepo.1.trans (phaseRotate_blochX_eq F P x),
      hrepo.2.1.trans (phaseRotate_blochY_eq F P x),
      hrepo.2.2.trans (phaseRotate_blochZ_eq F P x)⟩

end LocalHopfSpinorField

/-- A stage-indexed local Hopf fiber interface over recovered sites.  The field
`spinorField n` is the finite local qubit/Hopf data carried by the recovered
site set at stage `n`. -/
structure RecoveredStageHopfFiberInterface (site : Type*) where
  spinorField : ℕ → LocalHopfSpinorField site

namespace RecoveredStageHopfFiberInterface

variable {site : Type*}

/-- Stagewise local phase rotation of the Hopf fiber data. -/
def phaseRotate
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site) :
    RecoveredStageHopfFiberInterface site where
  spinorField n := (I.spinorField n).phaseRotate (P n)

/-- Every recovered stage/site has a unit Bloch observable. -/
theorem observableNormSq_eq_one_at
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.spinorField n).observableNormSq x = 1 := by
  exact LocalHopfSpinorField.observableNormSq_eq_one (I.spinorField n) x

/-- The interface agrees with the repo's qubit Bloch vector at every
stage/site. -/
theorem repo_blochVector_eq_hopf_at
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((I.spinorField n).spinor x) 0 = (I.spinorField n).blochX x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((I.spinorField n).spinor x) 1 = (I.spinorField n).blochY x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((I.spinorField n).spinor x) 2 = (I.spinorField n).blochZ x := by
  exact LocalHopfSpinorField.repo_blochVector_eq_hopf_at (I.spinorField n) x

/-- Stagewise local `U(1)` gauge choices leave all Hopf/Bloch coordinates
unchanged. -/
theorem phaseGauge_invariant_at
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    hopfPhaseInvariant
      ((P n).p x) ((P n).q x)
      ((I.spinorField n).a x) ((I.spinorField n).b x)
      ((I.spinorField n).c x) ((I.spinorField n).d x) := by
  exact LocalHopfSpinorField.phaseRotate_hopfPhaseInvariant
    (I.spinorField n) (P n) x

/-- After any stagewise local phase choice, the rotated field is still locally
Born/Bloch normalized. -/
theorem phaseRotate_observableNormSq_eq_one_at
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (((I.phaseRotate P).spinorField n).observableNormSq x) = 1 := by
  exact observableNormSq_eq_one_at (I.phaseRotate P) n x

/-- After any stagewise local phase choice, the repo Bloch vector still reports
the original local observables. -/
theorem phaseRotate_repo_blochVector_eq_at
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        (((I.phaseRotate P).spinorField n).spinor x) 0 =
          (I.spinorField n).blochX x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        (((I.phaseRotate P).spinorField n).spinor x) 1 =
          (I.spinorField n).blochY x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        (((I.phaseRotate P).spinorField n).spinor x) 2 =
          (I.spinorField n).blochZ x := by
  exact LocalHopfSpinorField.phaseRotate_repo_blochVector_eq
    (I.spinorField n) (P n) x

#print axioms LocalHopfSpinorField.observableNormSq_eq_one
#print axioms LocalHopfSpinorField.repo_blochVector_eq_hopf_at
#print axioms LocalHopfSpinorField.phaseRotate_repo_blochVector_eq
#print axioms RecoveredStageHopfFiberInterface.observableNormSq_eq_one_at
#print axioms RecoveredStageHopfFiberInterface.phaseGauge_invariant_at
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_repo_blochVector_eq_at

end RecoveredStageHopfFiberInterface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber
