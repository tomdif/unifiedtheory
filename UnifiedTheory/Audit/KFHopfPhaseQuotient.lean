/-
  Audit/KFHopfPhaseQuotient.lean

  Algebraic phase quotient for the Hopf/Bloch bridge.

  `KFHopfSpinorBlochBridge` proves that the Bloch coordinates are invariant
  under a common unit phase.  This file names the corresponding algebraic
  quotient: two real-coordinate spinors are related when one is obtained from
  the other by multiplying both complex components by the same unit phase.

  Lean proves this is an equivalence relation and that the three Bloch
  coordinates descend to the quotient.  This is still only the set-level
  quotient, not the topological Hopf fibration: no quotient topology, local
  trivialization, Chern class, or Hopf invariant is claimed here.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfSpinorBlochBridge

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFHopfPhaseQuotient

open UnifiedTheory.Audit.KFHopfSpinorBlochBridge

/-- A unit complex phase `p + iq`, represented in real coordinates. -/
structure UnitPhase where
  p : Real
  q : Real
  unit : p ^ 2 + q ^ 2 = 1

namespace UnitPhase

/-- The identity phase. -/
def one : UnitPhase where
  p := 1
  q := 0
  unit := by norm_num

/-- The inverse phase, given by complex conjugation. -/
def conj (P : UnitPhase) : UnitPhase where
  p := P.p
  q := -P.q
  unit := by
    nlinarith [P.unit]

/-- Product of unit phases. -/
def mul (P Q : UnitPhase) : UnitPhase where
  p := P.p * Q.p - P.q * Q.q
  q := P.p * Q.q + P.q * Q.p
  unit := by
    have h :
        (P.p * Q.p - P.q * Q.q) ^ 2 +
            (P.p * Q.q + P.q * Q.p) ^ 2 =
          (P.p ^ 2 + P.q ^ 2) * (Q.p ^ 2 + Q.q ^ 2) := by
      ring
    rw [h, P.unit, Q.unit]
    norm_num

end UnitPhase

/-- A two-component complex spinor `(a+ib,c+id)` written in real coordinates. -/
structure SpinorCoords where
  a : Real
  b : Real
  c : Real
  d : Real

namespace SpinorCoords

@[ext] theorem ext_coords {u v : SpinorCoords}
    (ha : u.a = v.a) (hb : u.b = v.b)
    (hc : u.c = v.c) (hd : u.d = v.d) :
    u = v := by
  cases u
  cases v
  simp_all

/-- The squared spinor norm. -/
def normSq (u : SpinorCoords) : Real :=
  spinorNormSq u.a u.b u.c u.d

/-- First Hopf/Bloch coordinate. -/
def blochX (u : SpinorCoords) : Real :=
  hopfX u.a u.b u.c u.d

/-- Second Hopf/Bloch coordinate. -/
def blochY (u : SpinorCoords) : Real :=
  hopfY u.a u.b u.c u.d

/-- Third Hopf/Bloch coordinate. -/
def blochZ (u : SpinorCoords) : Real :=
  hopfZ u.a u.b u.c u.d

/-- Squared Bloch-vector norm. -/
def blochNormSq (u : SpinorCoords) : Real :=
  KFHopfSpinorBlochBridge.blochNormSq u.a u.b u.c u.d

/-- Common unit-phase action on both complex components of a spinor. -/
def phaseAct (P : UnitPhase) (u : SpinorCoords) : SpinorCoords where
  a := phaseRe P.p P.q u.a u.b
  b := phaseIm P.p P.q u.a u.b
  c := phaseRe P.p P.q u.c u.d
  d := phaseIm P.p P.q u.c u.d

@[simp] theorem phaseAct_one (u : SpinorCoords) :
    phaseAct UnitPhase.one u = u := by
  ext <;> simp [phaseAct, UnitPhase.one, phaseRe, phaseIm]

/-- Applying a phase and then its conjugate returns the original spinor. -/
theorem phaseAct_conj_phaseAct (P : UnitPhase) (u : SpinorCoords) :
    phaseAct P.conj (phaseAct P u) = u := by
  have hp2 : P.p ^ 2 = 1 - P.q ^ 2 := by
    nlinarith [P.unit]
  ext <;>
    simp [phaseAct, UnitPhase.conj, phaseRe, phaseIm] <;>
    ring_nf <;>
    rw [hp2] <;>
    ring

/-- Phase multiplication agrees with composition of phase actions. -/
theorem phaseAct_mul (P Q : UnitPhase) (u : SpinorCoords) :
    phaseAct (P.mul Q) u = phaseAct P (phaseAct Q u) := by
  ext <;> simp [phaseAct, UnitPhase.mul, phaseRe, phaseIm] <;> ring

/-- Algebraic common-phase relation on real-coordinate spinors. -/
def PhaseRelated (u v : SpinorCoords) : Prop :=
  ∃ P : UnitPhase, v = phaseAct P u

theorem phaseRelated_refl (u : SpinorCoords) :
    PhaseRelated u u := by
  exact ⟨UnitPhase.one, by simp⟩

theorem phaseRelated_symm {u v : SpinorCoords}
    (h : PhaseRelated u v) :
    PhaseRelated v u := by
  rcases h with ⟨P, rfl⟩
  exact ⟨P.conj, (phaseAct_conj_phaseAct P u).symm⟩

theorem phaseRelated_trans {u v w : SpinorCoords}
    (huv : PhaseRelated u v)
    (hvw : PhaseRelated v w) :
    PhaseRelated u w := by
  rcases huv with ⟨P, rfl⟩
  rcases hvw with ⟨Q, rfl⟩
  exact ⟨Q.mul P, (phaseAct_mul Q P u).symm⟩

/-- The algebraic phase quotient as a Lean setoid. -/
def phaseSetoid : Setoid SpinorCoords where
  r := PhaseRelated
  iseqv := ⟨phaseRelated_refl, phaseRelated_symm, phaseRelated_trans⟩

theorem phaseRelated_normSq_eq {u v : SpinorCoords}
    (h : PhaseRelated u v) :
    normSq v = normSq u := by
  rcases h with ⟨P, rfl⟩
  simpa [normSq, phaseAct] using
    phase_preserves_spinorNormSq P.p P.q u.a u.b u.c u.d P.unit

theorem phaseRelated_blochX_eq {u v : SpinorCoords}
    (h : PhaseRelated u v) :
    blochX v = blochX u := by
  rcases h with ⟨P, rfl⟩
  simpa [blochX, phaseAct] using
    hopfX_phase_invariant P.p P.q u.a u.b u.c u.d P.unit

theorem phaseRelated_blochY_eq {u v : SpinorCoords}
    (h : PhaseRelated u v) :
    blochY v = blochY u := by
  rcases h with ⟨P, rfl⟩
  simpa [blochY, phaseAct] using
    hopfY_phase_invariant P.p P.q u.a u.b u.c u.d P.unit

theorem phaseRelated_blochZ_eq {u v : SpinorCoords}
    (h : PhaseRelated u v) :
    blochZ v = blochZ u := by
  rcases h with ⟨P, rfl⟩
  simpa [blochZ, phaseAct] using
    hopfZ_phase_invariant P.p P.q u.a u.b u.c u.d P.unit

/-- The complete Bloch coordinate triple is constant on phase-equivalence
classes. -/
theorem phaseRelated_bloch_eq {u v : SpinorCoords}
    (h : PhaseRelated u v) :
    blochX v = blochX u ∧
    blochY v = blochY u ∧
    blochZ v = blochZ u := by
  exact
    ⟨phaseRelated_blochX_eq h,
      phaseRelated_blochY_eq h,
      phaseRelated_blochZ_eq h⟩

/-- The algebraic quotient of spinors by common unit phase. -/
def PhaseSpinorQuotient : Type :=
  Quot phaseSetoid

/-- First Bloch coordinate on the phase quotient. -/
noncomputable def quotientBlochX : PhaseSpinorQuotient → Real :=
  Quot.lift blochX (by
    intro u v h
    exact (phaseRelated_blochX_eq h).symm)

/-- Second Bloch coordinate on the phase quotient. -/
noncomputable def quotientBlochY : PhaseSpinorQuotient → Real :=
  Quot.lift blochY (by
    intro u v h
    exact (phaseRelated_blochY_eq h).symm)

/-- Third Bloch coordinate on the phase quotient. -/
noncomputable def quotientBlochZ : PhaseSpinorQuotient → Real :=
  Quot.lift blochZ (by
    intro u v h
    exact (phaseRelated_blochZ_eq h).symm)

/-- The Bloch triple on the phase quotient. -/
noncomputable def quotientBloch :
    PhaseSpinorQuotient → Real × Real × Real :=
  fun q => (quotientBlochX q, quotientBlochY q, quotientBlochZ q)

@[simp] theorem quotientBlochX_mk (u : SpinorCoords) :
    quotientBlochX (Quot.mk phaseSetoid u) = blochX u :=
  rfl

@[simp] theorem quotientBlochY_mk (u : SpinorCoords) :
    quotientBlochY (Quot.mk phaseSetoid u) = blochY u :=
  rfl

@[simp] theorem quotientBlochZ_mk (u : SpinorCoords) :
    quotientBlochZ (Quot.mk phaseSetoid u) = blochZ u :=
  rfl

theorem quotientBloch_mk (u : SpinorCoords) :
    quotientBloch (Quot.mk phaseSetoid u) =
      (blochX u, blochY u, blochZ u) := by
  rfl

#print axioms UnitPhase.mul
#print axioms SpinorCoords.phaseSetoid
#print axioms SpinorCoords.phaseRelated_normSq_eq
#print axioms SpinorCoords.phaseRelated_bloch_eq
#print axioms SpinorCoords.quotientBloch
#print axioms SpinorCoords.quotientBloch_mk

end SpinorCoords

end UnifiedTheory.Audit.KFHopfPhaseQuotient
