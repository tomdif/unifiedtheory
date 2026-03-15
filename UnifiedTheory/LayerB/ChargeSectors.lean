/-
  LayerB/ChargeSectors.lean — Charge-sector decomposition and bound states

  Formalizes:
  1. Charge sectors D_q: defects grouped by charge value
  2. Sector composition law: D_q ⊕ D_q' ⊆ D_{q+q'}
  3. Bound states: pairs composing into neutral composites
  4. Bound state stability
  5. Superposition: widely separated defects have additive charge

  ALL PROVEN. No sorry. No axioms beyond Lean core.
-/
import UnifiedTheory.LayerB.DefectComposition

namespace UnifiedTheory.LayerB

open LayerA

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Charge sectors -/

/-- A defect belongs to **charge sector q** if its charge equals q. -/
def InSector (db : ComposableDefectBlock V) (q : ℝ) (d : db.Defect) : Prop :=
  charge db d = q

/-- **Sector composition law**: composing a defect from sector q
    with one from sector q' yields a defect in sector q + q'. -/
theorem sector_compose (db : ComposableDefectBlock V)
    (d₁ d₂ : db.Defect) (q₁ q₂ : ℝ)
    (h₁ : InSector db q₁ d₁) (h₂ : InSector db q₂ d₂) :
    InSector db (q₁ + q₂) (db.compose d₁ d₂) := by
  unfold InSector at *
  rw [charge_additive, h₁, h₂]

/-- **Conjugation flips sector**: if d ∈ D_q then d̄ ∈ D_{-q}. -/
theorem sector_conjugate (db : ComposableDefectBlock V)
    (d : db.Defect) (q : ℝ) (h : InSector db q d) :
    InSector db (-q) (db.conjugate d) := by
  unfold InSector at *
  rw [charge_conjugate, h]

/-- **Neutral sector is D_0**: a defect is neutral iff it is in sector 0. -/
theorem neutral_iff_sector_zero (db : ComposableDefectBlock V) (d : db.Defect) :
    IsNeutral db d ↔ InSector db 0 d := by
  rfl

/-- **Sector 0 is closed under composition.** -/
theorem sector_zero_closed (db : ComposableDefectBlock V) (d₁ d₂ : db.Defect)
    (h₁ : InSector db 0 d₁) (h₂ : InSector db 0 d₂) :
    InSector db 0 (db.compose d₁ d₂) := by
  have := sector_compose db d₁ d₂ 0 0 h₁ h₂
  simp only [add_zero] at this; exact this

/-- **Sector 0 is closed under conjugation.** -/
theorem sector_zero_conj_closed (db : ComposableDefectBlock V)
    (d : db.Defect) (h : InSector db 0 d) :
    InSector db 0 (db.conjugate d) := by
  have := sector_conjugate db d 0 h
  simp only [neg_zero] at this; exact this

/-! ### Bound states -/

/-- A **bound state** is a composite of two nontrivial defects
    that is neutral (charge zero). -/
structure BoundState (db : ComposableDefectBlock V) where
  /-- First constituent -/
  d₁ : db.Defect
  /-- Second constituent -/
  d₂ : db.Defect
  /-- Both are stable -/
  h₁_stable : db.Stable d₁
  h₂_stable : db.Stable d₂
  /-- Both are source-carrying (nontrivial) -/
  h₁_source : IsSourceCarrying db.toDefectBlock d₁
  h₂_source : IsSourceCarrying db.toDefectBlock d₂
  /-- The composite is neutral -/
  h_neutral : IsNeutral db (db.compose d₁ d₂)

/-- The composite defect of a bound state. -/
def BoundState.composite (db : ComposableDefectBlock V)
    (bs : BoundState db) : db.Defect :=
  db.compose bs.d₁ bs.d₂

/-- **Bound states are stable.** -/
theorem bound_state_stable (db : ComposableDefectBlock V)
    (bs : BoundState db) :
    db.Stable (bs.composite db) :=
  db.compose_stable bs.d₁ bs.d₂ bs.h₁_stable bs.h₂_stable

/-- **Bound states have zero charge.** -/
theorem bound_state_zero_charge (db : ComposableDefectBlock V)
    (bs : BoundState db) :
    charge db (bs.composite db) = 0 :=
  bs.h_neutral

/-- **Bound states are inert** (with nonzero bias scale):
    a neutral composite of two charged defects gravitates like nothing. -/
theorem bound_state_inert (db : ComposableDefectBlock V)
    (bs : BoundState db) (hscale : db.biasScale ≠ 0) :
    IsInert db.toDefectBlock (bs.composite db) := by
  exact (charge_determines_sector db (bs.composite db)
    (bound_state_stable db bs) hscale).mp bs.h_neutral

/-- **Conjugate pairs form bound states**: d and d̄ always
    compose into a bound state when both are source-carrying. -/
def conjugate_bound_state (db : ComposableDefectBlock V)
    (d : db.Defect) (hd : db.Stable d) (hs : IsSourceCarrying db.toDefectBlock d)
    (hs_conj : IsSourceCarrying db.toDefectBlock (db.conjugate d)) :
    BoundState db where
  d₁ := d
  d₂ := db.conjugate d
  h₁_stable := hd
  h₂_stable := db.conjugate_stable d hd
  h₁_source := hs
  h₂_source := hs_conj
  h_neutral := annihilation_charge db d

/-! ### Superposition principle -/

/-- **Superposition of charges**: the total charge of a sequence of
    defects equals the sum of individual charges. -/
theorem charge_sum (db : ComposableDefectBlock V)
    (d₁ d₂ d₃ : db.Defect) :
    charge db (db.compose (db.compose d₁ d₂) d₃) =
    charge db d₁ + charge db d₂ + charge db d₃ := by
  rw [charge_additive, charge_additive, add_assoc]

/-- **Far-field cancellation**: a conjugate pair has zero total charge,
    so its far-field gravitational response vanishes. -/
theorem far_field_cancellation (db : ComposableDefectBlock V) (d : db.Defect) :
    charge db (db.compose d (db.conjugate d)) = 0 :=
  annihilation_charge db d

/-- **Charge conservation under rearrangement**: composing in either
    order gives the same total charge. -/
theorem charge_compose_comm (db : ComposableDefectBlock V) (d₁ d₂ : db.Defect) :
    charge db (db.compose d₁ d₂) = charge db (db.compose d₂ d₁) := by
  rw [charge_additive, charge_additive, add_comm]

/-! ### Sector structure summary -/

/-- **Complete charge-sector theorem**: the defect sector decomposes
    into charge classes with all expected algebraic properties:
    (1) Composition respects sectors: D_q ⊕ D_q' ⊆ D_{q+q'}
    (2) Conjugation flips sectors: D_q → D_{-q}
    (3) Neutral sector D_0 is closed under composition and conjugation
    (4) Bound states (neutral composites of charged defects) are inert
    (5) Charge is additive and commutative -/
theorem charge_sector_structure (db : ComposableDefectBlock V)
    (hscale : db.biasScale ≠ 0) :
    -- (1) Sector composition
    (∀ d₁ d₂ q₁ q₂, InSector db q₁ d₁ → InSector db q₂ d₂ →
      InSector db (q₁ + q₂) (db.compose d₁ d₂))
    -- (2) Sector conjugation
    ∧ (∀ d q, InSector db q d → InSector db (-q) (db.conjugate d))
    -- (3) Neutral sector closed
    ∧ (∀ d₁ d₂, InSector db 0 d₁ → InSector db 0 d₂ →
        InSector db 0 (db.compose d₁ d₂))
    -- (4) Bound states are inert
    ∧ (∀ (bs : BoundState db), IsInert db.toDefectBlock (bs.composite db))
    -- (5) Charge is commutative
    ∧ (∀ d₁ d₂, charge db (db.compose d₁ d₂) = charge db (db.compose d₂ d₁)) :=
  ⟨sector_compose db,
   sector_conjugate db,
   sector_zero_closed db,
   fun bs => bound_state_inert db bs hscale,
   charge_compose_comm db⟩

end UnifiedTheory.LayerB
