/-
  LayerB/DefectComposition.lean — Defect charge algebra

  Formalizes the particle-like structure of defects:
  - Composition (additive in source and dressing)
  - Conserved charge Q = source strength
  - Charge conjugation (anti-defects)
  - Annihilation (d + d_bar is inert)
  - Neutral sector characterization

  ALL PROVEN. No sorry. No axioms beyond Lean core.
-/
import UnifiedTheory.LayerB.DefectEquivalence

namespace UnifiedTheory.LayerB

open LayerA

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Composable defect block

Extends DefectBlock with composition structure. -/

/-- A defect block with composition law. -/
structure ComposableDefectBlock (V : Type*) [AddCommGroup V] [Module ℝ V]
    extends DefectBlock V where
  /-- Composition of two defects -/
  compose : Defect → Defect → Defect
  /-- Composition preserves stability -/
  compose_stable : ∀ d₁ d₂, Stable d₁ → Stable d₂ → Stable (compose d₁ d₂)
  /-- Source strength is additive under composition -/
  compose_K_additive : ∀ d₁ d₂,
    sourceMeas.measure (toBF (compose d₁ d₂)).Kpart =
    sourceMeas.measure (toBF d₁).Kpart + sourceMeas.measure (toBF d₂).Kpart
  /-- Bias is additive under composition -/
  compose_bias_additive : ∀ d₁ d₂,
    (toNull (compose d₁ d₂)).bias =
    (toNull d₁).bias + (toNull d₂).bias
  /-- Charge conjugate: for every defect, there exists an anti-defect -/
  conjugate : Defect → Defect
  /-- Conjugate is stable if original is -/
  conjugate_stable : ∀ d, Stable d → Stable (conjugate d)
  /-- Conjugate has negated source strength -/
  conjugate_K_neg : ∀ d,
    sourceMeas.measure (toBF (conjugate d)).Kpart =
    -(sourceMeas.measure (toBF d).Kpart)
  /-- Conjugate has negated bias -/
  conjugate_bias_neg : ∀ d,
    (toNull (conjugate d)).bias = -(toNull d).bias

/-! ### Conserved charge -/

/-- The **charge** of a defect: Q(d) = source strength of K-part. -/
def charge (db : ComposableDefectBlock V) (d : db.Defect) : ℝ :=
  db.sourceMeas.measure (db.toBF d).Kpart

/-- **Charge additivity**: Q(d₁ + d₂) = Q(d₁) + Q(d₂). -/
theorem charge_additive (db : ComposableDefectBlock V) (d₁ d₂ : db.Defect) :
    charge db (db.compose d₁ d₂) = charge db d₁ + charge db d₂ :=
  db.compose_K_additive d₁ d₂

/-- **Charge of conjugate**: Q(d_bar) = -Q(d). -/
theorem charge_conjugate (db : ComposableDefectBlock V) (d : db.Defect) :
    charge db (db.conjugate d) = -(charge db d) :=
  db.conjugate_K_neg d

/-- **Inert defects have zero charge**. -/
theorem charge_zero_of_inert (db : ComposableDefectBlock V)
    (d : db.Defect) (hi : IsInert db.toDefectBlock d) :
    charge db d = 0 :=
  hi.1

/-- **Source-carrying defects have nonzero charge**. -/
theorem charge_nonzero_of_source (db : ComposableDefectBlock V)
    (d : db.Defect) (hs : IsSourceCarrying db.toDefectBlock d) :
    charge db d ≠ 0 :=
  hs

/-- **Charge determines sector**: Q = 0 iff inert (with nonzero bias scale). -/
theorem charge_determines_sector (db : ComposableDefectBlock V)
    (d : db.Defect) (hd : db.Stable d) (hscale : db.biasScale ≠ 0) :
    charge db d = 0 ↔ IsInert db.toDefectBlock d := by
  constructor
  · intro hQ
    constructor
    · exact hQ
    · have hbridge := db.sourceMatchesBias d hd
      change charge db d = _ at hbridge
      rw [hQ] at hbridge
      simp only [biasMeasure] at hbridge
      exact (mul_eq_zero.mp hbridge.symm).resolve_left hscale
  · exact fun hi => hi.1

/-! ### Annihilation -/

/-- **Annihilation theorem**: composing a defect with its conjugate
    produces zero charge. -/
theorem annihilation_charge (db : ComposableDefectBlock V) (d : db.Defect) :
    charge db (db.compose d (db.conjugate d)) = 0 := by
  rw [charge_additive, charge_conjugate, add_neg_cancel]

/-- **Annihilation produces zero bias**: the composed defect has
    zero focusing contribution. -/
theorem annihilation_bias (db : ComposableDefectBlock V) (d : db.Defect) :
    (db.toNull (db.compose d (db.conjugate d))).bias = 0 := by
  rw [db.compose_bias_additive, db.conjugate_bias_neg, add_neg_cancel]

/-- **Full annihilation**: d + d_bar is inert (with nonzero bias scale). -/
theorem annihilation_is_inert (db : ComposableDefectBlock V)
    (d : db.Defect) (hd : db.Stable d)
    (hscale : db.biasScale ≠ 0) :
    IsInert db.toDefectBlock (db.compose d (db.conjugate d)) := by
  have hstable := db.compose_stable d (db.conjugate d) hd (db.conjugate_stable d hd)
  exact (charge_determines_sector db _ hstable hscale).mp (annihilation_charge db d)

/-! ### Neutral sector -/

/-- A defect is **neutral** if its charge is zero. -/
def IsNeutral (db : ComposableDefectBlock V) (d : db.Defect) : Prop :=
  charge db d = 0

/-- Neutral defects form a sub-sector closed under composition. -/
theorem neutral_compose (db : ComposableDefectBlock V) (d₁ d₂ : db.Defect)
    (h₁ : IsNeutral db d₁) (h₂ : IsNeutral db d₂) :
    IsNeutral db (db.compose d₁ d₂) := by
  unfold IsNeutral at *
  rw [charge_additive, h₁, h₂, add_zero]

/-- Annihilation products are neutral. -/
theorem annihilation_neutral (db : ComposableDefectBlock V) (d : db.Defect) :
    IsNeutral db (db.compose d (db.conjugate d)) :=
  annihilation_charge db d

/-- Conjugation maps neutral to neutral. -/
theorem conjugate_neutral (db : ComposableDefectBlock V) (d : db.Defect)
    (hn : IsNeutral db d) : IsNeutral db (db.conjugate d) := by
  unfold IsNeutral at *
  rw [charge_conjugate, hn, neg_zero]

end UnifiedTheory.LayerB
