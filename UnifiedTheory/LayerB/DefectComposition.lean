/-
  LayerB/DefectComposition.lean — Defect charge algebra (DERIVED from linearity)

  Formalizes the particle-like structure of defects:
  - Composition = addition of perturbations in a vector space
  - Conjugation = negation of perturbation
  - Charge = linear functional on perturbations
  - Charge additivity, conjugation, annihilation: ALL DERIVED from linearity

  The key insight: instead of STIPULATING that charge is additive,
  we require that composition maps to vector addition and that
  charge is computed by a LINEAR functional. Then additivity is a
  THEOREM (from map_add), not a postulate.

  ALL PROVEN. No sorry. No axioms beyond Lean core.
-/
import UnifiedTheory.LayerB.DefectEquivalence

namespace UnifiedTheory.LayerB

open LayerA

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Composable defect block

Extends DefectBlock with composition structure and linear primitives.
Charge algebra is DERIVED from linearity, not stipulated. -/

/-- A defect block with composition law and linear structure.

    The key design: composition and conjugation are linked to VECTOR SPACE
    OPERATIONS via `perturbation`, `compose_is_add`, and `conjugate_is_neg`.
    Combined with linear functionals `charge_linear` and `bias_linear`,
    this allows DERIVING all charge algebra from linearity (map_add, map_neg).

    Previous version stipulated compose_K_additive etc. as fields.
    This version derives them as theorems from the linear structure. -/
structure ComposableDefectBlock (V : Type*) [AddCommGroup V] [Module ℝ V]
    extends DefectBlock V where
  /-- Each defect has an underlying perturbation in V -/
  perturbation : Defect → V
  /-- The charge is computed by a LINEAR functional on perturbations.
      charge(d) = charge_linear(perturbation(d)). Linearity is what
      makes charge additivity a THEOREM rather than a postulate. -/
  charge_linear : V →ₗ[ℝ] ℝ
  /-- charge_linear agrees with the source measurement on K-parts -/
  charge_eq : ∀ d, sourceMeas.measure (toBF d).Kpart = charge_linear (perturbation d)
  /-- The bias is computed by a LINEAR functional on perturbations -/
  bias_linear : V →ₗ[ℝ] ℝ
  /-- bias_linear agrees with the null bias -/
  bias_eq : ∀ d, (toNull d).bias = bias_linear (perturbation d)
  /-- Composition of two defects -/
  compose : Defect → Defect → Defect
  /-- Composition = addition of perturbations (DERIVATION PRIMITIVE).
      This is the key link: composition in the defect algebra corresponds
      to addition in the vector space V. -/
  compose_is_add : ∀ d₁ d₂,
    perturbation (compose d₁ d₂) = perturbation d₁ + perturbation d₂
  /-- Composition preserves stability -/
  compose_stable : ∀ d₁ d₂, Stable d₁ → Stable d₂ → Stable (compose d₁ d₂)
  /-- Charge conjugate: for every defect, there exists an anti-defect -/
  conjugate : Defect → Defect
  /-- Conjugation = negation of perturbation (DERIVATION PRIMITIVE) -/
  conjugate_is_neg : ∀ d, perturbation (conjugate d) = -(perturbation d)
  /-- Conjugate is stable if original is -/
  conjugate_stable : ∀ d, Stable d → Stable (conjugate d)

/-! ### Conserved charge -/

/-- The **charge** of a defect: Q(d) = source strength of K-part. -/
def charge (db : ComposableDefectBlock V) (d : db.Defect) : ℝ :=
  db.sourceMeas.measure (db.toBF d).Kpart

/-- **Charge additivity (DERIVED from linearity)**:
    Q(d₁ + d₂) = Q(d₁) + Q(d₂).

    Proof: charge = charge_linear ∘ perturbation (a linear functional).
    Composition maps to addition (compose_is_add).
    Linearity (map_add) gives additivity. NOT stipulated. -/
theorem charge_additive (db : ComposableDefectBlock V) (d₁ d₂ : db.Defect) :
    charge db (db.compose d₁ d₂) = charge db d₁ + charge db d₂ := by
  simp only [charge, db.charge_eq, db.compose_is_add, map_add]

/-- **Charge of conjugate (DERIVED from linearity)**: Q(d_bar) = -Q(d).
    Conjugation maps to negation (conjugate_is_neg).
    Linearity (map_neg) gives negation. -/
theorem charge_conjugate (db : ComposableDefectBlock V) (d : db.Defect) :
    charge db (db.conjugate d) = -(charge db d) := by
  simp only [charge, db.charge_eq, db.conjugate_is_neg, map_neg]

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

/-- **Annihilation produces zero bias (DERIVED from linearity)**: the composed
    defect has zero focusing contribution.
    bias = bias_linear ∘ perturbation. Compose = add, conjugate = neg.
    bias_linear(p + (-p)) = bias_linear(0) = 0 by linearity. -/
theorem annihilation_bias (db : ComposableDefectBlock V) (d : db.Defect) :
    (db.toNull (db.compose d (db.conjugate d))).bias = 0 := by
  simp only [db.bias_eq, db.compose_is_add, db.conjugate_is_neg, add_neg_cancel, map_zero]

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
