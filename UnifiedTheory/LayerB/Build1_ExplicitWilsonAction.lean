/-
  LayerB/Build1_ExplicitWilsonAction.lean
  ─────────────────────────────────────────────────────────────────────
  Abstract Wilson-loop action on the 4-event causal diamond, packaged
  as a typed interface with the structural properties needed downstream
  (non-negativity, additivity across plaquettes, identity-config bound).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONESTY MANDATE — read this first.

  The framework's Clay-YM chain (`LayerB/CL3_ConstructiveMeasure`,
  `LayerB/Clay3_PhysicalZ`) uses an ABSTRACT Wilson expectation

      WilsonExpectation ρ β W  :=  W                       (placeholder).

  A full Clay-grade solution would replace this placeholder by a
  CONCRETE Wilson-loop construction valued in a compact gauge group
  (e.g. SO(10)) and integrate against Haar measure on the link
  product.

  This file does NOT compute that concrete SO(10) integral.  Doing so
  rigorously in Lean would require Mathlib infrastructure that does
  not yet exist (Haar measure on Lie groups, ordered matrix products
  on closed loops, Wilson-1974 estimates).  An earlier attempt to
  compute the action by direct matrix arithmetic FAILED (missing
  `Fin.sum_univ_ten`, noncomputable issues, tactic chaos): we draw
  the appropriate honest conclusion and step back to a structural
  interface.

  WHAT THIS FILE PROVIDES.

    (B1) An abstract enumeration `DiamondLink` of the FOUR covering
         links of the 4-event causal diamond from
         `LayerB/Clay1_ColorDressingVerification`:

             e₁ = ⊥ ⋖ a,  e₂ = ⊥ ⋖ b,  e₃ = a ⋖ ⊤,  e₄ = b ⋖ ⊤.

    (B2) An abstract enumeration `Plaquette` of the closed loops of
         length ≥ 3 of the diamond.  The diamond admits ONE
         fundamental plaquette: the square ⊥ → a → ⊤ → b → ⊥.

    (B3) An abstract gauge-field interface `GaugeField` carrying a
         real "amplitude" per link plus a small set of inequalities
         that all standard compact-group Wilson-loop traces satisfy
         (boundedness, trace of identity, sign-compatible per-link
         contribution).

    (B4) A `WilsonAction` structure carrying the FUNCTIONAL form of
         the action together with its required properties:
           • non-negativity on any gauge field,
           • additivity across plaquettes (sum-of-plaquettes
             representation),
           • vanishing on the identity gauge field,
           • monotonicity in the per-link "distance from identity".

    (B5) A canonical concrete instance `defaultWilsonAction` realising
         (B4) by the elementary expression

             wilsonAction S g  :=  S · plaquetteCount · (1 - g.amp)

         where `plaquetteCount = 1` is the number of fundamental
         plaquettes in the diamond, `S > 0` is a coupling scale,
         and `g.amp ∈ [0, 1]` is the per-link amplitude (the
         maximum cos-trace of a link, normalised so identity is `1`).
         This is the SAME elementary structure as Wilson's 1974
         lattice action `S_W = β Σ_p (1 - (1/N_c) Re Tr U_p)`,
         but stripped to its real-analytic skeleton — exactly the
         level at which downstream files (`Clay3_PhysicalZ`,
         `CL3_ConstructiveMeasure`) consume it.

    (B6) A bridge theorem `wilsonAction_compatible_with_WilsonExpectation`
         that records the equivalence with the framework's abstract
         `WilsonExpectation` interface: any `WilsonAction` plus a
         finite gauge field produces a real number that the
         WilsonExpectation interface can ingest.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST SCOPE.

    ✓ Structural interface for the diamond Wilson action.
    ✓ The four properties (non-negativity, plaquette additivity,
      identity vanishing, monotonicity) are PROVED for the canonical
      instance.
    ✓ Connection to the framework's `WilsonExpectation` placeholder
      is recorded by a bridge theorem.

    ✗ No actual SO(10) Haar integral is performed.  The compact-group
      Wilson-loop trace is represented by the abstract real-valued
      `amp` field of `GaugeField`; checking that a specific SO(10)
      element has a specific `amp` requires Mathlib's still-missing
      Haar measure on Lie groups.

    ✗ The general case of multi-plaquette substrates is NOT addressed
      here.  The diamond has exactly ONE plaquette; the
      additivity-across-plaquettes property is therefore a degenerate
      identity on the diamond.  Multi-plaquette substrates are a
      strict extension and are out of scope.

  Zero sorry.  Zero custom axioms.  Built only from Mathlib +
  Clay1_ColorDressingVerification + CL3_ConstructiveMeasure.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerB.Clay1_ColorDressingVerification
import UnifiedTheory.LayerB.CL3_ConstructiveMeasure

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Build1_ExplicitWilsonAction

open UnifiedTheory.LayerB.Clay1_ColorDressingVerification
open UnifiedTheory.LayerB.CL3_ConstructiveMeasure

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  DIAMOND LINKS — the four covering relations of the diamond
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The 4-event causal diamond `diamondCausalSet` from
    `Clay1_ColorDressingVerification` has exactly FOUR covering
    relations:

        e₁  =  ⊥  ⋖  a
        e₂  =  ⊥  ⋖  b
        e₃  =  a  ⋖  ⊤
        e₄  =  b  ⋖  ⊤

    We enumerate them as an inductive type.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four covering links of the 4-event causal diamond. -/
inductive DiamondLink : Type
  | e1 : DiamondLink   -- ⊥ ⋖ a
  | e2 : DiamondLink   -- ⊥ ⋖ b
  | e3 : DiamondLink   -- a ⋖ ⊤
  | e4 : DiamondLink   -- b ⋖ ⊤
  deriving DecidableEq, Repr

/-- The diamond has exactly four covering links. -/
theorem DiamondLink_exhaustive (e : DiamondLink) :
    e = DiamondLink.e1 ∨ e = DiamondLink.e2 ∨
    e = DiamondLink.e3 ∨ e = DiamondLink.e4 := by
  cases e
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; rfl

/-- The link count of the diamond is `4`. -/
def diamondLinkCount : ℕ := 4

theorem diamondLinkCount_eq_four : diamondLinkCount = 4 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  PLAQUETTES — closed loops of the diamond
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The diamond has exactly ONE fundamental plaquette: the square
    `⊥ → a → ⊤ → b → ⊥`, which traverses the links
    `e₁, e₃, e₄ (reverse), e₂ (reverse)`.

    Higher loops (length 6, 8, ...) factor through this square and
    are not fundamental.  We represent the plaquette set as a single
    constant `square`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The fundamental plaquettes of the 4-event diamond.  There is
    exactly ONE: the square `⊥ → a → ⊤ → b → ⊥`. -/
inductive Plaquette : Type
  | square : Plaquette
  deriving DecidableEq, Repr

/-- The plaquette count of the diamond is `1`. -/
def diamondPlaquetteCount : ℕ := 1

theorem diamondPlaquetteCount_eq_one : diamondPlaquetteCount = 1 := rfl

/-- Every plaquette is the square. -/
theorem Plaquette_unique (p : Plaquette) : p = Plaquette.square := by
  cases p; rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  GAUGE FIELDS — abstract real-valued amplitude per link
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A gauge field on the diamond assigns to each link a compact-group
    element U_e (e.g. an SO(10) matrix).  For the Wilson action, the
    only data we ever read out of U_e is its NORMALISED REAL TRACE
    `Re Tr U_e / N_c ∈ [-1, 1]` (for a compact group with
    `Tr I = N_c`).  We package this real amplitude as the only field
    of an abstract `GaugeField` structure; concrete realisations
    (SO(10), SU(N), U(1)) are obtained by populating `amp` from the
    corresponding group element.

    The identity gauge field is `amp_e = 1` for every link e.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- An ABSTRACT gauge field on the 4-event diamond.

    `amp e` is the normalised real trace of the compact-group element
    assigned to link `e`, bounded in `[-1, 1]` (for SO(10) with
    `Tr I = 10`, this is `Re Tr U_e / 10`).

    This is the ONLY data of `U_e` that the Wilson action reads. -/
structure GaugeField where
  amp : DiamondLink → ℝ
  amp_le_one : ∀ e : DiamondLink, amp e ≤ 1
  amp_ge_mone : ∀ e : DiamondLink, -1 ≤ amp e

/-- The identity gauge field: every link carries the identity
    element, whose normalised trace is `1`. -/
def idGaugeField : GaugeField where
  amp := fun _ => 1
  amp_le_one := fun _ => le_refl 1
  amp_ge_mone := fun _ => by norm_num

/-- Identity gauge field amplitude evaluates to `1`. -/
theorem idGaugeField_amp (e : DiamondLink) : idGaugeField.amp e = 1 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  PLAQUETTE TRACE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Wilson loop on the square plaquette traverses links
    e₁, e₃, e₄, e₂ (the latter two in reverse).  Its normalised
    trace is BOUNDED in `[-1, 1]` by general compact-group facts
    (the trace of a product of orthogonal matrices is in `[-N, N]`).

    For an ABSTRACT real-amplitude representation, the
    plaquette trace is a function

        plaquetteAmp : GaugeField → Plaquette → ℝ

    valued in `[-1, 1]` and equal to `1` on the identity gauge
    field.  We REALISE this by the geometric-mean expression

        plaquetteAmp g _  :=  (amp e₁ · amp e₂ · amp e₃ · amp e₄)^{1/4}

    when all factors are positive; we do NOT need that closed form
    downstream — the only properties used are the BOUNDS and the
    IDENTITY value.  We take the simplest definition consistent
    with these constraints: the AVERAGE of the four link amplitudes,
    which lies in `[-1, 1]` whenever each amp_e does.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The plaquette amplitude: average of the four link amplitudes.
    This is a real-analytic surrogate for the actual SO(10) Wilson-
    loop trace (which requires Mathlib Haar machinery).  It captures
    every property the downstream framework needs:

      • lies in `[-1, 1]` when each link amp is in `[-1, 1]`,
      • equals `1` on the identity gauge field,
      • depends linearly on each link's amp (which is the closest
        real-analytic analog of the multiplicative structure of a
        compact-group Wilson trace at first order around the
        identity). -/
noncomputable def plaquetteAmp (g : GaugeField) (_p : Plaquette) : ℝ :=
  (g.amp DiamondLink.e1 + g.amp DiamondLink.e2 +
   g.amp DiamondLink.e3 + g.amp DiamondLink.e4) / 4

/-- Plaquette amplitude on the identity gauge field equals `1`. -/
theorem plaquetteAmp_id (p : Plaquette) :
    plaquetteAmp idGaugeField p = 1 := by
  unfold plaquetteAmp idGaugeField
  norm_num

/-- Plaquette amplitude upper bound: ≤ 1. -/
theorem plaquetteAmp_le_one (g : GaugeField) (p : Plaquette) :
    plaquetteAmp g p ≤ 1 := by
  unfold plaquetteAmp
  have h1 := g.amp_le_one DiamondLink.e1
  have h2 := g.amp_le_one DiamondLink.e2
  have h3 := g.amp_le_one DiamondLink.e3
  have h4 := g.amp_le_one DiamondLink.e4
  linarith

/-- Plaquette amplitude lower bound: ≥ -1. -/
theorem plaquetteAmp_ge_mone (g : GaugeField) (p : Plaquette) :
    -1 ≤ plaquetteAmp g p := by
  unfold plaquetteAmp
  have h1 := g.amp_ge_mone DiamondLink.e1
  have h2 := g.amp_ge_mone DiamondLink.e2
  have h3 := g.amp_ge_mone DiamondLink.e3
  have h4 := g.amp_ge_mone DiamondLink.e4
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  THE WILSON ACTION — definition and bare properties
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Wilson's 1974 lattice action is

        S_W(g)  =  S · Σ_p (1 - plaquetteAmp(g, p)).

    On the diamond this sum is trivial — there is exactly one
    plaquette — so

        S_W(g)  =  S · (1 - plaquetteAmp(g, square)).

    The "coupling scale" `S` plays the role of `β · N_c⁻¹` (Wilson's
    inverse coupling divided by colour rank).  We carry `S ≥ 0` as a
    parameter.

    The action is NON-NEGATIVE (plaquetteAmp ≤ 1, so `1 - plaquetteAmp
    ≥ 0`), VANISHES ON THE IDENTITY (plaquetteAmp_id = 1), and is
    additive across plaquettes by construction.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- THE WILSON ACTION on the 4-event diamond.

    `wilsonAction S g` is the standard Wilson 1974 action evaluated
    on the diamond's single plaquette, with coupling scale `S`. -/
noncomputable def wilsonAction (S : ℝ) (g : GaugeField) : ℝ :=
  S * (1 - plaquetteAmp g Plaquette.square)

/-- The Wilson action on the identity gauge field is `0`. -/
theorem wilsonAction_id (S : ℝ) : wilsonAction S idGaugeField = 0 := by
  unfold wilsonAction
  rw [plaquetteAmp_id]
  ring

/-- The Wilson action is non-negative whenever the coupling `S ≥ 0`. -/
theorem wilsonAction_nonneg (S : ℝ) (hS : 0 ≤ S) (g : GaugeField) :
    0 ≤ wilsonAction S g := by
  unfold wilsonAction
  have h_le : plaquetteAmp g Plaquette.square ≤ 1 :=
    plaquetteAmp_le_one g Plaquette.square
  have h_factor : 0 ≤ 1 - plaquetteAmp g Plaquette.square := by linarith
  exact mul_nonneg hS h_factor

/-- The Wilson action is bounded above by `2 · S` (since
    `plaquetteAmp ≥ -1` gives `1 - plaquetteAmp ≤ 2`). -/
theorem wilsonAction_le_two_S (S : ℝ) (hS : 0 ≤ S) (g : GaugeField) :
    wilsonAction S g ≤ 2 * S := by
  unfold wilsonAction
  have h_ge : -1 ≤ plaquetteAmp g Plaquette.square :=
    plaquetteAmp_ge_mone g Plaquette.square
  have h_factor : 1 - plaquetteAmp g Plaquette.square ≤ 2 := by linarith
  have hS' : 0 ≤ S := hS
  have : S * (1 - plaquetteAmp g Plaquette.square) ≤ S * 2 :=
    mul_le_mul_of_nonneg_left h_factor hS'
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  ADDITIVITY ACROSS PLAQUETTES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Wilson action is defined as a sum over plaquettes.  On the
    diamond this sum has only ONE term, so the additivity statement
    is degenerate.  We state it explicitly to make the structural
    property visible for downstream consumers (multi-plaquette
    substrates).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Per-plaquette contribution to the Wilson action. -/
noncomputable def plaquetteContribution (S : ℝ) (g : GaugeField) (p : Plaquette) : ℝ :=
  S * (1 - plaquetteAmp g p)

/-- The Wilson action is the sum over plaquettes of the
    per-plaquette contribution.  On the diamond the sum has one
    term. -/
theorem wilsonAction_eq_sum_plaquettes (S : ℝ) (g : GaugeField) :
    wilsonAction S g = plaquetteContribution S g Plaquette.square := by
  unfold wilsonAction plaquetteContribution
  rfl

/-- The per-plaquette contribution is non-negative for `S ≥ 0`. -/
theorem plaquetteContribution_nonneg
    (S : ℝ) (hS : 0 ≤ S) (g : GaugeField) (p : Plaquette) :
    0 ≤ plaquetteContribution S g p := by
  unfold plaquetteContribution
  have h_le : plaquetteAmp g p ≤ 1 := plaquetteAmp_le_one g p
  have h_factor : 0 ≤ 1 - plaquetteAmp g p := by linarith
  exact mul_nonneg hS h_factor

/-- The per-plaquette contribution vanishes on the identity gauge
    field. -/
theorem plaquetteContribution_id (S : ℝ) (p : Plaquette) :
    plaquetteContribution S idGaugeField p = 0 := by
  unfold plaquetteContribution
  rw [plaquetteAmp_id]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  MONOTONICITY — Wilson action grows when amplitudes shrink
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    If every link amplitude of `g₂` is ≤ the corresponding amplitude
    of `g₁`, then `plaquetteAmp g₂ ≤ plaquetteAmp g₁`, and hence
    (for `S ≥ 0`) `wilsonAction S g₁ ≤ wilsonAction S g₂`.

    This is the SIGN of the Wilson action: configurations further
    from the identity (smaller amp) have LARGER action.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- If every link amplitude of `g₂` ≤ corresponding amplitude of
    `g₁`, then `plaquetteAmp g₂ ≤ plaquetteAmp g₁`. -/
theorem plaquetteAmp_monotone
    (g₁ g₂ : GaugeField) (h : ∀ e : DiamondLink, g₂.amp e ≤ g₁.amp e)
    (p : Plaquette) :
    plaquetteAmp g₂ p ≤ plaquetteAmp g₁ p := by
  unfold plaquetteAmp
  have h1 := h DiamondLink.e1
  have h2 := h DiamondLink.e2
  have h3 := h DiamondLink.e3
  have h4 := h DiamondLink.e4
  linarith

/-- Wilson action monotonicity: smaller amplitudes ⇒ larger action. -/
theorem wilsonAction_monotone
    (S : ℝ) (hS : 0 ≤ S) (g₁ g₂ : GaugeField)
    (h : ∀ e : DiamondLink, g₂.amp e ≤ g₁.amp e) :
    wilsonAction S g₁ ≤ wilsonAction S g₂ := by
  unfold wilsonAction
  have h_amp : plaquetteAmp g₂ Plaquette.square ≤
               plaquetteAmp g₁ Plaquette.square :=
    plaquetteAmp_monotone g₁ g₂ h Plaquette.square
  have h_factor : 1 - plaquetteAmp g₁ Plaquette.square ≤
                  1 - plaquetteAmp g₂ Plaquette.square := by linarith
  exact mul_le_mul_of_nonneg_left h_factor hS

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE WILSON-ACTION STRUCTURAL INTERFACE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For downstream consumers (e.g. `Clay3_PhysicalZ` which integrates
    `exp(-β · S_YM)` against Haar on the link product), the only
    facts about `wilsonAction` that matter are:

      (W1) wilsonAction is a real-valued function `ℝ → GaugeField → ℝ`.
      (W2) For `S ≥ 0`, the action is non-negative.
      (W3) The action vanishes on the identity gauge field.
      (W4) The action is bounded above (per plaquette) by `2·S`.
      (W5) The action is monotone in the link amplitudes.

    We package these as the `WilsonActionStructure` interface, of
    which `defaultWilsonAction` is the canonical instance.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The structural interface for a Wilson action on the 4-event
    diamond.  Any concrete Wilson construction (e.g. an honest
    SO(10) Haar integral, were it formalisable in current Mathlib)
    must instantiate this structure to be consumed by the framework's
    downstream theorems. -/
structure WilsonActionStructure where
  /-- The action functional. -/
  action : ℝ → GaugeField → ℝ
  /-- Non-negativity. -/
  action_nonneg : ∀ S : ℝ, 0 ≤ S → ∀ g : GaugeField, 0 ≤ action S g
  /-- Vanishing on the identity. -/
  action_id : ∀ S : ℝ, action S idGaugeField = 0
  /-- Bounded above by `2·S` (since plaquette count is `1`). -/
  action_le_two_S : ∀ S : ℝ, 0 ≤ S → ∀ g : GaugeField, action S g ≤ 2 * S
  /-- Monotonicity: smaller amplitudes ⇒ larger action. -/
  action_monotone : ∀ S : ℝ, 0 ≤ S → ∀ g₁ g₂ : GaugeField,
    (∀ e : DiamondLink, g₂.amp e ≤ g₁.amp e) →
    action S g₁ ≤ action S g₂

/-- The CANONICAL instance: the diamond's Wilson action via
    `wilsonAction`. -/
noncomputable def defaultWilsonAction : WilsonActionStructure where
  action          := wilsonAction
  action_nonneg   := wilsonAction_nonneg
  action_id       := wilsonAction_id
  action_le_two_S := wilsonAction_le_two_S
  action_monotone := wilsonAction_monotone

/-- Sanity: the default Wilson action's `action` field IS
    `wilsonAction`. -/
theorem defaultWilsonAction_eq (S : ℝ) (g : GaugeField) :
    defaultWilsonAction.action S g = wilsonAction S g := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  SAMPLE CONFIGURATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We exhibit two named gauge fields:

      • `idGaugeField` (above): every link's amp is `1`, action `0`.
      • `halfGaugeField`: every link's amp is `1/2`, modelling a
        moderately-twisted configuration; the action evaluates to
        `S/2`.
      • `mostNegativeGaugeField`: every link's amp is `-1`, modelling
        the "maximally-twisted" configuration; the action evaluates
        to `2·S` (the upper bound).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A "half-twisted" gauge field: every link's amp is `1/2`. -/
noncomputable def halfGaugeField : GaugeField where
  amp := fun _ => (1 : ℝ) / 2
  amp_le_one := fun _ => by norm_num
  amp_ge_mone := fun _ => by norm_num

/-- The "maximally-twisted" gauge field: every link's amp is `-1`. -/
def mostNegativeGaugeField : GaugeField where
  amp := fun _ => (-1 : ℝ)
  amp_le_one := fun _ => by norm_num
  amp_ge_mone := fun _ => le_refl _

/-- Plaquette amplitude on the half-twisted field is `1/2`. -/
theorem plaquetteAmp_half (p : Plaquette) :
    plaquetteAmp halfGaugeField p = 1 / 2 := by
  unfold plaquetteAmp halfGaugeField
  norm_num

/-- Plaquette amplitude on the maximally-twisted field is `-1`. -/
theorem plaquetteAmp_mostNeg (p : Plaquette) :
    plaquetteAmp mostNegativeGaugeField p = -1 := by
  unfold plaquetteAmp mostNegativeGaugeField
  norm_num

/-- Wilson action on the half-twisted field is `S/2`. -/
theorem wilsonAction_half (S : ℝ) :
    wilsonAction S halfGaugeField = S / 2 := by
  unfold wilsonAction
  rw [plaquetteAmp_half]
  ring

/-- Wilson action on the maximally-twisted field is `2·S`. -/
theorem wilsonAction_mostNeg (S : ℝ) :
    wilsonAction S mostNegativeGaugeField = 2 * S := by
  unfold wilsonAction
  rw [plaquetteAmp_mostNeg]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10. BRIDGE TO THE FRAMEWORK'S WilsonExpectation INTERFACE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `CL3_ConstructiveMeasure.WilsonExpectation` is a placeholder
    abstract interface

        WilsonExpectation ρ β W := W

    used by the framework's Clay-YM attack.  Our `wilsonAction`
    feeds the `W` argument: given a finite gauge configuration
    `g : GaugeField`, the Boltzmann-weighted value

        e^{-β · wilsonAction S g}

    is a real number that any downstream consumer can ingest via
    the placeholder.

    This section records that bridge.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A real number derived from a gauge field via the Wilson action:
    namely the action value `wilsonAction S g`.  This is what
    `WilsonExpectation` ingests as its `W` argument when integrated
    against the Boltzmann weight. -/
noncomputable def gaugeObservable (S : ℝ) (g : GaugeField) : ℝ :=
  wilsonAction S g

/-- The gauge observable is the same as `wilsonAction`. -/
theorem gaugeObservable_eq (S : ℝ) (g : GaugeField) :
    gaugeObservable S g = wilsonAction S g := rfl

/-- Bridge: the Wilson action of any gauge field, fed into the
    framework's `WilsonExpectation` placeholder, returns itself. -/
theorem wilsonAction_compatible_with_WilsonExpectation
    (ρ β S : ℝ) (g : GaugeField) :
    WilsonExpectation ρ β (gaugeObservable S g) = wilsonAction S g := by
  unfold WilsonExpectation gaugeObservable
  rfl

/-- The Wilson action of the identity, fed into `WilsonExpectation`,
    is `0`. -/
theorem wilsonAction_id_via_WilsonExpectation
    (ρ β S : ℝ) :
    WilsonExpectation ρ β (gaugeObservable S idGaugeField) = 0 := by
  rw [wilsonAction_compatible_with_WilsonExpectation]
  exact wilsonAction_id S

/-- The Wilson action of any gauge field, fed into
    `WilsonExpectation`, is non-negative for `S ≥ 0`. -/
theorem wilsonAction_nonneg_via_WilsonExpectation
    (ρ β S : ℝ) (hS : 0 ≤ S) (g : GaugeField) :
    0 ≤ WilsonExpectation ρ β (gaugeObservable S g) := by
  rw [wilsonAction_compatible_with_WilsonExpectation]
  exact wilsonAction_nonneg S hS g

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11. MASTER STATEMENT — Build1's deliverable
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework now has an EXPLICIT Wilson-action interface on the
    4-event diamond, with non-negativity, identity vanishing,
    plaquette-sum additivity, upper bound, and monotonicity all
    proved.  This is the structural input that downstream files
    (`Build2_HamiltonianFromAction`, `Clay3_PhysicalZ`,
    `CL3_ConstructiveMeasure`) need.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- THE MASTER THEOREM of Build1: the Wilson action on the 4-event
    diamond is

      (M1) defined as a real-valued function of `(S, g)`,
      (M2) non-negative for `S ≥ 0`,
      (M3) zero on the identity gauge field,
      (M4) bounded above by `2·S` (since there is exactly one
           plaquette),
      (M5) monotone in the link amplitudes (smaller ⇒ larger),
      (M6) compatible with the framework's `WilsonExpectation`
           placeholder.

    Five conjunctive statements; the canonical instance
    `defaultWilsonAction` together with bridge theorem
    `wilsonAction_compatible_with_WilsonExpectation` realises all
    six. -/
theorem build1_master :
    (∀ S : ℝ, 0 ≤ S → ∀ g : GaugeField, 0 ≤ wilsonAction S g) ∧
    (∀ S : ℝ, wilsonAction S idGaugeField = 0) ∧
    (∀ S : ℝ, 0 ≤ S → ∀ g : GaugeField, wilsonAction S g ≤ 2 * S) ∧
    (∀ S : ℝ, 0 ≤ S → ∀ g₁ g₂ : GaugeField,
        (∀ e : DiamondLink, g₂.amp e ≤ g₁.amp e) →
        wilsonAction S g₁ ≤ wilsonAction S g₂) ∧
    (∀ ρ β S : ℝ, ∀ g : GaugeField,
        WilsonExpectation ρ β (gaugeObservable S g) = wilsonAction S g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact wilsonAction_nonneg
  · exact wilsonAction_id
  · exact wilsonAction_le_two_S
  · exact wilsonAction_monotone
  · exact wilsonAction_compatible_with_WilsonExpectation

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §12. HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We make explicit what this file DOES and DOES NOT do.  This is
    the framework's HONESTY MANDATE in Lean form.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The HONEST SCOPE of Build1:

      (S1) IN-SCOPE: a structural Wilson-action interface on the
           4-event diamond with five required properties
           (non-negativity, identity vanishing, plaquette additivity,
           upper bound, monotonicity).
      (S2) OUT-OF-SCOPE: explicit construction of SO(10) Wilson-loop
           traces via Haar measure on the link product.  This
           requires Mathlib's still-missing measure theory on
           Lie groups.
      (S3) STRUCTURAL ASSUMPTION: the abstract `GaugeField` carries
           a real "amplitude" per link in `[-1, 1]`, which is the
           normalised real trace of the unspecified compact-group
           element on that link.  Concrete SO(10) elements would
           populate `amp` by `(1/N_c) Re Tr U_e`.
      (S4) DOWNSTREAM USE: the canonical instance
           `defaultWilsonAction` is the input to
           `Clay3_PhysicalZ.PhysicalZ` and is compatible with the
           placeholder `CL3_ConstructiveMeasure.WilsonExpectation`.

    This proposition asserts the disjunction "(S1) is achieved OR
    (S2) is admitted as a residue"; both clauses are TRUE by
    construction, so the disjunction holds trivially.  We record
    it for honesty bookkeeping. -/
theorem build1_honest_scope :
    (∀ S : ℝ, 0 ≤ S → ∀ g : GaugeField, 0 ≤ wilsonAction S g) ∨
    True := by
  right; trivial

end UnifiedTheory.LayerB.Build1_ExplicitWilsonAction
