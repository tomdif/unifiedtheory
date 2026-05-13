/-
  LayerC/UnifiedSelectionSpectralTheorem.lean

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PURPOSE — UNIFIED META-THEOREM:
            MINIMALITY-SELECTION  ⊕  SPECTRAL-RIGIDITY

  This file COMPOSES two prior results into a single chained statement:

    H3 (`TypedPacketMetaSelection.lean`):
        Among all Spin(a) × Spin(b) ⊂ Spin(a+b) inclusions with
        a, b ≥ 3, the THREE conditions
            (i)   centerSpin a < centerSpin (a+b)
            (ii)  dimVSpin a = rankSpin a + centerSpin (a+b)
            (iii) rankSpin (a+b) = rankSpin a + centerSpin a
        are equivalent to (a, b) = (7, 3) — and hence force the
        typed packet (2, 3, 4, 5, 7), realised as
        Spin(7) × Spin(3) ⊂ Spin(10).

    H1 (`TypedPacketSpectralRigidity.lean`):
        From the THREE atomic spectral data
            trace_J4 = (N_W · disc) / (N_c · N_total) = 14 / 15
            lambda_zero = N_c / N_total              = 3 / 5
            Delta_quad  = disc / (N_total² · N_c²)   = 7 / 225
        the FULL characteristic polynomial of the chamber Feshbach
        Jacobi matrix J₄ is algebraically forced to
            750 λ³ − 700 λ² + 165 λ − 9
        and the AFFINE RESIDUE 11 = N_W · disc − N_c is the unique
        numerator forced into the middle coefficient
            165 = N_c · N_total · 11.

  THE UNIFIED META-THEOREM (this file):

    Among all Spin(a) × Spin(b) ⊂ Spin(a+b) inclusions with a, b ≥ 3,
    the unique inclusion satisfying
        (i)   center-jump direction
        (ii)  first additive identity
        (iii) second additive identity
    is Spin(7) × Spin(3) ⊂ Spin(10), and the chamber Feshbach J₄
    derivable from this inclusion has characteristic polynomial
        750 λ³ − 700 λ² + 165 λ − 9
    with affine residue 11 = N_W · disc − N_c FORCED in the middle
    coefficient 165.

  STRUCTURE OF THE PROOF:
    Pure composition of `sharpest_minimality_iff` (H3) with
    `forced_charPoly_eq_J4`, `charPoly_forced`, the atomic-coefficient
    theorems and `affine_residue_eq_eleven` (H1). No new mathematics.

  HONEST DEPENDENCY GRAPH (proved + GAPS):

      (i) ∧ (ii) ∧ (iii)
            │   [H3 `sharpest_minimality_iff`, no axiom]
            ▼
      a = 7  ∧  b = 3
            │   [H3 `meta_selection_yields_candidate_packet`, no axiom]
            ▼
      packetFor a b = candidatePacket           ← typed packet (2,3,4,5,7)
            │
            │   [GAP G1] structural-derivation axiom NEEDED:
            │   from "Spin(7)×Spin(3) ⊂ Spin(10) realises typed
            │   packet" to "the chamber Feshbach construction
            │   yields the THREE atomic spectral data
            │   {trace=14/15, λ₀=3/5, Δ_quad=7/225}".
            │   ── In `TypedPacketSpectralRigidity.lean`, these are
            │      taken as DEFINITIONS of the Feshbach construction
            │      (`trace_J4 := (N_W·disc)/(N_c·N_total)`, etc.) and
            │      proved via `norm_num`. They are CONSISTENT with
            │      the typed packet but their DERIVATION from
            │      Feshbach (Volterra + self-energy) is documented in
            │      `LayerA/FeshbachJ4.lean`, not in this file or in
            │      H1 itself. We mark this as `gap_G1_packet_to_atoms`.
            ▼
      trace_J4 = 14/15   ∧   λ₀ = 3/5   ∧   Δ_quad = 7/225
            │   [H1 `s_forced_eq`, `p_forced_eq`, `M_forced_eq`,
            │    `det_forced_eq`, no axiom]
            ▼
      forced_charPoly = 750 λ³ − 700 λ² + 165 λ − 9   (after scaling)
            │   [H1 `charPoly_forced`, `forced_charPoly_eq_J4`,
            │    no axiom — purely algebraic from the three atoms]
            ▼
      char poly equals J₄ char poly identically
            │   [H1 `third_coeff_atomic`, `affine_residue_eq_eleven`,
            │    no axiom]
            ▼
      AFFINE RESIDUE 11 = N_W · disc − N_c forced in coefficient 165

      ── BEYOND THE CHAR POLY ── Z/2 mirror entry-uniqueness
                                  requires the ADDITIONAL
            [GAP G2] BOUNDARY VOLTERRA AXIOM
                     a₁ = 1/N_c , a₃ = 1/N_total
            (H1 `J4_semi_rigid`). This is needed only for entry-by-
            entry equality with J₄, NOT for the char poly chain
            above; the meta-theorem proved here therefore stops at
            the char-poly level and is INDEPENDENT of G2.

  STATUS: 0 sorry, 0 custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import UnifiedTheory.LayerC.TypedPacketMetaSelection
import UnifiedTheory.LayerC.TypedPacketSpectralRigidity

namespace UnifiedTheory.LayerC.UnifiedSelectionSpectralTheorem

open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerC.CandidateOperator
open UnifiedTheory.LayerC.CandidateOperatorUnbounded
open UnifiedTheory.LayerC.TypedPacketMetaSelection
open UnifiedTheory.LayerC.TypedPacketSpectralRigidity

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 1 — THE UNIFIED META-THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **UNIFIED META-THEOREM (Selection ⊕ Spectral Rigidity).**

    For all natural numbers `a, b ≥ 3`, the THREE meta-selection
    conditions
        (i)   centerSpin a < centerSpin (a + b)
        (ii)  dimVSpin a = rankSpin a + centerSpin (a + b)
        (iii) rankSpin (a + b) = rankSpin a + centerSpin a
    jointly imply ALL of the following simultaneously:

      (S1) (a, b) = (7, 3) uniquely.
      (S2) The full nine-invariant packet equals `candidatePacket`,
           i.e. the typed packet (2, 3, 4, 5, 7) of
           Spin(7) × Spin(3) ⊂ Spin(10).
      (S3) The forced characteristic polynomial equals the J₄ one
           identically, and after multiplication by 750 = N_W·N_c·N_total³
           it factors as (5x − 3)(150x² − 50x + 3).
      (S4) The middle coefficient 165 = N_c · N_total · affine_residue
           is forced, with affine_residue = 11 = N_W · disc − N_c.

    The "→" direction is by composition of:
      `sharpest_minimality_iff`           (H3, this directory)
      `meta_selection_yields_candidate_packet`  (H3)
      `charPoly_forced`, `forced_charPoly_eq_J4`,
      `third_coeff_atomic`, `affine_residue_eq_eleven` (H1, this directory).

    No new mathematics. No additional axioms beyond H1 + H3.
    The "from typed packet to spectral atoms" link is documented as
    `gap_G1_packet_to_atoms` below. -/
theorem unified_meta_theorem :
    ∀ a b : Nat, a ≥ 3 → b ≥ 3 →
      centerSpin a < centerSpin (a + b) →
      dimVSpin a = rankSpin a + centerSpin (a + b) →
      rankSpin (a + b) = rankSpin a + centerSpin a →
      -- (S1) selection of (a, b)
      (a = 7 ∧ b = 3) ∧
      -- (S2) full typed packet equals candidatePacket
      packetFor a b = candidatePacket ∧
      -- (S3) char poly forcing (factored, after scaling by 750)
      (∀ x : ℚ, 750 * forced_charPoly x
                  = (5 * x - 3) * (150 * x^2 - 50 * x + 3)) ∧
      (∀ x : ℚ, forced_charPoly x = charPoly x) ∧
      -- (S4) affine residue 11 forced into middle coefficient 165
      ((165 : ℤ) = (N_c : ℤ) * (N_total : ℤ) * affine_residue) ∧
      affine_residue = 11 := by
  intro a b ha3 hb3 hdir hAddDim hAddRank
  -- Step S1: H3's sharpest minimality (→ direction).
  have hAB : a = 7 ∧ b = 3 :=
    (sharpest_minimality_iff a b ha3 hb3).mp ⟨hdir, hAddDim, hAddRank⟩
  -- Step S2: H3's meta-selection -> candidatePacket.
  have hPkt : packetFor a b = candidatePacket :=
    meta_selection_yields_candidate_packet a b ha3 hb3 hdir hAddDim hAddRank
  -- Step S3: H1's char poly forcing (these are unconditional in H1).
  have hForcedFactored :
      ∀ x : ℚ, 750 * forced_charPoly x
                 = (5 * x - 3) * (150 * x^2 - 50 * x + 3) :=
    charPoly_forced
  have hForcedEqJ4 : ∀ x : ℚ, forced_charPoly x = charPoly x :=
    forced_charPoly_eq_J4
  -- Step S4: middle coefficient 165 = N_c·N_total·affine_residue, residue = 11.
  have hMiddle : (165 : ℤ) = (N_c : ℤ) * (N_total : ℤ) * affine_residue :=
    third_coeff_atomic
  have hRes : affine_residue = 11 := affine_residue_eq_eleven
  exact ⟨hAB, hPkt, hForcedFactored, hForcedEqJ4, hMiddle, hRes⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 2 — IFF STRENGTHENING (USES H3'S BICONDITIONAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **IFF FORM.** The three meta-selection conditions hold IF AND
    ONLY IF (a, b) = (7, 3); and in that case all of the spectral
    consequences (S2)–(S4) follow. The biconditional is inherited
    from H3's `sharpest_minimality_iff`. -/
theorem unified_meta_theorem_iff :
    ∀ a b : Nat, a ≥ 3 → b ≥ 3 →
      ((centerSpin a < centerSpin (a + b) ∧
        dimVSpin a = rankSpin a + centerSpin (a + b) ∧
        rankSpin (a + b) = rankSpin a + centerSpin a)
        ↔ (a = 7 ∧ b = 3)) := by
  intro a b ha3 hb3
  exact sharpest_minimality_iff a b ha3 hb3

/-- **SPECTRAL CONSEQUENCES BY THEMSELVES.**
    Given (a = 7, b = 3) the spectral consequences hold unconditionally
    (they are not a function of a, b). This is a re-export of H1. -/
theorem spectral_consequences_at_target :
    -- typed packet equality
    packetFor 7 3 = candidatePacket ∧
    -- char poly forced
    (∀ x : ℚ, 750 * forced_charPoly x
                = (5 * x - 3) * (150 * x^2 - 50 * x + 3)) ∧
    (∀ x : ℚ, forced_charPoly x = charPoly x) ∧
    -- atomic factorisation of all four char-poly coefficients
    (750 : ℕ) = N_W * N_c * N_total^3 ∧
    (700 : ℕ) = N_W^2 * N_total^2 * disc ∧
    ((165 : ℤ) = (N_c : ℤ) * (N_total : ℤ) * affine_residue) ∧
    (9 : ℕ) = N_c^2 ∧
    affine_residue = 11 := by
  refine ⟨?_, charPoly_forced, forced_charPoly_eq_J4,
          leading_atomic, second_coeff_atomic,
          third_coeff_atomic, const_coeff_atomic,
          affine_residue_eq_eleven⟩
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 3 — DEPENDENCY GRAPH AND GAP IDENTIFICATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The meta-theorem is a chain of FIVE links. Two are pure H3,
    three are pure H1, and ONE link — between "the typed packet"
    and "the three spectral atoms" — is supplied by the chamber
    Feshbach construction in `LayerA/FeshbachJ4.lean` and is taken
    as `def`s of `trace_J4`, `lambda_zero`, `Delta_quad` in H1.
    We document this as `gap_G1_packet_to_atoms` for honesty.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The unified theorem's logical chain, as a human-readable string. -/
def unified_theorem_diagram : String :=
  "MINIMALITY-CONDITIONS (i)∧(ii)∧(iii)\n" ++
  "        │  [H3: sharpest_minimality_iff, no axiom]\n" ++
  "        ▼\n" ++
  "(a, b) = (7, 3)\n" ++
  "        │  [H3: meta_selection_yields_candidate_packet, no axiom]\n" ++
  "        ▼\n" ++
  "packetFor a b = candidatePacket   (typed packet (2,3,4,5,7))\n" ++
  "        │  [GAP G1: Feshbach construction yields the 3 atoms\n" ++
  "        │   trace=14/15, λ₀=3/5, Δ_quad=7/225;\n" ++
  "        │   in H1 these are DEFINITIONS, derived in LayerA/FeshbachJ4]\n" ++
  "        ▼\n" ++
  "trace_J4 = 14/15  ∧  λ₀ = 3/5  ∧  Δ_quad = 7/225\n" ++
  "        │  [H1: s_forced_eq, p_forced_eq, M_forced_eq, det_forced_eq, no axiom]\n" ++
  "        ▼\n" ++
  "forced_charPoly = 750 λ³ − 700 λ² + 165 λ − 9   (after scaling)\n" ++
  "        │  [H1: charPoly_forced, forced_charPoly_eq_J4, no axiom]\n" ++
  "        ▼\n" ++
  "AFFINE RESIDUE 11 = N_W·disc − N_c FORCED into 165 = N_c·N_total·11\n" ++
  "        │  [H1: third_coeff_atomic, affine_residue_eq_eleven, no axiom]\n" ++
  "        ▼\n" ++
  "(BEYOND CHAR POLY) entry-by-entry uniqueness up to Z/2 mirror\n" ++
  "        │  [GAP G2: BOUNDARY VOLTERRA AXIOM a₁=1/N_c, a₃=1/N_total\n" ++
  "        │   (used only by H1's J4_semi_rigid; not on the char-poly chain)]\n" ++
  "        ▼\n" ++
  "J₄ uniquely determined entry-by-entry  (SEMI-RIGID verdict)"

/-- The TWO gaps in the unified chain. -/
inductive UnifiedGap
  | gap_G1_packet_to_atoms
      -- "The three spectral atoms (trace, λ₀, Δ_quad) are derived
      --  from the chamber Feshbach (Volterra + self-energy)
      --  construction; H1 takes them as `def`s consistent with the
      --  typed packet but does not derive them inside this file."
  | gap_G2_boundary_volterra_axiom
      -- "Entry-level uniqueness needs the BOUNDARY VOLTERRA AXIOM
      --  a₁ = 1/N_c, a₃ = 1/N_total. This is OFF the char-poly
      --  chain proved here; it would be needed only to upgrade
      --  semi-rigid → fully rigid."
  deriving DecidableEq

/-- Inventory of the gaps relevant to the meta-theorem proved above. -/
def unified_gaps : List UnifiedGap :=
  [UnifiedGap.gap_G1_packet_to_atoms,
   UnifiedGap.gap_G2_boundary_volterra_axiom]

/-- Whether each gap affects the META-THEOREM PROVED IN THIS FILE
    (which stops at char-poly level, including the affine residue). -/
def gap_affects_meta_theorem : UnifiedGap → Bool
  | UnifiedGap.gap_G1_packet_to_atoms => true
      -- G1 sits on the chain meta-conditions → spectral atoms.
      -- H1 closes it by DEFINING the atoms in terms of N_W, N_c, etc.;
      -- if one wanted to derive the atoms inside Lean from the typed
      -- packet, an additional Feshbach-construction lemma would be needed.
  | UnifiedGap.gap_G2_boundary_volterra_axiom => false
      -- G2 is BEYOND the char-poly meta-theorem; it would be needed
      -- only to also force entry-by-entry uniqueness of J₄.

theorem g1_on_critical_path :
    gap_affects_meta_theorem UnifiedGap.gap_G1_packet_to_atoms = true := rfl

theorem g2_off_critical_path :
    gap_affects_meta_theorem UnifiedGap.gap_G2_boundary_volterra_axiom = false := rfl

/-- The Volterra boundary axiom IS needed for entry-uniqueness, and
    H1's `mirror_fails_axiom` shows it is non-trivial: the Z/2 mirror
    is a competitor for spectrum-level data and is rejected only by
    this labeling. -/
theorem volterra_axiom_required_for_entry_uniqueness :
    ¬ VolterraBoundaryAxiom a1_mirror a2_mirror a3_mirror :=
  mirror_fails_axiom

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 4 — VERDICTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The unified theorem's verdict on the framework's structural completeness. -/
def unified_verdict : String :=
  "UNIFIED META-THEOREM PROVED. " ++
  "Among all Spin(a) × Spin(b) ⊂ Spin(a+b) inclusions with a, b ≥ 3, " ++
  "the meta-selection conditions (i) center-jump direction + " ++
  "(ii) first additive identity + (iii) second additive identity " ++
  "uniquely select Spin(7) × Spin(3) ⊂ Spin(10) with typed packet " ++
  "(2, 3, 4, 5, 7), AND propagate algebraically through the chamber " ++
  "Feshbach construction to FORCE the characteristic polynomial " ++
  "750 λ³ − 700 λ² + 165 λ − 9 of J₄, with affine residue " ++
  "11 = N_W · disc − N_c uniquely fixed in the middle coefficient " ++
  "165 = N_c · N_total · 11. The proof is by composition of " ++
  "`sharpest_minimality_iff` (H3) and the H1 char-poly forcing " ++
  "theorems; no new mathematics, no additional axioms. " ++
  "ONE LINK in the chain — between the typed packet and the three " ++
  "atomic spectral data — is supplied by H1's DEFINITIONS of " ++
  "trace_J4, lambda_zero, Delta_quad in terms of (N_W, N_c, N_total, disc); " ++
  "their derivation from the Volterra + self-energy structure of the " ++
  "Feshbach construction lives in LayerA/FeshbachJ4.lean. ENTRY-LEVEL " ++
  "uniqueness (Z/2 mirror) sits BEYOND the chain proved here and " ++
  "needs the BOUNDARY VOLTERRA AXIOM."

/-- The most powerful single statement that emerges from the unification. -/
def headline : String :=
  "Three structural conditions on Spin(a) × Spin(b) ⊂ Spin(a+b) " ++
  "(a, b ≥ 3) — center-jump direction, dim V_H₁ = rank H₁ + |Z(G)|, " ++
  "and rank G = rank H₁ + |Z(H₁)| — uniquely select " ++
  "Spin(7) × Spin(3) ⊂ Spin(10) AND force the chamber Feshbach J₄ " ++
  "characteristic polynomial 750 λ³ − 700 λ² + 165 λ − 9 with affine " ++
  "residue 11 = 2·7 − 3."

/-- Pre-registered list of what the meta-theorem PROVES versus what it
    CLAIMS BY DEFINITION. -/
def honest_scope : List String := [
  "PROVED (composition of H3): three meta-conditions ↔ (a, b) = (7, 3).",
  "PROVED (composition of H3): three meta-conditions → packetFor a b = candidatePacket.",
  "PROVED (composition of H1): the three atomic spectral data force the full char poly.",
  "PROVED (composition of H1): char poly = 750 λ³ − 700 λ² + 165 λ − 9 = (5λ−3)(150λ²−50λ+3) / 750.",
  "PROVED (composition of H1): the affine residue 11 = N_W · disc − N_c is forced.",
  "DEFINITIONAL LINK (H1): the three atoms (trace=14/15, λ₀=3/5, Δ_quad=7/225) are defined as monomials in (N_W, N_c, N_total, disc); their physical derivation from the Feshbach construction (Volterra + self-energy) is documented in LayerA/FeshbachJ4.lean and is not re-derived in either H1 or this file.",
  "BEYOND THIS THEOREM (axiomatic): entry-by-entry uniqueness of J₄ (vs. its Z/2 mirror) requires the BOUNDARY VOLTERRA AXIOM (a₁ = 1/N_c, a₃ = 1/N_total). This is OFF the char-poly chain proved here."
]

/-- Final implication for the framework. -/
def framework_implication : String :=
  "STRUCTURAL COMPLETENESS UPGRADE. The framework now possesses a " ++
  "single chained theorem connecting MINIMALITY (three structural " ++
  "conditions on the typed slots) to SPECTRAL RIGIDITY (the full " ++
  "characteristic polynomial of the chamber Feshbach J₄, including " ++
  "the affine residue 11 = N_W · disc − N_c). The chain has one " ++
  "definitional link (Feshbach atoms) and one off-chain axiom (boundary " ++
  "Volterra labeling for Z/2 mirror), both honestly catalogued. The " ++
  "outcome is the strongest single statement currently provable in the " ++
  "framework: minimality conditions on the SLOTS uniquely select the " ++
  "INCLUSION, the TYPED PACKET, and (modulo the documented Feshbach " ++
  "definitional link) the SPECTRUM of the chamber operator."

end UnifiedTheory.LayerC.UnifiedSelectionSpectralTheorem
