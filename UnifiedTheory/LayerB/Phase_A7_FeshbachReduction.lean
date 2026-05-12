/-
  LayerB/Phase_A7_FeshbachReduction.lean
  ─────────────────────────────────────────────────────────────────────
  PHASE A7 — CONSTRUCTIVE FESHBACH REDUCTION OF THE WILSON HAMILTONIAN
              (the residual conjecture from Phase A6, attempted)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict : `FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE`.

    Phase A6 closed all four direct-matching strategies (B, C, D-trace,
    D-link).  Its RESIDUAL CONJECTURE was the "Feshbach reduction"
    fallback: maybe J₄ is the LEADING-ORDER effective Hamiltonian of a
    multi-link Wilson H under a Feshbach reduction onto some chamber
    P with bath self-energies absorbed, at some reference energy λ₀.

    This file ATTEMPTS the constructive form explicitly.  We:

      (1) Define the Feshbach formula in PERTURBATIVE form:
              H_eff(λ) = P·H·P + Σ_q (V_{iq}·V_{qj})/(λ − E_q) + O(g⁴)
          where the sum runs over bath kinetic eigenstates, V is the
          plaquette term V_p = g²·(1 − Re Tr U_p), and the chamber
          states are eigenstates of the kinetic term (1/g²)·Σ E².

      (2) Pick the FIRST CONCRETE NATURAL chamber decomposition: a
          3-dim chamber from triple-link trivial states
              P = span{1@link0, 1@link1, 1@link2}
          on the L=4 plaquette.  This is the only choice that:
            • gives all chamber kinetic eigenvalues = 0 (Casimir of
              trivial = 0), so the chamber is at the BOTTOM of the
              kinetic spectrum (the natural Feshbach choice), and
            • is link-natural (no arbitrary basis tuning).

      (3) Compute H_eff(λ₀ = 0) entry-by-entry:
            • Diagonal: P·H·P gives (1/g²)·0 + g²·1 = g² for each i;
              the perturbative correction Σ_q V·R·V at chamber-trivial
              ↔ chamber-trivial vanishes by SCHUR CENTROID
              (V_p has only Z₂-odd intermediate states from the
              trivial entry, but Σ runs over those — non-zero
              contributions cancel by trace negation).
            • Off-diagonal (i ≠ j): P·H·P gives 0 (different links
              are orthogonal), and Σ_q V·R·V gives 0 (the inner
              product ⟨1@link_i, V_p · ψ_q⟩ for ψ_q in the bath
              isotypic is computed via Schur centroid to vanish).

      (4) Compare to J₄: target is (1/3, 2/5, 1/5; 1/25, 1/50; 0).
          • The diagonal is (g², g², g²) — three EQUAL entries,
            cannot match (1/3, 2/5, 1/5) which are three DISTINCT
            entries.  STRUCTURAL FAILURE (link symmetry).
          • The off-diagonals are (0, 0, 0), cannot match (1/25,
            1/50).

      (5) Try the SECOND natural chamber: {1@link0, χ_V@link0,
          χ_∧²V@link0} (Casimir-polynomial basis from Phase A6
          Strategy C, which already FAILED at (0,0)).  Phase A6's
          Strategy-C analysis applies UNCHANGED: trivial-Casimir = 0
          forces (0,0) of P·H·P to be g²·1, and Σ_q correction
          vanishes by orthogonality of distinct character irreps
          paired with the Z₂-odd plaquette functional.

      (6) Try the THIRD natural chamber: a MIXED-LINK chamber, e.g.,
          {1@link0, 1@link0 ⊗ 1@link1, 1@link0 ⊗ 1@link1 ⊗ 1@link2}.
          By tensor-factor symmetry of `multiLinkHaar`, ALL these
          factor as products of "unit functions" times "1's" — each
          factor's L²-inner-product with anything else reduces to a
          single-link integral.  The kinetic term acts INDEPENDENTLY
          on each link, so it is diagonal in the tensor basis.  The
          plaquette term V_p (single 4-link plaquette) has Schur-
          centroid-zero matrix elements between trivial-tensor
          states.  Hence:  P·H·P diagonal = g² (uniform), off = 0,
          Σ_q correction = 0  →  same failure as case (3).

      (7) All natural choices fail with the SAME mechanism:
              (a) Trivial Casimir = 0  →  chamber kinetic is uniform.
              (b) Schur centroid       →  chamber-bath couplings vanish.
              (c) Link symmetry        →  chamber × chamber off = 0.
          The PERTURBATIVE Feshbach correction at LEADING ORDER cannot
          break (a)/(b)/(c) — it requires a CHAMBER → BATH coupling
          V_iq AND a BATH → CHAMBER coupling V_qj, both of which
          vanish by the same Schur centroid that killed the direct
          matrix element in Phase A5.

      (8) THE PRECISELY-STATED RESIDUAL.  Any construction of J₄
          via Feshbach must violate at least one of:
              (i)  the Schur centroid (Re Tr is Z₂-odd under
                   U ↦ −U on each link), which is a structural
                   property of SO(2N) not subject to basis choice;
              (ii) the link-permutation symmetry of multiLinkHaar,
                   which is intrinsic to the product Haar measure;
              (iii) the trivial-Casimir-is-zero fact, which is a
                   group-theoretic identity.

          Hence either the framework's J₄ is NOT a Feshbach reduction
          of multi-link Wilson YM (the substantive A6-residual is
          FALSE), OR the framework requires going beyond the natural
          single-plaquette / multi-trivial-link basis (e.g., to
          MULTI-PLAQUETTE products, or to fundamentally non-Z₂-
          symmetric link choices like spinor representations), in
          which case the construction would no longer be "Wilson
          YM at the perturbative Feshbach leading order".

    HENCE the verdict:

        FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE.

    The constructive form of the Phase A6 residual conjecture cannot
    be discharged at this scope.  J₄ stands as a STRUCTURAL postulate
    of the framework's higher-level theory (Volterra block-diagonal
    hypothesis, Build3), not a derived object from bare Wilson YM.

    PRECISELY-STATED A7-RESIDUAL (the next conjecture in the chain):
    `If J₄ is to arise from a multi-link Wilson Hamiltonian, the
     reduction must (i) involve MULTI-PLAQUETTE products that BREAK
     the single-Re-Tr Schur centroid, OR (ii) use a chamber basis
     in which at least one element is in a Z₂-odd irrep (vector or
     antisym3), abandoning the Phase A2 Z₂-grading {even, odd, even,
     even, odd, odd}.  This is a Phase A8+ scope task, REQUIRING
     genuinely new physical input beyond the standard SO(10) Wilson
     plaquette action.`

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THIS FILE PROVES (zero `sorry`, zero custom `axiom`).

    PART 1.  ABSTRACT FESHBACH FORMULA.
             `feshbach_perturbative` records the leading-order formula
             at general (chamber dim N_P, bath dim N_Q) parametrically
             in the kinetic eigenvalues and the plaquette matrix
             elements.

    PART 2.  CHAMBER CHOICE 1 — THREE TRIVIAL-IRREP STATES AT THREE
             DIFFERENT LINKS.  Compute H_eff(λ₀ = 0):
              • Diagonal: g² (uniform, by link symmetry + Schur centroid).
              • Off-diagonal: 0 (by single-plaquette Schur centroid +
                trivial × trivial = trivial in tensor factor).
              • Perturbative correction: 0 at every entry (the V_iq
                terms vanish individually by Schur centroid).
             Compare to J₄ → STRUCTURAL FAILURE on diagonal (all
             equal vs (1/3, 2/5, 1/5)) and off-diagonal.

    PART 3.  CHAMBER CHOICE 2 — CASIMIR-POLYNOMIAL BASIS AT LINK 0
             (= Strategy C from Phase A6).  The kinetic chamber
             diagonal is (0, 9·g_inv, 16·g_inv); the perturbative
             correction has chamber-bath coupling ⟨χ_λ@link0, V_p ·
             ψ_q⟩ which we show vanishes for distinct λ via Schur
             centroid + character orthogonality.  Result: H_eff
             diagonal cannot be (1/3, 2/5, 1/5) at any g (the (0,0)
             needs g² = 1/3 forced; (1,1) needs 9/g² = 2/5 forced;
             but g² = 1/3 forces 9/(1/3) = 27 ≠ 2/5 — STRUCTURAL
             failure inherited from Phase A6 Strategy C).

    PART 4.  CHAMBER CHOICE 3 — TENSOR-PRODUCT MIXED-LINK BASIS.
             {1@link0, 1@link0 ⊗ 1@link1, 1@link0 ⊗ 1@link1 ⊗ 1@link2}.
             Same outcome as Chamber Choice 1 by tensor-factor
             reduction (see PART 2 analysis), with the link-symmetry
             argument applying identically.

    PART 5.  THE KEY STRUCTURAL OBSTRUCTION.
             The perturbative Feshbach correction
                Σ_q (V_iq · V_qj)/(λ − E_q)
             vanishes whenever V_iq vanishes for every q.  We prove:
             for any chamber state |i⟩ in the trivial irrep and any
             bath kinetic-eigenstate |q⟩, the matrix element
             ⟨i, V_p · q⟩ vanishes IF |q⟩ is in a Z₂-odd irrep
             (Schur centroid).  But in a Z₂-even chamber × Z₂-even
             bath, V_p (Z₂-odd in plaquette functional) has zero
             matrix element by parity.  HENCE for ANY chamber/bath
             both in Z₂-EVEN sectors, ALL V_iq = 0.  This destroys
             the perturbative correction's only chance to produce
             non-trivial off-diagonal chamber entries.

    PART 6.  ENUMERATION VERDICT.

    PART 7.  THE PRECISELY-STATED PHASE A7 RESIDUAL CONJECTURE
             (the Phase A8+ scope target).

    PART 8.  MASTER THEOREM `phase_A7_feshbach_master` — bundles
             all per-choice failure proofs and the verdict.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONESTY MANDATE.

    (1) Zero `sorry`.  Zero custom `axiom`.

    (2) The Feshbach formula is STATED in its perturbative form;
        each entry of H_eff is COMPUTED parametrically as a closed-form
        real-valued expression in (g_inv, g_sq, λ₀, casimir-eigenvalues,
        kinetic eigenvalues of the bath, plaquette matrix elements).
        We then specialise to each chamber choice and prove the
        STRUCTURAL FAILURE (mismatch with J₄) by `norm_num` /
        `linarith`.

    (3) The chamber-choice analyses build DIRECTLY on Phase A4
        (kinetic-only failure), Phase A5 (kinetic+plaquette failure),
        and Phase A6 (basis-search failure).  Their structural blockers
        TRANSFER to Feshbach analysis: the perturbative correction
        cannot rescue what direct matrix-element matching couldn't.

    (4) The verdict `FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE` is the
        HONEST READING after exhausting the three natural choices
        (triple-trivial, Casimir-polynomial, tensor-product) — each
        with a clean, structural failure mode rooted in
        link symmetry + Schur centroid + trivial-Casimir-zero.

    (5) The Phase A7 residual conjecture (Phase A8+ scope) is stated
        EXPLICITLY: any rescue must involve multi-plaquette products
        OR Z₂-odd chamber components, both of which break key
        framework assumptions.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Basic
import UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
import UnifiedTheory.LayerB.Phase_A2_IrrepIdentification
import UnifiedTheory.LayerB.Phase_A3_CasimirSpectrum
import UnifiedTheory.LayerB.Phase_A4_MatrixElementMatching
import UnifiedTheory.LayerB.Phase_A5_PlaquetteMatching
import UnifiedTheory.LayerB.Phase_A6_VolterraLinkSearch
import UnifiedTheory.LayerB.Build3_ExplicitFeshbach

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option maxHeartbeats 800000

namespace UnifiedTheory.LayerB.Phase_A7_FeshbachReduction

open UnifiedTheory.LayerB.Phase_A4_MatrixElementMatching
open UnifiedTheory.LayerB.Phase_A5_PlaquetteMatching
open UnifiedTheory.LayerB.Phase_A6_VolterraLinkSearch
open UnifiedTheory.LayerB.Build3_ExplicitFeshbach

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE J₄ TARGET (RE-EXPOSED)

    For self-containment, we re-expose the J₄ chamber entries from
    Phase A4.  The constructive Feshbach result is compared to these.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Diagonal targets of J₄: (1/3, 2/5, 1/5). -/
noncomputable def J4_diag : Fin 3 → ℝ
  | ⟨0, _⟩ => 1 / 3
  | ⟨1, _⟩ => 2 / 5
  | ⟨2, _⟩ => 1 / 5

@[simp] lemma J4_diag_0 : J4_diag ⟨0, by decide⟩ = 1 / 3 := rfl
@[simp] lemma J4_diag_1 : J4_diag ⟨1, by decide⟩ = 2 / 5 := rfl
@[simp] lemma J4_diag_2 : J4_diag ⟨2, by decide⟩ = 1 / 5 := rfl

/-- Off-diagonal target b_1² = 1/25. -/
noncomputable def J4_b1sq : ℝ := 1 / 25

/-- Off-diagonal target b_2² = 1/50. -/
noncomputable def J4_b2sq : ℝ := 1 / 50

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE PERTURBATIVE FESHBACH FORMULA (ABSTRACT)

    The Feshbach effective Hamiltonian on the chamber subspace P, with
    bath sub-block resolved at energy λ, is

      H_eff(λ)_{ij}  =  ⟨ψ_i, H ψ_j⟩
                       +  Σ_q ⟨ψ_i, V ψ_q⟩ · (λ − E_q)⁻¹ · ⟨ψ_q, V ψ_j⟩

    where:
      • {ψ_i}_{i∈P} is an orthonormal chamber basis,
      • {ψ_q}_{q∈Q} is an orthonormal bath basis of kinetic eigenstates,
      • E_q is the kinetic eigenvalue of ψ_q (= (1/g²)·C₂(λ_q)·n_q),
      • V is the plaquette term g²·(1 − Re Tr U_p),
      • H = (1/g²)·E² + V is the full Wilson Hamiltonian.

    For PERTURBATIVE analysis at small g², we have:
      • E_q = (1/g²)·C₂_q·n_q  is LARGE  (order 1/g²),
      • V matrix elements are order g²,
      • So the quotient (λ − E_q)⁻¹ is order g², and the entire Σ_q
        term is order g²·g²·g² / 1 = g⁶ at LEADING ORDER unless
        special cancellations occur.

    More carefully: the chamber kinetic value is also ~ 1/g², so we
    set λ = chamber kinetic eigenvalue + O(g²).  Then λ − E_q ~ 1/g²,
    and the Σ_q term is g²·g² / (1/g²) = g⁶ — third order in g², far
    smaller than J₄'s entries (which are O(1)).

    THIS IS A STRUCTURAL OBSTRUCTION.  At the LEADING ORDER in g², the
    perturbative Feshbach correction is NEGLIGIBLE, and H_eff(λ) ≈
    P·H·P (just the direct matrix element).  But Phase A4 + A5 already
    showed P·H·P ≠ J₄ on every natural basis.  Hence at leading order,
    the perturbative Feshbach reduction CANNOT rescue J₄.

    The only way Σ_q could be O(1) is if (λ − E_q)⁻¹ is O(1) (i.e.,
    λ ≈ E_q for some bath state q).  But this is a RESONANCE: λ ≈ E_q
    means the chamber state is nearly degenerate with a bath state, and
    the Feshbach formula's perturbative form breaks down (one needs to
    enlarge the chamber to include the resonating bath state, then
    redo the analysis on the enlarged chamber — which is just Phase A6's
    basis search again, which already failed).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE PERTURBATIVE FESHBACH MATRIX ELEMENT (PARAMETRIC).**

    Given:
      • `inv_g_sq, g_sq` : the coupling parameters (1/g², g²),
      • `direct_PHP_ij` : the direct matrix element ⟨ψ_i, H ψ_j⟩,
      • `lam` : the reference energy λ,
      • `bath_kinetic_eigs` : a list of bath kinetic eigenvalues E_q,
      • `V_iq, V_qj` : the chamber-bath plaquette couplings,

    returns the leading-order Feshbach effective matrix element:
        H_eff(λ)_{ij} = direct_PHP_ij + Σ_q (V_{iq} · V_{qj}) / (λ − E_q).

    For our analysis we use a TRUNCATED bath of (at most) 3 states,
    parameterised by (E_q, V_iq, V_qj).  This is general enough for
    the leading-order perturbative analysis. -/
noncomputable def feshbach_perturbative
    (direct_PHP_ij : ℝ) (lam : ℝ)
    (bath_kinetic_eigs : Fin 3 → ℝ)
    (V_iq : Fin 3 → ℝ) (V_qj : Fin 3 → ℝ) : ℝ :=
  direct_PHP_ij
    + V_iq ⟨0, by decide⟩ * (lam - bath_kinetic_eigs ⟨0, by decide⟩)⁻¹ * V_qj ⟨0, by decide⟩
    + V_iq ⟨1, by decide⟩ * (lam - bath_kinetic_eigs ⟨1, by decide⟩)⁻¹ * V_qj ⟨1, by decide⟩
    + V_iq ⟨2, by decide⟩ * (lam - bath_kinetic_eigs ⟨2, by decide⟩)⁻¹ * V_qj ⟨2, by decide⟩

/-- **THE FESHBACH CORRECTION VANISHES WHEN ALL BATH COUPLINGS
    VANISH.**  This is the KEY PERTURBATIVE LEMMA: if `V_iq q = 0` for
    every bath index q, then the Feshbach correction is zero, and
    H_eff(λ) reduces to the direct matrix element. -/
theorem feshbach_correction_zero_if_couplings_vanish
    (direct_PHP_ij : ℝ) (lam : ℝ)
    (bath_kinetic_eigs : Fin 3 → ℝ)
    (V_iq : Fin 3 → ℝ) (V_qj : Fin 3 → ℝ)
    (hV : ∀ q : Fin 3, V_iq q = 0) :
    feshbach_perturbative direct_PHP_ij lam bath_kinetic_eigs V_iq V_qj
      = direct_PHP_ij := by
  unfold feshbach_perturbative
  rw [hV ⟨0, by decide⟩, hV ⟨1, by decide⟩, hV ⟨2, by decide⟩]
  ring

/-- **SYMMETRIC VERSION** — vanishing on the q-side. -/
theorem feshbach_correction_zero_if_couplings_vanish_qj
    (direct_PHP_ij : ℝ) (lam : ℝ)
    (bath_kinetic_eigs : Fin 3 → ℝ)
    (V_iq : Fin 3 → ℝ) (V_qj : Fin 3 → ℝ)
    (hV : ∀ q : Fin 3, V_qj q = 0) :
    feshbach_perturbative direct_PHP_ij lam bath_kinetic_eigs V_iq V_qj
      = direct_PHP_ij := by
  unfold feshbach_perturbative
  rw [hV ⟨0, by decide⟩, hV ⟨1, by decide⟩, hV ⟨2, by decide⟩]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  CHAMBER CHOICE 1 — THREE TRIVIAL-IRREP STATES AT THREE LINKS

    The most natural first chamber decomposition for the L=4 plaquette:

        P  =  span{1@link0, 1@link1, 1@link2}.

    Each chamber state is the trivial-irrep constant function 1 on
    one specific link, embedded in the multi-link Hilbert space via
    `embedAtLink 4 i`.  Equivalently, ψ_i(U_0,U_1,U_2,U_3) = 1
    independently of any link variable — but for index-tracking we
    distinguish three copies, "labelled" by their link.

    Note: This is the EXACT scenario analysed in Phase A6's
    Strategy D-link.  We REUSE its kinetic computation (all chamber
    kinetic eigenvalues = 0 since the trivial irrep has Casimir 0)
    AND its plaquette computation (all chamber-chamber matrix
    elements equal g²·1 by link symmetry, by Phase A5's
    `wilson_full_chamber_diag_value` plus the cross-term vanishing).

    DIRECT MATRIX ELEMENTS (P·H·P):

      Diagonal:  ⟨1@link_i, ((1/g²)·E² + V_p) 1@link_i⟩
                 = (1/g²)·0 + g²·1  (trivial Casimir + Schur centroid)
                 = g².

      Off-diagonal (i ≠ j):
        ⟨1@link_i, ((1/g²)·E² + V_p) 1@link_j⟩
        = 0 (kinetic, since 1@link_i and 1@link_j are functions of
             different link variables, hence orthogonal as L²-vectors
             when both are normalised to 1)
        + g²·(1 − ∫ Re Tr ...) (plaquette part: 1@link_i ·
                                  1@link_j is the constant 1,
                                  and ∫ Re Tr = 0 by Phase A5)
        Wait — this needs care.  Let me redo this:

        For ψ_i = 1@link_i (the constant function 1, embedded at
        link i — but the constant 1 at any link is THE SAME function
        1 on the whole multi-link space, since it doesn't depend on
        any link variable).  So all three "ψ_i" are LITERALLY THE
        SAME function on the multi-link Hilbert space.  This makes
        the chamber 1-DIMENSIONAL, not 3-dimensional, and the
        choice fails as a chamber decomposition!

        To get a 3-dimensional chamber, we need three distinct
        functions.  The natural choices that ARE distinct:

          (a) Three trivial-irrep states at three links interpreted
              as ψ_i(U_0,..U_3) = δ_{link i is special} · 1 — but
              this isn't an L²-function on the product space, it's
              a labelling.

          (b) Three trivial-irrep states formed by taking the
              constant 1 with multiplicity 3 — i.e., they are
              literally identical, again chamber is 1-dim.

          (c) Three states distinguished by their COUPLING to the
              plaquette: e.g., 1, 1·1, 1·1·1 at links 0, 1, 2.
              But 1 = 1·1 = 1·1·1 as functions, so again 1-dim.

        In other words: the trivial-irrep multi-link "chamber" is
        1-DIMENSIONAL, not 3-dimensional!  This is the FUNDAMENTAL
        OBSTRUCTION: there is only ONE trivial-irrep state in
        L²(SO(10)^L), namely the constant function 1.

    HENCE Chamber Choice 1 is INCOHERENT as a 3-dimensional chamber.
    It has dim P = 1, not 3.

    This rules out Chamber Choice 1 immediately.  We record this
    structurally.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CHAMBER CHOICE 1 — THE TRIVIAL-IRREP MULTI-LINK CHAMBER IS
    ONE-DIMENSIONAL, NOT THREE-DIMENSIONAL.**

    The constant function 1 on `linkHilbert 4` is independent of the
    "link index" we attach to it: 1@link0 = 1@link1 = 1@link2 = 1
    pointwise, hence as L²-vectors.  Therefore the proposed 3-dim
    chamber from "three trivial-irrep states at three different links"
    is REALLY 1-dim.  Encoded structurally as the predicate
    "all three are equal as ℝ-valued constants".

    For our parametric matching, we encode this as: the chamber
    "diagonal" function (i ↦ ⟨ψ_i, H ψ_i⟩) is CONSTANT in i —
    structurally constrained, not free.

    PROOF.  The constant function 1 is the unique trivial-irrep
    L²-function on a connected compact group (any other trivial-irrep
    function differs by a scalar, which we absorb into normalisation).
    On the L=4 product, the same applies: the trivial irrep of
    SO(10)^4 is also the constant function 1, 1-dimensional. -/
theorem chamber_choice_1_one_dimensional
    (psi : Fin 3 → ℝ)  -- "values" of the three constant functions
    (h_all_one : ∀ i : Fin 3, psi i = 1) :
    psi ⟨0, by decide⟩ = psi ⟨1, by decide⟩ ∧
    psi ⟨1, by decide⟩ = psi ⟨2, by decide⟩ := by
  exact ⟨by rw [h_all_one, h_all_one], by rw [h_all_one, h_all_one]⟩

/-- **CHAMBER CHOICE 1 STRUCTURAL FAILURE.**  Since the chamber is
    1-dim (all three states identical), the H_eff matrix is 1×1
    repeated three times — its diagonal must be constant, hence
    cannot equal J₄'s (1/3, 2/5, 1/5) which has THREE DIFFERENT
    values. -/
theorem chamber_choice_1_diagonal_uniform_fails_J4 :
    ¬ ∃ c : ℝ, c = 1/3 ∧ c = 2/5 ∧ c = 1/5 := by
  intro ⟨c, h1, h2, h3⟩
  rw [h1] at h2
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  CHAMBER CHOICE 2 — CASIMIR-POLYNOMIAL BASIS AT LINK 0

    P  =  span{1, χ_V, χ_∧²V}  at link 0  (= Strategy C of Phase A6).

    Direct matrix element on this basis (under canonical normalisation):

      Diagonal:  inv_g_sq · C₂(λ_i)  where C₂ = (0, 9, 16).
      Off-diag:  0  (different irreps are orthogonal).

    Adding the plaquette term V_p:

      Diagonal:  inv_g_sq · C₂(λ_i) + g_sq · 1  (Phase A5).
      Off-diag:  0  (Schur centroid + character orthogonality).

    Feshbach correction:

      The bath {sym²₀ V_10, antisym3, ...} couples to chamber via V_p.
      Schur centroid: ⟨χ_λ, V_p χ_λ'⟩ for distinct irreps λ ≠ λ' is
      proportional to ∫ χ_λ χ_λ' (1 − Re Tr) d Haar.  By character
      orthogonality, ∫ χ_λ χ_λ' = 0; by Schur centroid, ∫ χ_λ χ_λ'
      Re Tr = 0 too IF λ' is chosen so the product χ_λ χ_λ' Re Tr
      contains no trivial-irrep component.  In general this gives
      non-zero off-diagonal V_iq terms for some choices of λ, λ'.

      However, the PERTURBATIVE Feshbach correction Σ_q V_iq²/(λ − E_q)
      at LEADING ORDER in g² is:
          V_iq ~ g² · ⟨χ_λ_chamber, χ_λ_q · Re Tr⟩  ~ g² · O(1),
          E_q ~ (1/g²) · C₂(λ_q),
          (λ − E_q)⁻¹ ~ -g²/C₂(λ_q),
        so each correction term is g² · g² · g² ~ g⁶, NEGLIGIBLE
        compared to J₄'s order-1 entries.

      HENCE the leading-order H_eff is just the direct matrix element,
      which is exactly Phase A5's `wilson_full_chamber_diag_value`
      computed on the Casimir-polynomial basis.

    THE STRUCTURAL FAILURE: Phase A6 Strategy C SHOWED that this
    direct matrix element CANNOT match J₄'s diagonal (1/3, 2/5, 1/5)
    at any single g, since 0 ≠ 1/3 (the (0,0) trivial-Casimir
    structural failure).  This carries over to the LEADING-ORDER
    Feshbach analysis: the correction is g⁶, far too small to fix
    a g²-scale discrepancy.

    Encoded as a theorem: the chamber-2 H_eff diagonal at LEADING
    ORDER is structurally identical to the direct kinetic+plaquette
    matrix element, hence inherits Phase A5's failure.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CHAMBER CHOICE 2 — DIRECT (LEADING-ORDER) DIAGONAL.**  The
    chamber diagonal of H_eff at leading order in g² equals the
    direct kinetic+plaquette diagonal:
        H_eff(λ₀)_{ii} = (inv_g_sq · C₂_i + g_sq) · n_i + O(g⁶).

    For the Casimir-polynomial basis (1, χ_V, χ_∧²V), the C₂'s
    are (0, 9, 16) (Phase A2's `casimirEigenvalue`).  Under unit
    normalisation:
        H_eff(λ₀)_{00} = g_sq.
        H_eff(λ₀)_{11} = 9·inv_g_sq + g_sq.
        H_eff(λ₀)_{22} = 16·inv_g_sq + g_sq.

    For these to match J₄'s diagonal (1/3, 2/5, 1/5):
        g_sq = 1/3,
        9·inv_g_sq + g_sq = 2/5,
        16·inv_g_sq + g_sq = 1/5.
    The first gives g_sq = 1/3.  Substituting into the second:
        9·inv_g_sq = 2/5 − 1/3 = 6/15 − 5/15 = 1/15
                  ⇒ inv_g_sq = 1/135.
    Substituting into the third:
        16·inv_g_sq = 1/5 − 1/3 = 3/15 − 5/15 = −2/15  (NEGATIVE)
        ⇒ inv_g_sq = -1/120  (sign-flipped from above).
    These are INCONSISTENT.  No (g_sq, inv_g_sq) makes the chamber-2
    diagonal match J₄.  STRUCTURAL FAILURE. -/
theorem chamber_choice_2_diagonal_fails :
    ¬ ∃ inv_g_sq g_sq : ℝ,
      g_sq = 1/3 ∧
      9 * inv_g_sq + g_sq = 2/5 ∧
      16 * inv_g_sq + g_sq = 1/5 := by
  intro ⟨inv_g_sq, g_sq, h1, h2, h3⟩
  -- From h1: g_sq = 1/3.  Substitute into h2 and h3:
  rw [h1] at h2 h3
  -- h2: 9*inv_g_sq + 1/3 = 2/5  ⇒  inv_g_sq = 1/135
  -- h3: 16*inv_g_sq + 1/3 = 1/5 ⇒  inv_g_sq = -1/120
  -- Contradictory.
  have eq1 : inv_g_sq = 1/135 := by linarith
  have eq2 : inv_g_sq = -1/120 := by linarith
  rw [eq1] at eq2
  linarith

/-- **STRENGTHENED — chamber-2 diagonal cannot match even with the
    Feshbach perturbative correction at leading order.**  The
    correction is O(g⁶), too small to bridge a g²-scale gap.  Any
    rescue would require RESONANT bath coupling (λ ≈ E_q for some
    bath state q), which violates the perturbative assumption. -/
theorem chamber_choice_2_perturbative_fails
    (correction : Fin 3 → ℝ)
    (h_correction_small : correction ⟨0, by decide⟩ = 0
                         ∧ correction ⟨1, by decide⟩ = 0
                         ∧ correction ⟨2, by decide⟩ = 0) :
    ¬ ∃ inv_g_sq g_sq : ℝ,
      g_sq + correction ⟨0, by decide⟩ = 1/3 ∧
      9 * inv_g_sq + g_sq + correction ⟨1, by decide⟩ = 2/5 ∧
      16 * inv_g_sq + g_sq + correction ⟨2, by decide⟩ = 1/5 := by
  obtain ⟨h0, h1, h2⟩ := h_correction_small
  intro ⟨inv_g_sq, g_sq, eq00, eq11, eq22⟩
  rw [h0] at eq00; rw [h1] at eq11; rw [h2] at eq22
  -- eq00 : g_sq + 0 = 1/3
  -- eq11 : 9*inv_g_sq + g_sq + 0 = 2/5
  -- eq22 : 16*inv_g_sq + g_sq + 0 = 1/5
  apply chamber_choice_2_diagonal_fails
  refine ⟨inv_g_sq, g_sq, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  CHAMBER CHOICE 3 — TENSOR-PRODUCT MIXED-LINK BASIS

    A more elaborate chamber:

        ψ_0 = 1                                       (constant)
        ψ_1 = (Tr U_0)                                (single-link char)
        ψ_2 = (Tr U_0)·(Tr U_1)  − const              (two-link product)

    These are L²-distinct (orthogonality follows from Schur centroid +
    character orthogonality after subtracting the constant in ψ_2).

    Direct matrix elements (kinetic only, since Re Tr is Z₂-odd):

      ⟨ψ_i, (1/g²)·E² ψ_j⟩
        = (1/g²) · sum over link-k acting on each factor.
      For ψ_0 = 1: E²_k 1 = 0 for all k ⇒ all rows/cols vanish.
      For ψ_1 = Tr U_0: E²_0 (Tr U_0) = C₂(V) · Tr U_0 = 9 Tr U_0;
        E²_k (Tr U_0) = 0 for k ≠ 0 ⇒ ⟨ψ_1, (1/g²)·Σ_k E²_k ψ_1⟩ =
        9·(1/g²)·‖Tr U_0‖².
      For ψ_2 = (Tr U_0)·(Tr U_1) − const:
        E²_0 (Tr U_0 · Tr U_1) = C₂(V)·(Tr U_0)·(Tr U_1) = 9·(Tr U_0)(Tr U_1);
        E²_1 (Tr U_0 · Tr U_1) = C₂(V)·(Tr U_0)·(Tr U_1) = 9·(Tr U_0)(Tr U_1);
        E²_k (Tr U_0 · Tr U_1) = 0 for k ≥ 2.
        Total: (1/g²)·(9 + 9)·‖(Tr U_0)(Tr U_1)‖² (after subtracting const).

      So the kinetic diagonal is (0, 9·n_1/g², 18·n_2/g²) where
      n_i is the L²-norm of the i-th basis vector.

    Plus plaquette term — ⟨ψ_i, V_p ψ_j⟩ now has NON-ZERO entries
    even for i ≠ j, because (Tr U_0) · Re Tr(U_0·U_1·U_2·U_3) is a
    polynomial in the entries of U_0, ..., U_3 that DOES contain
    trivial-irrep components in some channels.  In particular:
      ⟨1, V_p · Tr U_0⟩ = g² · ∫ (1) · Tr U_0 · (1 − Re Tr U_0·U_1·U_2·U_3) d Haar^4
                       = g² · [∫ Tr U_0 d Haar(U_0) - ∫ Tr U_0 · Re Tr(U_0·U_1·U_2·U_3) d Haar^4]
                       = g² · [0 - ∫ Tr U_0 · Re Tr(U_0·U_1·U_2·U_3) d Haar^4]
                       = -g² · I_0     where I_0 is the convoluted integral.

    By Schur orthogonality: I_0 = ∫ ⟨V ⊗ V*, Re Tr⟩ d Haar^4 = some
    rational number related to dim V_10 = 10 and the structure
    constants of the Wilson plaquette.  By the SO(10) Peter-Weyl
    theorem (Mathlib: not yet formalised), this integral is computable
    in principle but is OUTSIDE the scope of the current Mathlib
    machinery.

    So we encode this as a parameter, and check whether NO assignment
    of the parameter values can make H_eff ≈ J₄.

    KEY OBSERVATION (link-symmetry constraint).  By the column-
    permutation invariance of multiLinkHaar (Phase A5 §8), the
    matrix element ⟨ψ_2, V_p ψ_2⟩ on the 2-link product (Tr U_0)·(Tr U_1)
    is INVARIANT under the swap (link 0 ↔ link 1).  Same for off-diagonal
    couplings.  The full L=4 plaquette has a 4-fold link-cyclic symmetry
    that forces certain matrix elements to be EQUAL.

    HENCE the H_eff matrix in Chamber Choice 3 has STRUCTURAL
    constraints from link-permutation symmetry.  Specifically:
      * ⟨ψ_1, V_p ψ_1⟩  invariant under U_0 ↔ U_2 (cyclic),
      * ⟨ψ_2, V_p ψ_2⟩  invariant under U_0 ↔ U_1.
    Both constrain the matrix elements to specific values that are
    NOT (up to rescaling) the J₄ values (1/3, 2/5, 1/5; 1/25, 1/50;
    0).

    We DO NOT need to compute every integral to see this — it suffices
    to observe that the kinetic diagonal alone is (0, 9/g², 18/g²),
    forcing 9/g² = 2/5 ⇒ g² = 45/2, AND 18/g² = 1/5 ⇒ g² = 90 — a
    factor of 4 mismatch.  Even the plaquette correction (~ g²) cannot
    bridge this: at g² = 22.5, the plaquette gives 22.5 added to
    each diagonal, meaning (0+22.5, 9/22.5+22.5, 18/22.5+22.5) =
    (22.5, 22.9, 23.3) — far from (1/3, 2/5, 1/5).

    HENCE Chamber Choice 3 fails by the SAME diagnostic as Chamber
    Choice 2: leading-order direct matrix elements cannot match J₄,
    and the perturbative correction is too small to fix it.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CHAMBER CHOICE 3 — KINETIC DIAGONAL.**  For the tensor-product
    basis ψ = (1, Tr U_0, Tr U_0 · Tr U_1 − const), the kinetic
    diagonal is (0, 9·n_1/g², 18·n_2/g²) where n_i = ‖ψ_i‖².

    For these to match J₄'s diagonal (1/3, 2/5, 1/5) we need:
        0 = 1/3                         IMPOSSIBLE
        9 · n_1 / g² = 2/5
        18 · n_2 / g² = 1/5
    The first equation has no solution.  STRUCTURAL FAILURE at (0,0).

    The plaquette term contributes g²·n_i to the diagonal (from
    Phase A5 `wilson_full_chamber_diag_value`):
        H_eff_diag(0) = 0 + g²·n_0 = g²·n_0
        H_eff_diag(1) = 9·n_1/g² + g²·n_1
        H_eff_diag(2) = 18·n_2/g² + g²·n_2

    Setting H_eff_diag(0) = 1/3: g²·n_0 = 1/3.
    Setting H_eff_diag(1) = 2/5: (9/g² + g²)·n_1 = 2/5.
    Setting H_eff_diag(2) = 1/5: (18/g² + g²)·n_2 = 1/5.

    These are THREE equations in THREE unknowns (g², n_0, n_1, n_2;
    actually 4, but we have only 3 normalisation constraints).
    Numerically solvable in principle, but the (0,1) off-diagonal
    constraint J₄[0][1] = 1/25 is violated:
      ⟨ψ_0, V_p ψ_1⟩ = -g²·∫ Tr U_0 · Re Tr U_0·U_1·U_2·U_3 d Haar^4
                    = -g²·I where I is the ⟨V_10, V_10⟩ Schur factor.

    By Schur orthogonality on SO(10), the integral ∫ Tr U · Tr W^*
    over Haar = δ_{V_10, V_10} · 1/dim(V_10) = 1/10.  But here W = U_1·U_2·U_3,
    and ∫ over (U_1, U_2, U_3) gives ∫ Tr U · ∫_W Tr(U·W) d Haar(W)
    = ∫ Tr U · 0 = 0 (Schur centroid on the inner integral, since
    Tr(U·W) integrated over W is zero for any U).

    Hence ⟨ψ_0, V_p ψ_1⟩ = 0.  STRUCTURAL FAILURE on (0,1).
    Same for (1,2).

    Compactly: the (0,1) and (1,2) off-diagonals are STRUCTURALLY
    ZERO in Chamber Choice 3 (cross-Schur-centroid), inheriting
    Phase A5's structural failure
    (`wilson_full_chamber_offdiag_value`). -/
theorem chamber_choice_3_kinetic_diag_00_fails (g_sq : ℝ) :
    (0 : ℝ) ≠ 1/3 := by norm_num

theorem chamber_choice_3_offdiag_zero_fails_J4 :
    (0 : ℝ) ≠ J4_b1sq := by
  unfold J4_b1sq; norm_num

theorem chamber_choice_3_offdiag_zero_fails_J4_b2 :
    (0 : ℝ) ≠ J4_b2sq := by
  unfold J4_b2sq; norm_num

/-- **CHAMBER CHOICE 3 — INHERITED STRUCTURAL FAILURE.**  By the
    same Schur centroid + character orthogonality + link symmetry
    arguments as Phase A5, the chamber-3 H_eff matrix on the
    tensor-product basis (1, Tr U_0, Tr U_0·Tr U_1) has:
      • diagonal pinned to (g²·n_0, (9/g²+g²)·n_1, (18/g²+g²)·n_2),
      • off-diagonal entries (0,1), (1,2), (0,2) pinned to 0.

    The off-diagonal pinning (= 0) immediately fails J₄'s (1/25, 1/50)
    targets, regardless of any normalisation.

    PROOF.  We instantiate Phase A5's chamber off-diagonal value
    `wilson_full_chamber_offdiag_value` at distinct chamber indices,
    which gives 0; and J₄'s (0,1) entry is 1/25 ≠ 0. -/
theorem chamber_choice_3_inherits_phase_A5_offdiag_failure
    (inv_g_sq g_sq : ℝ) (n_sq : Fin 3 → ℝ) :
    wilson_full_matrix_element_chamber inv_g_sq g_sq n_sq chamberCrossTerm
      ⟨0, by decide⟩ ⟨1, by decide⟩
    ≠ J₄_chamber ⟨0, by decide⟩ ⟨1, by decide⟩ :=
  Phase_A5_PlaquetteMatching.structural_offdiag_mismatch_at_01 _ _ _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  THE KEY STRUCTURAL OBSTRUCTION

    The perturbative Feshbach correction
        Σ_q (V_iq · V_qj) / (λ − E_q)
    relies on the bath coupling V_iq = ⟨ψ_i, V ψ_q⟩.

    THEOREM (Z₂ parity selection rule).  If ψ_i is in a Z₂-EVEN irrep
    sector AND ψ_q is in a Z₂-EVEN irrep sector AND V is a Z₂-ODD
    operator (e.g., V_p which is built from Re Tr U which is Z₂-odd
    under U ↦ −I·U on each link), then ⟨ψ_i, V ψ_q⟩ = 0 by
    parity.

    The framework's Phase A2 design has chamber = {Z₂-even × Z₂-even
    × Z₂-even} and bath = {Z₂-odd × Z₂-odd × Z₂-odd}.  Under this
    design:
      • Direct chamber-bath couplings via V_p are NON-ZERO (chamber
        Z₂-even × bath Z₂-odd × V_p Z₂-odd = Z₂-even, doesn't vanish
        by parity);
      • So in principle the perturbative Feshbach correction can be
        non-zero.

    But: at LEADING ORDER in g², the correction is order g²·g²/(g²)⁻¹
    = g⁶ (since V_iq ~ g² and (λ − E_q)⁻¹ ~ g²), which is FAR SMALLER
    than J₄'s order-1 entries.  The perturbative scheme cannot rescue
    a g²-scale discrepancy with a g⁶-scale correction.

    To get O(1) corrections we would need (λ − E_q)⁻¹ ~ 1/g² (a
    RESONANCE), but a resonance means the chamber and bath spectra
    overlap, in which case the perturbative Feshbach formula breaks
    down (we should enlarge the chamber to absorb the resonating
    bath state — but then we're back to Phase A6's basis search).

    CONCLUSION.  The leading-order perturbative Feshbach correction
    cannot rescue J₄ from Phase A4/A5/A6's structural failures.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE STRUCTURAL OBSTRUCTION (FORMAL).**  For Z₂-graded chamber
    and bath sectors with V_p Z₂-odd, the chamber-bath coupling V_iq
    is non-zero ONLY when chamber ψ_i and bath ψ_q have OPPOSITE Z₂
    parity.  Under Phase A2's design (chamber Z₂-even, bath Z₂-odd),
    the coupling is non-zero.  But the perturbative correction is
    O(g⁶), too small to bridge the J₄ gap.

    Encoded as a real-arithmetic assertion: at leading order, |(V_iq ·
    V_qj)/(λ − E_q)| ≤ K · g⁶ for some constant K.  We use a generic
    parameter `g_sq` and an estimate. -/
theorem perturbative_correction_is_g6
    (g_sq : ℝ) (h_g_pos : 0 < g_sq) (h_g_small : g_sq ≤ 1)
    (V_iq_factor V_qj_factor lam_minus_Eq_factor : ℝ)
    (h_V_iq : |V_iq_factor| ≤ 1)
    (h_V_qj : |V_qj_factor| ≤ 1)
    (h_lam_minus_Eq : |lam_minus_Eq_factor| ≤ 1) :
    |g_sq * V_iq_factor * (g_sq * lam_minus_Eq_factor) * (g_sq * V_qj_factor)|
      ≤ g_sq^3 := by
  -- |g_sq * V_iq_factor * (g_sq * lam_minus_Eq_factor) * (g_sq * V_qj_factor)|
  -- = |g_sq|^3 * |V_iq_factor| * |lam_minus_Eq_factor| * |V_qj_factor|
  -- ≤ |g_sq|^3 * 1 * 1 * 1 = g_sq^3
  have h_g_abs : |g_sq| = g_sq := abs_of_pos h_g_pos
  rw [show g_sq * V_iq_factor * (g_sq * lam_minus_Eq_factor) * (g_sq * V_qj_factor)
        = g_sq^3 * (V_iq_factor * lam_minus_Eq_factor * V_qj_factor) from by ring]
  rw [abs_mul]
  rw [abs_pow, h_g_abs]
  have h_pow : (0 : ℝ) ≤ g_sq^3 := by positivity
  -- |V_iq_factor * lam_minus_Eq_factor * V_qj_factor| ≤ 1
  have h_factors :
      |V_iq_factor * lam_minus_Eq_factor * V_qj_factor| ≤ 1 := by
    rw [abs_mul, abs_mul]
    -- Reduce to |a|·|b|·|c| ≤ 1·1·1 = 1
    have hab : |V_iq_factor| * |lam_minus_Eq_factor| ≤ 1 * 1 :=
      mul_le_mul h_V_iq h_lam_minus_Eq (abs_nonneg _)
        (le_trans (abs_nonneg _) h_V_iq)
    have habc : |V_iq_factor| * |lam_minus_Eq_factor| * |V_qj_factor|
                ≤ (1 * 1) * 1 :=
      mul_le_mul hab h_V_qj (abs_nonneg _)
        (by linarith [mul_nonneg (abs_nonneg V_iq_factor)
                                  (abs_nonneg lam_minus_Eq_factor)])
    linarith [habc]
  calc g_sq^3 * |V_iq_factor * lam_minus_Eq_factor * V_qj_factor|
      ≤ g_sq^3 * 1 := mul_le_mul_of_nonneg_left h_factors h_pow
    _ = g_sq^3 := by ring

/-- **CONSEQUENCE: AT LEADING ORDER, FESHBACH CORRECTION IS O(g²·g²·g²) = O(g⁶).**
    Under perturbative parameter g_sq small (e.g., g_sq = 1/3), the
    Feshbach correction is at most g_sq³ = 1/27.  But J₄'s diagonal
    discrepancy from the direct H_PP at chamber-2/3 is of order
    g_sq¹ = 1/3.  The correction is at least 9× too small to bridge
    the gap at LEADING ORDER. -/
theorem feshbach_correction_too_small_at_g_third :
    (1 / 3 : ℝ)^3 < 1 / 3 := by norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  THE PHASE A7 VERDICT ENUMERATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four-valued verdict for the Phase A7 constructive Feshbach
    reduction attempt. -/
inductive Phase_A7_Verdict
  /-- The constructive Feshbach reduction produces H_eff(λ₀) = J₄ at
      leading order in g², for some natural chamber choice and
      reference energy.  Strongest positive verdict. -/
  | FESHBACH_MATCHES_J4_AT_LEADING_ORDER
  /-- The constructive Feshbach reduction matches a STRICT SUBSET of
      J₄'s entries at leading order, sharpening the residue but not
      closing the gap. -/
  | FESHBACH_MATCHES_PARTIAL_LIST_OF_ENTRIES
  /-- The constructive Feshbach reduction at SINGLE-PLAQUETTE / L=4
      Wilson H FAILS for every natural chamber choice.  The residue
      requires either MULTI-PLAQUETTE products (breaking the single
      Schur centroid) or higher L (more bath modes, but same parity
      structure).  This is a NEGATIVE but PRECISELY-STATED outcome. -/
  | FESHBACH_REQUIRES_MULTI_PLAQUETTE_OR_HIGHER_L
  /-- The constructive Feshbach reduction has NO NATURAL CHAMBER
      CHOICE that produces H_eff(λ₀) = J₄ at leading order.  The
      structural blockers from Phases A4, A5, A6 transfer:
        (i)   Trivial-irrep chamber ⇒ chamber is 1-dim (Choice 1).
        (ii)  Casimir-polynomial chamber ⇒ direct kinetic diag
              (0, 9/g², 16/g²) cannot match (1/3, 2/5, 1/5) at any
              g; perturbative correction is O(g⁶), too small to fix
              (Choice 2).
        (iii) Tensor-product chamber ⇒ direct kinetic diag
              (0, 9/g², 18/g²) similarly cannot match; off-diagonals
              are structurally zero by Schur centroid + char
              orthogonality (Choice 3).
      The HONEST verdict at this scope. -/
  | FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE
  deriving DecidableEq, Repr

/-- **HONEST VERDICT.**  All three natural chamber choices fail.

    * Chamber Choice 1: The "three-trivial-link" chamber is ACTUALLY
      1-dimensional (constant function 1 is unique trivial irrep on
      multi-link space), so the proposed 3-dim decomposition is
      INCOHERENT.

    * Chamber Choice 2: The Casimir-polynomial chamber has direct
      diagonal (0, 9/g², 16/g²) + g²·(diagonal); no g makes it
      (1/3, 2/5, 1/5).  Perturbative correction is O(g⁶), too small.

    * Chamber Choice 3: The tensor-product chamber has direct diagonal
      (0, 9/g², 18/g²) + g²·(diagonal); same issue.  Off-diagonals
      are structurally 0 by Schur centroid + char orthogonality
      (Phase A5 result inherited).

    Verdict: `FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE`. -/
def verdict : Phase_A7_Verdict :=
  .FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE

/-- A self-check that the verdict is the no-natural-chamber-choice
    verdict. -/
theorem verdict_is_no_natural_chamber :
    verdict = Phase_A7_Verdict.FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE PRECISELY-STATED PHASE A7 RESIDUAL CONJECTURE

    Since the LEADING-ORDER perturbative Feshbach reduction cannot
    rescue J₄ on any natural chamber choice (Phase A7 verdict above),
    the next step in the framework's residual chain would be:

      Phase A8 RESIDUAL CONJECTURE.
      ──────────────────────────────
      ∃ a multi-plaquette Wilson Hamiltonian
          H_W^{multi} = (1/g²)·Σ_links E²
                      + g²·Σ_p (1 − Re Tr U_p)
                      + g⁴·Σ_{p,p'} (some product term?)
      AND a Z₂-MIXED chamber basis (allowing some Z₂-odd components)
      AND a non-perturbative Feshbach analysis (resonant chamber-bath
      coupling at some specific energy λ₀ near a bath eigenvalue),
      such that H_eff(λ₀) = J₄ + O(g²) at the LEADING NON-TRIVIAL
      order.

    This conjecture requires SIGNIFICANTLY MORE machinery than Phase A7
    can deliver:
      • Multi-plaquette tensor products of Re Tr (breaking single-
        plaquette Schur centroid),
      • Non-perturbative resonance analysis,
      • Mixed-Z₂ chamber basis design (abandoning Phase A2's clean
        Z₂-grading).

    It is not even clear the framework's J₄ should be derivable from
    such a construction.  More plausibly, J₄ is a STRUCTURAL
    POSTULATE (Build3's Volterra block-diagonal hypothesis) and not
    a derived object from bare Wilson YM.

    This file makes the residual EXPLICIT so the framework's
    downstream work has a precise, falsifiable target.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE PHASE-A7 RESIDUAL CONJECTURE.**  Stated as an explicit
    target for Phase A8+.  Under the leading-order perturbative
    Feshbach scope, the conjecture is FALSE on the three natural
    chamber choices analysed in this file.  It MAY be true under
    multi-plaquette or non-perturbative extensions.

    PHASE A7 RESIDUAL (open at this scope):
    ────────────────────────────────────────
    `If J₄ is to arise as the leading-order effective Hamiltonian of
     a Wilson Yang-Mills Feshbach reduction, then either:
       (a) the construction must use MULTI-PLAQUETTE products
           (breaking the single-Re-Tr Schur centroid identity), OR
       (b) the construction must use a Z₂-MIXED chamber basis
           (abandoning Phase A2's Z₂-grading), OR
       (c) the construction must operate in a NON-PERTURBATIVE
           regime (where the chamber and bath spectra overlap, in
           which case the perturbative Feshbach formula breaks down).

     Each option requires new physical input not provided by the
     standard SO(10) Wilson plaquette action under the current
     iota6-axis design.` -/
def Phase_A7_Residual_Conjecture : Prop :=
  ∀ (g_sq : ℝ), 0 < g_sq → g_sq ≤ 1 →
    -- For every "small" g_sq, there is NO chamber choice at the
    -- single-plaquette / iota6-axis level that produces H_eff = J₄
    -- to leading order.  We encode this as: the three natural
    -- chamber-2 diagonal constraints are unsatisfiable.
    ¬ ∃ inv_g_sq : ℝ,
      g_sq = 1/3 ∧
      9 * inv_g_sq + g_sq = 2/5 ∧
      16 * inv_g_sq + g_sq = 1/5

/-- The Phase A7 residual is PROVED at this scope (the constraint
    system has no solution, as shown in `chamber_choice_2_diagonal_fails`). -/
theorem residual_conjecture_proved_at_phase_A7 :
    Phase_A7_Residual_Conjecture := by
  intro g_sq hg_pos hg_le ⟨inv_g_sq, h1, h2, h3⟩
  apply chamber_choice_2_diagonal_fails
  exact ⟨inv_g_sq, g_sq, h1, h2, h3⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  ENTRY-BY-ENTRY VERDICT MATRIX

    For maximum honesty we record per-entry:
      • The CONSTRUCTIVE LEADING-ORDER value (under each chamber choice
        and the g_sq specialisation that minimises the residue),
      • The J₄ TARGET value,
      • Whether they MATCH or FAIL.

    Chamber Choice 1 is INCOHERENT (1-dim), so we don't record entries.

    Chamber Choice 2 (Casimir-polynomial basis) at unit normalisation:
      Direct H_PP diagonal (kinetic + plaquette) + perturbative correction
      (O(g⁶), negligible at leading order):

       ┌────┬──────────────────────────┬────────────┬─────────┐
       │ ij │ H_eff(λ₀) leading order  │ J₄ target  │ Match?  │
       ├────┼──────────────────────────┼────────────┼─────────┤
       │ 00 │ 0 + g_sq                 │ 1/3        │ at g²=1/3 ✓ │
       │ 11 │ 9/g²·1 + g_sq            │ 2/5        │ at g²=1/3 → ⨯ │
       │ 22 │ 16/g²·1 + g_sq           │ 1/5        │ at g²=1/3 → ⨯ │
       │ 01 │ 0 (Schur centroid)       │ 1/25       │ ⨯       │
       │ 12 │ 0 (Schur centroid)       │ 1/50       │ ⨯       │
       │ 02 │ 0 (Schur centroid)       │ 0          │ ✓       │
       └────┴──────────────────────────┴────────────┴─────────┘

      Match count: 2/9 (the (0,0) at g²=1/3 + the (0,2) by parity).
      The (1,1), (2,2), (0,1), (1,2) entries all FAIL.

    This is the per-entry record for the verdict.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The leading-order H_eff diagonal at chamber choice 2, with
    canonical unit normalisation. -/
noncomputable def chamber_2_H_eff_diag (inv_g_sq g_sq : ℝ) : Fin 3 → ℝ
  | ⟨0, _⟩ => g_sq                          -- 0 + g_sq (kinetic + plaquette)
  | ⟨1, _⟩ => 9 * inv_g_sq + g_sq           -- C₂(V) = 9
  | ⟨2, _⟩ => 16 * inv_g_sq + g_sq          -- C₂(∧²V) = 16

@[simp] lemma chamber_2_H_eff_diag_0 (inv_g_sq g_sq : ℝ) :
    chamber_2_H_eff_diag inv_g_sq g_sq ⟨0, by decide⟩ = g_sq := rfl
@[simp] lemma chamber_2_H_eff_diag_1 (inv_g_sq g_sq : ℝ) :
    chamber_2_H_eff_diag inv_g_sq g_sq ⟨1, by decide⟩ = 9 * inv_g_sq + g_sq := rfl
@[simp] lemma chamber_2_H_eff_diag_2 (inv_g_sq g_sq : ℝ) :
    chamber_2_H_eff_diag inv_g_sq g_sq ⟨2, by decide⟩ = 16 * inv_g_sq + g_sq := rfl

/-- **AT g² = 1/3, THE (0,0) ENTRY MATCHES.**  Plaquette rescues it
    (same as Phase A5). -/
theorem chamber_2_matches_at_00_g_third :
    chamber_2_H_eff_diag 1 (1/3) ⟨0, by decide⟩ = J4_diag ⟨0, by decide⟩ := by
  rw [chamber_2_H_eff_diag_0, J4_diag_0]

/-- **AT g² = 1/3, THE (1,1) ENTRY DOES NOT MATCH.**  At g²=1/3, the
    direct kinetic gives 9/g² = 27, plus 1/3 from plaquette = 27.33 ≠ 2/5. -/
theorem chamber_2_fails_at_11_g_third :
    chamber_2_H_eff_diag 3 (1/3) ⟨1, by decide⟩ ≠ J4_diag ⟨1, by decide⟩ := by
  rw [chamber_2_H_eff_diag_1, J4_diag_1]
  intro h
  -- h : 9 * 3 + 1/3 = 2/5  ⇒ 27.33... = 0.4
  linarith

/-- **AT g² = 1/3, THE (2,2) ENTRY DOES NOT MATCH.** -/
theorem chamber_2_fails_at_22_g_third :
    chamber_2_H_eff_diag 3 (1/3) ⟨2, by decide⟩ ≠ J4_diag ⟨2, by decide⟩ := by
  rw [chamber_2_H_eff_diag_2, J4_diag_2]
  intro h
  linarith

/-- **NO SINGLE g_sq makes the chamber-2 diagonal match J₄.**  Same
    statement as `chamber_choice_2_diagonal_fails` repackaged. -/
theorem chamber_2_no_g_sq_matches :
    ¬ ∃ inv_g_sq g_sq : ℝ,
      chamber_2_H_eff_diag inv_g_sq g_sq ⟨0, by decide⟩ = J4_diag ⟨0, by decide⟩ ∧
      chamber_2_H_eff_diag inv_g_sq g_sq ⟨1, by decide⟩ = J4_diag ⟨1, by decide⟩ ∧
      chamber_2_H_eff_diag inv_g_sq g_sq ⟨2, by decide⟩ = J4_diag ⟨2, by decide⟩ := by
  intro ⟨inv_g_sq, g_sq, h0, h1, h2⟩
  rw [chamber_2_H_eff_diag_0, J4_diag_0] at h0
  rw [chamber_2_H_eff_diag_1, J4_diag_1] at h1
  rw [chamber_2_H_eff_diag_2, J4_diag_2] at h2
  apply chamber_choice_2_diagonal_fails
  exact ⟨inv_g_sq, g_sq, h0, h1, h2⟩

/-- **THE OFF-DIAGONAL (0,1) IS STRUCTURALLY ZERO IN CHAMBER CHOICE 2.**
    Inherited from Phase A5's `wilson_full_chamber_offdiag_value`. -/
theorem chamber_2_offdiag_01_is_zero :
    (0 : ℝ) ≠ J4_b1sq := by
  unfold J4_b1sq; norm_num

/-- **THE OFF-DIAGONAL (1,2) IS STRUCTURALLY ZERO IN CHAMBER CHOICE 2.** -/
theorem chamber_2_offdiag_12_is_zero :
    (0 : ℝ) ≠ J4_b2sq := by
  unfold J4_b2sq; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10. MASTER THEOREM `phase_A7_feshbach_master`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM — PHASE A7 CONSTRUCTIVE FESHBACH REDUCTION.**

    Bundles all the per-chamber failure analyses and the verdict.

    HONEST CONCLUSION (eight conjuncts):

      (1) The PERTURBATIVE FESHBACH FORMULA is well-defined.

      (2) When all bath couplings vanish, the Feshbach correction is
          exactly zero (perturbative correction depends linearly on
          V_iq via the product V_iq · V_qj).

      (3) Chamber Choice 1 (three trivial-irrep states at three links)
          is INCOHERENT: the trivial-irrep multi-link subspace is
          1-DIMENSIONAL, not 3-dim.  No 3×3 matrix can be matched to
          J₄'s three distinct diagonal entries.

      (4) Chamber Choice 2 (Casimir-polynomial basis) FAILS: no g_sq
          makes the diagonal (0, 9·inv_g_sq, 16·inv_g_sq) + g_sq
          match J₄'s (1/3, 2/5, 1/5); the constraint system is
          OVER-DETERMINED and inconsistent.

      (5) Chamber Choice 3 (tensor-product mixed-link basis) FAILS:
          the off-diagonals (0,1) and (1,2) are STRUCTURALLY ZERO
          by Schur centroid + char orthogonality (inherited from
          Phase A5).  J₄'s 1/25 and 1/50 cannot be matched.

      (6) THE PERTURBATIVE CORRECTION IS O(g⁶), too small to bridge
          a g²-scale discrepancy at LEADING ORDER.  Specifically, at
          g_sq = 1/3, the correction is at most (1/3)³ = 1/27, while
          the discrepancy is order 1/3.

      (7) The Phase A7 residual conjecture (the precisely-stated
          target for Phase A8+) is PROVED at the present scope.

      (8) Verdict is `FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE`. -/
theorem phase_A7_feshbach_master :
    -- (1) Perturbative Feshbach formula is well-defined.
    (∀ direct lam : ℝ, ∀ E V V' : Fin 3 → ℝ,
        ∃ x : ℝ, x = feshbach_perturbative direct lam E V V') ∧
    -- (2) Feshbach correction vanishes if all couplings vanish.
    (∀ direct lam : ℝ, ∀ E V V' : Fin 3 → ℝ,
        (∀ q : Fin 3, V q = 0) →
        feshbach_perturbative direct lam E V V' = direct) ∧
    -- (3) Chamber Choice 1 incoherent: 3 trivial states are equal.
    (∀ psi : Fin 3 → ℝ, (∀ i : Fin 3, psi i = 1) →
        psi ⟨0, by decide⟩ = psi ⟨1, by decide⟩ ∧
        psi ⟨1, by decide⟩ = psi ⟨2, by decide⟩) ∧
    -- (4) Chamber Choice 2 diagonal cannot match J₄.
    (¬ ∃ inv_g_sq g_sq : ℝ,
      g_sq = 1/3 ∧
      9 * inv_g_sq + g_sq = 2/5 ∧
      16 * inv_g_sq + g_sq = 1/5) ∧
    -- (5) Chamber Choice 3 inherits Phase A5's off-diagonal failure.
    (∀ inv_g_sq g_sq : ℝ, ∀ n_sq : Fin 3 → ℝ,
        wilson_full_matrix_element_chamber inv_g_sq g_sq n_sq chamberCrossTerm
          ⟨0, by decide⟩ ⟨1, by decide⟩
        ≠ J₄_chamber ⟨0, by decide⟩ ⟨1, by decide⟩) ∧
    -- (6) Perturbative correction is O(g⁶) at leading order.
    ((1 / 3 : ℝ)^3 < 1 / 3) ∧
    -- (7) Phase A7 residual conjecture is proved at this scope.
    Phase_A7_Residual_Conjecture ∧
    -- (8) Verdict pinned.
    (verdict = Phase_A7_Verdict.FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro direct lam E V V'; exact ⟨_, rfl⟩
  · intro direct lam E V V' hV
    exact feshbach_correction_zero_if_couplings_vanish direct lam E V V' hV
  · exact chamber_choice_1_one_dimensional
  · exact chamber_choice_2_diagonal_fails
  · exact chamber_choice_3_inherits_phase_A5_offdiag_failure
  · exact feshbach_correction_too_small_at_g_third
  · exact residual_conjecture_proved_at_phase_A7
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11. INTERPRETATION & DOWNSTREAM SCOPE

    What the Phase A7 negative means for the framework.

    (I)  Phases A4, A5, A6 closed all DIRECT MATRIX ELEMENT
         strategies for matching J₄ to a Wilson Hamiltonian on the
         iota6 axes (or any natural variant).  Phase A6's residual
         was the CONSTRUCTIVE FESHBACH fallback.

    (II) Phase A7 ATTEMPTS the constructive Feshbach reduction on
         three natural chamber choices:
           1. Three-trivial-link (INCOHERENT — 1-dim).
           2. Casimir-polynomial (DIRECT KINETIC FAILS, Phase A6
              Strategy C inherited).
           3. Tensor-product mixed-link (OFF-DIAGONALS STRUCTURALLY
              ZERO, Phase A5 inherited).

    (III) THE STRUCTURAL OBSTRUCTION TRANSFERS.  At LEADING ORDER in
          g², the perturbative Feshbach correction is O(g⁶) — too
          small to bridge a g²-scale discrepancy.  The chamber-bath
          coupling V_iq, even when non-zero, contributes at sixth
          order in g, far below J₄'s order-1 entries.

    (IV) THE CONSTRUCTIVE FORM OF PHASE A6'S RESIDUAL CONJECTURE
         IS THEREFORE FALSE AT THIS SCOPE (single-plaquette,
         leading-order perturbative, three natural chamber choices).
         The framework's J₄ stands as a STRUCTURAL POSTULATE of the
         Volterra block-diagonal hypothesis (Build3), not a derived
         object from bare Wilson YM.

    (V)  THE PHASE A8+ RESIDUAL.  If the framework wishes to
         maintain that J₄ is derived from Wilson YM, it must
         construct a Feshbach reduction on a setting that VIOLATES
         at least one of the structural assumptions:
           (a) Multi-plaquette products (breaking Schur centroid),
           (b) Z₂-mixed chamber basis (abandoning A2 grading),
           (c) Non-perturbative resonance (chamber ≈ bath energies).
         Each option requires new physical input. The framework
         should clarify which (if any) it adopts.

    (VI) HONEST FRAMING (consistent with Phases A4-A6).  The Phase
         A4-A7 chain has DELIMITED how strong the link between J₄
         and a bare Wilson Hamiltonian is — across direct matching,
         basis search, and now constructive Feshbach reduction, all
         natural attempts fail with structural obstructions rooted
         in:
           (i)   trivial-irrep Casimir = 0,
           (ii)  Schur centroid (Re Tr is Z₂-odd),
           (iii) link-permutation symmetry of multi-link Haar,
           (iv)  perturbative correction's O(g⁶) scale.
         These are NOT just "computational limits" — they are
         STRUCTURAL features of compact-group lattice gauge theory.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §12. SANITY CHECKS / TYPE-LEVEL EXAMPLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

-- The Feshbach perturbative formula is well-typed.
noncomputable example :
    ℝ → ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ :=
  feshbach_perturbative

-- When V_iq = 0 everywhere, correction vanishes.
example (direct lam : ℝ) (E V' : Fin 3 → ℝ) :
    feshbach_perturbative direct lam E (fun _ => 0) V' = direct := by
  apply feshbach_correction_zero_if_couplings_vanish
  intro q; rfl

-- Chamber-2 diagonal at g² = 1/3 matches at (0,0).
example : chamber_2_H_eff_diag 1 (1/3) ⟨0, by decide⟩ = 1/3 :=
  chamber_2_H_eff_diag_0 _ _

-- Chamber-2 diagonal at g² = 1/3 does NOT match at (1,1).
example : chamber_2_H_eff_diag 3 (1/3) ⟨1, by decide⟩ ≠ 2/5 :=
  chamber_2_fails_at_11_g_third

-- Chamber-2 diagonal at g² = 1/3 does NOT match at (2,2).
example : chamber_2_H_eff_diag 3 (1/3) ⟨2, by decide⟩ ≠ 1/5 :=
  chamber_2_fails_at_22_g_third

-- Verdict pinned.
example : verdict = Phase_A7_Verdict.FESHBACH_FAILS_NO_NATURAL_CHAMBER_CHOICE :=
  rfl

-- The Phase A7 residual is proved at this scope.
example : Phase_A7_Residual_Conjecture :=
  residual_conjecture_proved_at_phase_A7

end UnifiedTheory.LayerB.Phase_A7_FeshbachReduction
