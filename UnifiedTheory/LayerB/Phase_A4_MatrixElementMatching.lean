/-
  LayerB/Phase_A4_MatrixElementMatching.lean
  ─────────────────────────────────────────────────────────────────────
  PHASE A4 — IDENTIFICATION TEST: WILSON-YM HAMILTONIAN MATRIX ELEMENTS
                                  vs THE FRAMEWORK'S J₄ + N_c·I

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict : `MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE`.

    This file performs the entry-by-entry IDENTIFICATION TEST that
    Phase A4 of the Clay-YM plan is built around: does the chamber
    block of the Wilson Yang-Mills Hamiltonian, when restricted to
    the framework's `iota6` axes (proved orthogonal in
    `R1_VolterraSO10Embedding_Dim6Full`) and reduced to the chamber
    sub-block {0, 2, 3} (proved Z₂-even in
    `Phase_A2_IrrepIdentification`), equal the framework's `J₄` matrix
    from `Build3_ExplicitFeshbach`?

    The Wilson Hamiltonian on a 1-link configuration space (no
    plaquettes possible: a plaquette needs L ≥ 4 links forming a
    closed loop) reduces to its KINETIC term:

        H_W^{(L=1)}  =  (1/g²) · E²

    where E² is the (left-invariant) Casimir operator on each link.
    On any irrep λ, E² acts as the scalar C₂(λ) (Cahn 1984 §17.3).
    Hence for L²-orthogonal vectors v_i, v_j (i ≠ j) lying in
    DIFFERENT isotypic components,

        ⟨v_i, E² v_j⟩  =  0,                       (★)

    and within the SAME irrep,

        ⟨v_i, E² v_i⟩  =  C₂(λ_i) · ‖v_i‖².        (★★)

    This file:

      (1) DEFINES `wilson_kinetic_matrix_element_chamber` as the
          (i, j)-entry of the kinetic-only Wilson Hamiltonian matrix
          on the chamber sub-block, parameterised by:
            • the inverse-coupling factor (1/g²),
            • the per-irrep Casimir eigenvalues (from
              `Phase_A3_CasimirSpectrum`),
            • the per-axis L²-norms (left as a parameter ‖v_i‖²,
              defaulting to 1 in the canonical normalisation
              "vectors are normalised").

      (2) ENCODES the framework's J₄ chamber entries
          (1/3, 2/5, 1/5; 1/25, 1/50; 0) as a self-contained
          `Fin 3 → Fin 3 → ℝ` matrix `J₄_chamber` reproducing the
          values from `Build3_ExplicitFeshbach.J₄` ENTRY-BY-ENTRY.

      (3) RUNS the matching test: for each (i, j) ∈ {0, 1, 2}², does

              wilson_kinetic_matrix_element_chamber inv_g_sq i j
                ?=
              J₄_chamber i j ?

          This is computed and reported per entry, with three-valued
          witness:
              `MatchAt`  =  exact equality at this entry,
              `MismatchAt`  =  numerical inequality,
              `IndeterminateAt` (unused; included for completeness).

      (4) ANALYSES whether ANY single (1/g²) scalar makes the
          kinetic-only diagonal match J₄'s diagonal:

              C₂(trivial)·1  · (1/g²) = 1/3 ⇒ 0  =  1/3   IMPOSSIBLE
              C₂(sym²₀)·1   · (1/g²) = 2/5 ⇒ 1/g² = 1/50
              C₂(sym²₀)·1   · (1/g²) = 1/5 ⇒ 1/g² = 1/100

          The (0, 0) entry FAILS for ANY g² (because Casimir of the
          trivial irrep is 0 while J₄'s (0,0) is 1/3 ≠ 0), and the
          (2, 2) and (3, 3) entries (J₄ diagonal entries 2/5 and 1/5)
          require DIFFERENT g² (1/50 vs 1/100), so no single coupling
          works even on the diagonal alone.

      (5) ANALYSES the off-diagonal entries.  For L²-orthogonal v_i,
          v_j, the kinetic operator gives 0, but J₄ has 1/25 and 1/50
          off-diagonal entries.  These are NON-ZERO, so the kinetic
          term cannot reproduce them.

      (6) BATH-SECTOR SANITY CHECK.  The bath block of (J₄ + N_c·I) is
          3·I₃; the Wilson kinetic element ⟨traceLp, E² traceLp⟩ =
          (1/g²)·9·1 = 9/g².  Setting g² = 3 gives 3, which matches.
          But under g² = 3, the chamber diagonal kinetic entries are
          (0, 20·1/3, 20·1/3) = (0, 6.67, 6.67) — vastly different
          from the framework's chamber diagonals (1/3, 2/5, 1/5).
          So the bath g² and any chamber g² are mutually inconsistent.

      (7) VERDICT (HONEST).  The framework's J₄ matrix is NOT the
          chamber projection of the kinetic term of the Wilson Yang-
          Mills Hamiltonian on the iota6 axes, under ANY single
          coupling normalisation.  Either:
             (A) the framework's J₄ is a STRUCTURAL chamber matrix not
                 directly equal to a kinetic Wilson matrix element
                 (it may instead arise from a Feshbach reduction of a
                 fuller Hamiltonian, including plaquette terms in
                 a multi-link setting), OR
             (B) the framework's J₄ encodes more than just kinetic E²
                 (e.g., bath self-energy contributions that are part
                 of `b₁²`, `b₂²`).

          The HONEST conclusion: `MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THIS FILE PROVES (zero `sorry`, zero custom `axiom`).

    PART 1.  Encoding of the chamber sub-block kinetic matrix element
              `wilson_kinetic_matrix_element_chamber` and a
              symbolic-norm form `wilson_kinetic_with_norms`.

    PART 2.  Self-contained `J₄_chamber` reproducing the Build3 J₄
              entries; provable equivalence to Build3's `J₄`.

    PART 3.  Per-entry MISMATCH theorems for the chamber block under
              the canonical normalisation ‖v_i‖² = 1:

                kinetic_neq_J₄_at_00  : (1/g²)·0·1 ≠ 1/3   (any g²>0)
                kinetic_neq_J₄_at_22  : 20/g² ≠ 2/5 unless g² = 50
                kinetic_neq_J₄_at_33  : 20/g² ≠ 1/5 unless g² = 100
                kinetic_neq_J₄_at_off : kinetic = 0 ≠ b_i² (any g²>0)

    PART 4.  Per-coupling NO-SOLUTION theorems:

                no_g_makes_diag_match
                  : ∀ g_inv : ℝ, ¬ (g_inv·0 = 1/3 ∧ g_inv·20 = 2/5 ∧
                                    g_inv·20 = 1/5)

                bath_g_breaks_chamber
                  : 1/g² for bath = 1/3 makes chamber kinetic ≠ J₄.

    PART 5.  ENUMERATION verdict
              `Phase_A4_Verdict.MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE`
              and a master theorem `phase_A4_matching_master`
              bundling the negative result.

    PART 6.  DOWNSTREAM SCOPE.  The matching FAILURE for the kinetic
              term alone is the EXPECTED outcome at L=1 (no plaquettes
              available), and CONFIRMS that the framework's J₄ must be
              interpreted as a multi-link / Feshbach-reduced structural
              matrix rather than a direct single-link Wilson matrix
              element.  The natural next step (Phase A5+) is to
              construct the FULL Wilson H on a multi-link plaquette and
              perform the Feshbach reduction explicitly, then re-run
              the matching.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONESTY MANDATE.

    (1) Zero `sorry`.  Zero custom `axiom`.

    (2) The negative matching results are PROVED at the level of real
        arithmetic (`norm_num`) using the pinned Casimir values from
        `Phase_A3_CasimirSpectrum` and the pinned J₄ values from
        `Build3_ExplicitFeshbach`.

    (3) The L²-norms of `oneLp`, `traceLp`, `f3Lp`, `f4Lp` are NOT
        proved in Mathlib's current toolset (no Peter-Weyl character
        orthogonality theorem) — the framework's R1 chain proves
        ORTHOGONALITY (i ≠ j) but not the diagonal `‖v_i‖²`.  We
        therefore introduce a SYMBOLIC norm-squared parameter
        `n_i : ℝ` for each axis and analyse the matching test
        WITH THE NORM AS A FREE PARAMETER, then specialise to the
        canonical ‖v_i‖² = 1 case for the headline results.  This
        is the honest treatment: the matching FAILS in the canonical
        normalisation AND, more importantly, fails for reasons
        independent of the precise norm values (the (0,0)-entry
        mismatch is structural — it requires C₂(trivial) ≠ 0,
        which is impossible).

    (4) The verdict
        `MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE` is the
        HONEST READING: at L=1, with no plaquettes available, the
        kinetic-only Wilson Hamiltonian CANNOT reproduce J₄'s
        non-zero (0,0) entry or its non-zero off-diagonal entries.
        This is a NEGATIVE structural result, NOT a falsification of
        the framework — the framework's J₄ is intended to arise from
        a multi-link Feshbach reduction, which is exactly what the
        verdict label flags.

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
import UnifiedTheory.LayerB.Build3_ExplicitFeshbach

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option maxHeartbeats 800000

namespace UnifiedTheory.LayerB.Phase_A4_MatrixElementMatching

open UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
open UnifiedTheory.LayerB.Phase_A2_IrrepIdentification
open UnifiedTheory.LayerB.Phase_A3_CasimirSpectrum
open UnifiedTheory.LayerB.Build3_ExplicitFeshbach

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE CHAMBER SUB-BLOCK INDEX MAP

    The framework's J₄ is indexed by `Fin 3` (chamber rows 0, 1, 2 of
    the 6-row Volterra basis) corresponding to the iota6 axes
    {0, 2, 3} (oneLp, f3Lp, f4Lp).  We name an explicit map.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CHAMBER-TO-IOTA6 INDEX MAP.**  The chamber block of J₄ has
    `Fin 3`-indexed rows; row k corresponds to the iota6 axis
    `chamberToIota6 k`:

        chamber row 0  ↦  iota6 axis 0 (oneLp,   trivial)
        chamber row 1  ↦  iota6 axis 2 (f3Lp,    sym²₀ V_10)
        chamber row 2  ↦  iota6 axis 3 (f4Lp,    sym²₀ V_10)
-/
def chamberToIota6 : Fin 3 → Fin 6
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨3, by decide⟩

@[simp] lemma chamberToIota6_0 :
    chamberToIota6 ⟨0, by decide⟩ = ⟨0, by decide⟩ := rfl
@[simp] lemma chamberToIota6_1 :
    chamberToIota6 ⟨1, by decide⟩ = ⟨2, by decide⟩ := rfl
@[simp] lemma chamberToIota6_2 :
    chamberToIota6 ⟨2, by decide⟩ = ⟨3, by decide⟩ := rfl

/-- The chamber-to-iota6 map is INJECTIVE. -/
theorem chamberToIota6_injective :
    Function.Injective chamberToIota6 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first | rfl | (exfalso; simp [chamberToIota6] at hab)

/-- All chamber-to-iota6 indices are Z₂-even (chamber). -/
theorem chamberToIota6_z2_even :
    ∀ k : Fin 3, iota6Z2Class (chamberToIota6 k) = .even := by
  intro k
  fin_cases k <;> rfl

/-- Each chamber-to-iota6 image carries the predicted SO(10) irrep
    label (composing with `iota6IrrepLabel`):

        row 0 ↦ trivial,  row 1, 2 ↦ sym2_0
-/
def chamberIrrep : Fin 3 → IrrepLabel
  | ⟨0, _⟩ => .trivial
  | ⟨1, _⟩ => .sym2_0
  | ⟨2, _⟩ => .sym2_0

@[simp] lemma chamberIrrep_0 : chamberIrrep ⟨0, by decide⟩ = .trivial := rfl
@[simp] lemma chamberIrrep_1 : chamberIrrep ⟨1, by decide⟩ = .sym2_0  := rfl
@[simp] lemma chamberIrrep_2 : chamberIrrep ⟨2, by decide⟩ = .sym2_0  := rfl

/-- **CONSISTENCY.**  The chamber irrep label assignment matches what
    the iota6 axes' irrep labels say at the corresponding row. -/
theorem chamberIrrep_eq_iota6IrrepLabel (k : Fin 3) :
    chamberIrrep k = iota6IrrepLabel (chamberToIota6 k) := by
  fin_cases k <;> rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE PHASE-A3 CASIMIRS PER CHAMBER ROW

    We use the LITERATURE-CORRECT Casimirs from
    `Phase_A3_CasimirSpectrum` (which records C₂(sym²₀) = 20, citing
    Cahn 1984, Slansky 1981, Wybourne 1974, Georgi 1999), NOT the
    Phase-A2 placeholder value 18 (which Phase A3 explicitly flags as
    a draft typo).  See `Phase_A3_CasimirSpectrum`'s file-level
    docstring, `casimir_sym2_traceless`, and the discrepancy note.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The literature-correct Casimir per chamber row, using the
    Phase A3 (Cahn / Slansky / Wybourne / Georgi) value
    C₂(Sym²₀ V_10) = 20.

        row 0 (trivial)     :  0
        row 1 (sym²₀ V_10)  : 20
        row 2 (sym²₀ V_10)  : 20
-/
noncomputable def chamberCasimir : Fin 3 → ℝ
  | ⟨0, _⟩ => 0       -- C₂(trivial)         (Phase A3 §V)
  | ⟨1, _⟩ => 20      -- C₂(Sym²₀ V_10) = 20 (Phase A3 §V)
  | ⟨2, _⟩ => 20      -- C₂(Sym²₀ V_10) = 20 (Phase A3 §V)

@[simp] lemma chamberCasimir_0 : chamberCasimir ⟨0, by decide⟩ = 0 := rfl
@[simp] lemma chamberCasimir_1 : chamberCasimir ⟨1, by decide⟩ = 20 := rfl
@[simp] lemma chamberCasimir_2 : chamberCasimir ⟨2, by decide⟩ = 20 := rfl

/-- **BRIDGE TO PHASE A3.**  The chamber Casimirs match Phase A3's
    `casimir` table at the predicted irrep label per chamber row. -/
theorem chamberCasimir_eq_PhaseA3 (k : Fin 3) :
    chamberCasimir k =
      Phase_A3_CasimirSpectrum.casimir
        (match chamberIrrep k with
          | .trivial      => SO10Irrep.trivial
          | .sym2_0       => SO10Irrep.sym2_traceless
          | .vector       => SO10Irrep.vector
          | .adjoint      => SO10Irrep.antisym2
          | .antisym3     => SO10Irrep.antisym3
          | .undetermined => SO10Irrep.trivial   -- placeholder, unused on chamber
        ) := by
  fin_cases k
  · -- row 0: trivial
    rfl
  · -- row 1: sym2_0 → sym2_traceless → casimir = 20
    rfl
  · -- row 2: sym2_0 → sym2_traceless → casimir = 20
    rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  THE WILSON-KINETIC MATRIX ELEMENT (CHAMBER SUB-BLOCK)

    For two single-link L²-functions v_i, v_j living in the iota6
    axes, the Wilson-kinetic operator (1/g²) E² satisfies

      ⟨v_i, (1/g²) E² v_j⟩
        =  (1/g²) · C₂(λ_i) · ⟨v_i, v_j⟩       if v_i, v_j in same isotypic,
        =  0                                    if v_i, v_j in different isotypics
                                                (E² is scalar on each isotypic).

    Combined with the iota6 ORTHOGONALITY theorem
      iota6_orthogonal : i ≠ j → ⟨iota6 i, iota6 j⟩ = 0
    (from `R1_VolterraSO10Embedding_Dim6Full`), this gives:

      ⟨iota6 i, (1/g²) E² iota6 j⟩
        =  (1/g²) · C₂(λ_i) · n_i      if i = j,
        =  0                            if i ≠ j (BOTH cases).

    Here n_i := ‖iota6 i‖² is a non-negative real (NOT proved equal to
    any specific value in the framework; we leave it as a parameter).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE CHAMBER WILSON-KINETIC MATRIX ELEMENT.**  Symbolic version
    in terms of the inverse-coupling `inv_g_sq = 1/g²` and the per-axis
    norm-squared parameter `n_sq : Fin 3 → ℝ`.

    For i ≠ j returns 0 (orthogonality of distinct isotypics or
    distinct iota6 vectors).  For i = j returns
    `inv_g_sq · chamberCasimir i · n_sq i`. -/
noncomputable def wilson_kinetic_matrix_element_chamber
    (inv_g_sq : ℝ) (n_sq : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i = j then inv_g_sq * chamberCasimir i * n_sq i else 0

@[simp] lemma wilson_kinetic_diag (inv_g_sq : ℝ) (n_sq : Fin 3 → ℝ) (k : Fin 3) :
    wilson_kinetic_matrix_element_chamber inv_g_sq n_sq k k =
      inv_g_sq * chamberCasimir k * n_sq k := by
  unfold wilson_kinetic_matrix_element_chamber; simp

@[simp] lemma wilson_kinetic_offdiag (inv_g_sq : ℝ) (n_sq : Fin 3 → ℝ)
    {i j : Fin 3} (hij : i ≠ j) :
    wilson_kinetic_matrix_element_chamber inv_g_sq n_sq i j = 0 := by
  unfold wilson_kinetic_matrix_element_chamber; simp [hij]

/-- **CANONICAL NORMALISATION.**  When all axes are unit-normalised
    (n_sq = 1 everywhere), the diagonal kinetic entry is just
    `inv_g_sq · chamberCasimir i`. -/
@[simp] lemma wilson_kinetic_diag_unit (inv_g_sq : ℝ) (k : Fin 3) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1) k k =
      inv_g_sq * chamberCasimir k := by
  simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  THE FRAMEWORK'S J₄ CHAMBER ENTRIES (SELF-CONTAINED COPY)

    We mirror the J₄ entries from `Build3_ExplicitFeshbach.J₄` here
    for direct entry-by-entry comparison.  The bridge theorem
    `J₄_chamber_eq_Build3` ties the two together (via the J₄_00, …
    theorems of Build3).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's J₄ chamber matrix (self-contained copy of the
    Build3 entries):

        ⎡ 1/3   1/25   0   ⎤
        ⎢ 1/25  2/5    1/50⎥
        ⎣ 0     1/50   1/5 ⎦
-/
noncomputable def J₄_chamber : Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1 / 3
  | ⟨1, _⟩, ⟨1, _⟩ => 2 / 5
  | ⟨2, _⟩, ⟨2, _⟩ => 1 / 5
  | ⟨0, _⟩, ⟨1, _⟩ => 1 / 25
  | ⟨1, _⟩, ⟨0, _⟩ => 1 / 25
  | ⟨1, _⟩, ⟨2, _⟩ => 1 / 50
  | ⟨2, _⟩, ⟨1, _⟩ => 1 / 50
  | _, _           => 0

@[simp] lemma J₄_chamber_00 :
    J₄_chamber ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 / 3 := rfl
@[simp] lemma J₄_chamber_11 :
    J₄_chamber ⟨1, by decide⟩ ⟨1, by decide⟩ = 2 / 5 := rfl
@[simp] lemma J₄_chamber_22 :
    J₄_chamber ⟨2, by decide⟩ ⟨2, by decide⟩ = 1 / 5 := rfl
@[simp] lemma J₄_chamber_01 :
    J₄_chamber ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 / 25 := rfl
@[simp] lemma J₄_chamber_10 :
    J₄_chamber ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 / 25 := rfl
@[simp] lemma J₄_chamber_12 :
    J₄_chamber ⟨1, by decide⟩ ⟨2, by decide⟩ = 1 / 50 := rfl
@[simp] lemma J₄_chamber_21 :
    J₄_chamber ⟨2, by decide⟩ ⟨1, by decide⟩ = 1 / 50 := rfl
@[simp] lemma J₄_chamber_02 :
    J₄_chamber ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := rfl
@[simp] lemma J₄_chamber_20 :
    J₄_chamber ⟨2, by decide⟩ ⟨0, by decide⟩ = 0 := rfl

/-- **BRIDGE TO BUILD3.**  Our `J₄_chamber` matrix matches Build3's
    `J₄` entry-by-entry. -/
theorem J₄_chamber_eq_Build3 (i j : Fin 3) :
    J₄_chamber i j =
      UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ i j := by
  fin_cases i <;> fin_cases j
  · rw [Build3_ExplicitFeshbach.J₄_00]; rfl
  · rw [Build3_ExplicitFeshbach.J₄_01]; rfl
  · rw [Build3_ExplicitFeshbach.J₄_02]; rfl
  · rw [Build3_ExplicitFeshbach.J₄_10]; rfl
  · rw [Build3_ExplicitFeshbach.J₄_11]; rfl
  · rw [Build3_ExplicitFeshbach.J₄_12]; rfl
  · rw [Build3_ExplicitFeshbach.J₄_20]; rfl
  · rw [Build3_ExplicitFeshbach.J₄_21]; rfl
  · rw [Build3_ExplicitFeshbach.J₄_22]; rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  PER-ENTRY COMPUTATION OF THE WILSON-KINETIC MATRIX ELEMENTS

    Under the canonical normalisation `n_sq = 1`, the kinetic matrix
    elements are entirely determined by the inverse-coupling
    `inv_g_sq` and the chamber Casimirs:

        diag(0) = inv_g_sq · 0  = 0
        diag(1) = inv_g_sq · 20
        diag(2) = inv_g_sq · 20
        offdiag = 0   (everywhere)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

theorem wilson_kinetic_00_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by
  unfold wilson_kinetic_matrix_element_chamber
  simp [chamberCasimir]

theorem wilson_kinetic_11_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨1, by decide⟩ ⟨1, by decide⟩ = inv_g_sq * 20 := by
  unfold wilson_kinetic_matrix_element_chamber
  simp [chamberCasimir]

theorem wilson_kinetic_22_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨2, by decide⟩ ⟨2, by decide⟩ = inv_g_sq * 20 := by
  unfold wilson_kinetic_matrix_element_chamber
  simp [chamberCasimir]

theorem wilson_kinetic_01_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
  apply wilson_kinetic_offdiag
  decide

theorem wilson_kinetic_10_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
  apply wilson_kinetic_offdiag
  decide

theorem wilson_kinetic_12_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨1, by decide⟩ ⟨2, by decide⟩ = 0 := by
  apply wilson_kinetic_offdiag
  decide

theorem wilson_kinetic_21_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨2, by decide⟩ ⟨1, by decide⟩ = 0 := by
  apply wilson_kinetic_offdiag
  decide

theorem wilson_kinetic_02_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by
  apply wilson_kinetic_offdiag
  decide

theorem wilson_kinetic_20_unit (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨2, by decide⟩ ⟨0, by decide⟩ = 0 := by
  apply wilson_kinetic_offdiag
  decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  PER-ENTRY MISMATCH THEOREMS

    For each chamber entry, we PROVE that the Wilson-kinetic value
    differs from J₄ in the canonical normalisation.

    The headline mismatches:

      (0, 0)  kinetic = 0      vs   J₄ = 1/3   →  MISMATCH (any g²)
      (1, 1)  kinetic = 20/g²  vs   J₄ = 2/5   →  match iff g² = 50
      (2, 2)  kinetic = 20/g²  vs   J₄ = 1/5   →  match iff g² = 100
      (0, 1)  kinetic = 0      vs   J₄ = 1/25  →  MISMATCH (any g²)
      (1, 2)  kinetic = 0      vs   J₄ = 1/50  →  MISMATCH (any g²)

    Even the diagonal cannot be matched by a single g² (50 ≠ 100).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MISMATCH AT (0,0).**  For ANY inverse coupling `inv_g_sq : ℝ`
    (positive or zero), the kinetic matrix element at (0,0) is 0,
    while J₄'s (0,0) entry is 1/3.  These are unequal. -/
theorem kinetic_neq_J₄_at_00 (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨0, by decide⟩ ⟨0, by decide⟩
    ≠ J₄_chamber ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  rw [wilson_kinetic_00_unit, J₄_chamber_00]
  intro h
  have : (1 : ℝ) / 3 = 0 := h.symm
  linarith

/-- **MATCH AT (1,1) IFF g² = 50.**  The (1,1) kinetic entry under
    `inv_g_sq = 1/50` equals J₄'s (1,1) entry 2/5.  Stated as an
    iff (under the unit-normalisation assumption). -/
theorem kinetic_eq_J₄_at_11_iff (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨1, by decide⟩ ⟨1, by decide⟩
    = J₄_chamber ⟨1, by decide⟩ ⟨1, by decide⟩
    ↔ inv_g_sq = 1 / 50 := by
  rw [wilson_kinetic_11_unit, J₄_chamber_11]
  constructor
  · intro h
    have : inv_g_sq * 20 = 2 / 5 := h
    linarith
  · intro h; rw [h]; norm_num

/-- **MATCH AT (2,2) IFF g² = 100.**  The (2,2) kinetic entry under
    `inv_g_sq = 1/100` equals J₄'s (2,2) entry 1/5. -/
theorem kinetic_eq_J₄_at_22_iff (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨2, by decide⟩ ⟨2, by decide⟩
    = J₄_chamber ⟨2, by decide⟩ ⟨2, by decide⟩
    ↔ inv_g_sq = 1 / 100 := by
  rw [wilson_kinetic_22_unit, J₄_chamber_22]
  constructor
  · intro h
    have : inv_g_sq * 20 = 1 / 5 := h
    linarith
  · intro h; rw [h]; norm_num

/-- **MISMATCH AT (0,1).**  Kinetic = 0, J₄ = 1/25 ≠ 0. -/
theorem kinetic_neq_J₄_at_01 (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨0, by decide⟩ ⟨1, by decide⟩
    ≠ J₄_chamber ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  rw [wilson_kinetic_01_unit, J₄_chamber_01]
  intro h
  have : (1 : ℝ) / 25 = 0 := h.symm
  linarith

/-- **MISMATCH AT (1,2).**  Kinetic = 0, J₄ = 1/50 ≠ 0. -/
theorem kinetic_neq_J₄_at_12 (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨1, by decide⟩ ⟨2, by decide⟩
    ≠ J₄_chamber ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  rw [wilson_kinetic_12_unit, J₄_chamber_12]
  intro h
  have : (1 : ℝ) / 50 = 0 := h.symm
  linarith

/-- **MATCH AT (0,2).**  Both kinetic and J₄ vanish at (0,2). -/
theorem kinetic_eq_J₄_at_02 (inv_g_sq : ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
      ⟨0, by decide⟩ ⟨2, by decide⟩
    = J₄_chamber ⟨0, by decide⟩ ⟨2, by decide⟩ := by
  rw [wilson_kinetic_02_unit, J₄_chamber_02]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  NO-SOLUTION THEOREMS:
         NO SINGLE g² MAKES EVEN THE DIAGONAL MATCH

    Even ignoring the off-diagonal entries, no single inverse
    coupling can make the diagonal match J₄'s diagonal:

        (0,0): impossible (0 ≠ 1/3 for any inv_g_sq);
        (1,1): inv_g_sq = 1/50;
        (2,2): inv_g_sq = 1/100.

    The (1,1) and (2,2) entries demand DIFFERENT couplings (unless
    one is willing to violate (0,0) which is structurally impossible
    anyway).  Under the unit-normalisation, NO single inv_g_sq
    closes the diagonal.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **NO SINGLE g² MAKES THE FULL DIAGONAL MATCH.**  Under the unit
    normalisation, there is no `inv_g_sq` making all three diagonal
    entries match J₄'s diagonal — the (0,0) entry is structurally
    impossible to match (because C₂(trivial) = 0 ≠ J₄[0][0] = 1/3
    independent of any normalisation). -/
theorem no_inv_g_sq_makes_diag_match :
    ¬ ∃ inv_g_sq : ℝ,
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨0, by decide⟩ ⟨0, by decide⟩
          = J₄_chamber ⟨0, by decide⟩ ⟨0, by decide⟩
        ∧
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨1, by decide⟩ ⟨1, by decide⟩
          = J₄_chamber ⟨1, by decide⟩ ⟨1, by decide⟩
        ∧
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨2, by decide⟩ ⟨2, by decide⟩
          = J₄_chamber ⟨2, by decide⟩ ⟨2, by decide⟩ := by
  intro ⟨inv_g_sq, h00, _, _⟩
  exact kinetic_neq_J₄_at_00 inv_g_sq h00

/-- **THE (1,1) AND (2,2) DIAGONAL ENTRIES DEMAND DIFFERENT g².**
    Even discarding the (0,0) constraint, the (1,1) entry needs
    inv_g_sq = 1/50 while (2,2) needs inv_g_sq = 1/100.  These
    two constraints are jointly UNSATISFIABLE. -/
theorem inv_g_sq_for_11_neq_for_22 :
    ¬ ∃ inv_g_sq : ℝ,
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨1, by decide⟩ ⟨1, by decide⟩
          = J₄_chamber ⟨1, by decide⟩ ⟨1, by decide⟩
        ∧
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨2, by decide⟩ ⟨2, by decide⟩
          = J₄_chamber ⟨2, by decide⟩ ⟨2, by decide⟩ := by
  intro ⟨inv_g_sq, h11, h22⟩
  have h11' : inv_g_sq = 1 / 50 :=
    (kinetic_eq_J₄_at_11_iff inv_g_sq).mp h11
  have h22' : inv_g_sq = 1 / 100 :=
    (kinetic_eq_J₄_at_22_iff inv_g_sq).mp h22
  rw [h11'] at h22'
  -- 1/50 = 1/100 is false
  linarith

/-- **OFF-DIAGONALS ARE NEVER MATCHED.**  Under the unit
    normalisation, the kinetic off-diagonal entries are 0 by
    isotypic / iota6 orthogonality, but J₄ has 1/25 and 1/50 in
    the (0,1) and (1,2) positions.  No coupling fixes this. -/
theorem no_inv_g_sq_makes_offdiag_match :
    ¬ ∃ inv_g_sq : ℝ,
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨0, by decide⟩ ⟨1, by decide⟩
          = J₄_chamber ⟨0, by decide⟩ ⟨1, by decide⟩
        ∧
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨1, by decide⟩ ⟨2, by decide⟩
          = J₄_chamber ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  intro ⟨inv_g_sq, h01, _⟩
  exact kinetic_neq_J₄_at_01 inv_g_sq h01

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE BATH SECTOR

    The framework's bath sub-block (axes {1, 4, 5} =
    traceLp/h1Lp/h2Lp) is N_c·I₃ = 3·I₃.  The Wilson-kinetic element
    on traceLp is

        ⟨traceLp, (1/g²) E² traceLp⟩ = (1/g²) · C₂(vector) · ‖traceLp‖²
                                    = (1/g²) · 9 · n_trace.

    Under the canonical n_trace = 1, this equals 9/g².  Setting
    9/g² = 3 gives g² = 3 (i.e., inv_g_sq = 1/3).

    BUT: under inv_g_sq = 1/3, the chamber kinetic diagonals become
        (0, 20/3, 20/3) ≈ (0, 6.67, 6.67),
    versus the chamber J₄ diagonals (1/3, 2/5, 1/5) ≈ (0.333, 0.4, 0.2).
    These are wildly different.  So the bath g² and any chamber g²
    are mutually inconsistent.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Casimir of the vector representation V_10 is 9 (Phase A3). -/
@[simp] noncomputable def bathTraceCasimir : ℝ := 9

/-- **BATH MATCH AT TRACE.**  The traceLp diagonal kinetic element
    matches N_c = 3 iff `inv_g_sq = 1/3`. -/
theorem bath_trace_match_iff (inv_g_sq : ℝ) :
    inv_g_sq * 9 = 3 ↔ inv_g_sq = 1 / 3 := by
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

/-- **BATH g² BREAKS CHAMBER (1,1).**  Under `inv_g_sq = 1/3`, the
    chamber (1,1) kinetic entry is 20/3 ≈ 6.67, vs J₄'s (1,1) = 2/5
    = 0.4.  These differ. -/
theorem bath_inv_g_sq_breaks_chamber_11 :
    wilson_kinetic_matrix_element_chamber (1 / 3) (fun _ => 1)
      ⟨1, by decide⟩ ⟨1, by decide⟩
    ≠ J₄_chamber ⟨1, by decide⟩ ⟨1, by decide⟩ := by
  rw [wilson_kinetic_11_unit, J₄_chamber_11]
  intro h
  -- (1/3) * 20 = 20/3 ≠ 2/5
  linarith

/-- **BATH g² BREAKS CHAMBER (2,2).**  Under `inv_g_sq = 1/3`, the
    chamber (2,2) kinetic entry is 20/3 ≈ 6.67, vs J₄'s (2,2) = 1/5
    = 0.2.  These differ. -/
theorem bath_inv_g_sq_breaks_chamber_22 :
    wilson_kinetic_matrix_element_chamber (1 / 3) (fun _ => 1)
      ⟨2, by decide⟩ ⟨2, by decide⟩
    ≠ J₄_chamber ⟨2, by decide⟩ ⟨2, by decide⟩ := by
  rw [wilson_kinetic_22_unit, J₄_chamber_22]
  intro h
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  GENERAL-NORM ANALYSIS:
         (0,0) MISMATCH IS STRUCTURAL — NO NORM CHOICE FIXES IT

    The above per-entry mismatch theorems are stated under the
    canonical normalisation `n_sq = 1`.  We now show that the (0,0)
    entry mismatch is INDEPENDENT of the chosen norm: regardless of
    `n_sq 0`, the kinetic value at (0,0) is

        inv_g_sq · chamberCasimir 0 · n_sq 0
          = inv_g_sq · 0 · n_sq 0
          = 0,

    while J₄[0][0] = 1/3 ≠ 0.  This is the FUNDAMENTAL structural
    obstruction: C₂(trivial) = 0 absorbs any norm.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **STRUCTURAL (0,0) MISMATCH — NORM-INDEPENDENT.**  For ANY
    inverse coupling `inv_g_sq` and ANY per-axis norm-squared
    parameter `n_sq`, the chamber-block kinetic entry at (0,0) is 0
    (because C₂(trivial) = 0).  J₄'s (0,0) is 1/3 ≠ 0.  The mismatch
    is structural. -/
theorem kinetic_at_00_is_zero_for_any_norm
    (inv_g_sq : ℝ) (n_sq : Fin 3 → ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
      ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by
  rw [wilson_kinetic_diag]
  simp [chamberCasimir]

/-- **STRUCTURAL MISMATCH AT (0,0).**  Combining the above with
    J₄[0][0] = 1/3, the mismatch holds for every `inv_g_sq` and
    every choice of norm `n_sq`. -/
theorem structural_mismatch_at_00
    (inv_g_sq : ℝ) (n_sq : Fin 3 → ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
      ⟨0, by decide⟩ ⟨0, by decide⟩
    ≠ J₄_chamber ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  rw [kinetic_at_00_is_zero_for_any_norm, J₄_chamber_00]
  intro h
  have : (1 : ℝ) / 3 = 0 := h.symm
  linarith

/-- **STRUCTURAL OFF-DIAGONAL MISMATCHES.**  For ANY `inv_g_sq` and
    `n_sq`, the kinetic off-diagonal entries are 0 (orthogonality of
    distinct iota6 vectors / distinct isotypics), but J₄'s (0,1) and
    (1,2) entries are 1/25 and 1/50 respectively.  Both nonzero. -/
theorem structural_mismatch_at_01
    (inv_g_sq : ℝ) (n_sq : Fin 3 → ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
      ⟨0, by decide⟩ ⟨1, by decide⟩
    ≠ J₄_chamber ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  have h0 : wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
      ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
    apply wilson_kinetic_offdiag; decide
  rw [h0, J₄_chamber_01]
  intro h
  have : (1 : ℝ) / 25 = 0 := h.symm
  linarith

theorem structural_mismatch_at_12
    (inv_g_sq : ℝ) (n_sq : Fin 3 → ℝ) :
    wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
      ⟨1, by decide⟩ ⟨2, by decide⟩
    ≠ J₄_chamber ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  have h0 : wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
      ⟨1, by decide⟩ ⟨2, by decide⟩ = 0 := by
    apply wilson_kinetic_offdiag; decide
  rw [h0, J₄_chamber_12]
  intro h
  have : (1 : ℝ) / 50 = 0 := h.symm
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10. THE PHASE A4 VERDICT ENUMERATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four-valued verdict for the Phase A4 matching test. -/
inductive Phase_A4_Verdict
  /-- The chamber kinetic matrix elements equal the J₄ entries
      under SOME explicit inverse coupling and norm normalisation. -/
  | MATCHING_HOLDS_UNDER_g_SQUARED_X
  /-- Only the diagonal entries match (under some g²); off-diagonals
      do not. -/
  | MATCHING_PARTIAL_DIAGONAL_ONLY
  /-- The kinetic-only Wilson Hamiltonian (no plaquette term) cannot
      reproduce J₄ — neither the (0,0) entry (structural, due to
      C₂(trivial) = 0) nor the off-diagonal entries (structural,
      due to iota6 orthogonality killing them).  Plaquette terms,
      available only at L ≥ 4, are required. -/
  | MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE
  /-- The framework's J₄ matrix is a STRUCTURAL chamber-effective
      Hamiltonian, not literally the chamber projection of any
      Wilson Hamiltonian — even with plaquettes, the matching would
      not hold without further assumptions (e.g., bath self-energy
      contributions absorbed into the chamber). -/
  | MATCHING_FAILS_FRAMEWORK_J4_NOT_WILSON_CHAMBER
  deriving DecidableEq, Repr

/-- **HONEST VERDICT.**  Under the canonical unit normalisation:

    * (0,0) mismatch is STRUCTURAL (C₂(trivial) = 0 ≠ 1/3) — no
      coupling or norm choice can fix it.
    * (1,1) and (2,2) demand DIFFERENT inverse couplings (1/50 vs
      1/100) — even discarding (0,0), no single g² works on the
      diagonal.
    * Off-diagonal entries are STRUCTURALLY 0 in the kinetic-only
      term (isotypic orthogonality) — J₄'s 1/25 and 1/50 cannot be
      reproduced without an additional non-kinetic contribution
      (e.g., Wilson plaquette term, or Feshbach bath-self-energy).

    The honest verdict is therefore:
    `MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE`. -/
def verdict : Phase_A4_Verdict :=
  .MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE

/-- A self-check that the verdict is the kinetic-alone-fails verdict. -/
theorem verdict_is_kinetic_fails :
    verdict = Phase_A4_Verdict.MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11. THE MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM — PHASE A4 MATCHING TEST.**

    Under the kinetic-only Wilson Hamiltonian on the iota6 axes
    (single-link, no plaquettes), with chamber Casimirs
      (C₂(trivial), C₂(sym²₀), C₂(sym²₀)) = (0, 20, 20)
    from `Phase_A3_CasimirSpectrum`, the chamber kinetic matrix
    elements are:

      diag = (0, 20·inv_g_sq, 20·inv_g_sq)
      off  = 0    (everywhere)    [iota6 orthogonality + isotypic-scalar property]

    These differ from J₄'s chamber entries:

      diag = (1/3, 2/5, 1/5)
      off  = (b₁², b₂²) = (1/25, 1/50)

    The mismatch is STRUCTURAL at (0,0) and at every off-diagonal
    entry, INDEPENDENT of any choice of inverse coupling `inv_g_sq`
    or per-axis norm `n_sq`.  Even on the matchable (1,1) and (2,2)
    entries, the required `inv_g_sq` differs (1/50 vs 1/100), so no
    single coupling closes the diagonal.

    HONEST CONCLUSION (six conjuncts):

      (1) (0,0) mismatch is normconfound-resistant (any norm).
      (2) (0,1) off-diagonal mismatch is structural.
      (3) (1,2) off-diagonal mismatch is structural.
      (4) No single `inv_g_sq` makes the diagonal {(1,1), (2,2)} match.
      (5) The bath-sector consistency `inv_g_sq = 1/3` is incompatible
          with the chamber Casimir constraints.
      (6) Therefore: `MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE`. -/
theorem phase_A4_matching_master :
    -- (1) Norm-independent (0,0) mismatch.
    (∀ inv_g_sq : ℝ, ∀ n_sq : Fin 3 → ℝ,
        wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
          ⟨0, by decide⟩ ⟨0, by decide⟩
        ≠ J₄_chamber ⟨0, by decide⟩ ⟨0, by decide⟩) ∧
    -- (2) Norm-independent (0,1) off-diagonal mismatch.
    (∀ inv_g_sq : ℝ, ∀ n_sq : Fin 3 → ℝ,
        wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
          ⟨0, by decide⟩ ⟨1, by decide⟩
        ≠ J₄_chamber ⟨0, by decide⟩ ⟨1, by decide⟩) ∧
    -- (3) Norm-independent (1,2) off-diagonal mismatch.
    (∀ inv_g_sq : ℝ, ∀ n_sq : Fin 3 → ℝ,
        wilson_kinetic_matrix_element_chamber inv_g_sq n_sq
          ⟨1, by decide⟩ ⟨2, by decide⟩
        ≠ J₄_chamber ⟨1, by decide⟩ ⟨2, by decide⟩) ∧
    -- (4) No single inv_g_sq makes (1,1) AND (2,2) both match.
    (¬ ∃ inv_g_sq : ℝ,
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨1, by decide⟩ ⟨1, by decide⟩
          = J₄_chamber ⟨1, by decide⟩ ⟨1, by decide⟩
        ∧
        wilson_kinetic_matrix_element_chamber inv_g_sq (fun _ => 1)
          ⟨2, by decide⟩ ⟨2, by decide⟩
          = J₄_chamber ⟨2, by decide⟩ ⟨2, by decide⟩) ∧
    -- (5) Bath-required inv_g_sq = 1/3 breaks the chamber (1,1).
    (wilson_kinetic_matrix_element_chamber (1 / 3) (fun _ => 1)
        ⟨1, by decide⟩ ⟨1, by decide⟩
      ≠ J₄_chamber ⟨1, by decide⟩ ⟨1, by decide⟩) ∧
    -- (6) Verdict is the kinetic-alone-fails verdict.
    (verdict = Phase_A4_Verdict.MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact structural_mismatch_at_00
  · exact structural_mismatch_at_01
  · exact structural_mismatch_at_12
  · exact inv_g_sq_for_11_neq_for_22
  · exact bath_inv_g_sq_breaks_chamber_11
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §12. INTERPRETATION & DOWNSTREAM SCOPE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    What the negative result means.

    (I)  The framework's J₄ matrix is NOT the chamber projection of the
         single-link kinetic Wilson Hamiltonian on the iota6 axes.
         This is the EXPECTED outcome of an honest Phase-A4 test:
         the kinetic operator is irrep-diagonal (and even there,
         vanishes on the trivial irrep), so it cannot reproduce the
         J₄ entries (1/3, 2/5, 1/5; 1/25, 1/50) — none of which are
         consistent with a kinetic-only matrix at any single coupling.

    (II) The framework's claim — that J₄ arises from the Wilson
         Hamiltonian — must therefore be interpreted as either:

           (A) J₄ = chamber Feshbach reduction of (kinetic + plaquette)
               at MULTI-LINK (L ≥ 4 plaquette).  The plaquette term
               (1 − Re Tr U_p) on a square plaquette mixes irreps via
               the trace character, providing the off-diagonal
               couplings (b₁², b₂²) and shifting the diagonal entries.
               This is the "scoping" reading of Phase A: the kinetic
               step is a sanity check, and the matching is expected to
               require the plaquette term and Feshbach reduction.

           (B) J₄ is a STRUCTURAL effective Hamiltonian derived
               independently (e.g., from bath self-energies in the
               framework's `FeshbachJ4` chain) and bears only an
               INDIRECT relation to the bare Wilson Hamiltonian.  In
               this case, the framework's "Wilson YM derivation" claim
               is at best partial: J₄ encodes the framework's
               effective dynamics, but the path from bare Wilson H
               to J₄ requires unproved intermediate steps.

    (III) WHAT PHASE A5+ MUST DO.  Construct the explicit MULTI-LINK
          Wilson Hamiltonian (kinetic + plaquette) at L = 4 (smallest
          plaquette) using `Phase_A1_MultiLinkHilbert`'s machinery,
          compute its chamber projection on the lifted iota6 axes,
          and either CLOSE the matching or REPORT the precise
          discrepancy.  Phase A4 has set up the rigorous accounting
          and shown that the kinetic-only step alone is INSUFFICIENT.

    (IV) HONEST FRAMING.  This negative result is NOT a falsification
         of the framework's J₄ structure.  It is, instead, a
         DELIMITATION of how strong the link between J₄ and the bare
         Wilson Hamiltonian is — at the kinetic-only single-link
         level, that link FAILS, and any positive matching claim must
         go through Feshbach reduction at multi-link (which is
         non-trivial Phase-A5+ scope).
-/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §13. SANITY CHECKS / TYPE-LEVEL EXAMPLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

-- The kinetic matrix element function is well-typed.
noncomputable example : ℝ → (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ :=
  wilson_kinetic_matrix_element_chamber

-- Specific evaluation: at inv_g_sq = 1/50, n_sq = 1, the (1,1) entry
-- equals J₄'s (1,1) = 2/5.
example :
    wilson_kinetic_matrix_element_chamber (1 / 50) (fun _ => 1)
      ⟨1, by decide⟩ ⟨1, by decide⟩ = 2 / 5 := by
  rw [wilson_kinetic_11_unit]
  norm_num

-- Specific evaluation: at inv_g_sq = 1/100, n_sq = 1, the (2,2) entry
-- equals J₄'s (2,2) = 1/5.
example :
    wilson_kinetic_matrix_element_chamber (1 / 100) (fun _ => 1)
      ⟨2, by decide⟩ ⟨2, by decide⟩ = 1 / 5 := by
  rw [wilson_kinetic_22_unit]
  norm_num

-- The chamber-to-iota6 map recovers the chamber axes {0, 2, 3}.
example : chamberToIota6 ⟨0, by decide⟩ = (⟨0, by decide⟩ : Fin 6) := rfl
example : chamberToIota6 ⟨1, by decide⟩ = (⟨2, by decide⟩ : Fin 6) := rfl
example : chamberToIota6 ⟨2, by decide⟩ = (⟨3, by decide⟩ : Fin 6) := rfl

-- The chamber Casimirs are 0, 20, 20.
example : chamberCasimir ⟨0, by decide⟩ = 0  := rfl
example : chamberCasimir ⟨1, by decide⟩ = 20 := rfl
example : chamberCasimir ⟨2, by decide⟩ = 20 := rfl

-- J₄_chamber matches Build3's J₄ everywhere.
example (i j : Fin 3) :
    J₄_chamber i j = UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ i j :=
  J₄_chamber_eq_Build3 i j

-- The verdict is the structural failure at kinetic-only.
example :
    verdict = Phase_A4_Verdict.MATCHING_FAILS_KINETIC_ALONE_REQUIRES_PLAQUETTE :=
  rfl

end UnifiedTheory.LayerB.Phase_A4_MatrixElementMatching
