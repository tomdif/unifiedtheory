/-
  LayerB/Phase_E3_PeterWeyl_RHSFix.lean
  ─────────────────────────────────────────────────────────────────────
  RHS BUG FIX FOR `SO10_chi_vector_chi_vector_integral`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict:
      `RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY`

    The original named open Prop in `Phase_E3_PeterWeyl_Mathlib.lean`
    stated the (vector, vector) Schur diagonal as

        SO10_chi_vector_chi_vector_integral
          :=  ∫ U  χ_vector(U) · χ_vector(U)  dHaar  =  1 / 10.

    This RHS is WRONG.  By Schur orthonormality of irreducible
    characters of a compact group,
        ∫_G  |χ_λ(g)|²  d μ_Haar  =  1
    (NOT `1 / d_λ`).  The value `1 / d_λ = 1 / 10` is the matrix-
    element Schur identity
        ∫_G  U_{ii}²  d μ_Haar  =  1 / N
    for a SINGLE diagonal matrix element of the carrier irrep — a
    DIFFERENT identity.

    For SO(10)'s vector representation, χ_vector(U) = Tr(U), so
        (Tr U)²  =  ∑_i U_{ii}²  +  ∑_{i≠j} U_{ii} U_{jj}.

    Today, BOTH ingredients of the trace-squared integral were
    proved UNCONDITIONALLY in this repository:

      • M1 (`Phase_E3_RowPermutationSymmetry_Proof`):
          ∫ ∑_i U_{ii}²  dHaar  =  1
        (per-index value 1/10, summed over 10 indices = 1).

      • M2 (`Phase_E3_Weingarten_OffDiagonal_Proof`):
          ∀ i ≠ j,  ∫ U_{ii} U_{jj}  dHaar  =  0,
        and the chained corollary
          ∫ (Tr U)²  dHaar  =  1.

    Hence the CORRECTED Prop with RHS = 1 is now PROVABLE
    UNCONDITIONALLY.  This file:

      (1) States the corrected Prop
            `SO10_chi_vector_chi_vector_integral_corrected : Prop
              =  ∫ (reTraceSO10 U)²  dHaar  =  1`.

      (2) Discharges it unconditionally via M1 + M2.

      (3) Provides the corrected joint bridge
            `peter_weyl_closes_R2_and_DLR_corrected`.

      (4) Records the original RHS bug as a documented retraction.

      (5) Provides BOTH identity values explicitly so downstream
          consumers — whichever value they actually require —
          have a sharp, theorem-form result to call into:
              ∫ (Tr U)²    = 1            (character orthonormality);
              ∫ U_{i,i}²   = 1 / 10       (matrix-element Schur);
              ∫ ∑_i U_{i,i}²  = 1         (diagonal sum).

      (6) Records the honest verdict enum.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THE DOWNSTREAM ACTUALLY CONSUMES.

    A grep across the LayerB folder finds the original buggy Prop
    `SO10_chi_vector_chi_vector_integral` referenced in only TWO
    places outside `Phase_E3_PeterWeyl_Mathlib.lean`:

      • `Phase_E3_Weingarten_Diagonal.lean` lines 67, 86, 544 —
        purely DOCUMENTATION COMMENTS that point back to the named
        residual.  No live `import`-time consumption.

    The DLR file's `IsSchurOrthogonalSO10` Prop encodes a generic
    table  `if lam=mu then 1 / dim lam else 0`.  For (vector, vector)
    with `dim vector = 10` this gives  `1 / 10`.  But the consumer
    function `chiChar` evaluates  χ_vector U  to  reTraceSO10 U,
    i.e. the FULL trace, NOT a single matrix element.  So the
    `IsSchurOrthogonalSO10` (vector, vector) entry as currently
    stated is itself an instance of the SAME RHS bug pattern
    (the table conflates "matrix-element Schur" with "character
    orthonormality").  The DLR file does NOT actually consume the
    (vector, vector) entry as a hypothesis in any of its theorems
    — `IsSchurOrthogonalSO10` is defined but never used as an input.

    The R2 file `R2_SO10HaarIntegral.lean` consumes only the
    centroid identity (`∫ Tr U = 0`), which is unconditional.
    There is NO live downstream consumer of the original buggy
    `1 / 10` value for the trace-squared integral.

    CONCLUSION.  The bridge update is a clean swap: where downstream
    needs the (vector, vector) Schur orthonormality of characters
    on SO(10), the value is `1` (and now provable unconditionally).
    Where the matrix-element value is needed, it is also available
    here as a separate explicit theorem.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONESTY MANDATE.

    (1) Zero `sorry`.  Zero custom `axiom`.

    (2) The corrected Prop is PROVED UNCONDITIONALLY in this file
        by chaining `SO10_trace_squared_integral_unconditional`
        (M2 file, which itself chains M1 + M2 internally).

    (3) The original `SO10_chi_vector_chi_vector_integral` Prop in
        `Phase_E3_PeterWeyl_Mathlib.lean` is NOT modified by this
        file (we only ADD a corrected version here, to keep this
        file self-contained and downstream-safe).  An audit-style
        replacement of the buggy Prop in the original file is
        flagged by the retraction notice below.

    (4) BOTH identities (character-orthonormality value `1`, and
        matrix-element value `1 / 10`) are provided as explicit
        theorems, so downstream readers can pick the one they
        actually consume.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CITATIONS.

    [Fol95]  Folland, A Course in Abstract Harmonic Analysis,
             CRC 1995, §5.3 — Schur orthogonality of characters
             on compact groups: ∫ |χ_λ|² dHaar = 1 (orthonormality).
    [HoR70]  Hewitt-Ross, Abstract Harmonic Analysis, Vol. II,
             Springer 1970, §27.20 — character orthonormality.
    [Cea93]  Collins-Śniady, "Integration with respect to the
             Haar measure on unitary, orthogonal and symplectic
             group", Commun. Math. Phys. 264 (2006) 773 —
             matrix-element Weingarten ⟨U_{ii}²⟩ = 1/N.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
import UnifiedTheory.LayerB.R2_SO10HaarIntegral
import UnifiedTheory.LayerB.Phase_E3_DLR_CharacterExpansion
import UnifiedTheory.LayerB.Phase_A3_CasimirSpectrum
import UnifiedTheory.LayerB.Phase_E3_RowPermutationSymmetry_Proof
import UnifiedTheory.LayerB.Phase_E3_Weingarten_OffDiagonal_Proof
import UnifiedTheory.LayerB.Phase_E3_PeterWeyl_Mathlib

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option maxHeartbeats 800000

namespace UnifiedTheory.LayerB.Phase_E3_PeterWeyl_RHSFix

open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
open UnifiedTheory.LayerB.R2_SO10HaarIntegral
open UnifiedTheory.LayerB.Phase_E3_DLR_CharacterExpansion
open UnifiedTheory.LayerB.Phase_A3_CasimirSpectrum
open UnifiedTheory.LayerB.Phase_E3_RowPermutationSymmetry_Proof
open UnifiedTheory.LayerB.Phase_E3_Weingarten_OffDiagonal_Proof
open UnifiedTheory.LayerB.Phase_E3_PeterWeyl_Mathlib

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE RETRACTION NOTICE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **RETRACTION NOTICE.**

    The original `SO10_chi_vector_chi_vector_integral` in
    `Phase_E3_PeterWeyl_Mathlib.lean` (line 549–552) stated the RHS
    as `1 / 10`:

        SO10_chi_vector_chi_vector_integral : Prop
          :=  ∫ U  χ_vector(U) · χ_vector(U)  dHaar
                =  1 / (dim SO10Irrep.vector : ℝ)
                =  1 / 10.

    By Schur orthonormality of characters of a finite-dimensional
    irreducible representation of a compact group,
        ∫_G  |χ_λ|² dHaar  =  1
    (NOT `1 / d_λ`).

    For SO(10)'s vector representation, χ_vector U = Tr(U), so the
    correct value is `∫ (Tr U)² dHaar = 1`.

    The `1 / 10 = 1 / N` is the MATRIX-ELEMENT Schur identity
        ∫ U_{i,i}² dHaar = 1 / N,
    which is a DIFFERENT identity (one diagonal entry, not the
    full character).

    BOTH identities are now PROVED UNCONDITIONALLY in this
    repository:
      • ∫ (Tr U)² dHaar = 1
        (`SO10_trace_squared_integral_unconditional`,
         from M1 + M2);
      • ∫ U_{i,i}² dHaar = 1 / 10
        (`SO10_diagonal_squared_haar_integral_unconditional`,
         from M1 alone).

    This file SUPPLIES THE CORRECTED Prop, DISCHARGES IT
    UNCONDITIONALLY, AND PROVIDES THE BRIDGE UPDATE.  The original
    buggy Prop in `Phase_E3_PeterWeyl_Mathlib.lean` is left in
    place for backward source compatibility but should be
    considered DEPRECATED and replaced by the corrected version
    `SO10_chi_vector_chi_vector_integral_corrected` here. -/
def rhs_bug_retraction_notice : String :=
  "Retraction: the RHS of SO10_chi_vector_chi_vector_integral in " ++
  "Phase_E3_PeterWeyl_Mathlib.lean was 1/10. By Schur orthonormality " ++
  "of irreducible characters on a compact group, the correct value " ++
  "is 1. The 1/10 value is the matrix-element identity ∫ U_{ii}² = 1/N, " ++
  "a different identity. The corrected Prop " ++
  "SO10_chi_vector_chi_vector_integral_corrected is now PROVED " ++
  "UNCONDITIONALLY in Phase_E3_PeterWeyl_RHSFix.lean via M1+M2."

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE CORRECTED PROP — RHS = 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE CORRECTED (vector, vector) DIAGONAL SCHUR INTEGRAL.**

    Named Prop predicate for the highest-leverage diagonal entry of
    the SO(10) Schur orthonormality table, with the CORRECT RHS
    value `1`:

        ∫_{SO(10)}  reTraceSO10(U)²  d μ_Haar  =  1.

    Equivalently, since `chiChar SO10Irrep.vector = reTraceSO10` by
    `rfl`:

        ∫_{SO(10)}  χ_vector(U) · χ_vector(U)  d μ_Haar  =  1.

    This is character orthonormality
        ∫ |χ_λ|² dHaar = 1
    for the vector irrep of SO(10).  The original Prop in
    `Phase_E3_PeterWeyl_Mathlib.lean` stated `1 / 10` here; that
    was the matrix-element value, not the character value.

    UNLIKE the original Prop, this one is PROVED UNCONDITIONALLY
    (see `SO10_chi_vector_chi_vector_integral_corrected_proved`
    below), via the chain M1 + M2 from
    `Phase_E3_RowPermutationSymmetry_Proof`
    + `Phase_E3_Weingarten_OffDiagonal_Proof`. -/
def SO10_chi_vector_chi_vector_integral_corrected : Prop :=
  ∫ U : G_SO10, (reTraceSO10 U)^2 ∂haarMeasureSO10 = 1

/-- **EQUIVALENT FORM** of the corrected Prop, in product (not
    square) notation.  The two forms differ only by `pow 2` vs
    `· * ·` and are interconvertible via `sq`. -/
def SO10_chi_vector_chi_vector_integral_corrected_mul : Prop :=
  ∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1

/-- The square form and the product form of the corrected Prop are
    equivalent.  This is purely the `pow 2 = · * ·` rewrite
    (`sq`). -/
theorem corrected_pow_eq_mul :
    SO10_chi_vector_chi_vector_integral_corrected
      ↔ SO10_chi_vector_chi_vector_integral_corrected_mul := by
  unfold SO10_chi_vector_chi_vector_integral_corrected
         SO10_chi_vector_chi_vector_integral_corrected_mul
  constructor
  · intro h
    have h_eq : (fun U : G_SO10 => (reTraceSO10 U)^2)
              = (fun U : G_SO10 => reTraceSO10 U * reTraceSO10 U) := by
      funext U
      exact sq (reTraceSO10 U)
    rw [h_eq] at h
    exact h
  · intro h
    have h_eq : (fun U : G_SO10 => (reTraceSO10 U)^2)
              = (fun U : G_SO10 => reTraceSO10 U * reTraceSO10 U) := by
      funext U
      exact sq (reTraceSO10 U)
    rw [h_eq]
    exact h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  UNCONDITIONAL DISCHARGE OF THE CORRECTED PROP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **UNCONDITIONAL DISCHARGE OF THE CORRECTED PROP.**

    Direct from `SO10_trace_squared_integral_unconditional`
    (Phase_E3_Weingarten_OffDiagonal_Proof), which itself chains:
      • M1: `rowPermutationSymmetrySO10_proved` (gives diagonal
            ∑_i U_{ii}² → 1 unconditional);
      • M2: `offDiagonalDiagSquaredCorrelation_zero_proved`
            (gives off-diagonal U_{ii} U_{jj} → 0 unconditional).

    Together they force ∫ (Tr U)² dHaar = 1.

    NO HYPOTHESES.  Pure Mathlib + Mathlib-backed Haar measure on
    SO(10).  Zero `sorry`, zero custom `axiom`. -/
theorem SO10_chi_vector_chi_vector_integral_corrected_proved :
    SO10_chi_vector_chi_vector_integral_corrected := by
  unfold SO10_chi_vector_chi_vector_integral_corrected
  -- Goal: ∫ U, (reTraceSO10 U)^2 ∂haarMeasureSO10 = 1
  -- Convert (·)^2 to (· * ·) and apply the M2 unconditional theorem.
  have h_pt : (fun U : G_SO10 => (reTraceSO10 U)^2)
            = (fun U : G_SO10 => reTraceSO10 U * reTraceSO10 U) := by
    funext U
    exact sq (reTraceSO10 U)
  rw [h_pt]
  exact SO10_trace_squared_integral_unconditional

/-- **The product-form variant**, also unconditional. -/
theorem SO10_chi_vector_chi_vector_integral_corrected_mul_proved :
    SO10_chi_vector_chi_vector_integral_corrected_mul :=
  SO10_trace_squared_integral_unconditional

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  THE BOTH-VALUES TABLE — CHARACTER vs MATRIX-ELEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Downstream consumers may need EITHER of two distinct values:
      • The CHARACTER value, `∫ (Tr U)² = 1` (Schur orthonormality).
      • The MATRIX-ELEMENT value, `∫ U_{i,i}² = 1 / N` (Weingarten).

    Both are now available unconditionally.  We expose them side-by-
    side here as a sharp lookup. -/

/-- **CHARACTER-ORTHONORMALITY VALUE** for SO(10) vector irrep:
        ∫_{SO(10)}  (Tr U)²  d Haar  =  1.

    UNCONDITIONAL.  Direct alias of `SO10_trace_squared_integral_unconditional`. -/
theorem character_orthonormality_value :
    ∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1 :=
  SO10_trace_squared_integral_unconditional

/-- **MATRIX-ELEMENT WEINGARTEN VALUE** for SO(10):  for any single
    diagonal index i ∈ Fin 10,
        ∫_{SO(10)}  U_{i,i}²  d Haar  =  1 / 10.

    UNCONDITIONAL.  Direct alias of
    `SO10_diagonal_squared_haar_integral_unconditional`. -/
theorem matrix_element_weingarten_value (i : Fin d10) :
    ∫ U : G_SO10, (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                    (U : Matrix (Fin d10) (Fin d10) ℝ) i i ∂haarMeasureSO10
      = 1 / 10 :=
  SO10_diagonal_squared_haar_integral_unconditional i

/-- **DIAGONAL-SUM IDENTITY** (as a sanity check that the two values
    are consistent):
        ∫_{SO(10)}  ∑_i U_{i,i}²  d Haar  =  1.

    UNCONDITIONAL.  Direct alias of
    `SO10_sum_diagonal_squared_haar_integral_unconditional`.  Note
    that 10 · (1/10) = 1, consistent with the per-index value
    `1/10` and the sum-over-indices value `1`. -/
theorem diagonal_sum_value :
    ∫ U : G_SO10, (∑ i, (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                          (U : Matrix (Fin d10) (Fin d10) ℝ) i i)
        ∂haarMeasureSO10
      = 1 :=
  SO10_sum_diagonal_squared_haar_integral_unconditional

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  THE CORRECTED BRIDGE — peter_weyl_closes_R2_and_DLR_corrected
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The original `peter_weyl_closes_R2_and_DLR`
    (Phase_E3_PeterWeyl_Mathlib.lean line 635) packaged the
    bridges to R2 and DLR in the buggy form RHS = 1/10.  We now
    package the corrected bridges:

      (R2 SIDE)   ∫ reTrace(U)²  dHaar  =  1.  (UNCONDITIONAL.)
      (DLR SIDE)  ∫ χ_vec(U) · χ_vec(U)  dHaar  =  1.  (UNCONDITIONAL.)

    SCOPE OF THE CORRECTED BRIDGE.  As discussed in the file
    docstring, no live downstream consumer actually consumes the
    1/10 value for the trace-squared integral; the buggy Prop
    appears only as documentation comments in
    `Phase_E3_Weingarten_Diagonal.lean` (lines 67, 86, 544).
    Therefore the corrected bridge can be discharged
    UNCONDITIONALLY without further reconnection: it directly
    delivers the actually-correct values (both = 1) at the two
    bridge points, and these values do match what character
    orthonormality requires. -/

/-- **R2 BRIDGE (CORRECTED), UNCONDITIONAL.**

    The R2 sharp-interface (vector, vector) channel diagonal Schur
    integral is closed UNCONDITIONALLY at the corrected value 1. -/
theorem R2_vector_diagonal_corrected_unconditional :
    ∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1 :=
  SO10_trace_squared_integral_unconditional

/-- **DLR BRIDGE (CORRECTED), UNCONDITIONAL.**

    The GJ3 / DLR character-expansion (vector, vector) entry,
    written in the chiChar form, is closed UNCONDITIONALLY at the
    corrected value 1. -/
theorem DLR_vector_vector_diagonal_corrected_unconditional :
    ∫ U : G_SO10,
        chiChar SO10Irrep.vector U * chiChar SO10Irrep.vector U
        ∂haarMeasureSO10
      = 1 := by
  -- chiChar SO10Irrep.vector = reTraceSO10 by rfl (chi_vector @[simp] lemma).
  simp only [chi_vector]
  exact SO10_trace_squared_integral_unconditional

/-- **JOINT BRIDGE (CORRECTED), UNCONDITIONAL.**

    The corrected (vector, vector) Schur orthonormality identity
    discharges BOTH:
      • the R2 sharp-interface (vector, vector) channel
        diagonal at the correct value `1`,
      • the GJ3 / DLR character-expansion (vector, vector)
        diagonal at the correct value `1`,
    UNCONDITIONALLY, with no Peter-Weyl Mathlib hypothesis
    required.  Both bridges are direct consequences of the M1+M2
    chain proven today in
    `Phase_E3_RowPermutationSymmetry_Proof` +
    `Phase_E3_Weingarten_OffDiagonal_Proof`. -/
theorem peter_weyl_closes_R2_and_DLR_corrected :
    -- (R2 SIDE)
    (∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1)
    ∧
    -- (DLR SIDE)
    (∫ U : G_SO10,
        chiChar SO10Irrep.vector U * chiChar SO10Irrep.vector U
        ∂haarMeasureSO10
      = 1) := by
  refine ⟨?_, ?_⟩
  · exact R2_vector_diagonal_corrected_unconditional
  · exact DLR_vector_vector_diagonal_corrected_unconditional

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  INTERACTION WITH THE ORIGINAL BUGGY PROP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For backward compatibility, we expose the relationship between
    the original (buggy) Prop and the corrected Prop. -/

/-- **THE ORIGINAL PROP IS UNDISCHARGEABLE** (under the standard
    interpretation `chiChar SO10Irrep.vector = reTraceSO10`).

    More precisely: assuming the corrected (true) Prop
    (`SO10_chi_vector_chi_vector_integral_corrected`, value 1) the
    original Prop (value `1/10`) would force `1 = 1/10`, which is
    false.  Hence the original Prop is INCONSISTENT with the
    proven character orthonormality identity, and cannot be
    discharged in this framework — the bug is REAL.

    NOTE.  We do not prove `¬ SO10_chi_vector_chi_vector_integral`
    directly here (as a Prop manipulation), because that would
    require chaining `chiChar SO10Irrep.vector U = reTraceSO10 U`
    by `rfl` and the M1+M2 chain.  Instead we record this
    observation as a structural lemma asserting
    "if the original Prop held, then 1 = 1/10", which is
    sufficient to make the bug visible. -/
theorem original_buggy_prop_implies_one_eq_one_tenth
    (h_buggy : SO10_chi_vector_chi_vector_integral) : (1 : ℝ) = 1 / 10 := by
  -- h_buggy : ∫ chiChar vector · chiChar vector ∂haar = 1 / dim vector.
  -- chiChar vector = reTraceSO10 (rfl), and ∫ reTrace · reTrace = 1
  -- by the corrected unconditional identity.
  have h_corrected : ∫ U : G_SO10,
      chiChar SO10Irrep.vector U * chiChar SO10Irrep.vector U
        ∂haarMeasureSO10
      = 1 := DLR_vector_vector_diagonal_corrected_unconditional
  unfold SO10_chi_vector_chi_vector_integral at h_buggy
  -- h_buggy : ∫ … = 1 / (dim vector : ℝ)
  -- h_corrected : ∫ … = 1
  -- So  1 = 1 / (dim vector : ℝ).
  have h_dim : (dim SO10Irrep.vector : ℝ) = 10 := by unfold dim; norm_num
  rw [h_dim] at h_buggy
  -- h_buggy : ∫ … = 1 / 10
  -- h_corrected : ∫ … = 1
  rw [h_buggy] at h_corrected
  linarith

/-- **THE ORIGINAL BUGGY PROP IS FALSE** (corollary of the above).

    Direct corollary: since `1 ≠ 1 / 10` in `ℝ`, the original
    `SO10_chi_vector_chi_vector_integral` Prop is FALSE — it has
    been refuted by the M1+M2 chain. -/
theorem original_buggy_prop_is_false :
    ¬ SO10_chi_vector_chi_vector_integral := by
  intro h
  have := original_buggy_prop_implies_one_eq_one_tenth h
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  HONEST VERDICT (ENUM)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The verdict for the RHS-bug-fix attempt. -/
inductive RHSFixVerdict
  /-- TIER A (THIS FILE'S VERDICT):  The RHS bug is FIXED, the
      corrected Prop is PROVED UNCONDITIONALLY, and BOTH bridges
      (R2 + GJ3 / DLR) are DISCHARGED UNCONDITIONALLY at the
      corrected values.  No downstream reconnection required: no
      live consumer was reading the buggy `1/10` value. -/
  | RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY
  /-- TIER B:  The RHS bug is fixed and the corrected Prop is
      proved, but downstream files need to be reconnected to the
      corrected Prop (their existing imports point to the buggy
      one).  This file would still discharge the corrected Prop
      but would flag the reconnection as outstanding. -/
  | RHS_BUG_FIXED_BRIDGES_NEED_RECONNECTION
  /-- TIER C:  Downstream files actually consume BOTH the
      character-orthonormality value (1) AND the matrix-element
      value (1/10).  In that case BOTH identities are required;
      this file provides them.  This is the cleanest outcome
      mathematically — the buggy Prop was a name collision, not
      a wrong value, and BOTH numbers are right in their
      respective contexts. -/
  | RHS_BUG_FIXED_DOWNSTREAM_NEEDS_BOTH_VALUES
  deriving DecidableEq, Repr

/-- **THE VERDICT FOR THIS FILE.**

    Tier A: `RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY`.

    Justification.  A grep over LayerB finds the original buggy
    Prop's name only in:
      • `Phase_E3_PeterWeyl_Mathlib.lean` (the buggy file itself),
      • `Phase_E3_Weingarten_Diagonal.lean` lines 67, 86, 544
        (DOCUMENTATION COMMENTS only — no live consumption).
    The DLR file's `IsSchurOrthogonalSO10` Prop is defined but
    not used as a hypothesis in any DLR theorem.  The R2 file
    consumes only `∫ Tr U = 0`, which is unconditional.

    Therefore the corrected bridges (R2 + GJ3 / DLR, both at
    value 1) close the actual mathematical content — character
    orthonormality of χ_vector — UNCONDITIONALLY, with no
    downstream reconnection required for any live consumer.

    BOTH explicit values (character: 1, matrix-element: 1/10)
    are exposed in §4 in case a future downstream reader needs
    the matrix-element form. -/
def rhs_fix_verdict : RHSFixVerdict :=
  .RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY

/-- Self-check on the verdict. -/
theorem rhs_fix_verdict_check :
    rhs_fix_verdict
      = RHSFixVerdict.RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY :=
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  STATUS / DOCUMENTATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Status string for this file. -/
def phase_E3_peterweyl_RHS_fix_status : String :=
  "Phase E3 Peter-Weyl RHS bug fix: " ++
  "SO10_chi_vector_chi_vector_integral original RHS was 1/10 (matrix " ++
  "element value); CORRECTED RHS is 1 (character orthonormality). " ++
  "Corrected Prop SO10_chi_vector_chi_vector_integral_corrected " ++
  "discharged UNCONDITIONALLY via M1+M2 (chained " ++
  "Phase_E3_RowPermutationSymmetry_Proof and " ++
  "Phase_E3_Weingarten_OffDiagonal_Proof). Joint bridge " ++
  "peter_weyl_closes_R2_and_DLR_corrected delivers (R2-side) ∫ Tr U² = 1 " ++
  "and (DLR-side) ∫ χ_vec² = 1, both unconditional. BOTH values " ++
  "(character: 1, matrix-element: 1/10) exposed as separate theorems " ++
  "for downstream consumption. Original buggy Prop is FALSE (refuted " ++
  "by original_buggy_prop_is_false). Verdict: " ++
  "RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY."

/-- Reference list for this file. -/
def phase_E3_peterweyl_RHS_fix_references : List String :=
  [ "[Fol95]  Folland, A Course in Abstract Harmonic Analysis, CRC 1995, §5.3"
  , "[HoR70]  Hewitt-Ross, Abstract Harmonic Analysis, Vol. II, Springer 1970, §27.20"
  , "[Cea93]  Collins-Śniady, Commun. Math. Phys. 264 (2006) 773"
  , "[Wey46]  Weyl, The Classical Groups, Princeton 1946, §VII (orthogonal group integrals)" ]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  THE MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM:  PHASE E3 — PETER-WEYL RHS BUG FIX.**

    Bundles the structural content of this file:

    (M1)  The corrected Prop is PROVED UNCONDITIONALLY:
            `SO10_chi_vector_chi_vector_integral_corrected_proved`.

    (M2)  The product-form variant is PROVED UNCONDITIONALLY:
            `SO10_chi_vector_chi_vector_integral_corrected_mul_proved`.

    (M3)  Both forms are equivalent: `corrected_pow_eq_mul`.

    (M4)  CHARACTER-ORTHONORMALITY VALUE (= 1) is unconditional.

    (M5)  MATRIX-ELEMENT WEINGARTEN VALUE (= 1/10) is unconditional
            for every diagonal index i ∈ Fin 10.

    (M6)  DIAGONAL-SUM IDENTITY (∑_i ∫ U_{i,i}² = 1) is unconditional.

    (M7)  The corrected JOINT BRIDGE (R2 + DLR, both at value 1) is
            DISCHARGED UNCONDITIONALLY:
              `peter_weyl_closes_R2_and_DLR_corrected`.

    (M8)  The original buggy Prop is FALSE (its discharge would
            force `1 = 1/10`):
              `original_buggy_prop_is_false`.

    (M9)  The verdict is
            `RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY`.

    Zero `sorry`.  Zero custom `axiom`. -/
theorem phase_E3_peterweyl_RHS_fix_master :
    -- (M1) Corrected Prop, unconditional.
    SO10_chi_vector_chi_vector_integral_corrected
    ∧
    -- (M2) Corrected Prop, product form, unconditional.
    SO10_chi_vector_chi_vector_integral_corrected_mul
    ∧
    -- (M3) The two forms are equivalent.
    (SO10_chi_vector_chi_vector_integral_corrected
      ↔ SO10_chi_vector_chi_vector_integral_corrected_mul)
    ∧
    -- (M4) Character-orthonormality value (= 1).
    (∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1)
    ∧
    -- (M5) Matrix-element Weingarten value (= 1/10), per index.
    (∀ i : Fin d10,
        ∫ U : G_SO10,
            (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
              (U : Matrix (Fin d10) (Fin d10) ℝ) i i
            ∂haarMeasureSO10
          = 1 / 10)
    ∧
    -- (M6) Diagonal-sum identity (= 1).
    (∫ U : G_SO10,
        (∑ i, (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                (U : Matrix (Fin d10) (Fin d10) ℝ) i i)
        ∂haarMeasureSO10
      = 1)
    ∧
    -- (M7) JOINT BRIDGE (R2 + DLR, both at value 1), unconditional.
    ((∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1)
      ∧
     (∫ U : G_SO10,
        chiChar SO10Irrep.vector U * chiChar SO10Irrep.vector U
        ∂haarMeasureSO10
      = 1))
    ∧
    -- (M8) The original buggy Prop is FALSE.
    (¬ SO10_chi_vector_chi_vector_integral)
    ∧
    -- (M9) Verdict.
    (rhs_fix_verdict
      = RHSFixVerdict.RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (M1)
    exact SO10_chi_vector_chi_vector_integral_corrected_proved
  · -- (M2)
    exact SO10_chi_vector_chi_vector_integral_corrected_mul_proved
  · -- (M3)
    exact corrected_pow_eq_mul
  · -- (M4)
    exact character_orthonormality_value
  · -- (M5)
    intro i
    exact matrix_element_weingarten_value i
  · -- (M6)
    exact diagonal_sum_value
  · -- (M7)
    exact peter_weyl_closes_R2_and_DLR_corrected
  · -- (M8)
    exact original_buggy_prop_is_false
  · -- (M9)
    rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE STATEMENT** for this file.

    PROVED UNCONDITIONALLY (no sorry, no axiom):

      ✓ The corrected Prop with RHS = 1 is provable.
      ✓ Both square form and product form are provable, and are
        equivalent.
      ✓ Both downstream values (character: 1, matrix-element: 1/10)
        are theorems — pick the right one for your context.
      ✓ The corrected joint bridge (R2 + DLR) is unconditional;
        no downstream reconnection required for any live consumer.
      ✓ The original buggy Prop (RHS = 1/10) is REFUTED.
      ✓ The retraction notice is documented in §1.

    NOT CLAIMED HERE:

      ✗ Modification of the original `SO10_chi_vector_chi_vector_integral`
        Prop in `Phase_E3_PeterWeyl_Mathlib.lean` (left in place
        for backward source compatibility, marked deprecated by
        retraction notice).
      ✗ Any other Schur orthonormality identity for SO(10) irreps
        beyond (vector, vector) — antisym2, sym2_traceless,
        antisym3, antisym4, spinor_pos, spinor_neg remain open
        per Phase_E3_PeterWeyl_Mathlib.lean's scope.
      ✗ Mathlib gap closure for general compact Hausdorff groups —
        this file ONLY closes the SO(10) (vector, vector) entry,
        and ONLY because M1 + M2 give it directly.

    HONEST CLAIM.  This file delivers a SHARP RHS-bug fix:
    the (vector, vector) Schur orthonormality identity for SO(10)
    is now provable UNCONDITIONALLY at the correct value `1`,
    bridging both the R2 sharp-interface and GJ3 / DLR character-
    expansion residuals at their intended downstream values
    without any further Mathlib Peter-Weyl input. -/
theorem honest_scope_phase_E3_peterweyl_RHS_fix :
    -- Corrected Prop is unconditional.
    SO10_chi_vector_chi_vector_integral_corrected ∧
    -- Both forms agree.
    (SO10_chi_vector_chi_vector_integral_corrected
      ↔ SO10_chi_vector_chi_vector_integral_corrected_mul) ∧
    -- Both downstream values are theorems.
    (∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1) ∧
    (∀ i : Fin d10,
        ∫ U : G_SO10,
            (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
              (U : Matrix (Fin d10) (Fin d10) ℝ) i i
            ∂haarMeasureSO10
          = 1 / 10) ∧
    -- Joint bridge unconditional.
    ((∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1)
      ∧
     (∫ U : G_SO10,
        chiChar SO10Irrep.vector U * chiChar SO10Irrep.vector U
        ∂haarMeasureSO10
      = 1)) ∧
    -- Original buggy Prop refuted.
    (¬ SO10_chi_vector_chi_vector_integral) ∧
    -- Verdict.
    (rhs_fix_verdict
      = RHSFixVerdict.RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact SO10_chi_vector_chi_vector_integral_corrected_proved
  · exact corrected_pow_eq_mul
  · exact character_orthonormality_value
  · intro i; exact matrix_element_weingarten_value i
  · exact peter_weyl_closes_R2_and_DLR_corrected
  · exact original_buggy_prop_is_false
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11.  FINAL SANITY EXAMPLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

-- The verdict is the expected enum value.
example : rhs_fix_verdict
    = RHSFixVerdict.RHS_BUG_FIXED_BRIDGES_DISCHARGED_UNCONDITIONALLY := rfl

-- The corrected Prop is true.
example : SO10_chi_vector_chi_vector_integral_corrected :=
  SO10_chi_vector_chi_vector_integral_corrected_proved

-- Character orthonormality value (corrected) = 1.
example : ∫ U : G_SO10, reTraceSO10 U * reTraceSO10 U ∂haarMeasureSO10 = 1 :=
  character_orthonormality_value

-- Matrix-element Weingarten value (per index) = 1/10.
example (i : Fin d10) :
    ∫ U : G_SO10, (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                    (U : Matrix (Fin d10) (Fin d10) ℝ) i i ∂haarMeasureSO10
      = 1 / 10 :=
  matrix_element_weingarten_value i

-- Diagonal-sum identity = 1 (consistent with 10 · (1/10) = 1).
example : ∫ U : G_SO10, (∑ i, (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                                (U : Matrix (Fin d10) (Fin d10) ℝ) i i)
              ∂haarMeasureSO10
            = 1 :=
  diagonal_sum_value

-- The original buggy Prop is FALSE.
example : ¬ SO10_chi_vector_chi_vector_integral :=
  original_buggy_prop_is_false

-- The DLR-side bridge value is 1.
example : ∫ U : G_SO10,
    chiChar SO10Irrep.vector U * chiChar SO10Irrep.vector U
    ∂haarMeasureSO10
  = 1 :=
  DLR_vector_vector_diagonal_corrected_unconditional

end UnifiedTheory.LayerB.Phase_E3_PeterWeyl_RHSFix
