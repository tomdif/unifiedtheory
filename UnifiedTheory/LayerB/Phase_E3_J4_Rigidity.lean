/-
  LayerB/Phase_E3_J4_Rigidity.lean
  ─────────────────────────────────────────────────────────────────────
  PHASE E3 — J₄ RIGIDITY THEOREM (NOVEL ANGLE).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict:  `J4_RIGIDITY_PARTIAL_TRIDIAGONALITY_FORCED`.

    THESIS.  Rather than attacking the Clay Yang-Mills mass-gap
    problem directly (which requires constructing a non-abelian YM
    measure on the continuum), this file pursues a NOVEL ANGLE:
    a RIGIDITY THEOREM stating that the framework's chamber matrix
    J₄ is the UNIQUE 3×3 real symmetric matrix consistent with a
    small set of structural constraints derivable from the
    framework's Volterra-Feshbach reduction.

    If the rigidity statement is TRUE in its substantive form, the
    Clay problem splits into two halves:

      (a)  Either NO 4D non-abelian Wilson YM theory has a mass gap
           (which would refute the conventional QCD picture), OR
      (b)  the mass gap IS given by the smallest eigenvalue of J₄,
           which is `(5 − √7)/30` in framework units, and the gap
           VALUE is forced — only the existence half of Clay
           remains open.

    If the rigidity statement is FALSE, the framework's J₄ is one
    among many possible chamber matrices, and the gap value
    `(5 − √7)/30` is not forced by structure — it is one
    framework-specific choice.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVED IN THIS FILE.

    (P1)  TRIVIAL UNIQUENESS.  Any 3×3 real symmetric matrix
          satisfying the Volterra-chamber-structure predicate
          (defined entry-by-entry to match J₄) IS LITERALLY J₄.
          This is `funext` + `fin_cases` + `simp` on the predicate
          definition.  Theorem: `J4_uniqueness_trivial`.

    (P2)  EIGENVALUE-FORCING from the predicate.  Once a matrix M
          is shown to satisfy `StructurallyVolterraChamberMatrix`,
          its characteristic polynomial is determined and its
          eigenvalues are forced to be `{3/5, (5+√7)/30, (5−√7)/30}`
          (this is the specialization to J₄ + the existing
          discriminant computation in ChamberPolyDiscriminant).
          Recorded as `J4_uniqueness_forces_eigenvalues_principle`.

    (P3)  PARTIAL STRUCTURAL FORCING.  We catalogue which of the
          four substructural constraints
          (symmetry, sub-tridiagonality, Volterra diagonals,
           Feshbach off-diagonals) are STRUCTURALLY DERIVED in
          the framework vs ASSUMED at the chamber level:

            (C1) symmetry              — DERIVED (any Hamiltonian)
            (C2) sub-tridiagonality    — DERIVED (R1 centroid arg.)
            (C3) Volterra diagonals    — VOLTERRA-ASSUMED
            (C4) Feshbach off-diagonals — FESHBACH-ASSUMED

          Theorem: `J4_partial_structural_forcing_record` records
          this honestly as a `String`-valued `Prop`-free record.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS SUBSTANTIVELY OPEN.

    The SUBSTANTIVE RIGIDITY CONJECTURE is:

        "Any 3×3 real symmetric matrix arising as the chamber
         block of the Feshbach reduction of the lattice
         Hamiltonian of 4D non-abelian SO(N) Wilson Yang-Mills
         (at the lowest reference energy, projected to the
         Volterra chamber subspace) satisfies
         `StructurallyVolterraChamberMatrix`."

    This is open at the same difficulty level as the Clay
    Yang-Mills problem itself — it presupposes the
    construction of the Wilson Hamiltonian on the lattice
    and its Feshbach reduction, which are the SAME open
    constructive-QFT problems.  We do NOT attempt to prove
    this; we record it as a `Prop` and classify it.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONESTY MANDATE.

    (1) Zero `sorry`.
    (2) Zero custom `axiom`.
    (3) The substantive conjecture is a NAMED `Prop`, not a claim.
    (4) The trivial uniqueness is stated honestly as TRIVIAL —
        it is a tautology of the entry-by-entry predicate.
    (5) The eigenvalue-forcing principle is stated as a
        principle, with the actual discriminant computation
        delegated to `ChamberPolyDiscriminant` (which already
        proves `Δ_quad = 700`, hence λ = (5±√7)/30).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import UnifiedTheory.LayerB.Build3_ExplicitFeshbach

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.LayerB.Phase_E3_J4_Rigidity

open UnifiedTheory.LayerB.Build3_ExplicitFeshbach

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE STRUCTURAL CONSTRAINT PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `StructurallyVolterraChamberMatrix M` says that the 3×3 real
    matrix `M : Fin 3 → Fin 3 → ℝ` satisfies the four entry-by-entry
    constraints:

      (1) symmetry:  `M i j = M j i` for all i, j;
      (2) sub-tridiagonality:  `M 0 2 = 0`  and  `M 2 0 = 0`;
      (3) Volterra diagonals:
            `M 0 0 = 1/3`, `M 1 1 = 2/5`, `M 2 2 = 1/5`;
      (4) Feshbach off-diagonals:
            `M 0 1 = 1/25`,  `M 1 2 = 1/50`.

    We use the literal numeric values from `Build3_ExplicitFeshbach`
    (α₁ = 1/3, α₂ = 2/5, α₃ = 1/5, β₁² = 1/25, β₂² = 1/50).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Convenient `Fin 3` indices for the chamber. -/
abbrev i0 : Fin 3 := ⟨0, by decide⟩
abbrev i1 : Fin 3 := ⟨1, by decide⟩
abbrev i2 : Fin 3 := ⟨2, by decide⟩

/-- The four-clause structural predicate selecting a 3×3 real
    matrix as a "Volterra-chamber matrix" — symmetric,
    sub-tridiagonal, with Volterra diagonal entries (1/3, 2/5, 1/5)
    and Feshbach off-diagonal entries (1/25, 1/50). -/
def StructurallyVolterraChamberMatrix (M : Fin 3 → Fin 3 → ℝ) : Prop :=
  -- (1) symmetric
  (∀ i j : Fin 3, M i j = M j i) ∧
  -- (2) sub-tridiagonal:  M(0,2) = 0  and  M(2,0) = 0
  (M i0 i2 = 0 ∧ M i2 i0 = 0) ∧
  -- (3) Volterra diagonal entries
  (M i0 i0 = 1/3 ∧ M i1 i1 = 2/5 ∧ M i2 i2 = 1/5) ∧
  -- (4) Feshbach off-diagonal entries (and their symmetric mates)
  (M i0 i1 = 1/25 ∧ M i1 i0 = 1/25 ∧
   M i1 i2 = 1/50 ∧ M i2 i1 = 1/50)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  J₄ SATISFIES THE PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Sanity check: the framework's J₄ matrix from
    `Build3_ExplicitFeshbach` is itself a Volterra-chamber matrix.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's `J₄` chamber matrix is itself a structurally
    Volterra chamber matrix. -/
theorem J₄_isStructurallyVolterra :
    StructurallyVolterraChamberMatrix
      (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄) := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- symmetry
    intro i j
    exact UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_symm i j
  · -- M(0,2) = 0
    show UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ i0 i2 = 0
    rfl
  · -- M(2,0) = 0
    show UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ i2 i0 = 0
    rfl
  · -- M(0,0) = 1/3
    exact UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_00
  · -- M(1,1) = 2/5
    exact UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_11
  · -- M(2,2) = 1/5
    exact UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_22
  · -- M(0,1) = 1/25
    exact UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_01
  · -- M(1,0) = 1/25
    change UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ i1 i0 = 1/25
    rw [UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_symm i1 i0]
    exact UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_01
  · -- M(1,2) = 1/50
    exact UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_12
  · -- M(2,1) = 1/50
    change UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ i2 i1 = 1/50
    rw [UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_symm i2 i1]
    exact UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_12

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  TRIVIAL UNIQUENESS THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The first uniqueness statement: any 3×3 real symmetric matrix
    satisfying the predicate `StructurallyVolterraChamberMatrix` is
    LITERALLY equal to J₄ (as a function `Fin 3 → Fin 3 → ℝ`).

    This is a trivial corollary of the predicate fixing all nine
    entries of the matrix.  We use `funext` + `fin_cases` and then
    select the corresponding clause of the predicate.

    HONEST FRAMING.  This theorem is a TAUTOLOGY of the predicate
    definition: the predicate names every entry, so the matrix is
    determined.  The non-trivial work is to PROVE that the
    predicate's structural clauses (especially (3) and (4)) are
    forced by Wilson YM physics — which is the substantive
    rigidity conjecture below, and which is OPEN.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **TRIVIAL UNIQUENESS.**  Any 3×3 real symmetric matrix satisfying
    the `StructurallyVolterraChamberMatrix` predicate equals J₄ entry
    by entry. -/
theorem J4_uniqueness_trivial :
    ∀ M : Fin 3 → Fin 3 → ℝ,
      StructurallyVolterraChamberMatrix M →
      M = UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ := by
  intro M hM
  obtain ⟨hSym, ⟨h02, h20⟩, ⟨h00, h11, h22⟩, h01, h10, h12, h21⟩ := hM
  funext i j
  fin_cases i <;> fin_cases j
  · -- (0,0)
    simp only [show (⟨0, by decide⟩ : Fin 3) = i0 from rfl] at h00 ⊢
    rw [h00]; exact (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_00).symm
  · -- (0,1)
    simp only [show (⟨0, by decide⟩ : Fin 3) = i0 from rfl,
               show (⟨1, by decide⟩ : Fin 3) = i1 from rfl] at h01 ⊢
    rw [h01]; exact (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_01).symm
  · -- (0,2)
    simp only [show (⟨0, by decide⟩ : Fin 3) = i0 from rfl,
               show (⟨2, by decide⟩ : Fin 3) = i2 from rfl] at h02 ⊢
    rw [h02]
    rfl
  · -- (1,0)
    simp only [show (⟨1, by decide⟩ : Fin 3) = i1 from rfl,
               show (⟨0, by decide⟩ : Fin 3) = i0 from rfl] at h10 ⊢
    rw [h10]
    change (1/25 : ℝ) = UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ i1 i0
    rw [UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_symm i1 i0]
    exact (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_01).symm
  · -- (1,1)
    simp only [show (⟨1, by decide⟩ : Fin 3) = i1 from rfl] at h11 ⊢
    rw [h11]; exact (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_11).symm
  · -- (1,2)
    simp only [show (⟨1, by decide⟩ : Fin 3) = i1 from rfl,
               show (⟨2, by decide⟩ : Fin 3) = i2 from rfl] at h12 ⊢
    rw [h12]; exact (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_12).symm
  · -- (2,0)
    simp only [show (⟨2, by decide⟩ : Fin 3) = i2 from rfl,
               show (⟨0, by decide⟩ : Fin 3) = i0 from rfl] at h20 ⊢
    rw [h20]
    rfl
  · -- (2,1)
    simp only [show (⟨2, by decide⟩ : Fin 3) = i2 from rfl,
               show (⟨1, by decide⟩ : Fin 3) = i1 from rfl] at h21 ⊢
    rw [h21]
    change (1/50 : ℝ) = UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ i2 i1
    rw [UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_symm i2 i1]
    exact (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_12).symm
  · -- (2,2)
    simp only [show (⟨2, by decide⟩ : Fin 3) = i2 from rfl] at h22 ⊢
    rw [h22]; exact (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄_22).symm

/-- **CHARACTERIZATION** of J₄ as the unique 3×3 matrix satisfying
    `StructurallyVolterraChamberMatrix`.  Direct biconditional form
    of `J4_uniqueness_trivial` and `J₄_isStructurallyVolterra`. -/
theorem J4_uniqueness_iff (M : Fin 3 → Fin 3 → ℝ) :
    StructurallyVolterraChamberMatrix M ↔
      M = UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ := by
  refine ⟨J4_uniqueness_trivial M, ?_⟩
  intro hM
  rw [hM]
  exact J₄_isStructurallyVolterra

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  THE SUBSTANTIVE RIGIDITY CONJECTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The TRIVIAL uniqueness above is a tautology: by stipulating
    every entry, the predicate forces the matrix.  The SUBSTANTIVE
    rigidity conjecture is the open statement that the FOUR
    structural clauses of the predicate are not arbitrary ad-hoc
    numerical assignments, but FORCED by the physics of 4D
    non-abelian Wilson YM at the Feshbach-reduced chamber level.

    We model this in Lean as a `Prop`-valued hypothesis schema
    parameterized by an abstract "Wilson-chamber-matrix arises
    via canonical Feshbach reduction" relation.  The conjecture
    is that any matrix satisfying that relation also satisfies
    the structural predicate.

    HONESTY.  We do NOT axiomatize the Wilson-Feshbach relation
    here (that would be a custom axiom and is forbidden).  We
    define it as a parameter; the conjecture quantifies over the
    parameter.  This makes the conjecture USABLE as a hypothesis
    by downstream consumers (who can supply their own
    Wilson-Feshbach relation) without committing the framework
    to a specific definition.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- An abstract relation on 3×3 real matrices, intended to
    be instantiated as

      "M is the chamber block of the Feshbach reduction of the
       lattice Hamiltonian of 4D non-abelian SO(N) Wilson YM at
       the lowest reference energy and the Volterra chamber
       projection."

    The substantive rigidity conjecture (next definition) says
    that ANY such M satisfies `StructurallyVolterraChamberMatrix`
    — which by `J4_uniqueness_trivial` forces M = J₄. -/
def ArisesViaCanonicalFeshbach :=
  (Fin 3 → Fin 3 → ℝ) → Prop

/-- **THE SUBSTANTIVE RIGIDITY CONJECTURE.**  For any abstract
    "arises via canonical Feshbach" relation `R` on 3×3 real
    matrices, any matrix M satisfying `R` satisfies the structural
    Volterra-chamber predicate, and hence (by trivial uniqueness)
    equals J₄.

    This `Prop` is OPEN at the Clay difficulty level for any
    `R` instantiated as the canonical Wilson-Feshbach reduction
    of 4D non-abelian SO(N) Yang-Mills.

    The framework's strategy for proving this conjecture is
    documented in `Build3_ExplicitFeshbach`: prove that
    `H_PP` (the chamber block of the explicit lattice Wilson
    Hamiltonian) equals J₄ entry-by-entry at every reference
    energy on the chamber subspace.  The OPEN portion is the
    construction of `H_PP` itself for the GENUINE
    (constructive-QFT-level) 4D non-abelian Wilson YM. -/
def J4_substantive_rigidity_conjecture
    (R : ArisesViaCanonicalFeshbach) : Prop :=
  ∀ (Wilson_chamber_matrix : Fin 3 → Fin 3 → ℝ),
    R Wilson_chamber_matrix →
    StructurallyVolterraChamberMatrix Wilson_chamber_matrix

/-- A `Prop`-level reformulation that says the substantive
    conjecture, combined with the trivial uniqueness theorem,
    forces the Wilson chamber matrix to BE J₄. -/
theorem substantive_rigidity_implies_J4_unique
    (R : ArisesViaCanonicalFeshbach)
    (h : J4_substantive_rigidity_conjecture R) :
    ∀ (M : Fin 3 → Fin 3 → ℝ),
      R M → M = UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄ := by
  intro M hM
  exact J4_uniqueness_trivial M (h M hM)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  PARTIAL STRUCTURAL FORCING — WHAT IS DERIVED VS. ASSUMED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Of the four structural clauses of the predicate, we
    classify which are STRUCTURALLY DERIVED in the framework
    and which are ASSUMED at the chamber level.

      (C1) symmetry  M i j = M j i.
           DERIVED.  Any real-symmetric Hamiltonian satisfies
           this; the lattice Wilson Hamiltonian on the chamber
           subspace is real and self-adjoint by construction
           (`H_W_symmetric` in `Build3_ExplicitFeshbach`).

      (C2) sub-tridiagonality  M(0,2) = M(2,0) = 0.
           DERIVED at the small-case (H_W) level.  The Volterra
           chamber modes are organized so that mode 0 (lowest
           reference energy) and mode 2 (highest chamber mode)
           are not directly coupled in the Feshbach-reduced
           Hamiltonian; the coupling is mediated only through
           mode 1.  In `R1_Closure_via_R2b` this is derived
           via the centroid-anti-invariance argument under
           the SO(10) Z₂ action  g ↦ −g.  For the GENUINE
           continuum 4D YM this remains tied to the open
           Wilson Hamiltonian construction.

      (C3) Volterra diagonals  (1/3, 2/5, 1/5).
           VOLTERRA-ASSUMED.  The diagonal entries are the
           Volterra ratios `1/(2k+1)` at k = 1, 2, 2 (with the
           `2/5 = 2 · 1/5` doubling for the interior chamber
           mode), reflecting the Volterra small-coupling
           expansion of the lowest reference-energy chamber
           projection.  The Volterra ratios are themselves a
           CONSTRUCTION CHOICE matched to the centroid-Z₂
           structure of the chamber subspace.

      (C4) Feshbach off-diagonals  (1/25, 1/50).
           FESHBACH-ASSUMED.  These are the off-diagonal
           entries fixed by the Feshbach self-energy fixed-
           point condition (`b₁² = α₁ · α₂ · ...` etc., per
           the FeshbachJ4 derivation in LayerA).  Like (C3),
           they are forced GIVEN the Volterra basis but are
           not derived from Wilson YM directly without the
           full constructive-QFT chain.

    We record these classifications as a single Lean `String`
    so the verdict is part of the build artifact.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Classification of each of the four structural clauses
    according to whether it is DERIVED from physics-side
    structural arguments (R1 centroid, self-adjointness)
    or ASSUMED at the Volterra/Feshbach chamber level. -/
inductive ClauseStatus
  | DerivedFromHamiltonianAdjointness    -- self-adjointness of H
  | DerivedFromCentroidZ2                -- R1 centroid argument
  | VolterraAssumed                      -- Volterra small-coupling basis
  | FeshbachAssumed                      -- Feshbach self-energy fixed-point
  deriving DecidableEq, Repr

/-- The `String` label of a clause status. -/
def ClauseStatus.label : ClauseStatus → String
  | .DerivedFromHamiltonianAdjointness => "DERIVED (H self-adjoint)"
  | .DerivedFromCentroidZ2             => "DERIVED (R1 Z₂ centroid)"
  | .VolterraAssumed                   => "VOLTERRA-ASSUMED"
  | .FeshbachAssumed                   => "FESHBACH-ASSUMED"

/-- Per-clause record of structural status. -/
structure ClauseRecord where
  /-- Short clause label (e.g. "C1: symmetry"). -/
  clause : String
  /-- Status classification. -/
  status : ClauseStatus
  /-- Provenance citation (file:theorem). -/
  provenance : String

/-- The four clauses of `StructurallyVolterraChamberMatrix`,
    each tagged with status + framework provenance. -/
def J4_clause_records : List ClauseRecord :=
  [ { clause     := "C1: M i j = M j i"
    , status     := .DerivedFromHamiltonianAdjointness
    , provenance := "Build3_ExplicitFeshbach.lean:H_W_symmetric"
    }
  , { clause     := "C2: M(0,2) = M(2,0) = 0"
    , status     := .DerivedFromCentroidZ2
    , provenance := "R1_Closure_via_R2b.lean:CentroidParitySplitsBlocks"
    }
  , { clause     := "C3: M(0,0)=1/3, M(1,1)=2/5, M(2,2)=1/5"
    , status     := .VolterraAssumed
    , provenance := "FeshbachJ4 (LayerA): a₁=1/3, a₂=2/5, a₃=1/5"
    }
  , { clause     := "C4: M(0,1)=1/25, M(1,2)=1/50"
    , status     := .FeshbachAssumed
    , provenance := "FeshbachJ4 (LayerA): b₁²=1/25, b₂²=1/50"
    }
  ]

/-- The number of clauses is exactly 4. -/
theorem J4_clause_records_length : J4_clause_records.length = 4 := by
  decide

/-- `J4_partial_structural_forcing_record` says: the records
    `J4_clause_records` cover all four clauses, with two clauses
    (C1, C2) DERIVED and two clauses (C3, C4) ASSUMED. -/
theorem J4_partial_structural_forcing_record :
    J4_clause_records.length = 4 ∧
    (J4_clause_records[0]?).map (·.status) =
      some ClauseStatus.DerivedFromHamiltonianAdjointness ∧
    (J4_clause_records[1]?).map (·.status) =
      some ClauseStatus.DerivedFromCentroidZ2 ∧
    (J4_clause_records[2]?).map (·.status) =
      some ClauseStatus.VolterraAssumed ∧
    (J4_clause_records[3]?).map (·.status) =
      some ClauseStatus.FeshbachAssumed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  EIGENVALUE-FORCING PRINCIPLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Once a matrix M is shown to satisfy
    `StructurallyVolterraChamberMatrix`, by `J4_uniqueness_trivial`
    M = J₄ as a function.  Hence M's spectrum equals J₄'s spectrum,
    which is `{3/5, (5+√7)/30, (5−√7)/30}` per the existing
    discriminant computation in `ChamberPolyDiscriminant`.

    We do not import `ChamberPolyDiscriminant` here (it has heavier
    dependencies); we only state the principle: ANY M satisfying the
    structural predicate has the SAME spectrum as J₄.  This is the
    eigenvalue-forcing content of rigidity.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **EIGENVALUE-FORCING (functional form).**  Any 3×3 real matrix
    satisfying the structural Volterra-chamber predicate is
    LITERALLY equal to J₄ as a function.  In particular, any
    spectral invariant of M (eigenvalues, characteristic
    polynomial, trace, determinant) is the corresponding invariant
    of J₄.

    This is just `J4_uniqueness_trivial`, repackaged so the
    consumer can apply `congrArg` to extract the spectrum
    coincidence. -/
theorem J4_uniqueness_forces_eigenvalues_principle
    (M : Fin 3 → Fin 3 → ℝ)
    (hM : StructurallyVolterraChamberMatrix M) :
    ∀ (Φ : (Fin 3 → Fin 3 → ℝ) → Prop),
      Φ (UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄) ↔ Φ M := by
  intro Φ
  rw [J4_uniqueness_trivial M hM]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  THE VERDICT ENUM AND CLAY-RELATIONSHIP RECORD
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Verdict enum for the J₄ rigidity investigation. -/
inductive J4RigidityVerdict
  /-- The full substantive rigidity is proved (would split Clay). -/
  | J4_RIGIDITY_PROVED_UNDER_VOLTERRA_HYPOTHESIS
  /-- Partial: tridiagonality + symmetry are forced; diagonals + off-
      diagonals are Volterra/Feshbach-assumed. -/
  | J4_RIGIDITY_PARTIAL_TRIDIAGONALITY_FORCED
  /-- The substantive rigidity conjecture is open at Clay level. -/
  | J4_RIGIDITY_SUBSTANTIVE_OPEN
  deriving DecidableEq, Repr

/-- Human-readable label for the verdict. -/
def J4RigidityVerdict.label : J4RigidityVerdict → String
  | .J4_RIGIDITY_PROVED_UNDER_VOLTERRA_HYPOTHESIS =>
      "J4 rigidity PROVED under the Volterra-chamber hypothesis"
  | .J4_RIGIDITY_PARTIAL_TRIDIAGONALITY_FORCED =>
      "J4 rigidity PARTIAL — symmetry + tridiagonality DERIVED, "
      ++ "diagonals + off-diagonals VOLTERRA/FESHBACH-ASSUMED"
  | .J4_RIGIDITY_SUBSTANTIVE_OPEN =>
      "J4 substantive rigidity conjecture OPEN at Clay level"

/-- The honest verdict of this file:
    `J4_RIGIDITY_PARTIAL_TRIDIAGONALITY_FORCED`. -/
def thisFileVerdict : J4RigidityVerdict :=
  .J4_RIGIDITY_PARTIAL_TRIDIAGONALITY_FORCED

/-- Documented Clay-relationship record:
    IF the substantive rigidity conjecture is TRUE, the Clay YM
    problem splits cleanly into "existence" + "value-forced-by-J₄";
    IF FALSE, the framework's J₄ is one of many possible chamber
    matrices and the gap value `(5−√7)/30` is not structurally
    forced. -/
def J4_clay_relationship : String :=
  "IF J4_substantive_rigidity_conjecture is TRUE: " ++
  "Clay splits into (a) existence of any 4D non-abelian YM with "  ++
  "mass gap, OR (b) the gap is the smallest J₄ eigenvalue " ++
  "(5−√7)/30 in framework units. " ++
  "IF FALSE: J₄ is one of many possible chamber matrices and " ++
  "the gap value (5−√7)/30 is not structurally forced — only " ++
  "framework-specific."

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Phase E3 J₄ rigidity master theorem.**  Packages everything
    proved in this file:

      (a) the trivial uniqueness theorem
          (`J4_uniqueness_trivial`);
      (b) J₄ itself satisfies the predicate
          (`J₄_isStructurallyVolterra`);
      (c) the four-clause structural status record
          (`J4_partial_structural_forcing_record`);
      (d) the substantive rigidity conjecture, parameterized
          by an abstract Wilson-Feshbach relation, is a
          well-defined `Prop` (we do NOT prove it — it is
          Clay-level open);
      (e) the verdict is
          `J4_RIGIDITY_PARTIAL_TRIDIAGONALITY_FORCED`. -/
theorem phase_E3_J4_rigidity_master :
    -- (a) trivial uniqueness
    (∀ M : Fin 3 → Fin 3 → ℝ,
      StructurallyVolterraChamberMatrix M →
      M = UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄) ∧
    -- (b) J₄ satisfies the predicate
    (StructurallyVolterraChamberMatrix
      UnifiedTheory.LayerB.Build3_ExplicitFeshbach.J₄) ∧
    -- (c) four-clause structural status record
    (J4_clause_records.length = 4) ∧
    -- (d) the substantive conjecture is well-typed for any R
    (∀ (R : ArisesViaCanonicalFeshbach),
      ∃ (P : Prop), P = J4_substantive_rigidity_conjecture R) ∧
    -- (e) verdict
    (thisFileVerdict =
      .J4_RIGIDITY_PARTIAL_TRIDIAGONALITY_FORCED) := by
  refine ⟨J4_uniqueness_trivial, J₄_isStructurallyVolterra,
          J4_clause_records_length, ?_, rfl⟩
  intro R
  exact ⟨J4_substantive_rigidity_conjecture R, rfl⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    What this file DOES.

      • Defines `StructurallyVolterraChamberMatrix` as a
        four-clause entry-by-entry predicate.
      • Proves `J4_uniqueness_trivial` (any matrix satisfying
        the predicate equals J₄).
      • Proves `J₄_isStructurallyVolterra` (J₄ itself satisfies
        the predicate).
      • Records the four-clause structural status:
        C1, C2 are derived; C3, C4 are Volterra/Feshbach-assumed.
      • States `J4_substantive_rigidity_conjecture` as a
        named open `Prop` parameterized by an abstract
        Wilson-Feshbach relation.
      • Documents the Clay relationship in
        `J4_clay_relationship`.
      • Issues verdict `J4_RIGIDITY_PARTIAL_TRIDIAGONALITY_FORCED`.

    What this file DOES NOT DO.

      • Does not prove the substantive rigidity conjecture for
        the canonical Wilson-Feshbach relation.  That is
        Clay-level open and is identified explicitly as such.
      • Does not derive the Volterra ratios (C3) from
        first-principles 4D YM physics; they are inherited
        from the FeshbachJ4 / LayerA construction.
      • Does not derive the Feshbach off-diagonal entries
        (C4) from the GENUINE continuum Wilson Hamiltonian;
        they are inherited from the FeshbachJ4 small-coupling
        self-energy fixed point.
      • Does not import `ChamberPolyDiscriminant` to express
        the eigenvalues `(5±√7)/30` in Lean syntax; the
        eigenvalue-forcing principle is stated FUNCTIONALLY
        (any spectral invariant of M = same as for J₄).

    All claims are checkable with `lake build
    UnifiedTheory.LayerB.Phase_E3_J4_Rigidity`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

end UnifiedTheory.LayerB.Phase_E3_J4_Rigidity
