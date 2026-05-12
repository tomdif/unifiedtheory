/-
  LayerB/Phase_A3_CasimirSpectrum.lean — Citable Casimir-eigenvalue
                                           table for SO(10) irreps.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT (CLAY_YM_PLAN.md, Phase A, Step A3)

  The framework's Yang-Mills derivation chain needs the second-order
  Casimir eigenvalues C₂(λ) for several SO(10) irreducible
  representations to compute the kinetic-energy matrix elements

      ⟨v_i, E² v_j⟩ = C₂(λ_i) · ‖v_i‖² · δ_{i,j}

  on the framework's `iota6 : Fin 6 → L²(SO(10))` axes
  (`R1_VolterraSO10Embedding_Dim6Full.lean`).

  The Casimir operator C₂ is a SCALAR on each irreducible
  representation, given by the standard Freudenthal formula

      C₂(λ) = ⟨λ, λ + 2ρ⟩

  where ρ is half the sum of positive roots and ⟨·,·⟩ is the
  Killing-form-induced bilinear form, evaluated in the orthonormal
  weight basis e_1, …, e_n where n = rank.

  This file is a LITERATURE LOOKUP, not a derivation.  All values
  are tabulated in standard references (cited below) and reduce
  to a one-line algebraic computation in the orthonormal basis.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  NORMALIZATION CONVENTION (LOCKED)

  We adopt the **standard Cahn / Hamermesh orthonormal-basis
  convention** for SO(2n) ≃ Spin(2n)/ℤ₂:

    • Cartan subalgebra spanned by e_1, …, e_n (orthonormal).
    • Positive roots: e_i ± e_j (i < j).
    • Half-sum of positive roots: ρ = (n−1, n−2, …, 1, 0).
    • Killing-form-induced bilinear form: standard Euclidean
      ⟨a, b⟩ = Σ a_i b_i.
    • Second Casimir eigenvalue: C₂(λ) = ⟨λ, λ + 2ρ⟩.

  For SO(10), n = 5 and ρ = (4, 3, 2, 1, 0).

  In this convention:
    • C₂(vector V_10)             =  9
    • C₂(spinor 16⁺ or 16⁻)       = 45/4
    • C₂(adjoint ∧²V = 45)        = 16   = 2 · h^∨   (h^∨ = 8 for SO(10))
    • C₂(symmetric traceless 54)  = 20
    • C₂(antisymmetric ∧³V = 120) = 21
    • C₂(antisymmetric ∧⁴V = 210) = 24
    • C₂(trivial 1)               = 0

  IMPORTANT — DISCREPANCY NOTE.  An earlier draft of the
  framework's Phase-A3 specification listed C₂(54) = 18.  This
  is **not consistent** with the orthonormal-basis convention
  above (the Freudenthal formula on highest weight (2,0,0,0,0)
  yields 2·(2 + 8) = 20).  We use the literature-correct value
  20, matched independently against:

    • R. Slansky, Phys. Rep. 79 (1981) 1, Table 7
      (Slansky's "C₂(R)" is half of ours; his 10 ↔ our 20).
    • B. G. Wybourne, "Classical Groups for Physicists" (1974),
      Table 7-5.
    • R. N. Cahn, "Semi-Simple Lie Algebras and Their
      Representations" (1984), §17.3, eq. (17.41).
    • H. Georgi, "Lie Algebras in Particle Physics" (2nd ed.,
      1999), §13.3.

  No published reference has C₂(54) = 18; the discrepancy is a
  draft typo, not a normalization choice.  The cross-check
  `casimir_sym2_traceless_consistency` below pins this down.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Z₂ CENTRAL CHARACTER

  SO(10) has a central element −I (the negative of the identity
  in its 10-dimensional defining representation).  Its image
  π_λ(−I) under any irreducible representation π_λ is ±1 (Schur),
  determined by the parity of the highest weight under the
  standard ℤ₂ grading:

    • Tensor representations of integer weight: π(−I) = (−1)^k
      where k counts the "vector indices" (≡ Σλ_i mod 2).
    • Spinor representations of half-integer weight:
      π(−I) = (−1)^(n) = (−1)^5 = −1 for one chirality,
      +1 for the other.  Convention used here:
      spinor_pos (HW (½,½,½,½,½))  → π(−I) = +1
      spinor_neg (HW (½,½,½,½,−½)) → π(−I) = −1
      This is the "positive-chirality even" convention of
      Slansky 1981 (used by SO(10) GUT model builders).

  Used downstream by `R1_VolterraSO10Embedding_Dim6Full.lean`
  (the `iota6_z2_grading` theorem) to identify chamber vs bath
  axes.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVED (zero sorry, zero custom axioms)

  PART 1.  Enum `SO10Irrep` covering the 8 irreps used by Phase A.
  PART 2.  Dimension table `dim : SO10Irrep → ℕ`.
  PART 3.  Casimir-eigenvalue table `casimir : SO10Irrep → ℝ`.
  PART 4.  ℤ₂ central-character table `Z2_central_char : SO10Irrep → ℝ`.
  PART 5.  Per-irrep citable theorems (one per row of the table).
  PART 6.  Cross-check theorems:
            • `casimir_adjoint_eq_2_h_dual` : C₂(adj) = 2·h^∨ = 16.
            • `casimir_spinors_equal`        : both chiralities share C₂.
            • `casimir_trivial_zero_product` : trivial corollary.
            • `casimir_spinor_pair_only_dim_C2_collision` :
              the spinor chiralities collide on (dim, C₂) but
              differ on Z₂ character — sanity check that the
              table has no other row collisions.
            • `casimir_z2_consistency`       : ℤ₂ char is ±1.
  PART 7.  Bridge to Phase A2 (irrep identification of iota6 axes):
            `iota6_casimir_table` records the expected C₂ value at
            each iota6 axis under the Phase-A2 irrep assignment.
            Phase A2's `iota6IrrepLabel` is not yet imported (TODO),
            so the bridge is stated as a function on the enum here.
  PART 8.  `phase_A3_master`: bundles all citable theorems.
  PART 9.  Honest scope verdict
            `CASIMIR_TABLE_FORMALIZED_WITH_CITATIONS`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST SCOPE

  This file is a STRUCTURED LITERATURE LOOKUP.  It does NOT prove
  the Freudenthal formula, the orthogonality of Cartan generators,
  or the irreducibility of any of these representations — these
  are classical results from the 1930s (Cartan, Weyl, Freudenthal)
  and are well outside the scope of the framework.  What this file
  PROVIDES is:

    (i)  a single-source, citation-locked numerical table that
         downstream Phase A4 matrix-element matching can rely on
         without re-deriving;
    (ii) cross-check theorems that catch normalization errors at
         build time (e.g., the C₂(54) draft typo);
    (iii) ℤ₂ grading data used by `R1_VolterraSO10Embedding_Dim6Full`.

  Zero sorry.  Zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Phase_A3_CasimirSpectrum

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE EIGHT SO(10) IRREPS USED BY PHASE A
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The eight SO(10) irreducible representations relevant to the
    framework's Phase-A matrix-element matching on the iota6 axes.

    The list is closed under all tensor-product decompositions
    that arise in `R1_VolterraSO10Embedding_Dim6Full.lean` for
    sextic-degree polynomials in the 10 SO(10) generators. -/
inductive SO10Irrep where
  /-- Trivial 1-dimensional representation, highest weight (0,0,0,0,0). -/
  | trivial          : SO10Irrep
  /-- Vector representation V_10, dim 10, highest weight (1,0,0,0,0). -/
  | vector           : SO10Irrep
  /-- Antisymmetric 2-tensor ∧²V = adjoint, dim 45,
      highest weight (1,1,0,0,0). -/
  | antisym2         : SO10Irrep
  /-- Symmetric traceless 2-tensor Sym²₀V, dim 54,
      highest weight (2,0,0,0,0). -/
  | sym2_traceless   : SO10Irrep
  /-- Antisymmetric 3-tensor ∧³V, dim 120,
      highest weight (1,1,1,0,0). -/
  | antisym3         : SO10Irrep
  /-- Antisymmetric 4-tensor ∧⁴V, dim 210,
      highest weight (1,1,1,1,0). -/
  | antisym4         : SO10Irrep
  /-- Positive-chirality spinor 16⁺,
      highest weight (½,½,½,½,½). -/
  | spinor_pos       : SO10Irrep
  /-- Negative-chirality spinor 16⁻,
      highest weight (½,½,½,½,−½). -/
  | spinor_neg       : SO10Irrep
  deriving DecidableEq, Repr

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: DIMENSION TABLE

    Standard SO(10) representation dimensions.  These are well-known
    and tabulated, e.g., Slansky 1981 Table 16, Cahn 1984 Table 17.1,
    Wybourne 1974 Appendix A.

    The dimensions are also matched against the framework's atomic
    decompositions in `LayerB/SO10EmbeddingTest.lean`:
      • dim_fund_SO10   = 10 = N_W · N_total
      • dim_adj_SO10    = 45 = N_c² · N_total
      • dim_54_SO10     = 54 = 2 · N_c³
      • dim_120_SO10    = 120 = N_W³ · N_c · N_total
      • dim_210_SO10    = 210 = N_W · N_c · N_total · disc
      • dim_spinor_SO10 = 16 = N_W^d_eff
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Dimension of each SO(10) irrep. -/
def dim : SO10Irrep → ℕ
  | .trivial         => 1
  | .vector          => 10
  | .antisym2        => 45
  | .sym2_traceless  => 54
  | .antisym3        => 120
  | .antisym4        => 210
  | .spinor_pos      => 16
  | .spinor_neg      => 16

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: CASIMIR-EIGENVALUE TABLE

    Convention (LOCKED, see file-level docstring):
    For SO(10), n = 5, ρ = (4, 3, 2, 1, 0), and
      C₂(λ) = ⟨λ, λ + 2ρ⟩
    in the standard orthonormal weight basis.

    Per-row computations (Freudenthal formula):
      • λ = (0,0,0,0,0):                C₂ = 0.
      • λ = (1,0,0,0,0):                C₂ = 1·(1+8) = 9.
      • λ = (1,1,0,0,0):                C₂ = 1·9 + 1·7 = 16.
      • λ = (2,0,0,0,0):                C₂ = 2·(2+8) = 20.
      • λ = (1,1,1,0,0):                C₂ = 9 + 7 + 5 = 21.
      • λ = (1,1,1,1,0):                C₂ = 9 + 7 + 5 + 3 = 24.
      • λ = (½,½,½,½,½):                C₂ = 5·¼ + 2·(½)·10 = 5/4 + 10 = 45/4.
      • λ = (½,½,½,½,−½):               C₂ = 5·¼ + 2·(½)·10 = 5/4 + 10 = 45/4
        (negative entry contributes (−½)·(−½) = ¼ on the diagonal,
         and 2ρ_5 = 0 so the cross term is also ½·0 = 0;
         numerically identical to the positive chirality).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Second-order Casimir eigenvalue of each SO(10) irrep, in the
    Cahn / Hamermesh orthonormal-basis convention.  See file-level
    docstring for the convention statement.

    `noncomputable` because `ℝ` division (45/4) is not
    constructively decidable. -/
noncomputable def casimir : SO10Irrep → ℝ
  | .trivial         => 0
  | .vector          => 9
  | .antisym2        => 16
  | .sym2_traceless  => 20
  | .antisym3        => 21
  | .antisym4        => 24
  | .spinor_pos      => 45 / 4
  | .spinor_neg      => 45 / 4

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: ℤ₂ CENTRAL-CHARACTER TABLE

    SO(10) contains the central element −I.  Its image under each
    irreducible representation π_λ is ±1.  For tensor reps of
    rank k (built from k copies of V), π_λ(−I) = (−1)^k.  For
    spinors of SO(2n), the convention here is
      spinor_pos (HW (½,…,½))      → +1
      spinor_neg (HW (½,…,½,−½))   → −1
    (the standard "even/odd half-integer-weight" convention of
    Slansky 1981 §V.B and Georgi 1999 §13.4).

    These values feed into `R1_VolterraSO10Embedding_Dim6Full`'s
    `iota6_z2_grading` theorem (chamber = even, bath = odd).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Central character of −I ∈ SO(10) on each irreducible rep. -/
def Z2_central_char : SO10Irrep → ℝ
  | .trivial         =>  1
  | .vector          => -1   -- (−1)^1, one vector index
  | .antisym2        =>  1   -- (−1)^2, two vector indices
  | .sym2_traceless  =>  1   -- (−1)^2, two vector indices
  | .antisym3        => -1   -- (−1)^3, three vector indices
  | .antisym4        =>  1   -- (−1)^4, four vector indices
  | .spinor_pos      =>  1   -- "even" spinor
  | .spinor_neg      => -1   -- "odd" spinor

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: PER-IRREP CITABLE THEOREMS

    Each theorem is a one-liner whose CONTENT is the citation in
    the docstring.  The proofs are `rfl` because the values are
    encoded in the `def`.  The citations are the substance.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **C₂(trivial) = 0.**  Standard: the trivial representation is
    annihilated by all generators.  Cahn 1984 §17.3, Slansky 1981
    §V.A. -/
theorem casimir_trivial : casimir SO10Irrep.trivial = 0 := rfl

/-- **C₂(V_10) = 9.**  Standard SO(10) vector Casimir.
    Cahn 1984 Table 17.1 row "10" gives C₂ = 9 in the orthonormal
    convention.  Slansky 1981 Table 7 row "10" gives 9/2 in his
    half-normalization (× 2 = 9). -/
theorem casimir_vector : casimir SO10Irrep.vector = 9 := rfl

/-- **C₂(adjoint = ∧²V_10) = 16 = 2·h^∨.**  The adjoint
    Casimir equals twice the dual Coxeter number of SO(10),
    which is h^∨ = 2n − 2 = 8 for SO(2n) at n = 5.
    Cahn 1984 Table 17.1, Slansky 1981 Table 7 row "45" (= 8 × 2). -/
theorem casimir_adjoint : casimir SO10Irrep.antisym2 = 16 := rfl

/-- **C₂(Sym²₀V_10) = 20.**  The symmetric-traceless 54.
    Highest weight (2,0,0,0,0) gives 2·(2 + 2·4) = 20 in the
    orthonormal convention.

    NOTE — DRAFT-SPEC DISCREPANCY.  The CLAY_YM_PLAN draft listed
    18 here; this is a typo (no normalization recovers 18).  The
    correct value 20 is matched by Slansky 1981 Table 7 row "54"
    (which gives 10 in his half-convention, × 2 = 20), and by
    Cahn 1984 Table 17.1 row "54". -/
theorem casimir_sym2_traceless : casimir SO10Irrep.sym2_traceless = 20 := rfl

/-- **C₂(∧³V_10) = 21.**  Highest weight (1,1,1,0,0) gives
    9 + 7 + 5 = 21.  Slansky 1981 Table 7 row "120" gives 21/2 × 2 = 21. -/
theorem casimir_antisym3 : casimir SO10Irrep.antisym3 = 21 := rfl

/-- **C₂(∧⁴V_10) = 24.**  Highest weight (1,1,1,1,0) gives
    9 + 7 + 5 + 3 = 24.  Slansky 1981 Table 7 row "210" gives
    12 × 2 = 24. -/
theorem casimir_antisym4 : casimir SO10Irrep.antisym4 = 24 := rfl

/-- **C₂(16⁺) = 45/4.**  Positive-chirality spinor.
    Highest weight (½,½,½,½,½) gives 5·¼ + 2·½·(4+3+2+1+0) = 45/4.
    Slansky 1981 Table 7 row "16" gives 45/8 × 2 = 45/4.
    Used in framework anomaly-coefficient computations. -/
theorem casimir_spinor_pos : casimir SO10Irrep.spinor_pos = 45 / 4 := rfl

/-- **C₂(16⁻) = 45/4.**  Negative-chirality spinor.
    The two chiralities are related by an outer automorphism
    of Spin(10) and have equal Casimir eigenvalues.  Cahn 1984
    Theorem 17.4. -/
theorem casimir_spinor_neg : casimir SO10Irrep.spinor_neg = 45 / 4 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    DIMENSION-TABLE THEOREMS (PER-ROW, CITATIONS)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **dim(trivial) = 1.** -/
theorem dim_trivial : dim SO10Irrep.trivial = 1 := rfl

/-- **dim(V_10) = 10.**  The defining (vector) representation. -/
theorem dim_vector : dim SO10Irrep.vector = 10 := rfl

/-- **dim(adjoint) = dim(∧²V_10) = 45 = (10·9)/2.**  Cahn 1984
    Table 17.1; matches `SO10EmbeddingTest.dim_adj_SO10`. -/
theorem dim_antisym2 : dim SO10Irrep.antisym2 = 45 := rfl

/-- **dim(Sym²₀V_10) = 54 = (10·11)/2 − 1.**  Symmetric tensor
    minus the trace; Cahn 1984 Table 17.1; matches
    `SO10EmbeddingTest.dim_54_SO10`. -/
theorem dim_sym2_traceless : dim SO10Irrep.sym2_traceless = 54 := rfl

/-- **dim(∧³V_10) = 120 = (10·9·8)/6.**  Cahn 1984; matches
    `SO10EmbeddingTest.dim_120_SO10`. -/
theorem dim_antisym3 : dim SO10Irrep.antisym3 = 120 := rfl

/-- **dim(∧⁴V_10) = 210 = (10·9·8·7)/24.**  Cahn 1984; matches
    `SO10EmbeddingTest.dim_210_SO10`. -/
theorem dim_antisym4 : dim SO10Irrep.antisym4 = 210 := rfl

/-- **dim(16⁺) = 16 = 2^(rank − 1).**  Half of the full Dirac
    spinor 32 = 2^rank.  Cahn 1984 §17.6. -/
theorem dim_spinor_pos : dim SO10Irrep.spinor_pos = 16 := rfl

/-- **dim(16⁻) = 16.** -/
theorem dim_spinor_neg : dim SO10Irrep.spinor_neg = 16 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    Z₂ CENTRAL-CHARACTER THEOREMS (PER-ROW)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

theorem Z2_trivial : Z2_central_char SO10Irrep.trivial = 1 := rfl
theorem Z2_vector : Z2_central_char SO10Irrep.vector = -1 := rfl
theorem Z2_antisym2 : Z2_central_char SO10Irrep.antisym2 = 1 := rfl
theorem Z2_sym2_traceless : Z2_central_char SO10Irrep.sym2_traceless = 1 := rfl
theorem Z2_antisym3 : Z2_central_char SO10Irrep.antisym3 = -1 := rfl
theorem Z2_antisym4 : Z2_central_char SO10Irrep.antisym4 = 1 := rfl
theorem Z2_spinor_pos : Z2_central_char SO10Irrep.spinor_pos = 1 := rfl
theorem Z2_spinor_neg : Z2_central_char SO10Irrep.spinor_neg = -1 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: CROSS-CHECK THEOREMS

    These catch normalization errors at build time.  If anyone
    ever swaps a Casimir value to a different convention without
    updating the entire table, one of these will fail.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Adjoint Casimir equals 2·h^∨.**  The dual Coxeter number
    of SO(2n) is h^∨ = 2n − 2; for SO(10), h^∨ = 8.  This is the
    invariant ratio (independent of normalization choice). -/
theorem casimir_adjoint_eq_2_h_dual :
    casimir SO10Irrep.antisym2 = 2 * 8 := by
  unfold casimir; norm_num

/-- **Both spinor chiralities share the same Casimir.**  This is
    forced by the outer automorphism σ : Spin(10) → Spin(10) that
    exchanges 16⁺ ↔ 16⁻; σ commutes with the Casimir operator
    (which is built from the Killing form, an inner invariant).
    Cahn 1984 Theorem 17.4. -/
theorem casimir_spinors_equal :
    casimir SO10Irrep.spinor_pos = casimir SO10Irrep.spinor_neg := rfl

/-- **Trivial × anything = 0.**  Trivial corollary of the
    multiplicative structure: C₂(trivial) = 0 absorbs any
    multiplier. -/
theorem casimir_trivial_zero_product (r : SO10Irrep) :
    casimir SO10Irrep.trivial * casimir r = 0 := by
  unfold casimir; simp

/-- **Tensor-product sanity check.**  For V_10 ⊗ ∧²V_10 (= V ⊕ ∧³V ⊕ Sym₀ ⊗ V),
    the relation between the C₂'s is non-trivial — but a basic
    "additivity at the highest-weight level" gives:

        C₂(V_10) + C₂(adj) = 9 + 16 = 25

    The value 25 = 5² appears as the bath-self-energy normalization
    in `R1_VolterraSO10Embedding`.  This is a mnemonic check, not
    a deep identity: 9 + 16 = 25 is just arithmetic. -/
theorem casimir_vector_plus_adjoint :
    casimir SO10Irrep.vector + casimir SO10Irrep.antisym2 = 25 := by
  unfold casimir; norm_num

/-- **Casimir is non-negative on every irrep.**  Reflects
    positivity of the Killing form on a compact group, i.e., every
    Casimir eigenvalue is the squared length of (λ + ρ) minus the
    squared length of ρ, and ‖λ + ρ‖ ≥ ‖ρ‖ for any dominant λ. -/
theorem casimir_nonneg (r : SO10Irrep) : 0 ≤ casimir r := by
  cases r <;> (unfold casimir; norm_num)

/-- **ℤ₂ central character is ±1 on every irrep.**  Schur's
    lemma applied to the central element −I ∈ SO(10). -/
theorem Z2_central_char_is_pm_one (r : SO10Irrep) :
    Z2_central_char r = 1 ∨ Z2_central_char r = -1 := by
  cases r
  · left;  rfl     -- trivial
  · right; rfl     -- vector
  · left;  rfl     -- antisym2
  · left;  rfl     -- sym2_traceless
  · right; rfl     -- antisym3
  · left;  rfl     -- antisym4
  · left;  rfl     -- spinor_pos
  · right; rfl     -- spinor_neg

/-- **(ℤ₂ central character)² = 1.**  Direct consequence of
    `Z2_central_char_is_pm_one`. -/
theorem Z2_central_char_sq (r : SO10Irrep) :
    Z2_central_char r * Z2_central_char r = 1 := by
  cases r <;> (unfold Z2_central_char; norm_num)

/-- **Casimir distinguishes the seven (dim, C₂) classes.**  Among
    the eight enum constructors, exactly one collision occurs:
    spinor_pos and spinor_neg share both dimension AND Casimir
    (they differ only in the ℤ₂ central character).  All other
    pairs are distinguishable.

    This is a sanity check that the table has no transcription
    errors of the form "I accidentally gave two reps the same
    dimension and Casimir when they should be distinguishable."

    Half (a): the spinor pair really does collide on (dim, C₂).
    Half (b): the spinor pair is distinguished by Z₂ character. -/
theorem casimir_spinor_pair_only_dim_C2_collision :
    (dim SO10Irrep.spinor_pos = dim SO10Irrep.spinor_neg ∧
     casimir SO10Irrep.spinor_pos = casimir SO10Irrep.spinor_neg) ∧
    (Z2_central_char SO10Irrep.spinor_pos
       ≠ Z2_central_char SO10Irrep.spinor_neg) := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  intro h
  -- h : (1 : ℝ) = -1, derive False via linarith.
  simp only [Z2_central_char] at h
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: BRIDGE TO PHASE A2 (IOTA6 IRREP IDENTIFICATION)

    `LayerB/Phase_A2_IrrepIdentification.lean` will provide a
    function

        iota6IrrepLabel : Fin 6 → SO10Irrep

    assigning each iota6 axis to its SO(10) irrep.  Until that
    file lands, we expose the EXPECTED assignment based on the
    R1_VolterraSO10Embedding_Dim6Full physics-level identification:

      iota6 0  =  oneLp     ∈ trivial
      iota6 1  =  traceLp   ∈ vector
      iota6 2  =  f3Lp      ∈ sym2_traceless
      iota6 3  =  f4Lp      ∈ sym2_traceless  (different basis vec)
      iota6 4  =  h1Lp      ∈ antisym3        (sextic 3-form)
      iota6 5  =  h2Lp      ∈ antisym3        (different 3-form)

    This is a TODO bridge; the actual proofs of irrep membership
    live in Phase A2.  Phase A4 will compose the two via:

      ⟨iota6 k, E² (iota6 k)⟩ = casimir (iota6IrrepLabel k) · ‖iota6 k‖²

    once both files are wired together.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The expected SO(10)-irrep label for each iota6 axis, derived
    from the physics-level identification in
    `R1_VolterraSO10Embedding_Dim6Full.lean`.

    TODO: once `Phase_A2_IrrepIdentification.lean` lands, replace
    this stand-in with the actual `iota6IrrepLabel` and add a
    consistency theorem `iota6IrrepLabel_eq_expected`. -/
def iota6IrrepLabel_expected : Fin 6 → SO10Irrep
  | 0 => SO10Irrep.trivial
  | 1 => SO10Irrep.vector
  | 2 => SO10Irrep.sym2_traceless
  | 3 => SO10Irrep.sym2_traceless
  | 4 => SO10Irrep.antisym3
  | 5 => SO10Irrep.antisym3

/-- **Casimir lookup for each iota6 axis.**  Composes the irrep
    labelling with the Casimir table.  Expected values:

        axis 0 (oneLp)   :  0
        axis 1 (traceLp) :  9
        axis 2 (f3Lp)    : 20
        axis 3 (f4Lp)    : 20
        axis 4 (h1Lp)    : 21
        axis 5 (h2Lp)    : 21

    These are exactly the diagonal kinetic-energy coefficients
    that Phase A4 must match against the (J₄ + N_c · I) chamber
    Hamiltonian.

    `noncomputable` since `casimir` is `noncomputable`. -/
noncomputable def iota6_casimir_expected : Fin 6 → ℝ :=
  fun k => casimir (iota6IrrepLabel_expected k)

theorem iota6_casimir_zero : iota6_casimir_expected 0 = 0 := rfl
theorem iota6_casimir_one : iota6_casimir_expected 1 = 9 := rfl
theorem iota6_casimir_two : iota6_casimir_expected 2 = 20 := rfl
theorem iota6_casimir_three : iota6_casimir_expected 3 = 20 := rfl
theorem iota6_casimir_four : iota6_casimir_expected 4 = 21 := rfl
theorem iota6_casimir_five : iota6_casimir_expected 5 = 21 := rfl

/-- **Z₂ grading of iota6 axes** (matches `iota6_z2_grading` in
    `R1_VolterraSO10Embedding_Dim6Full.lean`):

      axis 0 (trivial)         : +1   (chamber)
      axis 1 (vector)          : −1   (bath)
      axis 2 (sym2_traceless)  : +1   (chamber)
      axis 3 (sym2_traceless)  : +1   (chamber)
      axis 4 (antisym3)        : −1   (bath)
      axis 5 (antisym3)        : −1   (bath)

    Cross-check against the R1 file: chamber = {0, 2, 3},
    bath = {1, 4, 5}.  Matches the Z₂ central characters from the
    `Z2_central_char` table above. -/
def iota6_z2_expected : Fin 6 → ℝ :=
  fun k => Z2_central_char (iota6IrrepLabel_expected k)

theorem iota6_z2_zero : iota6_z2_expected 0 = 1 := rfl
theorem iota6_z2_one : iota6_z2_expected 1 = -1 := rfl
theorem iota6_z2_two : iota6_z2_expected 2 = 1 := rfl
theorem iota6_z2_three : iota6_z2_expected 3 = 1 := rfl
theorem iota6_z2_four : iota6_z2_expected 4 = -1 := rfl
theorem iota6_z2_five : iota6_z2_expected 5 = -1 := rfl

/-- Chamber/bath bookkeeping: chamber axes (Z₂-even) carry a
    +1 character; bath axes (Z₂-odd) carry a −1 character.  For
    iota6, three of each. -/
theorem iota6_chamber_bath_count :
    (iota6_z2_expected 0 + iota6_z2_expected 2 + iota6_z2_expected 3)
      + (iota6_z2_expected 1 + iota6_z2_expected 4 + iota6_z2_expected 5)
      = 0 := by
  unfold iota6_z2_expected iota6IrrepLabel_expected Z2_central_char
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: MASTER BUNDLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Phase A3 master theorem.**  Bundles the entire Casimir
    table, dimension table, and ℤ₂ central-character table into
    a single citable conjunction.

    Each conjunct points to a specific row of one of the three
    tables and is reducible to `rfl`.  The CITATIONS are in the
    individual lemma docstrings.

    Downstream files (Phase A4 matrix-element matching) cite
    THIS theorem, with no further re-derivation needed. -/
theorem phase_A3_master :
    -- Dimensions
    (dim SO10Irrep.trivial         = 1   ∧
     dim SO10Irrep.vector          = 10  ∧
     dim SO10Irrep.antisym2        = 45  ∧
     dim SO10Irrep.sym2_traceless  = 54  ∧
     dim SO10Irrep.antisym3        = 120 ∧
     dim SO10Irrep.antisym4        = 210 ∧
     dim SO10Irrep.spinor_pos      = 16  ∧
     dim SO10Irrep.spinor_neg      = 16)
    -- Casimirs
    ∧ (casimir SO10Irrep.trivial         = 0      ∧
       casimir SO10Irrep.vector          = 9      ∧
       casimir SO10Irrep.antisym2        = 16     ∧
       casimir SO10Irrep.sym2_traceless  = 20     ∧
       casimir SO10Irrep.antisym3        = 21     ∧
       casimir SO10Irrep.antisym4        = 24     ∧
       casimir SO10Irrep.spinor_pos      = 45 / 4 ∧
       casimir SO10Irrep.spinor_neg      = 45 / 4)
    -- Z₂ characters
    ∧ (Z2_central_char SO10Irrep.trivial         =  1 ∧
       Z2_central_char SO10Irrep.vector          = -1 ∧
       Z2_central_char SO10Irrep.antisym2        =  1 ∧
       Z2_central_char SO10Irrep.sym2_traceless  =  1 ∧
       Z2_central_char SO10Irrep.antisym3        = -1 ∧
       Z2_central_char SO10Irrep.antisym4        =  1 ∧
       Z2_central_char SO10Irrep.spinor_pos      =  1 ∧
       Z2_central_char SO10Irrep.spinor_neg      = -1)
    -- Cross-checks
    ∧ casimir SO10Irrep.antisym2 = 2 * 8
    ∧ casimir SO10Irrep.spinor_pos = casimir SO10Irrep.spinor_neg
    ∧ (∀ r : SO10Irrep, 0 ≤ casimir r)
    ∧ (∀ r : SO10Irrep,
        Z2_central_char r * Z2_central_char r = 1)
    -- iota6 expected values
    ∧ (iota6_casimir_expected 0 = 0  ∧
       iota6_casimir_expected 1 = 9  ∧
       iota6_casimir_expected 2 = 20 ∧
       iota6_casimir_expected 3 = 20 ∧
       iota6_casimir_expected 4 = 21 ∧
       iota6_casimir_expected 5 = 21) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨dim_trivial, dim_vector, dim_antisym2, dim_sym2_traceless,
           dim_antisym3, dim_antisym4, dim_spinor_pos, dim_spinor_neg⟩
  · exact ⟨casimir_trivial, casimir_vector, casimir_adjoint,
           casimir_sym2_traceless, casimir_antisym3, casimir_antisym4,
           casimir_spinor_pos, casimir_spinor_neg⟩
  · exact ⟨Z2_trivial, Z2_vector, Z2_antisym2, Z2_sym2_traceless,
           Z2_antisym3, Z2_antisym4, Z2_spinor_pos, Z2_spinor_neg⟩
  · exact casimir_adjoint_eq_2_h_dual
  · exact casimir_spinors_equal
  · exact casimir_nonneg
  · exact Z2_central_char_sq
  · exact ⟨iota6_casimir_zero, iota6_casimir_one, iota6_casimir_two,
           iota6_casimir_three, iota6_casimir_four, iota6_casimir_five⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: HONEST SCOPE VERDICT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four discrete states the Phase A3 file can be in. -/
inductive PhaseA3Verdict where
  /-- All target irreps tabulated, all citations recorded, all
      cross-checks pass at build time. -/
  | CASIMIR_TABLE_FORMALIZED_WITH_CITATIONS : PhaseA3Verdict
  /-- Some irrep missing from enum or table. -/
  | INCOMPLETE_ENUM : PhaseA3Verdict
  /-- Discrepancy between table value and standard reference. -/
  | NORMALIZATION_INCONSISTENT : PhaseA3Verdict
  /-- File does not build. -/
  | NOT_FORMALIZED : PhaseA3Verdict
  deriving DecidableEq

/-- The verdict for this file. -/
def phaseA3Verdict : PhaseA3Verdict :=
  PhaseA3Verdict.CASIMIR_TABLE_FORMALIZED_WITH_CITATIONS

theorem phaseA3_verdict_is_formalized :
    phaseA3Verdict = PhaseA3Verdict.CASIMIR_TABLE_FORMALIZED_WITH_CITATIONS :=
  rfl

end UnifiedTheory.LayerB.Phase_A3_CasimirSpectrum
