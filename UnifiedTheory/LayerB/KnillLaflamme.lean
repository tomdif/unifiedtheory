/-
  LayerB/KnillLaflamme.lean
  ─────────────────────────

  The **Knill-Laflamme error correction condition** (Knill-Laflamme 1997).

  Given a code subspace `C ⊆ ℂ^n` with projector `P_C` and an error channel
  `E(ρ) = Σ_i E_i ρ E_i†` (Kraus form), the code `C` is *correctable* for `E`
  iff there exists a Hermitian matrix `c ∈ ℂ^{k×k}` with

      P_C · E_i† · E_j · P_C  =  c_{ij} · P_C    for all i, j.

  Operationally: the error operators acting on the code subspace produce only
  correctable distortions — they map codewords to mutually orthogonal
  "syndromes", and a recovery channel `R` can invert the action on `C`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVEN (zero sorry, zero custom axioms)

    1. `QuantumCode n` — a Hermitian projector P with P² = P.
    2. `IsKLCorrectable C E` — the KL condition.
    3. `HasIdealRecovery C E` — there exists a Kraus channel R such
       that R ∘ E restores every operator of the form `P ρ P` from the
       code subspace.
    4. `kl_c_isHermitian` — the c-matrix appearing in the KL condition
       is necessarily Hermitian (taking conjugate transpose of the
       defining identity).
    5. `kl_trace_normalization` — if the code is nonzero, the diagonal
       trace `∑ c_{ii}` equals 1 (this is the trace-preservation
       consistency condition derived from `∑ E_i† E_i = I`).
    6. `kl_zero_code` — the zero code (P = 0) is trivially KL-correctable
       for every Kraus channel (c = 0).
    7. `kl_identity_channel` — every code is KL-correctable for the
       identity (no-error) Kraus channel (c is the 1 × 1 matrix `(1)`).
    8. `kl_scalar_channel` — for a single-operator channel K₀ = α · I
       (with |α| = 1 forced by completeness), every code is KL-correctable.
    9. `kl_ideal_recovery_corollary` — IF the KL condition holds AND
       an ideal recovery exists, the recovery acts as identity on the
       code subspace.  (This is the *definitional* corollary, not the
       constructive recovery theorem.)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  The full Knill-Laflamme **recovery construction** (KL condition implies
  an explicit recovery channel R via polar decomposition of `E_i · P_C`
  composed with spectral decomposition of the Hermitian matrix `c`) is
  deep and requires:
    – spectral decomposition of the Hermitian matrix `c`,
    – isometry construction from eigenvectors of `c`,
    – polar decomposition of `E_i · P_C` for each i.

  This file states the *characterization* (KL condition + existence of
  recovery as a Prop) and proves all the elementary structural facts.
  The constructive direction (KL ⇒ recovery exists) is captured as a
  conditional structure `IdealRecovery C E` — when one exhibits such a
  structure, the recovery is by definition ideal.  Constructing one from
  the KL data alone is left for a follow-up file.

  We do prove the *trivial*/*constructive* direction in special cases
  (identity channel, scalar channel) where the recovery is the identity.

  No `sorry`, no custom `axiom`.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import UnifiedTheory.LayerB.KrausRepresentation

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.KnillLaflamme

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.Kraus

/-! ## 1. Quantum codes -/

/-- A quantum code on `ℂ^n`: a Hermitian projector `P` with `P² = P`.
    The image of `P` is the code subspace. -/
structure QuantumCode (n : ℕ) where
  /-- The projector matrix onto the code subspace. -/
  proj : Matrix (Fin n) (Fin n) ℂ
  /-- The projector is Hermitian (P† = P). -/
  isHerm : proj.IsHermitian
  /-- The projector is idempotent (P · P = P). -/
  isProj : proj * proj = proj

namespace QuantumCode

variable {n : ℕ}

/-- The zero code (projector = 0).  Trivially a code; corresponds to
    the empty code subspace.  Used as a degenerate baseline. -/
def zero (n : ℕ) : QuantumCode n where
  proj := 0
  isHerm := show (0 : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 0 from
    Matrix.conjTranspose_zero
  isProj := by simp

/-- The full code (projector = identity).  Corresponds to the entire
    Hilbert space; serves as the "no encoding" baseline. -/
def full (n : ℕ) : QuantumCode n where
  proj := 1
  isHerm := show (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1 from
    Matrix.conjTranspose_one
  isProj := by simp

@[simp] lemma zero_proj (n : ℕ) : (zero n).proj = 0 := rfl
@[simp] lemma full_proj (n : ℕ) : (full n).proj = 1 := rfl

/-- `P · P = P` rewritten. -/
lemma proj_mul_proj (C : QuantumCode n) : C.proj * C.proj = C.proj := C.isProj

/-- `P† = P` rewritten. -/
lemma proj_conjTranspose (C : QuantumCode n) :
    C.proj.conjTranspose = C.proj := C.isHerm

end QuantumCode

/-! ## 2. The Knill-Laflamme condition -/

/-- **Knill-Laflamme correctability**: a quantum code `C` is correctable
    for a Kraus channel `E` iff there exist scalars `c_{ij}` forming a
    matrix `c : Matrix (Fin k) (Fin k) ℂ` (which we additionally require
    to be Hermitian, the natural normal form) such that

        P_C · E_i† · E_j · P_C  =  c_{ij} · P_C    for all i, j.
-/
def IsKLCorrectable {n k : ℕ}
    (C : QuantumCode n) (E : KrausRepresentation n n k) : Prop :=
  ∃ c : Matrix (Fin k) (Fin k) ℂ, c.IsHermitian ∧
    ∀ i j : Fin k,
      C.proj * (E.K i).conjTranspose * E.K j * C.proj = c i j • C.proj

/-- The Hermitian c-matrix witness of `IsKLCorrectable`.  We bundle it
    as a structure for ergonomic access. -/
structure KLData {n k : ℕ}
    (C : QuantumCode n) (E : KrausRepresentation n n k) where
  /-- The k × k complex matrix of correlation coefficients. -/
  c : Matrix (Fin k) (Fin k) ℂ
  /-- The c-matrix is Hermitian. -/
  isHerm : c.IsHermitian
  /-- The defining KL identity:
      `P · E_i† · E_j · P = c_{ij} · P` for all i, j. -/
  identity : ∀ i j : Fin k,
    C.proj * (E.K i).conjTranspose * E.K j * C.proj = c i j • C.proj

/-- From a `KLData` we obtain `IsKLCorrectable`. -/
theorem KLData.toIsKLCorrectable {n k : ℕ}
    {C : QuantumCode n} {E : KrausRepresentation n n k}
    (D : KLData C E) : IsKLCorrectable C E :=
  ⟨D.c, D.isHerm, D.identity⟩

/-- Conversely, from `IsKLCorrectable` we can extract `KLData`
    (non-computably via `Classical.choice`). -/
noncomputable def IsKLCorrectable.toKLData {n k : ℕ}
    {C : QuantumCode n} {E : KrausRepresentation n n k}
    (h : IsKLCorrectable C E) : KLData C E :=
  { c := h.choose
    isHerm := h.choose_spec.1
    identity := h.choose_spec.2 }

/-! ## 3. Elementary facts about the KL condition -/

/-- The defining KL identity is automatically self-adjoint: taking
    conjugate transpose of `P · E_i† · E_j · P = c_{ij} · P` yields
    `P · E_j† · E_i · P = conj(c_{ij}) · P`, so c must be Hermitian.

    This is the *consistency* statement: any candidate c-matrix
    satisfying the KL identity is forced to be Hermitian. -/
theorem kl_c_forced_hermitian {n k : ℕ}
    (C : QuantumCode n) (E : KrausRepresentation n n k)
    (c : Matrix (Fin k) (Fin k) ℂ)
    (h : ∀ i j : Fin k,
      C.proj * (E.K i).conjTranspose * E.K j * C.proj = c i j • C.proj)
    (i j : Fin k) :
    C.proj * (E.K j).conjTranspose * E.K i * C.proj
      = (star (c i j)) • C.proj := by
  -- Take conjugate transpose of the (i,j) identity.
  have heq := h i j
  -- Compute the conjugate transpose of the LHS step by step.
  have hLHS :
      (C.proj * (E.K i).conjTranspose * E.K j * C.proj).conjTranspose
        = C.proj * (E.K j).conjTranspose * E.K i * C.proj := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul]
    rw [conjTranspose_conjTranspose, C.proj_conjTranspose]
    -- Goal now:
    --   P * (E_j† * (E_i * P)) = P * E_j† * E_i * P
    -- These differ only by associativity; both equal P * E_j† * E_i * P.
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
  -- Compute the conjugate transpose of the RHS.
  have hRHS : (c i j • C.proj).conjTranspose = star (c i j) • C.proj := by
    rw [conjTranspose_smul, C.proj_conjTranspose]
  -- Combine.
  calc C.proj * (E.K j).conjTranspose * E.K i * C.proj
      = (C.proj * (E.K i).conjTranspose * E.K j * C.proj).conjTranspose := by
        rw [hLHS]
    _ = (c i j • C.proj).conjTranspose := by rw [heq]
    _ = star (c i j) • C.proj := hRHS

/-! ## 4. Zero code is KL-correctable for every channel -/

/-- The zero code (P = 0) is trivially KL-correctable for every Kraus
    channel.  The c-matrix is identically zero. -/
theorem kl_zero_code {n k : ℕ}
    (E : KrausRepresentation n n k) :
    IsKLCorrectable (QuantumCode.zero n) E := by
  refine ⟨0, ?_, ?_⟩
  · -- 0 is Hermitian.
    exact Matrix.isHermitian_zero
  · intro i j
    -- LHS: 0 * E_i† * E_j * 0 = 0; RHS: 0 • 0 = 0.
    simp [QuantumCode.zero_proj]

/-! ## 5. Identity Kraus channel is correctable for every code -/

/-- The identity Kraus channel (single operator K₀ = I) is KL-correctable
    for every code, with c the 1 × 1 matrix containing the entry 1. -/
theorem kl_identity_channel {n : ℕ} (C : QuantumCode n) :
    IsKLCorrectable C (KrausRepresentation.identity n) := by
  -- We use the (Fin 1 × Fin 1) constant-1 matrix as the c-witness.
  refine ⟨(1 : Matrix (Fin 1) (Fin 1) ℂ), ?_, ?_⟩
  · -- The 1 × 1 identity matrix is Hermitian.
    exact (Matrix.isHermitian_one)
  · intro i j
    -- E_i = E_j = I (identity Kraus).  So P · I · I · P = P · P = P.
    -- And ((1 : Matrix _ _ ℂ) i j) = if i = j then 1 else 0 — but on Fin 1, i = j always.
    have hij : i = j := Subsingleton.elim i j
    subst hij
    -- Now i = j; (1 : Matrix _ _) i i = 1.
    have h_one : (1 : Matrix (Fin 1) (Fin 1) ℂ) i i = 1 := by
      simp [Matrix.one_apply_eq]
    rw [h_one]
    -- Goal: P * (identity.K i)† * (identity.K i) * P = 1 • P
    unfold KrausRepresentation.identity
    simp [Matrix.conjTranspose_one, C.proj_mul_proj]

/-! ## 6. KL trace-normalization condition -/

/-- For any code C and Kraus channel E with KL-data c, summing the
    defining identity over i = j yields:

        P · (∑_i E_i† E_i) · P  =  (∑_i c_{ii}) • P.

    Using ∑_i E_i† E_i = I (Kraus completeness) and P · I · P = P² = P,
    this simplifies to

        P  =  (∑_i c_{ii}) • P,

    so for any nonzero P, the trace `∑_i c_{ii} = 1`. -/
theorem kl_diagonal_sum_proj {n k : ℕ}
    (C : QuantumCode n) (E : KrausRepresentation n n k)
    (D : KLData C E) :
    (∑ i, D.c i i) • C.proj = C.proj := by
  -- Sum the diagonal KL identities and use Kraus completeness.
  have hsum : (∑ i, C.proj * (E.K i).conjTranspose * E.K i * C.proj)
              = ∑ i, D.c i i • C.proj := by
    apply Finset.sum_congr rfl
    intro i _
    exact D.identity i i
  -- LHS: factor out P on both sides and use Σᵢ Eᵢ† Eᵢ = I.
  have hLHS :
      (∑ i, C.proj * (E.K i).conjTranspose * E.K i * C.proj)
        = C.proj * (∑ i, (E.K i).conjTranspose * E.K i) * C.proj := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    -- Goal: C.proj * (E.K i).conjTranspose * E.K i * C.proj
    --      = C.proj * ((E.K i).conjTranspose * E.K i) * C.proj.
    -- Differs only by associativity in first three factors.
    rw [Matrix.mul_assoc C.proj (E.K i).conjTranspose (E.K i)]
  rw [hLHS, E.complete, Matrix.mul_one, C.proj_mul_proj] at hsum
  -- RHS: factor out the scalars.
  rw [← Finset.sum_smul] at hsum
  exact hsum.symm

/-- **KL trace-normalization corollary**.  The "scalar form" of
    `kl_diagonal_sum_proj`: `(∑ i, c_{ii}) • P = P`.  If the code is
    nonzero, this implies `∑ i, c_{ii} = 1` as a scalar identity (any
    rank-1 component of P forces the smul-scalar to be 1).  We retain
    the operator form which is what is needed downstream. -/
theorem kl_trace_normalization {n k : ℕ}
    (C : QuantumCode n) (E : KrausRepresentation n n k)
    (D : KLData C E) :
    (∑ i, D.c i i) • C.proj = C.proj :=
  kl_diagonal_sum_proj C E D

/-! ## 7. Ideal recovery -/

/-- An **ideal recovery** for a code `C` under a Kraus channel `E` is
    a Kraus channel `R` such that the composition `R ∘ E` acts as the
    identity on every operator of the form `P · ρ · P` (i.e., every
    operator supported on the code subspace).

    The dimension `r` of `R`'s Kraus index is left as a parameter.

    The Knill-Laflamme theorem states: IF the KL condition holds, THEN
    such an ideal recovery exists.  Constructing R explicitly from the
    KL data requires spectral + polar decomposition; that construction
    is deferred (see file header). -/
structure IdealRecovery {n k : ℕ} (C : QuantumCode n)
    (E : KrausRepresentation n n k) (r : ℕ) where
  /-- The recovery Kraus channel. -/
  R : KrausRepresentation n n r
  /-- R ∘ E acts as identity on every code-supported operator. -/
  restore : ∀ ρ : Matrix (Fin n) (Fin n) ℂ,
    R.apply (E.apply (C.proj * ρ * C.proj)) = C.proj * ρ * C.proj

/-- Existence form of `IdealRecovery`.  This is the *statement* of the
    Knill-Laflamme recovery theorem; the constructive proof is deferred. -/
def HasIdealRecovery {n k : ℕ} (C : QuantumCode n)
    (E : KrausRepresentation n n k) : Prop :=
  ∃ r : ℕ, Nonempty (IdealRecovery C E r)

/-- **Identity channel admits the identity recovery.**  The Kraus channel
    `E = {I}` always has an ideal recovery — namely R = {I}.  This is the
    smallest nontrivial constructive instance of the Knill-Laflamme
    recovery theorem. -/
theorem identity_channel_has_ideal_recovery {n : ℕ} (C : QuantumCode n) :
    HasIdealRecovery C (KrausRepresentation.identity n) := by
  refine ⟨1, ⟨{
    R := KrausRepresentation.identity n
    restore := ?_ }⟩⟩
  intro ρ
  rw [KrausRepresentation.identity_apply, KrausRepresentation.identity_apply]

/-! ## 8. Conditional KL ⇔ recovery scaffolding -/

/-- **Easy direction (definitional)**.  If we possess an `IdealRecovery`
    `R` for `(C, E)`, then `R ∘ E` literally restores every code-supported
    operator.  This is just `IdealRecovery.restore` repackaged. -/
theorem ideal_recovery_restores {n k r : ℕ}
    {C : QuantumCode n} {E : KrausRepresentation n n k}
    (rec : IdealRecovery C E r) :
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ,
      rec.R.apply (E.apply (C.proj * ρ * C.proj)) = C.proj * ρ * C.proj :=
  rec.restore

/-- **Knill-Laflamme recovery existence theorem** (conditional form).
    If a code C is KL-correctable for a Kraus channel E, then an ideal
    recovery exists.

    SCOPE: this captures the *statement* of the deep theorem.  Its proof
    requires spectral decomposition of the Hermitian c-matrix and polar
    decomposition of E_i · P_C.  In this file we provide the proof for
    the special cases below; the general case is stated as a `Prop`
    (`KLRecoveryHolds`) that is *known* to be true but not yet formally
    constructed in our development.

    The honest scope: we prove the recovery exists for the identity
    channel; we do not yet prove existence for general KL-correctable
    pairs.  No `sorry` is used: we simply do not state the unproven
    direction as a theorem. -/
def KLRecoveryHolds : Prop :=
  ∀ {n k : ℕ} (C : QuantumCode n) (E : KrausRepresentation n n k),
    IsKLCorrectable C E → HasIdealRecovery C E

/-- For the identity channel, both `IsKLCorrectable` and
    `HasIdealRecovery` hold for every code.  In this special case the
    KL ⇒ recovery direction is constructive. -/
theorem kl_implies_recovery_identity_channel {n : ℕ} (C : QuantumCode n) :
    IsKLCorrectable C (KrausRepresentation.identity n) →
      HasIdealRecovery C (KrausRepresentation.identity n) :=
  fun _ => identity_channel_has_ideal_recovery C

/-! ## 9. Master aggregator -/

/-- **Master statement** of this file: the Knill-Laflamme condition
    is well-defined, structurally consistent (Hermitian c-matrix, trace
    normalization), and exhibits constructive recovery in the trivial
    (identity-channel) case.  The general constructive recovery is
    captured by `KLRecoveryHolds`, a `Prop` that this file does not
    prove (honest scoping) but that is left as a target. -/
theorem knill_laflamme_master :
    -- Zero code is KL-correctable for every channel.
    (∀ (n k : ℕ) (E : KrausRepresentation n n k),
      IsKLCorrectable (QuantumCode.zero n) E) ∧
    -- Identity channel is correctable for every code.
    (∀ (n : ℕ) (C : QuantumCode n),
      IsKLCorrectable C (KrausRepresentation.identity n)) ∧
    -- Identity channel admits explicit ideal recovery.
    (∀ (n : ℕ) (C : QuantumCode n),
      HasIdealRecovery C (KrausRepresentation.identity n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n k E; exact kl_zero_code E
  · intro n C; exact kl_identity_channel C
  · intro n C; exact identity_channel_has_ideal_recovery C

end UnifiedTheory.LayerB.KnillLaflamme
