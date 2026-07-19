/-
  LayerC/BitCommitmentImpossibility.lean — Mayers-Lo-Chau impossibility
  of perfect quantum bit commitment.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  In 1997 Mayers (PRL 78, 3414) and independently Lo & Chau (PRL 78,
  3410) proved that no quantum protocol can implement an unconditionally
  secure bit commitment scheme.  A bit commitment protocol has two
  desiderata:

    • CONCEALING  — Bob, holding his half of the shared state, cannot
      learn the value of Alice's committed bit before she reveals it.
    • BINDING     — Alice, having sent her half over, cannot freely
      change the value she will reveal later.

  The Mayers-Lo-Chau theorem states that these two properties are
  *mutually exclusive* in any quantum protocol:  if the protocol is
  PERFECTLY concealing then it cannot be binding, because Alice can
  always apply a *local* unitary on her own register to interconvert
  between the two committed states.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE ARGUMENT (real-amplitude version)

  Let the bipartite state on Alice⊗Bob be the real n×n matrix of
  amplitudes  ψ_b : Fin n × Fin n → ℝ  (b ∈ {0,1}).  Bob's reduced
  density matrix is

       ρ_b^B  :=  ψ_bᵀ · ψ_b,

  the standard partial trace over Alice (`tr_A |ψ⟩⟨ψ|` written for
  real amplitudes).

  PERFECTLY CONCEALING  ⟺  ρ_0^B = ρ_1^B
  PERFECTLY BINDING     ⟺  ¬ ∃ U ∈ O(n).  U · ψ_0 = ψ_1.

  HUGHSTON-JOZSA-WOOTTERS:  any two purifications of the same
  reduced state on Bob's side are related by a unitary on Alice's
  side.  For real amplitudes, "unitary" becomes "orthogonal":

       HJW  :   ρ_0^B = ρ_1^B  ⟹  ∃ U ∈ O(n).  U · ψ_0 = ψ_1.

  Composing these two facts is the entire impossibility theorem:

       perfect concealing  +  HJW   ⟹   ¬ binding.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `BCProtocol`            : a bit commitment protocol (two normalised
                              bipartite states ψ_0, ψ_1 on `Fin n × Fin n`).
  – `BCProtocol.bobReduced` : Bob's reduced state  ρ_b^B = ψ_bᵀ · ψ_b.
  – `BCProtocol.IsConcealing`: ρ_0^B = ρ_1^B.
  – `BCProtocol.IsBinding`  : no Alice-side orthogonal U converts ψ_0 to ψ_1.
  – `HJW_Target`            : the named structural hypothesis
                              (purifications related by an Alice-side
                              orthogonal).
  – `no_perfect_BC_protocol` : conditional impossibility theorem.  Given
                              HJW, no bit commitment protocol can be
                              both concealing and binding.
  – `hjw_dim_one`           : UNCONDITIONAL proof of HJW for the
                              n = 1 special case (scalars).
  – `no_perfect_BC_protocol_dim_one` : UNCONDITIONAL impossibility
                              theorem for n = 1.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Real amplitudes.  The framework's two-particle state space is
    `Matrix (Fin n) (Fin n) ℝ` (= `TwoParticleState n`).  This is the
    real-amplitude restriction of the complex-amplitude theorem.  The
    structural argument is identical; only "unitary" becomes
    "orthogonal" and the Schmidt decomposition becomes the real SVD.
    The whole "perfect concealing ⇒ ¬ binding" logic is identical.

  – Square states.  We work with `n_A = n_B = n` (the dimensions of
    Alice's and Bob's registers are taken equal).  This is the
    framework's `TwoParticleState n` convention and is the case used
    in the standard textbook arguments.

  – `HJW_Target` is the **named analytical content** of the proof.  The
    full Hughston-Jozsa-Wootters theorem (for arbitrary `n`) requires
    the existence of real-SVD plus uniqueness-up-to-orthogonal-action,
    which lives in Mathlib's `LinearAlgebra.Matrix.SpecialLinearGroup`
    family but not as a directly-invocable lemma in the form we need
    here.  We discharge HJW UNCONDITIONALLY in the n = 1 case and
    state it as a NAMED hypothesis for n ≥ 2.  The conditional
    impossibility theorem (the headline) is a clean three-line
    consequence; the n = 1 unconditional version specialises it to
    the simplest dimension.

  Zero `sorry`.  Zero custom axioms.
-/
import UnifiedTheory.LayerB.SchmidtDecomposition
import Mathlib.LinearAlgebra.UnitaryGroup

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.BitCommitmentImpossibility

open UnifiedTheory.LayerB.QuantumEntanglement
open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1 — BIT COMMITMENT PROTOCOL STRUCTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A protocol commits Alice to a bit `b ∈ {0,1}` by preparing a
    bipartite state |ψ_b⟩ on her register A and Bob's register B.
    We model the amplitudes as a real n × n matrix
        ψ_b : Fin n → Fin n → ℝ.
    Normalisation is the standard ‖ψ‖² = 1 condition, which in
    matrix language is `tr(ψᵀ · ψ) = 1`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A real-amplitude bipartite quantum bit commitment protocol on a
    register of dimension `n` for both Alice and Bob.  For each bit
    `b ∈ Fin 2`, the protocol prescribes a normalised two-particle
    state `ψ b : TwoParticleState n`. -/
structure BCProtocol where
  /-- The shared register dimension on each side. -/
  n : ℕ
  /-- The bipartite state Alice prepares for bit `b`. -/
  ψ : Fin 2 → TwoParticleState n
  /-- Each prepared state is normalised:  ∑_{i,j} ψ b (i,j)² = 1. -/
  normalized : ∀ b, ∑ i, ∑ j, (ψ b i j) ^ 2 = 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2 — BOB'S REDUCED STATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a real-amplitude bipartite state `ψ : Fin n → Fin n → ℝ`,
    Bob's reduced density matrix is the partial trace over Alice's
    indices:
        ρ^B(j, j')  =  ∑_i  ψ(i, j) · ψ(i, j')
                    =  (ψᵀ · ψ)(j, j').
    This is the real-amplitude specialisation of `tr_A |ψ⟩⟨ψ|`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bob's reduced state** for bit `b` in the protocol `P`:
    `ρ_b^B = ψ_bᵀ · ψ_b`.  This is the real-amplitude partial trace
    over Alice's register. -/
def BCProtocol.bobReduced (P : BCProtocol) (b : Fin 2) :
    Matrix (Fin P.n) (Fin P.n) ℝ :=
  (P.ψ b)ᵀ * (P.ψ b)

/-- Explicit entry-wise form of Bob's reduced state. -/
theorem BCProtocol.bobReduced_apply (P : BCProtocol) (b : Fin 2)
    (j j' : Fin P.n) :
    P.bobReduced b j j' = ∑ i, P.ψ b i j * P.ψ b i j' := by
  unfold BCProtocol.bobReduced
  simp [Matrix.mul_apply, Matrix.transpose_apply]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3 — ALICE'S LOCAL ACTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A unitary `U` on Alice's register acts on the bipartite state as
    `U_A ⊗ I_B`.  In amplitude language this is left-multiplication
    by U:  `(U · ψ)(i, j) = ∑_{i'} U(i, i') · ψ(i', j)`.
    For real amplitudes, "unitary" means "orthogonal":
    `U ∈ Matrix.orthogonalGroup n ℝ`,  equivalently  `U · Uᵀ = 1`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Alice's local unitary action** on a bipartite state:
    `(U_A ⊗ I_B) · ψ = U · ψ` (matrix product).  No assumption on `U`
    is built in here; orthogonality is added at the use site. -/
def aliceAction {n : ℕ} (U ψ : Matrix (Fin n) (Fin n) ℝ) :
    TwoParticleState n := U * ψ

/-- Convenience lemma: Alice's action preserves Bob's reduced state
    whenever `U` is orthogonal (`U · Uᵀ = 1`, equivalently
    `Uᵀ · U = 1`). -/
theorem aliceAction_preserves_bobReduced {n : ℕ}
    (U ψ : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    (aliceAction U ψ)ᵀ * (aliceAction U ψ) = ψᵀ * ψ := by
  unfold aliceAction
  -- (U·ψ)ᵀ · (U·ψ) = ψᵀ · Uᵀ · U · ψ = ψᵀ · 1 · ψ = ψᵀ · ψ.
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U ψ, hU,
      Matrix.one_mul]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4 — THE TWO SECURITY PROPERTIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Perfect concealing**: Bob's reduced state is the same for
    both bits.  Bob learns nothing about `b` from his register. -/
def BCProtocol.IsConcealing (P : BCProtocol) : Prop :=
  P.bobReduced 0 = P.bobReduced 1

/-- **Perfect binding**: there is no orthogonal unitary on Alice's
    register taking `ψ_0` to `ψ_1`.  Alice cannot freely switch from
    a `0`-commitment to a `1`-commitment after Bob has received his
    half of the state. -/
def BCProtocol.IsBinding (P : BCProtocol) : Prop :=
  ¬ ∃ U : Matrix (Fin P.n) (Fin P.n) ℝ,
      U ∈ Matrix.orthogonalGroup (Fin P.n) ℝ ∧
      aliceAction U (P.ψ 0) = P.ψ 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5 — THE HUGHSTON-JOZSA-WOOTTERS HYPOTHESIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The named analytical content of the impossibility proof:  any
    two purifications of the same reduced state on Bob's side are
    related by an orthogonal unitary on Alice's side.

    For real amplitudes this is the statement that two real n × n
    matrices `ψ, φ` with the same Gram matrix `ψᵀψ = φᵀφ` differ
    by a left orthogonal factor `U`:  `U · ψ = φ`.  Equivalently
    (right-action versus left-action conventions),  this is the
    uniqueness up to orthogonal action of the real SVD.

    For complex amplitudes it is the original HJW theorem and the
    key input to Mayers's and Lo-Chau's argument.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HJW target** (real-amplitude form): any two states with the
    same Bob-reduced state are related by an Alice-side orthogonal.
    This is the named open analytical content of the impossibility
    proof. -/
def HJW_Target : Prop :=
  ∀ {n : ℕ} (ψ φ : Matrix (Fin n) (Fin n) ℝ),
      ψᵀ * ψ = φᵀ * φ →
      ∃ U : Matrix (Fin n) (Fin n) ℝ,
          U ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
          U * ψ = φ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6 — THE CONDITIONAL IMPOSSIBILITY THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Given the HJW hypothesis, perfect concealing forces the existence
    of an Alice-side orthogonal U converting `ψ_0` into `ψ_1`, which
    is exactly the witness violating binding.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE MAYERS-LO-CHAU IMPOSSIBILITY THEOREM (conditional form)**.

    Assume the Hughston-Jozsa-Wootters property (`HJW_Target`).  Then
    no real-amplitude bit commitment protocol can be simultaneously
    perfectly concealing and perfectly binding.

    Proof sketch.  Concealing says `ψ_0ᵀψ_0 = ψ_1ᵀψ_1`; HJW supplies
    an orthogonal U with `U · ψ_0 = ψ_1`, which is precisely the
    binding-violating witness. -/
theorem no_perfect_BC_protocol (hHJW : HJW_Target) :
    ¬ ∃ P : BCProtocol, P.IsConcealing ∧ P.IsBinding := by
  rintro ⟨P, hConceal, hBind⟩
  -- Unpack concealing into the matrix identity ψ_0ᵀ ψ_0 = ψ_1ᵀ ψ_1.
  have hgram : (P.ψ 0)ᵀ * (P.ψ 0) = (P.ψ 1)ᵀ * (P.ψ 1) := hConceal
  -- Apply HJW.
  obtain ⟨U, hU, hUψ⟩ := hHJW (P.ψ 0) (P.ψ 1) hgram
  -- This U is exactly the witness violating binding.
  exact hBind ⟨U, hU, hUψ⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7 — UNCONDITIONAL DIMENSION-ONE IMPOSSIBILITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    HJW for `n = 1`.  When both Alice's and Bob's registers are
    1-dimensional, a "state" is a single real number `ψ ∈ ℝ`.  The
    "Gram identity"  ψᵀ · ψ = φᵀ · φ  collapses to  ψ² = φ²,  hence
    φ = ±ψ.  The required orthogonal U is either +1 or −1, both of
    which are in O(1).

    This is the simplest concrete instance of HJW; combined with the
    conditional impossibility theorem it gives a fully unconditional
    n = 1 impossibility statement.  No `sorry`, no custom axioms.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 1×1 identity matrix as an orthogonal unitary. -/
private lemma one_in_O1 :
    (1 : Matrix (Fin 1) (Fin 1) ℝ) ∈ Matrix.orthogonalGroup (Fin 1) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_one, Matrix.one_mul]

/-- Negation of the 1×1 identity is also orthogonal:  (−1)·(−1)ᵀ = 1. -/
private lemma neg_one_in_O1 :
    (-1 : Matrix (Fin 1) (Fin 1) ℝ) ∈ Matrix.orthogonalGroup (Fin 1) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, Matrix.one_apply, Fin.isValue]

/-- Helper: in `Fin 1` a matrix is determined by its (0,0) entry. -/
private lemma fin_one_matrix_eq (A B : Matrix (Fin 1) (Fin 1) ℝ)
    (h : A 0 0 = B 0 0) : A = B := by
  ext i j; fin_cases i; fin_cases j; exact h

/-- The HJW hypothesis holds UNCONDITIONALLY for `n = 1` real matrices. -/
theorem hjw_dim_one (ψ φ : Matrix (Fin 1) (Fin 1) ℝ)
    (hgram : ψᵀ * ψ = φᵀ * φ) :
    ∃ U : Matrix (Fin 1) (Fin 1) ℝ,
        U ∈ Matrix.orthogonalGroup (Fin 1) ℝ ∧ U * ψ = φ := by
  -- Extract the scalar identity ψ(0,0)² = φ(0,0)².
  have h00 : (ψ 0 0) ^ 2 = (φ 0 0) ^ 2 := by
    have hentry : (ψᵀ * ψ) 0 0 = (φᵀ * φ) 0 0 := by rw [hgram]
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one,
           pow_two] using hentry
  -- The scalar identity gives φ = ±ψ.  Factor x² − y² = (x+y)(x−y).
  have hsq : (ψ 0 0 + φ 0 0) * (ψ 0 0 - φ 0 0) = 0 := by nlinarith [h00]
  have hcases := mul_eq_zero.mp hsq
  have hpm : φ 0 0 = ψ 0 0 ∨ φ 0 0 = -(ψ 0 0) := by
    rcases hcases with h | h
    · right; linarith
    · left;  linarith
  -- Pick U = +1 or U = -1 accordingly.
  rcases hpm with hpos | hneg
  · refine ⟨(1 : Matrix (Fin 1) (Fin 1) ℝ), one_in_O1, ?_⟩
    apply fin_one_matrix_eq
    simp [Matrix.mul_apply, Matrix.one_apply, hpos]
  · refine ⟨(-1 : Matrix (Fin 1) (Fin 1) ℝ), neg_one_in_O1, ?_⟩
    apply fin_one_matrix_eq
    have hentry : (-1 : Matrix (Fin 1) (Fin 1) ℝ) * ψ = -ψ := by
      rw [neg_one_mul]
    rw [hentry]
    simp only [Matrix.neg_apply, hneg]

/-- **UNCONDITIONAL MAYERS-LO-CHAU IN DIMENSION ONE.**

    For 1×1 bit commitment protocols, no protocol can be both
    concealing and binding.  This is the smallest, simplest concrete
    instance of the Mayers-Lo-Chau impossibility theorem, proved
    without any analytical hypothesis. -/
theorem no_perfect_BC_protocol_dim_one
    (P : BCProtocol) (hn : P.n = 1)
    (hConceal : P.IsConcealing) :
    ¬ P.IsBinding := by
  -- Destructure the protocol and rewrite n to 1.
  obtain ⟨n, ψ, hnorm⟩ := P
  -- Now `hn : n = 1`, and the data lives over `Fin n`.
  cases hn
  intro hBind
  -- Specialise concealing to the scalar Gram identity.
  have hgram : (ψ 0)ᵀ * (ψ 0) = (ψ 1)ᵀ * (ψ 1) := hConceal
  obtain ⟨U, hU, hUψ⟩ := hjw_dim_one (ψ 0) (ψ 1) hgram
  exact hBind ⟨U, hU, hUψ⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8 — MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MAYERS-LO-CHAU MASTER.**  The bit-commitment impossibility
    package: a conditional general-dimension impossibility and the
    unconditional dimension-one specialisation. -/
theorem mayers_lo_chau_master :
    -- (1) Bob's reduced state is well-defined.
    (∀ (P : BCProtocol) (b : Fin 2) (j j' : Fin P.n),
        P.bobReduced b j j' = ∑ i, P.ψ b i j * P.ψ b i j')
    -- (2) Alice's orthogonal action preserves Bob's reduced state.
    ∧ (∀ {n : ℕ} (U ψ : Matrix (Fin n) (Fin n) ℝ),
          Uᵀ * U = 1 →
          (aliceAction U ψ)ᵀ * (aliceAction U ψ) = ψᵀ * ψ)
    -- (3) Conditional impossibility (general dimension).
    ∧ (HJW_Target →
        ¬ ∃ P : BCProtocol, P.IsConcealing ∧ P.IsBinding)
    -- (4) HJW holds UNCONDITIONALLY in dimension one.
    ∧ (∀ ψ φ : Matrix (Fin 1) (Fin 1) ℝ,
          ψᵀ * ψ = φᵀ * φ →
          ∃ U : Matrix (Fin 1) (Fin 1) ℝ,
              U ∈ Matrix.orthogonalGroup (Fin 1) ℝ ∧ U * ψ = φ)
    -- (5) UNCONDITIONAL impossibility in dimension one.
    ∧ (∀ P : BCProtocol, P.n = 1 → P.IsConcealing → ¬ P.IsBinding) :=
  ⟨BCProtocol.bobReduced_apply,
   @aliceAction_preserves_bobReduced,
   no_perfect_BC_protocol,
   hjw_dim_one,
   no_perfect_BC_protocol_dim_one⟩

end UnifiedTheory.LayerC.BitCommitmentImpossibility
