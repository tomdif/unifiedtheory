/-
  UnifiedTheory/LayerC/HardyReconstruction.lean
  ─────────────────────────────────────────────

  **Hardy's 2001 reconstruction of quantum mechanics from
  five reasonable operational axioms.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  In "Quantum Theory from Five Reasonable Axioms" (arXiv:
  quant-ph/0101012, 2001), Lucien Hardy derives the
  Hilbert-space formalism of quantum mechanics by characterising
  the function K(N), where:
    * N = the maximum number of perfectly distinguishable states
          of a system,
    * K = the number of real parameters needed to specify
          a general (mixed) state.

  Five operational axioms — probability, simplicity, subspaces,
  composite systems, continuity — force `K = N^r` for a positive
  integer r ∈ {1, 2, 3, …}.  Axiom 5 (continuity) rules out
  r = 1 (classical probability theory), and a further argument
  rules out r ≥ 3.  The remaining choice r = 2 yields K = N²,
  which is exactly the parameter count of N × N Hermitian
  density matrices — i.e. quantum mechanics.

  This file isolates the **combinatorial backbone** of Hardy's
  argument as a structurally clean Lean theorem.  We package
  Hardy's K(N) as a structure carrying its axiomatic content,
  prove the K(2^n) = (2^n)² identity unconditionally by
  induction on n via multiplicativity and K(2) = 4, and state
  the general K(N) = N² result as a named target that needs
  per-prime input data (or the full Hardy continuity argument)
  to close.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HARDY'S FIVE AXIOMS, CONDENSED

    A1 (Probability).  Relative frequencies tend to
       probabilities in the long run.
    A2 (Simplicity).  K is a function of N alone — K = K(N) —
       and the function is well-defined.
    A3 (Subspaces).  A system restricted to an M-state
       subspace behaves as an M-state system: K(M) governs it.
    A4 (Composites).  For composite systems built from
       sub-systems of sizes N_A and N_B:
         N(N_A · N_B) = N_A · N_B,
         K(N_A · N_B) = K(N_A) · K(N_B).
    A5 (Continuity).  Between any two pure states there is a
       continuous reversible transformation.

  In Hardy's analysis A1 + A2 + A3 force K(N) to be a power
  of N — K(N) = N^r — and A4 forces r to be a fixed integer
  independent of N.  A5 forces r ≥ 2 (a pure 2-state classical
  system would need K = 2 = N, but no continuous reversible
  transformation connects the two pure states of a classical
  bit).  A further r ≥ 3 ruled out by Hardy's compositional
  state-counting argument gives r = 2.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE SHIPS

    * `HardyFramework` — a structure packaging K as ℕ → ℕ with
       the multiplicativity axiom (A4) and the unit/quantum
       boundary conditions K(1) = 1, K(2) = 4 already chosen
       to encode A5 (continuity ⇒ r ≥ 2) at the seed N = 2.
    * `hardy_K_two_pow` — UNCONDITIONAL: K(2^n) = (2^n)^2
       for all n.  Pure induction using A4 and K(2) = 4.
    * `hardy_K_one_sq` — K(1) = 1² and `hardy_K_two_sq`
       — K(2) = 2².
    * `Hardy_5_Axioms` — the five-axiom hypothesis bundled
       as a Prop attached to a framework.
    * `hardy_reconstructs_QM_on_powers_of_two` — the headline
       partial reconstruction: on N = 2^n, the framework's K(N)
       agrees with the QM density-matrix parameter count N².
    * `Classical_r1_ruled_out` — algebraic witness that the
       r = 1 (classical) framework with K(N) = N is incompatible
       with Hardy's K(2) = 4 seed.
    * `NoHigherR_Target` — the named target ruling out r ≥ 3.
    * `Hardy_KN_eq_NSquared_Target` — the named target
       extending K(N) = N² from N = 2^n to all positive N.

  Zero `sorry`.  Zero custom `axiom`.  ~600 lines.

  Honest scope.  The file proves the n = 2^k case of Hardy's
  theorem UNCONDITIONALLY from the axiomatised seed; the full
  N case and the r ≥ 3 elimination are stated as named targets
  (Props requiring extra structure — per-prime data or Hardy's
  continuity argument).  This is the same scoping discipline
  as PBRTheorem.lean (combinatorial backbone proved, QM
  derivation of the seed deferred) and as HardyParadox.lean
  (LHV impossibility proved, QM realisation deferred).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.HardyReconstruction

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE HARDY FRAMEWORK STRUCTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A `HardyFramework` packages Hardy's K(N) function together
    with the axiomatic constraints arising from A2, A4 and A5.
    A1 (probability convergence) and A3 (subspaces) are scoping
    axioms — they justify the existence and well-definedness of
    K(N) and the substitutability of M-state subsystems for
    M-state systems — and are not refuted by the K-value side
    of the framework.  A2 ("K is a function of N") is built into
    the Lean signature `K : ℕ → ℕ`. A4 (multiplicativity) and
    A5 (continuity-forced seed K(2) = 4 instead of the classical
    K(2) = 2) are explicit fields.

    Why K(2) = 4 encodes A5.

    Hardy's analysis shows that the only solutions to K(N) =
    K(N_A)·K(N_B) with K(1) = 1 and K nondecreasing in N are
    K(N) = N^r for r ∈ ℕ.  The smallest case discriminating
    the candidate exponents is N = 2: r = 1 gives K(2) = 2
    (classical bit), r = 2 gives K(2) = 4 (qubit, four real
    parameters for a 2×2 Hermitian density matrix), r = 3
    gives K(2) = 8 and so on. Axiom 5 forces r ≥ 2, and the
    Hardy compositional argument rules out r ≥ 3.  We absorb
    those two arguments into the choice K(2) = 4.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A Hardy framework**: the K(N) function together with the
    operational axioms A2, A4 and A5 (seed value).

    Fields:
      * `K : ℕ → ℕ` — the number of real parameters needed to
        specify a state of a system with N maximally
        distinguishable states. Axiom A2 ("K is a function
        of N alone") is built in by typing.
      * `K_mult` — Axiom A4: K is multiplicative on composite
        system sizes.  This is the operational content of
        independent composition: probabilities of independent
        joint outcomes factor, and the parameter count of the
        joint system is the product of the parameter counts of
        its parts.
      * `K_one` — Axiom A3 boundary case: a 1-state system has
        a single trivial state, hence K(1) = 1.
      * `K_two_quantum` — Axiom A5 seed: continuity-plus-no-
        higher-r forces K(2) = 4 (qubit parameter count).
        This is the QM-not-classical discriminator at N = 2. -/
structure HardyFramework where
  /-- Number of real parameters needed to specify a state on an
      N-distinguishable-states system. -/
  K : ℕ → ℕ
  /-- Axiom A4 (composites): K is multiplicative on system sizes. -/
  K_mult : ∀ a b : ℕ, K (a * b) = K a * K b
  /-- Axiom A3 boundary: K(1) = 1. -/
  K_one : K 1 = 1
  /-- Axiom A5 seed: K(2) = 4 (qubit case, r = 2). -/
  K_two_quantum : K 2 = 4

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: BASIC CONSEQUENCES OF THE AXIOMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

namespace HardyFramework

variable (F : HardyFramework)

/-- K(1) = 1 = 1², the unit / trivial-system case. -/
theorem K_one_sq : F.K 1 = 1 ^ 2 := by
  simpa [pow_two] using F.K_one

/-- K(2) = 4 = 2², the qubit / quantum-bit case. -/
theorem K_two_sq : F.K 2 = 2 ^ 2 := by
  simpa [pow_two] using F.K_two_quantum

/-- A useful reformulation of multiplicativity in `pow_two`
    shape: K(a)·K(b) = K(a·b). -/
theorem K_mult_symm (a b : ℕ) : F.K a * F.K b = F.K (a * b) :=
  (F.K_mult a b).symm

/-- K applied to an n-fold product `2 * (2 * (... * 2))` is
    a useful intermediate.  We use it to show K(2^n) = 4^n. -/
theorem K_two_pow_succ (n : ℕ) :
    F.K (2 ^ (n + 1)) = F.K 2 * F.K (2 ^ n) := by
  have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by
    rw [pow_succ, mul_comm]
  rw [hpow, F.K_mult]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: HARDY'S K(2^n) = (2^n)² — UNCONDITIONAL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    By induction on n. Base case n = 0: K(1) = 1 = 1² by
    `K_one`. Inductive step: assume K(2^n) = (2^n)². Then
        K(2^(n+1)) = K(2) · K(2^n)    (by `K_two_pow_succ`)
                   = 4 · (2^n)²        (by `K_two_quantum` and IH)
                   = (2 · 2^n)²        (algebra)
                   = (2^(n+1))²        (pow_succ).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Hardy's theorem on powers of two (UNCONDITIONAL).**

    For every n ∈ ℕ, the parameter count K(2^n) equals (2^n)².
    The proof uses only the multiplicativity axiom A4
    (`K_mult`), the unit boundary K(1) = 1 (A3, `K_one`),
    and the qubit seed K(2) = 4 (A5, `K_two_quantum`).

    This is the part of Hardy's reconstruction that is purely
    combinatorial — no real-number continuity argument is
    needed once the K(2) = 4 seed is fixed. -/
theorem hardy_K_two_pow (n : ℕ) : F.K (2 ^ n) = (2 ^ n) ^ 2 := by
  induction n with
  | zero =>
    -- K(2^0) = K(1) = 1 = 1² = (2^0)²
    simp [F.K_one]
  | succ n ih =>
    -- K(2^(n+1)) = K(2) · K(2^n) = 4 · (2^n)² = (2^(n+1))²
    have step₁ : F.K (2 ^ (n + 1)) = F.K 2 * F.K (2 ^ n) :=
      F.K_two_pow_succ n
    have step₂ : F.K 2 * F.K (2 ^ n) = 4 * (2 ^ n) ^ 2 := by
      rw [F.K_two_quantum, ih]
    have step₃ : (4 : ℕ) * (2 ^ n) ^ 2 = (2 ^ (n + 1)) ^ 2 := by
      have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
      rw [h2]; ring
    rw [step₁, step₂, step₃]

/-- Explicit numerical specialisations — concrete sanity
    checks of `hardy_K_two_pow`. -/
theorem hardy_K_4 : F.K 4 = 16 := by
  have := F.hardy_K_two_pow 2
  -- 2^2 = 4 and (2^2)^2 = 16
  norm_num at this
  exact this

/-- K(8) = 64.  Three-qubit register has 8 distinguishable
    states and 64 real density-matrix parameters. -/
theorem hardy_K_8 : F.K 8 = 64 := by
  have := F.hardy_K_two_pow 3
  norm_num at this
  exact this

/-- K(16) = 256 (four qubits). -/
theorem hardy_K_16 : F.K 16 = 256 := by
  have := F.hardy_K_two_pow 4
  norm_num at this
  exact this

/-- K(32) = 1024 (five qubits). -/
theorem hardy_K_32 : F.K 32 = 1024 := by
  have := F.hardy_K_two_pow 5
  norm_num at this
  exact this

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: K AT COMPOSITE SIZES BUILT FROM 2 AND 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Multiplicativity propagates the K(2^n) = (2^n)² identity
    to all products of powers of two, in particular making
    K(2^a · 2^b) = K(2^a) · K(2^b) = (2^a · 2^b)² hold.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- K of a product of two powers of two factors squarely. -/
theorem hardy_K_two_pow_mul (a b : ℕ) :
    F.K (2 ^ a * 2 ^ b) = (2 ^ a * 2 ^ b) ^ 2 := by
  rw [F.K_mult, F.hardy_K_two_pow a, F.hardy_K_two_pow b]
  ring

/-- K of a 1 · M product equals K(M).  Useful for handling
    "absorb the unit" simplifications. -/
theorem hardy_K_one_mul (M : ℕ) : F.K (1 * M) = F.K M := by
  rw [F.K_mult, F.K_one, one_mul]

/-- K of an M · 1 product equals K(M). -/
theorem hardy_K_mul_one (M : ℕ) : F.K (M * 1) = F.K M := by
  rw [F.K_mult, F.K_one, mul_one]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE 5-AXIOM PROPOSITION AND HARDY HEADLINE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Hardy's five operational axioms bundled as a Prop** for
    a given framework.  The Prop asserts that the framework
    satisfies:
      * A2 / A4 — K is a multiplicative function of N (built
        into the structure: `K : ℕ → ℕ`, `K_mult`).
      * A3 — K(1) = 1 (trivial subsystem boundary).
      * A5 — K(2) = 4 (continuity + no-higher-r seed).

    A1 (frequencies-tend-to-probabilities) and the
    subspace-substitution part of A3 are scoping axioms
    operating on the WORLD generating K, not on K itself; they
    are not refutable by inspection of K-values, so they are
    not encoded as Lean Props here. -/
def Hardy_5_Axioms (F : HardyFramework) : Prop :=
  (∀ a b : ℕ, F.K (a * b) = F.K a * F.K b) ∧
  F.K 1 = 1 ∧
  F.K 2 = 4

/-- Every `HardyFramework` satisfies the 5 axioms (by
    construction — the axioms are the structure's fields). -/
theorem hardyFramework_satisfies_5_axioms (F : HardyFramework) :
    Hardy_5_Axioms F := by
  refine ⟨?_, ?_, ?_⟩
  · exact F.K_mult
  · exact F.K_one
  · exact F.K_two_quantum

/-- **Hardy reconstruction theorem (POWERS OF TWO).**

    For every Hardy framework F and every n ∈ ℕ, the framework's
    parameter count K(2^n) equals the QM density-matrix parameter
    count (2^n)².

    This is the unconditional combinatorial part of Hardy's
    reconstruction: the multiplicativity axiom A4 plus the
    seed K(2) = 4 already forces K to coincide with the QM
    parameter count on every power of two.  The seed K(2) = 4
    encodes the substantive content of A5 (the continuity
    argument ruling out the classical r = 1 alternative). -/
theorem hardy_reconstructs_QM_on_powers_of_two
    (F : HardyFramework) (n : ℕ) :
    F.K (2 ^ n) = (2 ^ n) ^ 2 :=
  F.hardy_K_two_pow n

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE CLASSICAL r = 1 ALTERNATIVE IS RULED OUT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Hardy's K = N^r exponent is the discriminant between
    classical probability theory (r = 1, K(N) = N) and quantum
    mechanics (r = 2, K(N) = N²).  Axiom 5 (continuity of pure
    states) is what rules out r = 1: for r = 1 a 2-state system
    has K(2) = 2 = N, which gives no headroom for a continuous
    reversible transformation between the two pure states.

    We materialise the obstruction as a direct algebraic
    incompatibility: the classical framework with K(N) = N
    would have K(2) = 2, contradicting the Hardy seed
    K(2) = 4.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The would-be classical (r = 1) K function.  Multiplicative
    (`a · b = a · b`) and K(1) = 1, BUT K(2) = 2 ≠ 4. -/
def K_classical : ℕ → ℕ := fun N => N

/-- The classical K function is multiplicative. -/
theorem K_classical_mult (a b : ℕ) :
    K_classical (a * b) = K_classical a * K_classical b := by
  rfl

/-- K_classical(1) = 1. -/
theorem K_classical_one : K_classical 1 = 1 := rfl

/-- K_classical(2) = 2, NOT 4.  This is the algebraic obstruction
    to interpreting the framework as classical probability theory:
    K(2) = 2 violates the Hardy A5-seed K(2) = 4. -/
theorem K_classical_two : K_classical 2 = 2 := rfl

/-- **Classical r = 1 is ruled out (algebraic witness).**

    There is no `HardyFramework` instance built from the
    classical K_classical function, because K_classical(2) = 2
    while a Hardy framework requires K(2) = 4. -/
theorem Classical_r1_ruled_out :
    ¬ ∃ F : HardyFramework, F.K = K_classical := by
  intro ⟨F, hF⟩
  have h1 : F.K 2 = 4 := F.K_two_quantum
  have h2 : F.K 2 = 2 := by rw [hF]; rfl
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE r ≥ 3 ALTERNATIVE — NAMED TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The r ≥ 3 elimination in Hardy's paper is the second
    structural argument.  Sketch (Hardy 2001 §6.2):
    If K(N) = N^r for r ≥ 3 then the composite-system parameter
    count grows faster than the number of pure states allows
    under continuity, leading to a contradiction with subspace
    closure (A3) when restricting to a 2-state subspace of a
    composite system.

    We do NOT formalise this argument here.  Instead we record
    its conclusion — "no Hardy framework has K(2) = 8" — as a
    named target Prop suitable for a follow-up file.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The would-be r = 3 K function: K(N) = N^3. -/
def K_r3 : ℕ → ℕ := fun N => N ^ 3

/-- K_r3 is multiplicative on ℕ. -/
theorem K_r3_mult (a b : ℕ) :
    K_r3 (a * b) = K_r3 a * K_r3 b := by
  unfold K_r3; ring

/-- K_r3(1) = 1. -/
theorem K_r3_one : K_r3 1 = 1 := by unfold K_r3; ring

/-- K_r3(2) = 8, NOT 4 — the algebraic obstruction to r = 3
    as a Hardy framework. -/
theorem K_r3_two : K_r3 2 = 8 := by unfold K_r3; norm_num

/-- **r ≥ 3 is ruled out (algebraic witness, for r = 3 case).**

    Like classical r = 1, the K_r3 candidate violates the
    Hardy seed K(2) = 4: it gives K(2) = 8. -/
theorem r3_ruled_out :
    ¬ ∃ F : HardyFramework, F.K = K_r3 := by
  intro ⟨F, hF⟩
  have h1 : F.K 2 = 4 := F.K_two_quantum
  have h2 : F.K 2 = 8 := by rw [hF]; exact K_r3_two
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- **Named target: full Hardy r ≥ 3 elimination.**

    "For every integer r ≥ 3 there is no operationally-consistent
    K(N) = N^r framework arising from Hardy's five axioms."

    The Lean statement here is the formal Prop; the proof is
    the Hardy compositional argument (2001 §6.2) and is parked.
    Closing this Prop would require formalising the
    subspace-restriction step (A3) plus the compositional
    parameter-counting bound. -/
def NoHigherR_Target : Prop :=
  ∀ r : ℕ, 3 ≤ r →
    ¬ ∃ F : HardyFramework, ∀ N : ℕ, F.K N = N ^ r

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: GENERAL K(N) = N² — NAMED TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The general statement "K(N) = N² for every N ≥ 1" requires
    EXTRA structure beyond K(2) = 4 + multiplicativity: it
    requires K to be specified on every prime, with K(p) = p²
    on each prime p, before multiplicativity propagates the
    identity to all positive N.

    Hardy's paper closes this gap by using A3 (subspaces) to
    embed a generic N-state system inside an M-state system
    with M a power of 2 chosen so 2^k ≥ N, and then peeling
    off the structure inside the embedding.  The argument is
    delicate enough that we park it as a named target.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Named target: Hardy K(N) = N² for all positive N.**

    The full Hardy 2001 result.  Closing this requires either:
      (a) specifying K on every prime (per-prime data), then
          using multiplicativity (A4) to propagate, or
      (b) formalising Hardy's subspace argument (A3) plus
          continuity (A5) to force K(p) = p² for every prime p.

    The K(2^n) = (2^n)² half of this Prop is closed
    unconditionally by `hardy_K_two_pow`. -/
def Hardy_KN_eq_NSquared_Target : Prop :=
  ∀ F : HardyFramework, ∀ N : ℕ, 0 < N → F.K N = N ^ 2

/-- **Hardy K(N) = N² holds on the n = 2^k subset of N**
    (unconditional partial form of the named target). -/
theorem Hardy_KN_eq_NSquared_on_two_powers
    (F : HardyFramework) (k : ℕ) :
    F.K (2 ^ k) = (2 ^ k) ^ 2 :=
  F.hardy_K_two_pow k

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: CONSISTENCY — THE QUANTUM FRAMEWORK EXISTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Sanity: the structural definition is not vacuous.  We
    exhibit the canonical quantum framework K(N) = N² and
    verify it is a HardyFramework instance.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The canonical quantum K-function: K(N) = N². -/
def K_quantum : ℕ → ℕ := fun N => N ^ 2

/-- K_quantum is multiplicative. -/
theorem K_quantum_mult (a b : ℕ) :
    K_quantum (a * b) = K_quantum a * K_quantum b := by
  unfold K_quantum; ring

/-- K_quantum(1) = 1. -/
theorem K_quantum_one : K_quantum 1 = 1 := by unfold K_quantum; ring

/-- K_quantum(2) = 4 — the qubit parameter count. -/
theorem K_quantum_two : K_quantum 2 = 4 := by unfold K_quantum; norm_num

/-- **The canonical Hardy framework**: K(N) = N².  This is the
    QM solution.  Its existence shows the `HardyFramework`
    structure is not vacuous. -/
def quantumFramework : HardyFramework where
  K := K_quantum
  K_mult := K_quantum_mult
  K_one := K_quantum_one
  K_two_quantum := K_quantum_two

/-- The quantum framework's K is K_quantum, by definition. -/
theorem quantumFramework_K :
    quantumFramework.K = K_quantum := rfl

/-- Specialise the Hardy headline to the canonical quantum
    framework: K_quantum(2^n) = (2^n)². -/
theorem quantum_K_two_pow (n : ℕ) :
    K_quantum (2 ^ n) = (2 ^ n) ^ 2 :=
  quantumFramework.hardy_K_two_pow n

/-- On the canonical quantum framework, the general K(N) = N²
    identity holds unconditionally for every N (this is
    K_quantum's defining identity). -/
theorem quantum_K_eq_N_sq (N : ℕ) :
    quantumFramework.K N = N ^ 2 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: HARDY MASTER STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Hardy master statement (this file).**

    The Hardy 5-axiom framework recovers the QM parameter count
    K(N) = N² UNCONDITIONALLY on N = 2^n, and rules out the
    classical (r = 1) alternative algebraically at N = 2.  The
    extensions to all N and to r ≥ 3 elimination are recorded
    as named targets.  The structure is consistent: the
    canonical quantum K_quantum(N) = N² is a `HardyFramework`. -/
theorem hardy_master :
    -- (i) Every Hardy framework reconstructs QM on powers of two:
    (∀ F : HardyFramework, ∀ n : ℕ, F.K (2 ^ n) = (2 ^ n) ^ 2)
    ∧
    -- (ii) Every Hardy framework satisfies the 5 axioms:
    (∀ F : HardyFramework, Hardy_5_Axioms F)
    ∧
    -- (iii) Classical r = 1 is ruled out:
    (¬ ∃ F : HardyFramework, F.K = K_classical)
    ∧
    -- (iv) r = 3 is ruled out (algebraic witness):
    (¬ ∃ F : HardyFramework, F.K = K_r3)
    ∧
    -- (v) The structure is consistent (quantumFramework exists):
    (∃ F : HardyFramework, ∀ N : ℕ, F.K N = N ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F n; exact F.hardy_K_two_pow n
  · intro F; exact hardyFramework_satisfies_5_axioms F
  · exact Classical_r1_ruled_out
  · exact r3_ruled_out
  · exact ⟨quantumFramework, quantum_K_eq_N_sq⟩

end HardyFramework

end UnifiedTheory.LayerC.HardyReconstruction
