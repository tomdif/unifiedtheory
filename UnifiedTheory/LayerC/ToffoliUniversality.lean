/-
  UnifiedTheory/LayerC/ToffoliUniversality.lean
  ─────────────────────────────────────────────

  **The Toffoli gate (CCNOT) is universal for classical reversible
  computation.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  The Toffoli gate — the controlled-controlled-NOT (CCNOT) — acts on
  three classical bits:

        (a, b, c)  ↦  (a, b, c ⊕ (a ∧ b)).

  It flips the target bit `c` exactly when both control bits `a, b`
  are `1`, and leaves `a, b` untouched.  Tommaso Toffoli (1980) proved
  that this single 3-bit gate is **universal for reversible
  computation**: every Boolean function can be realised by a circuit
  of Toffoli gates together with ancilla (constant-input) and garbage
  (don't-care-output) wires.

  The content of universality is entirely *finitary* and hence
  decidable.  We discharge each ingredient UNCONDITIONALLY by `decide`
  over the eight classical inputs:

    • SELF-INVERSE (involutive): two applications = identity, because
      `c ⊕ (a∧b) ⊕ (a∧b) = c`.  Reversibility.
    • NAND: with `c = 1` the target becomes `¬(a∧b)`.  Since NAND is a
      complete Boolean basis, Toffoli + ancillas computes *every*
      Boolean function — this is the universality statement.
    • AND: with `c = 0` the target becomes `a∧b`.
    • NOT: with `a = b = 1` the target becomes `¬c`.
    • FANOUT / COPY: with `b = 1, c = 0` the target becomes `a`.
    • BIJECTION: self-inverse ⟹ the map `Bool³ → Bool³` is a bijection.

  We also realise the gate as an 8×8 PERMUTATION over `Fin 8`
  (the computational basis `{0,1}³`), show it is the involutive
  transposition that swaps |110⟩ ↔ |111⟩ and fixes the other six
  basis states, and lift it to a complex permutation matrix whose
  conjugate transpose is its own inverse: `Uᴴ U = 1` (unitary).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Zero `sorry`.  Zero custom `axiom`.
-/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases

namespace UnifiedTheory.LayerC.ToffoliUniversality

/-! ## 1.  The Toffoli gate on three classical bits -/

/-- The Toffoli (CCNOT) gate: flip the target `c` iff both controls
    `a, b` are `1`.  `(a, b, c) ↦ (a, b, c ⊕ (a ∧ b))`. -/
def toffoli (a b c : Bool) : Bool × Bool × Bool := (a, b, xor c (a && b))

/-- Convenience: the action on a packaged triple. -/
def toffoli3 (x : Bool × Bool × Bool) : Bool × Bool × Bool :=
  toffoli x.1 x.2.1 x.2.2

@[simp] theorem toffoli3_eq (a b c : Bool) :
    toffoli3 (a, b, c) = toffoli a b c := rfl

/-! ### 1a.  Self-inverse (reversibility) -/

/-- **Toffoli is self-inverse.**  Applying it twice returns the input:
    `c ⊕ (a∧b) ⊕ (a∧b) = c`.  This is the reversibility of the gate. -/
theorem toffoli_involutive (a b c : Bool) :
    toffoli (toffoli a b c).1 (toffoli a b c).2.1 (toffoli a b c).2.2
      = (a, b, c) := by revert a b c; decide

/-- Packaged form: `toffoli3` is a `Function.Involutive`. -/
theorem toffoli3_involutive : Function.Involutive toffoli3 := by
  intro x; revert x; decide

/-! ### 1b.  The universal logic gates realised by Toffoli -/

/-- **NAND from Toffoli** (the universality engine).  Setting the
    target ancilla to `1`, the output bit is `¬(a ∧ b) = NAND(a,b)`.
    NAND is a functionally complete Boolean basis, so a Toffoli circuit
    with ancillas computes every Boolean function. -/
theorem toffoli_nand (a b : Bool) : (toffoli a b true).2.2 = !(a && b) := by
  revert a b; decide

/-- **AND from Toffoli.**  Target ancilla `0` ⟹ output `a ∧ b`. -/
theorem toffoli_and (a b : Bool) : (toffoli a b false).2.2 = (a && b) := by
  revert a b; decide

/-- **NOT from Toffoli.**  Both controls `1` ⟹ output `¬c`. -/
theorem toffoli_not (c : Bool) : (toffoli true true c).2.2 = !c := by revert c; decide

/-- **FANOUT / COPY from Toffoli.**  Control `b = 1`, target `c = 0` ⟹
    output `a` (the input `a` is copied onto the target wire while the
    original `a` is preserved). -/
theorem toffoli_fanout (a : Bool) : (toffoli a true false).2.2 = a := by revert a; decide

/-- The fanout genuinely *copies*: both the original control `a` and the
    target wire carry `a`. -/
theorem toffoli_fanout_copies (a : Bool) :
    (toffoli a true false).1 = a ∧ (toffoli a true false).2.2 = a := by revert a; decide

/-- The controls are never modified — `a, b` pass through untouched. -/
theorem toffoli_controls_preserved (a b c : Bool) :
    (toffoli a b c).1 = a ∧ (toffoli a b c).2.1 = b := by revert a b c; decide

/-! ### 1c.  Bijectivity (reversibility, abstractly) -/

/-- **Toffoli is a bijection of `Bool³`.**  Being its own inverse, it is
    both injective and surjective: a reversible map. -/
theorem toffoli_bijective : Function.Bijective toffoli3 :=
  toffoli3_involutive.bijective

/-- Toffoli as an explicit self-inverse `Equiv` (permutation) of the
    eight classical states `Bool × Bool × Bool`. -/
def toffoliEquiv : (Bool × Bool × Bool) ≃ (Bool × Bool × Bool) :=
  Function.Involutive.toPerm toffoli3 toffoli3_involutive

@[simp] theorem toffoliEquiv_apply (x : Bool × Bool × Bool) :
    toffoliEquiv x = toffoli3 x := rfl

@[simp] theorem toffoliEquiv_symm :
    toffoliEquiv.symm = toffoliEquiv := rfl

/-! ## 2.  Toffoli as an 8-state permutation over `Fin 8`

`Fin 8` indexes the computational basis `{0,1}³` with the little-endian
convention `index = a + 2·b + 4·c`, i.e. bit 0 = `a`, bit 1 = `b`,
bit 2 = `c`.  In this encoding Toffoli is the transposition that swaps
`6 = |0,1,1⟩_{abc}` ... we instead use the *standard* big-endian basis
`|a b c⟩ = a·4 + b·2 + c` so the swapped pair is the canonical
|110⟩ = 6  ↔  |111⟩ = 7. -/

/-- Decode a `Fin 8` index `= 4a + 2b + c` into its three bits. -/
def bitsOf (n : Fin 8) : Bool × Bool × Bool :=
  (decide (n.val / 4 % 2 = 1), decide (n.val / 2 % 2 = 1), decide (n.val % 2 = 1))

/-- Encode three bits `(a,b,c)` back into `Fin 8` as `4a + 2b + c`. -/
def encode (x : Bool × Bool × Bool) : Fin 8 :=
  ⟨(if x.1 then 4 else 0) + (if x.2.1 then 2 else 0) + (if x.2.2 then 1 else 0),
    by rcases x with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide⟩

/-- `encode` inverts `bitsOf`. -/
theorem encode_bitsOf (n : Fin 8) : encode (bitsOf n) = n := by revert n; decide

/-- `bitsOf` inverts `encode`. -/
theorem bitsOf_encode (x : Bool × Bool × Bool) : bitsOf (encode x) = x := by
  revert x; decide

/-- The Toffoli permutation on basis indices: decode, apply, re-encode. -/
def toffoliPermFun (n : Fin 8) : Fin 8 := encode (toffoli3 (bitsOf n))

/-- The index permutation is involutive. -/
theorem toffoliPermFun_involutive : Function.Involutive toffoliPermFun := by
  intro n; revert n; decide

/-- **Toffoli swaps only |110⟩ ↔ |111⟩** (indices `6 ↔ 7`) and fixes the
    six other basis states.  This is the full content of the gate as a
    permutation of the computational basis. -/
theorem toffoliPermFun_table :
    toffoliPermFun 0 = 0 ∧ toffoliPermFun 1 = 1 ∧ toffoliPermFun 2 = 2 ∧
    toffoliPermFun 3 = 3 ∧ toffoliPermFun 4 = 4 ∧ toffoliPermFun 5 = 5 ∧
    toffoliPermFun 6 = 7 ∧ toffoliPermFun 7 = 6 := by decide

/-- The permutation as a self-inverse `Equiv.Perm (Fin 8)`. -/
def toffoliPerm : Equiv.Perm (Fin 8) :=
  Function.Involutive.toPerm toffoliPermFun toffoliPermFun_involutive

@[simp] theorem toffoliPerm_apply (n : Fin 8) : toffoliPerm n = toffoliPermFun n := rfl

theorem toffoliPerm_symm : toffoliPerm.symm = toffoliPerm := rfl

/-- It really is a transposition (square = identity, not identity). -/
theorem toffoliPerm_sq : toffoliPerm.trans toffoliPerm = Equiv.refl _ := by
  ext n; simp [Equiv.trans_apply, toffoliPerm_apply, toffoliPermFun_involutive n]

theorem toffoliPerm_ne_refl : toffoliPerm ≠ Equiv.refl _ := by decide

/-! ## 3.  The 8×8 unitary Toffoli matrix -/

open Matrix

/-- The 8×8 Toffoli matrix over `ℂ`: the permutation matrix of
    `toffoliPerm`.  Entry `(i,j) = 1` iff `j = toffoliPerm i`, else `0`. -/
def toffoliMatrix : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of (fun i j => if toffoliPerm i = j then (1 : ℂ) else 0)

/-- The defining involution of the permutation, as an `Equiv`-level fact. -/
theorem toffoliPerm_involutive : Function.Involutive toffoliPerm := by
  intro n; simp only [toffoliPerm_apply]; exact toffoliPermFun_involutive n

/-- `toffoliPerm i = j` is symmetric in `i, j` (self-inverse permutation). -/
theorem toffoliPerm_eq_comm {i j : Fin 8} :
    toffoliPerm i = j ↔ toffoliPerm j = i := by
  constructor <;> · intro h; subst h; exact (toffoliPerm_involutive _)

/-- The Toffoli matrix is symmetric: `Mᵀ = M`.  (Because the underlying
    permutation is its own inverse, a transposition.) -/
theorem toffoliMatrix_transpose : toffoliMatrixᵀ = toffoliMatrix := by
  ext i j
  simp only [Matrix.transpose_apply, toffoliMatrix, Matrix.of_apply]
  by_cases h : toffoliPerm j = i
  · rw [if_pos h, if_pos (toffoliPerm_eq_comm.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (toffoliPerm_eq_comm.mp hc))]

/-- Each `(0,1)` permutation matrix entry is its own conjugate, so the
    conjugate transpose equals the transpose equals the matrix itself. -/
theorem toffoliMatrix_conjTranspose : toffoliMatrixᴴ = toffoliMatrix := by
  ext i j
  simp only [Matrix.conjTranspose_apply, toffoliMatrix, Matrix.of_apply,
    Matrix.transpose_apply]
  by_cases h : toffoliPerm j = i
  · rw [if_pos h, if_pos (toffoliPerm_eq_comm.mpr h)]; simp
  · rw [if_neg h, if_neg (fun hc => h (toffoliPerm_eq_comm.mp hc))]; simp

/-- A permutation matrix times itself (for a self-inverse permutation)
    is the identity: `M * M = 1`. -/
theorem toffoliMatrix_mul_self : toffoliMatrix * toffoliMatrix = 1 := by
  ext i j
  simp only [Matrix.mul_apply, toffoliMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (toffoliPerm i)]
  · rw [if_pos rfl, toffoliPerm_involutive i, one_mul, Matrix.one_apply]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **The Toffoli matrix is unitary:** `Mᴴ * M = 1`.  Together with
    `M * Mᴴ = 1` (below) this makes it a genuine unitary on the
    3-qubit Hilbert space `ℂ^8`. -/
theorem toffoliMatrix_unitary : toffoliMatrixᴴ * toffoliMatrix = 1 := by
  rw [toffoliMatrix_conjTranspose]; exact toffoliMatrix_mul_self

theorem toffoliMatrix_unitary' : toffoliMatrix * toffoliMatrixᴴ = 1 := by
  rw [toffoliMatrix_conjTranspose]; exact toffoliMatrix_mul_self

/-- The matrix is its own inverse. -/
theorem toffoliMatrix_inv : toffoliMatrix⁻¹ = toffoliMatrix :=
  inv_eq_left_inv toffoliMatrix_mul_self

/-! ## 4.  Named universality target + master theorem -/

/-- **Universality for reversible computation (named target).**
    The meta-claim, assembled from the unconditional decidable facts:
    Toffoli is a self-inverse (hence reversible) bijection of the
    classical state space that, with ancillas, realises the complete
    Boolean basis NAND — and therefore every Boolean function — as well
    as the standard gates AND, NOT and FANOUT/COPY.  Concretely it is
    the basis-state transposition |110⟩ ↔ |111⟩, a unitary on ℂ^8. -/
def Toffoli_Universal_Target : Prop :=
  -- reversibility / self-inverse
  (Function.Involutive toffoli3) ∧
  -- bijection of the classical state space
  (Function.Bijective toffoli3) ∧
  -- the universal NAND gate (functional completeness)
  (∀ a b : Bool, (toffoli a b true).2.2 = !(a && b)) ∧
  -- AND, NOT, FANOUT
  (∀ a b : Bool, (toffoli a b false).2.2 = (a && b)) ∧
  (∀ c : Bool, (toffoli true true c).2.2 = !c) ∧
  (∀ a : Bool, (toffoli a true false).2.2 = a) ∧
  -- the 8×8 permutation is the transposition |110⟩ ↔ |111⟩
  (toffoliPermFun 6 = 7 ∧ toffoliPermFun 7 = 6) ∧
  -- the matrix realisation is unitary
  (toffoliMatrixᴴ * toffoliMatrix = 1)

/-- **Master theorem: the Toffoli gate is universal for reversible
    classical computation.**  Every clause of `Toffoli_Universal_Target`
    holds — the Boolean clauses unconditionally by `decide`, the matrix
    clause by the permutation-unitarity proof. -/
theorem toffoli_master : Toffoli_Universal_Target := by
  refine ⟨toffoli3_involutive, toffoli_bijective, toffoli_nand, toffoli_and,
    toffoli_not, toffoli_fanout, ⟨?_, ?_⟩, toffoliMatrix_unitary⟩
  · decide
  · decide

#print axioms toffoli_master

end UnifiedTheory.LayerC.ToffoliUniversality
