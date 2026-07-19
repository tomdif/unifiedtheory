/-
  LayerB/StabiliserCodes.lean
  ────────────────────────────

  **Pauli stabiliser formalism — the 3-qubit bit-flip code.**

  A *stabiliser code* (Gottesman 1997) is the simultaneous +1
  eigenspace of an abelian subgroup `S ⊆ P_n` of the n-qubit Pauli
  group with `-I ∉ S`.  This file ships the simplest non-trivial
  example — the **3-qubit bit-flip code** — and proves that it
  satisfies the Knill-Laflamme correctability condition for the
  single-qubit bit-flip error channel.

  Stabiliser generators of the 3-qubit bit-flip code:

      S₁ = Z ⊗ Z ⊗ I,    S₂ = I ⊗ Z ⊗ Z .

  The code subspace is two-dimensional:

      C = span { |000⟩, |111⟩ }

  with projector

      P_C = |000⟩⟨000| + |111⟩⟨111| .

  The bit-flip error channel has four Kraus operators (after
  normalisation):

      K_i  =  (1/2) · E_i,    where
      E_0  = I_8,
      E_1  = X ⊗ I ⊗ I,
      E_2  = I ⊗ X ⊗ I,
      E_3  = I ⊗ I ⊗ X .

  These satisfy ∑ᵢ E_i† E_i = 4·I, so the K_i form a valid Kraus
  representation: ∑ᵢ K_i† K_i = I.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVEN (zero `sorry`, zero custom `axiom`)

    1. `bitFlipPauliI/X1/X2/X3` — the four 8 × 8 error matrices.
       Each is Hermitian, self-inverse, and unitary.
    2. `bitFlipCodeProjector` — the explicit 8 × 8 code projector.
       Hermitian and idempotent.
    3. `bitFlipQuantumCode : QuantumCode 8` — bundled into the
       `KnillLaflamme` `QuantumCode` structure.
    4. `bitFlipErrorChannel : KrausRepresentation 8 8 4` — the
       4-operator Kraus representation `K_i = (1/2) E_i`.
    5. `bitFlipCode_isKLCorrectable` — the headline:

           IsKLCorrectable bitFlipQuantumCode bitFlipErrorChannel

       The c-matrix is c = (1/4) · I_4 (Hermitian).  The KL identity
       reduces to:
         · i = j: P · K_i† K_i · P = (1/4) P
         · i ≠ j: P · K_i† K_j · P = 0

       Both follow from the elementary fact that any 8 × 8 matrix
       whose four "corner" entries (0,0), (0,7), (7,0), (7,7) all
       vanish has zero conjugation `P · M · P`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  This is the *worked example* opening the QEC pillar.  We do NOT
  formalise the general stabiliser formalism (arbitrary n-qubit
  abelian stabilisers, syndrome measurement, recovery synthesis,
  Steane / Shor / surface codes).  We do verify that the simplest
  stabiliser code satisfies the Knill-Laflamme condition for its
  natural error model — i.e., the framework's central QEC criterion
  fires correctly on a concrete code.

  All proofs are explicit 8 × 8 entry-level computations done via
  `fin_cases` + `simp [Matrix.mul_apply, Fin.sum_univ_eight, ...]`,
  hence definitionally checked.

  No `sorry`, no custom `axiom`.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import UnifiedTheory.LayerB.KrausRepresentation
import UnifiedTheory.LayerB.KnillLaflamme

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.LayerB.StabiliserCodes

open Matrix Complex
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.LayerB.KnillLaflamme

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART A — The four 8 × 8 error matrices.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We encode three-qubit basis states as `Fin 8` indices with the
    convention

        |abc⟩  ↔  4a + 2b + c     (a, b, c ∈ {0, 1}).

    Under this convention the single-qubit X errors are the
    permutation matrices realising the swap:

        X₁ = X ⊗ I ⊗ I :  0↔4, 1↔5, 2↔6, 3↔7
        X₂ = I ⊗ X ⊗ I :  0↔2, 1↔3, 4↔6, 5↔7
        X₃ = I ⊗ I ⊗ X :  0↔1, 2↔3, 4↔5, 6↔7 . -/

/-- The 8 × 8 identity matrix (the "no-error" Pauli I ⊗ I ⊗ I). -/
def bitFlipPauliI : Matrix (Fin 8) (Fin 8) ℂ := (1 : Matrix (Fin 8) (Fin 8) ℂ)

/-- The 8 × 8 matrix `X ⊗ I ⊗ I`: bit-flip on qubit 1. -/
def bitFlipPauliX1 : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

/-- The 8 × 8 matrix `I ⊗ X ⊗ I`: bit-flip on qubit 2. -/
def bitFlipPauliX2 : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0]

/-- The 8 × 8 matrix `I ⊗ I ⊗ X`: bit-flip on qubit 3. -/
def bitFlipPauliX3 : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART B — Hermiticity of the three X errors.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `X₁† = X₁`.  Each X-string is real, symmetric, hence Hermitian. -/
theorem bitFlipPauliX1_conjTranspose :
    bitFlipPauliX1.conjTranspose = bitFlipPauliX1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipPauliX1, Matrix.conjTranspose_apply, Complex.conj_ofNat]

theorem bitFlipPauliX2_conjTranspose :
    bitFlipPauliX2.conjTranspose = bitFlipPauliX2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipPauliX2, Matrix.conjTranspose_apply, Complex.conj_ofNat]

theorem bitFlipPauliX3_conjTranspose :
    bitFlipPauliX3.conjTranspose = bitFlipPauliX3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipPauliX3, Matrix.conjTranspose_apply, Complex.conj_ofNat]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART C — Self-inverse property: E_i · E_i = I.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

theorem bitFlipPauliX1_sq : bitFlipPauliX1 * bitFlipPauliX1 = bitFlipPauliI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipPauliX1, bitFlipPauliI, Matrix.mul_apply, Fin.sum_univ_eight,
          Matrix.one_apply]

theorem bitFlipPauliX2_sq : bitFlipPauliX2 * bitFlipPauliX2 = bitFlipPauliI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipPauliX2, bitFlipPauliI, Matrix.mul_apply, Fin.sum_univ_eight,
          Matrix.one_apply]

theorem bitFlipPauliX3_sq : bitFlipPauliX3 * bitFlipPauliX3 = bitFlipPauliI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipPauliX3, bitFlipPauliI, Matrix.mul_apply, Fin.sum_univ_eight,
          Matrix.one_apply]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART D — The bit-flip code projector.

    `P_C = |000⟩⟨000| + |111⟩⟨111|`, i.e. the diagonal 8×8 matrix
    with entries 1 at positions 0 and 7 and zero elsewhere.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 3-qubit bit-flip code projector onto `span{|000⟩, |111⟩}`. -/
def bitFlipCodeProjector : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

/-- `P_C` is Hermitian. -/
theorem bitFlipCodeProjector_isHermitian :
    bitFlipCodeProjector.IsHermitian := by
  unfold IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipCodeProjector, Matrix.conjTranspose_apply, Complex.conj_ofNat]

/-- `P_C` is idempotent: `P_C · P_C = P_C`. -/
theorem bitFlipCodeProjector_idempotent :
    bitFlipCodeProjector * bitFlipCodeProjector = bitFlipCodeProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipCodeProjector, Matrix.mul_apply, Fin.sum_univ_eight]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART E — The bit-flip code as a `QuantumCode 8`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 3-qubit bit-flip code packaged as a `KnillLaflamme.QuantumCode`. -/
def bitFlipQuantumCode : QuantumCode 8 where
  proj := bitFlipCodeProjector
  isHerm := bitFlipCodeProjector_isHermitian
  isProj := bitFlipCodeProjector_idempotent

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART F — The 4-error Kraus channel `K_i = (1/2) · E_i`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four bit-flip error operators (unscaled): `{I, X₁, X₂, X₃}`. -/
def bitFlipErrors : Fin 4 → Matrix (Fin 8) (Fin 8) ℂ
  | ⟨0, _⟩ => bitFlipPauliI
  | ⟨1, _⟩ => bitFlipPauliX1
  | ⟨2, _⟩ => bitFlipPauliX2
  | ⟨3, _⟩ => bitFlipPauliX3
  | ⟨n + 4, h⟩ => absurd h (by omega)

@[simp] lemma bitFlipErrors_zero : bitFlipErrors 0 = bitFlipPauliI := rfl
@[simp] lemma bitFlipErrors_one : bitFlipErrors 1 = bitFlipPauliX1 := rfl
@[simp] lemma bitFlipErrors_two : bitFlipErrors 2 = bitFlipPauliX2 := rfl
@[simp] lemma bitFlipErrors_three : bitFlipErrors 3 = bitFlipPauliX3 := rfl

/-- The normalised Kraus operators: `K_i = (1/2) · E_i`. -/
noncomputable def bitFlipKraus : Fin 4 → Matrix (Fin 8) (Fin 8) ℂ :=
  fun i => ((1/2 : ℂ)) • bitFlipErrors i

/-- For each error, `E_i† · E_i = I`. -/
private lemma bitFlipErrors_conjT_mul_self (i : Fin 4) :
    (bitFlipErrors i).conjTranspose * (bitFlipErrors i) = bitFlipPauliI := by
  fin_cases i
  · -- i = 0: I† · I = I
    show bitFlipPauliI.conjTranspose * bitFlipPauliI = bitFlipPauliI
    unfold bitFlipPauliI
    rw [Matrix.conjTranspose_one, Matrix.one_mul]
  · -- i = 1: X₁† · X₁ = X₁ · X₁ = I
    show bitFlipPauliX1.conjTranspose * bitFlipPauliX1 = bitFlipPauliI
    rw [bitFlipPauliX1_conjTranspose, bitFlipPauliX1_sq]
  · -- i = 2
    show bitFlipPauliX2.conjTranspose * bitFlipPauliX2 = bitFlipPauliI
    rw [bitFlipPauliX2_conjTranspose, bitFlipPauliX2_sq]
  · -- i = 3
    show bitFlipPauliX3.conjTranspose * bitFlipPauliX3 = bitFlipPauliI
    rw [bitFlipPauliX3_conjTranspose, bitFlipPauliX3_sq]

/-- Auxiliary scalar identity: `(1/2)* · (1/2) = 1/4` in ℂ. -/
private lemma half_conj_half : starRingEnd ℂ (1/2 : ℂ) * (1/2 : ℂ) = (1/4 : ℂ) := by
  -- 1/2 is real, so its conjugate is itself.
  have h : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
  rw [h, Complex.conj_ofReal]
  norm_num

/-- Kraus completeness for `K_i = (1/2) E_i`:  ∑ᵢ K_i† K_i = I. -/
private lemma bitFlipKraus_complete :
    (∑ i, (bitFlipKraus i).conjTranspose * (bitFlipKraus i))
      = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  -- K_i = (1/2) E_i, so K_i† K_i = (1/4) E_i† E_i = (1/4) I.  Sum gives I.
  have h_term : ∀ i,
      (bitFlipKraus i).conjTranspose * (bitFlipKraus i)
        = ((1/4 : ℂ)) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
    intro i
    unfold bitFlipKraus
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [bitFlipErrors_conjT_mul_self i]
    -- bitFlipPauliI is definitionally (1 : Matrix _ _ ℂ).
    show (star (1/2 : ℂ) * (1/2 : ℂ)) • (1 : Matrix (Fin 8) (Fin 8) ℂ)
        = ((1/4 : ℂ)) • (1 : Matrix (Fin 8) (Fin 8) ℂ)
    congr 1
    -- star == starRingEnd on ℂ.
    exact half_conj_half
  simp_rw [h_term]
  -- Sum of four copies of (1/4) • I = I.
  rw [← Finset.sum_smul]
  -- ∑_{i:Fin 4} (1/4) = 1.
  have h_sum : (∑ _ : Fin 4, (1/4 : ℂ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [h_sum, one_smul]

/-- The bit-flip Kraus channel. -/
noncomputable def bitFlipErrorChannel : KrausRepresentation 8 8 4 where
  K := bitFlipKraus
  complete := bitFlipKraus_complete

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART G — Key vanishing lemma: corner-zero matrices have
    zero conjugation by `P_C`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- For any 8 × 8 matrix `M` whose four "corner" entries
    `M(0,0), M(0,7), M(7,0), M(7,7)` all vanish, we have
    `P_C · M · P_C = 0`.

    We first compute the inner product `P_C · M` explicitly (it has
    nonzero rows only at indices 0 and 7), then post-multiply by P_C. -/
private lemma proj_mul_zero_of_corners_zero
    (M : Matrix (Fin 8) (Fin 8) ℂ)
    (h00 : M 0 0 = 0) (h07 : M 0 7 = 0)
    (h70 : M 7 0 = 0) (h77 : M 7 7 = 0) :
    bitFlipCodeProjector * M * bitFlipCodeProjector = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_eight]
  -- Goal: ∑ k, (∑ l, P i l * M l k) * P k j = 0.
  -- For each (i, j), inner sum collapses by P_C definition,
  -- outer sum collapses by P_C definition, giving 4 corner entries.
  fin_cases i <;> fin_cases j <;>
    simp [bitFlipCodeProjector, h00, h07, h70, h77]


/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART H — Corner entries of all 16 products `E_i · E_j`.

    The error products `E_i · E_j` are themselves Pauli X-strings
    (modulo overall sign).  The masks (which qubits are flipped):

       i\j |  0    1    2    3
       ----+------------------------
        0  |  I   X₁   X₂   X₃     ← mask 0, 4, 2, 1
        1  | X₁    I  X₁X₂ X₁X₃   ← mask 4, 0, 6, 5
        2  | X₂  X₂X₁  I   X₂X₃   ← mask 2, 6, 0, 3
        3  | X₃  X₃X₁ X₃X₂  I     ← mask 1, 5, 3, 0

    Diagonal (i=j): identity, corners (1, 0, 0, 1).
    Off-diagonal: non-identity Pauli with mask ∈ {1, …, 6},
    corners all zero.  (Mask 7 = X⊗X⊗X never appears in the
    1-qubit bit-flip error model.)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-! ### Diagonal products: E_i · E_i = I. -/

private lemma errors_mul_diag (i : Fin 4) :
    (bitFlipErrors i) * (bitFlipErrors i) = bitFlipPauliI := by
  fin_cases i
  · show bitFlipPauliI * bitFlipPauliI = bitFlipPauliI
    unfold bitFlipPauliI
    rw [Matrix.one_mul]
  · exact bitFlipPauliX1_sq
  · exact bitFlipPauliX2_sq
  · exact bitFlipPauliX3_sq

/-! ### Off-diagonal corner-vanishing lemmas.

    For each (i, j) with i ≠ j, we exhibit the four corner entries of
    `E_i · E_j` and show they vanish.  We do this by direct
    computation. -/

/-- Helper tactic: prove all four corner entries vanish via direct
    matrix multiplication.  Used by every off-diagonal case below. -/

private lemma X1_corners :
    bitFlipPauliX1 0 0 = 0 ∧ bitFlipPauliX1 0 7 = 0
  ∧ bitFlipPauliX1 7 0 = 0 ∧ bitFlipPauliX1 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [bitFlipPauliX1]

private lemma X2_corners :
    bitFlipPauliX2 0 0 = 0 ∧ bitFlipPauliX2 0 7 = 0
  ∧ bitFlipPauliX2 7 0 = 0 ∧ bitFlipPauliX2 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [bitFlipPauliX2]

private lemma X3_corners :
    bitFlipPauliX3 0 0 = 0 ∧ bitFlipPauliX3 0 7 = 0
  ∧ bitFlipPauliX3 7 0 = 0 ∧ bitFlipPauliX3 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [bitFlipPauliX3]

/-- `X₁ X₂ = X ⊗ X ⊗ I` (mask 6 = bits 1,2 flipped).  Corners 0,7 are
    zero because flipping 2 bits cannot map |000⟩ to |000⟩, |111⟩, or
    swap them. -/
private lemma X1X2_corners :
    (bitFlipPauliX1 * bitFlipPauliX2) 0 0 = 0
  ∧ (bitFlipPauliX1 * bitFlipPauliX2) 0 7 = 0
  ∧ (bitFlipPauliX1 * bitFlipPauliX2) 7 0 = 0
  ∧ (bitFlipPauliX1 * bitFlipPauliX2) 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bitFlipPauliX1, bitFlipPauliX2, Matrix.mul_apply, Fin.sum_univ_eight]

private lemma X2X1_corners :
    (bitFlipPauliX2 * bitFlipPauliX1) 0 0 = 0
  ∧ (bitFlipPauliX2 * bitFlipPauliX1) 0 7 = 0
  ∧ (bitFlipPauliX2 * bitFlipPauliX1) 7 0 = 0
  ∧ (bitFlipPauliX2 * bitFlipPauliX1) 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bitFlipPauliX1, bitFlipPauliX2, Matrix.mul_apply, Fin.sum_univ_eight]

private lemma X1X3_corners :
    (bitFlipPauliX1 * bitFlipPauliX3) 0 0 = 0
  ∧ (bitFlipPauliX1 * bitFlipPauliX3) 0 7 = 0
  ∧ (bitFlipPauliX1 * bitFlipPauliX3) 7 0 = 0
  ∧ (bitFlipPauliX1 * bitFlipPauliX3) 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bitFlipPauliX1, bitFlipPauliX3, Matrix.mul_apply, Fin.sum_univ_eight]

private lemma X3X1_corners :
    (bitFlipPauliX3 * bitFlipPauliX1) 0 0 = 0
  ∧ (bitFlipPauliX3 * bitFlipPauliX1) 0 7 = 0
  ∧ (bitFlipPauliX3 * bitFlipPauliX1) 7 0 = 0
  ∧ (bitFlipPauliX3 * bitFlipPauliX1) 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bitFlipPauliX1, bitFlipPauliX3, Matrix.mul_apply, Fin.sum_univ_eight]

private lemma X2X3_corners :
    (bitFlipPauliX2 * bitFlipPauliX3) 0 0 = 0
  ∧ (bitFlipPauliX2 * bitFlipPauliX3) 0 7 = 0
  ∧ (bitFlipPauliX2 * bitFlipPauliX3) 7 0 = 0
  ∧ (bitFlipPauliX2 * bitFlipPauliX3) 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bitFlipPauliX2, bitFlipPauliX3, Matrix.mul_apply, Fin.sum_univ_eight]

private lemma X3X2_corners :
    (bitFlipPauliX3 * bitFlipPauliX2) 0 0 = 0
  ∧ (bitFlipPauliX3 * bitFlipPauliX2) 0 7 = 0
  ∧ (bitFlipPauliX3 * bitFlipPauliX2) 7 0 = 0
  ∧ (bitFlipPauliX3 * bitFlipPauliX2) 7 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bitFlipPauliX2, bitFlipPauliX3, Matrix.mul_apply, Fin.sum_univ_eight]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART I — Bundle all 16 cases of `P · E_i† · E_j · P`.

    Since each E_i is Hermitian (E_i† = E_i), we have
    `E_i† · E_j = E_i · E_j`.  We list all 16 cases here.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Each unscaled error is Hermitian: `E_i† = E_i`. -/
private lemma bitFlipErrors_conjT (i : Fin 4) :
    (bitFlipErrors i).conjTranspose = bitFlipErrors i := by
  fin_cases i
  · show bitFlipPauliI.conjTranspose = bitFlipPauliI
    unfold bitFlipPauliI; exact Matrix.conjTranspose_one
  · exact bitFlipPauliX1_conjTranspose
  · exact bitFlipPauliX2_conjTranspose
  · exact bitFlipPauliX3_conjTranspose

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART J — The c-matrix witness and the KL identity for each
    (i, j) pair.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The KL c-matrix for the bit-flip code: `c = (1/4) · I₄`. -/
noncomputable def bitFlipCMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1/4 : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

theorem bitFlipCMatrix_isHermitian : bitFlipCMatrix.IsHermitian := by
  unfold IsHermitian bitFlipCMatrix
  rw [conjTranspose_smul, Matrix.conjTranspose_one]
  congr 1
  -- star (1/4 : ℂ) = 1/4 since 1/4 is real.
  show star (1/4 : ℂ) = (1/4 : ℂ)
  have h : (1/4 : ℂ) = ((1/4 : ℝ) : ℂ) := by norm_num
  rw [h]
  exact Complex.conj_ofReal _

/-! ### The "P · K_i† · K_j · P" identity, case by case. -/


/-- A unified rewriting of `P · K_i† · K_j · P` in terms of the
    unscaled errors:

      P · K_i† · K_j · P = (1/4) · (P · E_i · E_j · P).

    (Both `E_i` are Hermitian, so `E_i† = E_i`.) -/
private lemma kraus_kl_unfold (i j : Fin 4) :
    bitFlipCodeProjector * (bitFlipKraus i).conjTranspose * (bitFlipKraus j)
        * bitFlipCodeProjector
      = ((1/4 : ℂ)) • (bitFlipCodeProjector * (bitFlipErrors i)
                          * (bitFlipErrors j) * bitFlipCodeProjector) := by
  unfold bitFlipKraus
  rw [conjTranspose_smul, bitFlipErrors_conjT]
  -- Both scalars (star (1/2)) and (1/2) commute past matrix multiplications.
  -- We use simp with all the smul-mul lemmas to push scalars out.
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  -- Now both sides are of the form (some_scalar) • (P * E_i * E_j * P).
  congr 1
  -- The scalar simplifies via the half-times-conjugate identity.
  -- Order may be `(1/2) * star (1/2)` or `star (1/2) * (1/2)`; mul_comm fixes.
  rw [mul_comm]
  exact half_conj_half

/-! ### The 16 cases of `P · E_i · E_j · P`. -/

/-- For `i = j`: `P · E_i · E_i · P = P · I · P = P · P = P`. -/
private lemma proj_error_diag (i : Fin 4) :
    bitFlipCodeProjector * (bitFlipErrors i) * (bitFlipErrors i)
        * bitFlipCodeProjector = bitFlipCodeProjector := by
  rw [Matrix.mul_assoc bitFlipCodeProjector (bitFlipErrors i) (bitFlipErrors i)]
  rw [errors_mul_diag i]
  -- Goal: P * I * P = P
  show bitFlipCodeProjector * bitFlipPauliI * bitFlipCodeProjector
      = bitFlipCodeProjector
  unfold bitFlipPauliI
  rw [Matrix.mul_one, bitFlipCodeProjector_idempotent]

/-- For `(i, j) = (0, k)` with k ≠ 0: `E_0 · E_k = I · E_k = E_k`,
    a single-qubit X, whose corners vanish. -/
private lemma proj_error_0k {k : Fin 4} (h : k ≠ 0) :
    bitFlipCodeProjector * bitFlipPauliI * (bitFlipErrors k)
        * bitFlipCodeProjector = 0 := by
  unfold bitFlipPauliI
  rw [Matrix.mul_one]
  -- Now P * E_k * P = 0.
  fin_cases k
  · exact absurd rfl h
  · obtain ⟨h00, h07, h70, h77⟩ := X1_corners
    exact proj_mul_zero_of_corners_zero bitFlipPauliX1 h00 h07 h70 h77
  · obtain ⟨h00, h07, h70, h77⟩ := X2_corners
    exact proj_mul_zero_of_corners_zero bitFlipPauliX2 h00 h07 h70 h77
  · obtain ⟨h00, h07, h70, h77⟩ := X3_corners
    exact proj_mul_zero_of_corners_zero bitFlipPauliX3 h00 h07 h70 h77

/-- For `(i, j) = (k, 0)` with k ≠ 0: same, E_k · E_0 = E_k. -/
private lemma proj_error_k0 {k : Fin 4} (h : k ≠ 0) :
    bitFlipCodeProjector * (bitFlipErrors k) * bitFlipPauliI
        * bitFlipCodeProjector = 0 := by
  unfold bitFlipPauliI
  rw [Matrix.mul_one]
  fin_cases k
  · exact absurd rfl h
  · obtain ⟨h00, h07, h70, h77⟩ := X1_corners
    exact proj_mul_zero_of_corners_zero bitFlipPauliX1 h00 h07 h70 h77
  · obtain ⟨h00, h07, h70, h77⟩ := X2_corners
    exact proj_mul_zero_of_corners_zero bitFlipPauliX2 h00 h07 h70 h77
  · obtain ⟨h00, h07, h70, h77⟩ := X3_corners
    exact proj_mul_zero_of_corners_zero bitFlipPauliX3 h00 h07 h70 h77

/-- For two-qubit X products with i, j ∈ {1, 2, 3}, i ≠ j:
    `P · X_i · X_j · P = 0`. -/
private lemma proj_error_two_x_distinct
    {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    bitFlipCodeProjector * (bitFlipErrors i) * (bitFlipErrors j)
        * bitFlipCodeProjector = 0 := by
  -- Rewrite as P * (E_i · E_j) * P then use corner-vanishing.
  rw [Matrix.mul_assoc bitFlipCodeProjector (bitFlipErrors i) (bitFlipErrors j)]
  fin_cases i <;> fin_cases j <;>
    first
    | (exact absurd rfl hi)
    | (exact absurd rfl hj)
    | (exact absurd rfl hij)
    | (· obtain ⟨h00, h07, h70, h77⟩ := X1X2_corners
         exact proj_mul_zero_of_corners_zero _ h00 h07 h70 h77)
    | (· obtain ⟨h00, h07, h70, h77⟩ := X2X1_corners
         exact proj_mul_zero_of_corners_zero _ h00 h07 h70 h77)
    | (· obtain ⟨h00, h07, h70, h77⟩ := X1X3_corners
         exact proj_mul_zero_of_corners_zero _ h00 h07 h70 h77)
    | (· obtain ⟨h00, h07, h70, h77⟩ := X3X1_corners
         exact proj_mul_zero_of_corners_zero _ h00 h07 h70 h77)
    | (· obtain ⟨h00, h07, h70, h77⟩ := X2X3_corners
         exact proj_mul_zero_of_corners_zero _ h00 h07 h70 h77)
    | (· obtain ⟨h00, h07, h70, h77⟩ := X3X2_corners
         exact proj_mul_zero_of_corners_zero _ h00 h07 h70 h77)

/-- The master "P · E_i · E_j · P" identity, distinguishing i = j and
    i ≠ j cases. -/
private lemma proj_error_master (i j : Fin 4) :
    bitFlipCodeProjector * (bitFlipErrors i) * (bitFlipErrors j)
        * bitFlipCodeProjector
      = (if i = j then 1 else 0 : ℂ) • bitFlipCodeProjector := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, one_smul]
    exact proj_error_diag i
  · rw [if_neg h, zero_smul]
    -- Distribute over the (i, j) ≠ diagonal cases.
    by_cases hi0 : i = 0
    · subst hi0
      have hj0 : j ≠ 0 := fun hj => h hj.symm
      -- (0, j) case
      show bitFlipCodeProjector * bitFlipPauliI * (bitFlipErrors j)
            * bitFlipCodeProjector = 0
      exact proj_error_0k hj0
    · by_cases hj0 : j = 0
      · subst hj0
        -- (i, 0) case
        show bitFlipCodeProjector * (bitFlipErrors i) * bitFlipPauliI
              * bitFlipCodeProjector = 0
        exact proj_error_k0 hi0
      · -- i, j both ≠ 0, and i ≠ j: two-qubit X case.
        exact proj_error_two_x_distinct hi0 hj0 h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART K — Headline: bit-flip code satisfies KL conditions.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The 3-qubit bit-flip code satisfies the Knill-Laflamme
    correctability condition for the single-qubit bit-flip error
    channel.**

    The c-matrix is `c = (1/4) · I_4`, Hermitian.  For diagonal
    entries `c_{ii} = 1/4` and off-diagonal `c_{ij} = 0`.

    Operationally: the four error syndromes (no-error + three
    single-qubit X errors) are mutually distinguishable on the code
    subspace, and the standard recovery procedure (measure
    stabilisers Z⊗Z⊗I and I⊗Z⊗Z, deduce which X was applied, undo
    it) restores the logical qubit. -/
theorem bitFlipCode_isKLCorrectable :
    IsKLCorrectable bitFlipQuantumCode bitFlipErrorChannel := by
  refine ⟨bitFlipCMatrix, bitFlipCMatrix_isHermitian, ?_⟩
  intro i j
  show bitFlipQuantumCode.proj * (bitFlipErrorChannel.K i).conjTranspose
        * (bitFlipErrorChannel.K j) * bitFlipQuantumCode.proj
      = bitFlipCMatrix i j • bitFlipQuantumCode.proj
  -- Unfold all the wrappers.
  show bitFlipCodeProjector * (bitFlipKraus i).conjTranspose
        * (bitFlipKraus j) * bitFlipCodeProjector
      = bitFlipCMatrix i j • bitFlipCodeProjector
  rw [kraus_kl_unfold i j, proj_error_master i j]
  -- LHS: (1/4) • (if i=j then 1 else 0) • P
  -- RHS: bitFlipCMatrix i j • P
  rw [smul_smul]
  -- Need: (1/4) * (if i=j then 1 else 0) = bitFlipCMatrix i j.
  -- Distinguish i = j and i ≠ j.
  by_cases h : i = j
  · subst h
    simp [bitFlipCMatrix, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
  · rw [if_neg h]
    have h_off : bitFlipCMatrix i j = 0 := by
      unfold bitFlipCMatrix
      rw [Matrix.smul_apply, Matrix.one_apply_ne h, smul_eq_mul, mul_zero]
    rw [h_off]
    simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART L — Master record.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Stabiliser-codes master statement.**

    The 3-qubit bit-flip code is a Hermitian projector, the four
    scaled X errors form a valid Kraus channel, and the
    Knill-Laflamme correctability condition holds.  This opens the
    QEC pillar of the framework with a concrete worked example. -/
theorem stabiliserCodes_master :
    bitFlipCodeProjector.IsHermitian
  ∧ bitFlipCodeProjector * bitFlipCodeProjector = bitFlipCodeProjector
  ∧ (∑ i : Fin 4, (bitFlipKraus i).conjTranspose * (bitFlipKraus i))
        = (1 : Matrix (Fin 8) (Fin 8) ℂ)
  ∧ IsKLCorrectable bitFlipQuantumCode bitFlipErrorChannel := by
  refine ⟨bitFlipCodeProjector_isHermitian,
          bitFlipCodeProjector_idempotent,
          bitFlipKraus_complete,
          bitFlipCode_isKLCorrectable⟩

end UnifiedTheory.LayerB.StabiliserCodes

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms UnifiedTheory.LayerB.StabiliserCodes.bitFlipCode_isKLCorrectable
#print axioms UnifiedTheory.LayerB.StabiliserCodes.stabiliserCodes_master
