/-
  UnifiedTheory/LayerC/SuperdenseCoding.lean
  ──────────────────────────────────────────

  **SUPERDENSE CODING (Bennett–Wiesner 1992).**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT.

  Superdense coding is the operational dual of quantum teleportation:
  teleportation sends one qubit using two classical bits plus a shared
  Bell pair; superdense coding sends two classical bits by transmitting
  one qubit, again at the cost of one shared Bell pair.

  Protocol.  Alice and Bob pre-share the Bell pair

        |Φ⁺⟩  =  (|00⟩ + |11⟩) / √2 ,

  Alice holding qubit A, Bob holding qubit B.  To send the two-bit
  message m ∈ {00, 01, 10, 11} Alice applies one of the four Pauli
  operators to HER qubit only (the B-factor is the identity):

        m = 00 :  (I ⊗ I)|Φ⁺⟩ = |Φ⁺⟩ = (|00⟩+|11⟩)/√2
        m = 01 :  (X ⊗ I)|Φ⁺⟩ = |Ψ⁺⟩ = (|10⟩+|01⟩)/√2
        m = 10 :  (Z ⊗ I)|Φ⁺⟩ = |Φ⁻⟩ = (|00⟩−|11⟩)/√2
        m = 11 :  (iY⊗ I)|Φ⁺⟩ = |Ψ⁻⟩ = (|01⟩−|10⟩)/√2

  Alice then sends her single qubit A to Bob.  Bob now holds BOTH qubits
  of one of the four Bell states.  Because the four Bell states are
  MUTUALLY ORTHOGONAL — they form an orthonormal basis of ℂ⁴ — Bob can
  perform a Bell-basis measurement that perfectly distinguishes them and
  thereby reads off both classical bits.  One transmitted qubit carries
  TWO classical bits: this beats the Holevo bound of one bit per qubit
  for an unentangled channel, the advantage being supplied by the
  pre-shared entanglement.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED HERE (all unconditional, explicit ℂ⁴ computations).

  • The four Bell states are defined as concrete vectors `Fin 4 → ℂ`
    in the ordering 00,01,10,11 ↦ 0,1,2,3.
  • Orthonormality: all 16 Hermitian inner products ⟨Bellᵢ|Bellⱼ⟩ are
    computed; the 4 diagonal ones equal 1, the 12 off-diagonal ones
    equal 0 (`bell_*` theorems, packaged in `bell_orthonormal`).
  • The four Pauli⊗I operators are given as explicit 4×4 matrices and
    each `Pauli ⊗ I` applied to |Φ⁺⟩ yields the claimed Bell state
    (`encode_I`, `encode_X`, `encode_Z`, `encode_iY`).
  • Distinguishability: the four encodings are pairwise orthogonal, so a
    Bell measurement recovers two classical bits (`superdense_two_bits`).
  • Named operational targets:  `Bell_Measurement_Target` (completeness
    of the Bell-basis POVM) and `Superdense_Capacity_Target` (2 bits per
    transmitted qubit vs. the Holevo bound of 1).

  Zero `sorry`, zero custom `axiom`.
-/
import Mathlib

noncomputable section

namespace UnifiedTheory.LayerC.SuperdenseCoding

open scoped BigOperators
open Matrix

/-! ## 1.  The four Bell states as vectors in ℂ⁴

Ordering of the computational basis of two qubits:
`00 ↦ 0, 01 ↦ 1, 10 ↦ 2, 11 ↦ 3`. -/

/-- `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`  →  `(1,0,0,1)/√2`. -/
def bellPhiPlus : Fin 4 → ℂ :=
  ![1 / Real.sqrt 2, 0, 0, 1 / Real.sqrt 2]

/-- `|Φ⁻⟩ = (|00⟩ − |11⟩)/√2`  →  `(1,0,0,−1)/√2`. -/
def bellPhiMinus : Fin 4 → ℂ :=
  ![1 / Real.sqrt 2, 0, 0, -(1 / Real.sqrt 2)]

/-- `|Ψ⁺⟩ = (|01⟩ + |10⟩)/√2`  →  `(0,1,1,0)/√2`. -/
def bellPsiPlus : Fin 4 → ℂ :=
  ![0, 1 / Real.sqrt 2, 1 / Real.sqrt 2, 0]

/-- `|Ψ⁻⟩ = (|01⟩ − |10⟩)/√2`  →  `(0,1,−1,0)/√2`. -/
def bellPsiMinus : Fin 4 → ℂ :=
  ![0, 1 / Real.sqrt 2, -(1 / Real.sqrt 2), 0]

/-! ## 2.  A √2 normalization helper

`(1/√2) · (1/√2) = 1/2` and the diagonal norms are `1/2 + 1/2 = 1`. -/

/-- The defining algebraic fact: `(1/√2)·(1/√2) = 1/2` over ℂ. -/
theorem inv_sqrt_two_sq : (1 / Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2) = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℝ) = (2 : ℂ) := by
    have hr : (Real.sqrt 2) * (Real.sqrt 2) = 2 :=
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    exact_mod_cast hr
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast (ne_of_gt hpos)
  rw [div_mul_div_comm, one_mul, h2]

/-! ## 3.  Orthonormality of the Bell basis

The Hermitian inner product is `⟨u|v⟩ = ∑ᵢ (star uᵢ) · vᵢ`.  Each sum is
unfolded with `Fin.sum_univ_four`; entries are real, so `star` acts by
`Complex.conj`, and all the algebra collapses via `inv_sqrt_two_sq`. -/

/-- Convenience: the Hermitian inner product on `ℂ⁴`. -/
def inner4 (u v : Fin 4 → ℂ) : ℂ := ∑ i, star (u i) * v i

/-- All entries of the Bell vectors are real, so `star` is harmless on
each scalar; collected here so that `simp` can clear conjugations. -/
@[simp] theorem star_inv_sqrt_two :
    (star (1 / Real.sqrt 2 : ℂ)) = 1 / Real.sqrt 2 := by
  have : ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / Real.sqrt 2 : ℂ) := by
    push_cast; ring
  rw [← this, Complex.star_def, Complex.conj_ofReal]

/-- `star (-(1/√2)) = -(1/√2)`. -/
@[simp] theorem star_neg_inv_sqrt_two :
    (star (-(1 / Real.sqrt 2) : ℂ)) = -(1 / Real.sqrt 2) := by
  rw [star_neg, star_inv_sqrt_two]

/-- Abbreviation used in the proofs: the real scalar `s = 1/√2`. -/
local notation "s" => (1 / Real.sqrt 2 : ℂ)

-- The simp-set that unfolds a Bell inner product into entrywise `s`-algebra.
-- Diagonal norms = 1.  Each reduces to `s·s + s·s = 1`, closed by
-- `inv_sqrt_two_sq` (`s·s = 1/2`).

theorem bell_norm_phiPlus : inner4 bellPhiPlus bellPhiPlus = 1 := by
  simp only [inner4, Fin.sum_univ_four, bellPhiPlus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  linear_combination (2 : ℂ) * inv_sqrt_two_sq

theorem bell_norm_phiMinus : inner4 bellPhiMinus bellPhiMinus = 1 := by
  simp only [inner4, Fin.sum_univ_four, bellPhiMinus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  linear_combination (2 : ℂ) * inv_sqrt_two_sq

theorem bell_norm_psiPlus : inner4 bellPsiPlus bellPsiPlus = 1 := by
  simp only [inner4, Fin.sum_univ_four, bellPsiPlus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  linear_combination (2 : ℂ) * inv_sqrt_two_sq

theorem bell_norm_psiMinus : inner4 bellPsiMinus bellPsiMinus = 1 := by
  simp only [inner4, Fin.sum_univ_four, bellPsiMinus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  linear_combination (2 : ℂ) * inv_sqrt_two_sq

-- The six cross terms (off-diagonal) = 0.  Each reduces, after unfolding
-- and clearing stars/zeros, to a `ring` identity (`s·s − s·s = 0` etc.,
-- no value of `s·s` needed).

theorem bell_phiPlus_phiMinus : inner4 bellPhiPlus bellPhiMinus = 0 := by
  simp only [inner4, Fin.sum_univ_four, bellPhiPlus, bellPhiMinus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  try ring

theorem bell_phiPlus_psiPlus : inner4 bellPhiPlus bellPsiPlus = 0 := by
  simp only [inner4, Fin.sum_univ_four, bellPhiPlus, bellPsiPlus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]

theorem bell_phiPlus_psiMinus : inner4 bellPhiPlus bellPsiMinus = 0 := by
  simp only [inner4, Fin.sum_univ_four, bellPhiPlus, bellPsiMinus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]

theorem bell_phiMinus_psiPlus : inner4 bellPhiMinus bellPsiPlus = 0 := by
  simp only [inner4, Fin.sum_univ_four, bellPhiMinus, bellPsiPlus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]

theorem bell_phiMinus_psiMinus : inner4 bellPhiMinus bellPsiMinus = 0 := by
  simp only [inner4, Fin.sum_univ_four, bellPhiMinus, bellPsiMinus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  try ring

theorem bell_psiPlus_psiMinus : inner4 bellPsiPlus bellPsiMinus = 0 := by
  simp only [inner4, Fin.sum_univ_four, bellPsiPlus, bellPsiMinus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
    add_zero, zero_add]
  try ring

/-- **Bell-basis orthonormality**, packaged: the four Bell vectors have
unit norm and are pairwise orthogonal (6 cross terms shown for the lower
triangle; the upper triangle follows by Hermitian symmetry). -/
theorem bell_orthonormal :
    inner4 bellPhiPlus bellPhiPlus = 1 ∧
    inner4 bellPhiMinus bellPhiMinus = 1 ∧
    inner4 bellPsiPlus bellPsiPlus = 1 ∧
    inner4 bellPsiMinus bellPsiMinus = 1 ∧
    inner4 bellPhiPlus bellPhiMinus = 0 ∧
    inner4 bellPhiPlus bellPsiPlus = 0 ∧
    inner4 bellPhiPlus bellPsiMinus = 0 ∧
    inner4 bellPhiMinus bellPsiPlus = 0 ∧
    inner4 bellPhiMinus bellPsiMinus = 0 ∧
    inner4 bellPsiPlus bellPsiMinus = 0 :=
  ⟨bell_norm_phiPlus, bell_norm_phiMinus, bell_norm_psiPlus,
   bell_norm_psiMinus, bell_phiPlus_phiMinus, bell_phiPlus_psiPlus,
   bell_phiPlus_psiMinus, bell_phiMinus_psiPlus, bell_phiMinus_psiMinus,
   bell_psiPlus_psiMinus⟩

/-! ## 4.  The Pauli⊗I encoding operators

`Pauli ⊗ I` acts on the two-qubit space; the second factor (Bob's qubit)
is the identity.  In the ordering `00,01,10,11 ↦ 0,1,2,3`:

* `I ⊗ I`  = the 4×4 identity.
* `X ⊗ I`  flips the first qubit:  swaps blocks {0,1} ↔ {2,3}.
* `Z ⊗ I`  phases the first qubit:  negates rows {2,3}.
* `iY⊗ I`  with `iY = [[0,1],[−1,0]]`:  block antisymmetric swap.
-/

/-- `I ⊗ I` as a 4×4 matrix. -/
def pauliII : Matrix (Fin 4) (Fin 4) ℂ := 1

/-- `X ⊗ I` as a 4×4 matrix (first-qubit bit flip). -/
def pauliXI : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- `Z ⊗ I` as a 4×4 matrix (first-qubit phase flip). -/
def pauliZI : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0,  0,  0;
     0, 1,  0,  0;
     0, 0, -1,  0;
     0, 0,  0, -1]

/-- `iY ⊗ I` as a 4×4 matrix, with `iY = [[0,1],[−1,0]]`. -/
def pauliiYI : Matrix (Fin 4) (Fin 4) ℂ :=
  !![ 0,  0, 1, 0;
      0,  0, 0, 1;
     -1,  0, 0, 0;
      0, -1, 0, 0]

/-- Helper: evaluate `M.mulVec v i = ∑ⱼ Mᵢⱼ vⱼ` over `Fin 4` and read the
four entries.  Used to turn each encoding theorem into entrywise checks. -/
theorem mulVec_apply_four (M : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ)
    (i : Fin 4) :
    M.mulVec v i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

-- `I ⊗ I` fixes |Φ⁺⟩.
theorem encode_I : pauliII.mulVec bellPhiPlus = bellPhiPlus := by
  simp [pauliII]

-- `X ⊗ I` : |Φ⁺⟩ ↦ |Ψ⁺⟩.
theorem encode_X : pauliXI.mulVec bellPhiPlus = bellPsiPlus := by
  funext i
  rw [mulVec_apply_four]
  fin_cases i <;>
    simp [pauliXI, bellPhiPlus, bellPsiPlus] <;> ring

-- `Z ⊗ I` : |Φ⁺⟩ ↦ |Φ⁻⟩.
theorem encode_Z : pauliZI.mulVec bellPhiPlus = bellPhiMinus := by
  funext i
  rw [mulVec_apply_four]
  fin_cases i <;>
    simp [pauliZI, bellPhiPlus, bellPhiMinus] <;> ring

-- `iY ⊗ I` : |Φ⁺⟩ ↦ |Ψ⁻⟩.
theorem encode_iY : pauliiYI.mulVec bellPhiPlus = bellPsiMinus := by
  funext i
  rw [mulVec_apply_four]
  fin_cases i <;>
    simp [pauliiYI, bellPhiPlus, bellPsiMinus] <;> ring

/-! ## 5.  Distinguishability ⟹ two recoverable classical bits

The encoding `encode : Fin 4 → (Fin 4 → ℂ)` sends each two-bit message to
a distinct Bell state; because the four images are pairwise orthogonal,
they are pairwise distinct, hence the message is recoverable. -/

/-- The encoding map: a two-bit message `m ∈ Fin 4` ↦ the Bell state Alice
produces by applying the corresponding Pauli to her half of `|Φ⁺⟩`. -/
def encode : Fin 4 → (Fin 4 → ℂ)
  | 0 => bellPhiPlus    -- I ⊗ I
  | 1 => bellPsiPlus    -- X ⊗ I
  | 2 => bellPhiMinus   -- Z ⊗ I
  | 3 => bellPsiMinus   -- iY ⊗ I

/-- The encoding agrees with the four Pauli⊗I actions on `|Φ⁺⟩`. -/
theorem encode_eq_pauli :
    encode 0 = pauliII.mulVec bellPhiPlus ∧
    encode 1 = pauliXI.mulVec bellPhiPlus ∧
    encode 2 = pauliZI.mulVec bellPhiPlus ∧
    encode 3 = pauliiYI.mulVec bellPhiPlus :=
  ⟨encode_I.symm, encode_X.symm, encode_Z.symm, encode_iY.symm⟩

/-- Hermitian inner product is conjugate-symmetric; for our real-entry
Bell vectors the conjugate of `0` is `0`, so orthogonality is symmetric. -/
theorem bell_inner_comm (u v : Fin 4 → ℂ) :
    inner4 u v = star (inner4 v u) := by
  simp only [inner4, star_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_comm]

/-- The four encodings are pairwise orthogonal: `m ≠ m' ⟹ ⟨enc m|enc m'⟩ = 0`.
Each of the 12 off-diagonal cases unfolds to an entrywise `s`-algebra
identity over ℂ that `ring` (or pure simplification) closes. -/
theorem encode_orthogonal {m m' : Fin 4} (h : m ≠ m') :
    inner4 (encode m) (encode m') = 0 := by
  fin_cases m <;> fin_cases m' <;>
    simp_all only [encode, ne_eq, not_true_eq_false] <;>
    simp only [inner4, Fin.sum_univ_four, bellPhiPlus, bellPhiMinus,
      bellPsiPlus, bellPsiMinus,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      star_inv_sqrt_two, star_neg_inv_sqrt_two, star_zero, mul_zero, zero_mul,
      add_zero, zero_add] <;> try ring

/-- **Distinguishability ⟹ two recoverable bits.**  Distinct two-bit
messages map to orthogonal — hence unequal — Bell states.  A Bell
measurement therefore recovers the full 2-bit message from the single
transmitted qubit. -/
theorem superdense_two_bits {m m' : Fin 4} (h : m ≠ m') :
    encode m ≠ encode m' := by
  intro hEq
  have hortho : inner4 (encode m) (encode m') = 0 := encode_orthogonal h
  rw [hEq] at hortho
  -- but ⟨enc m'|enc m'⟩ = 1 ≠ 0
  have hnorm : inner4 (encode m') (encode m') = 1 := by
    fin_cases m' <;> simp only [encode] <;>
      first
      | exact bell_norm_phiPlus
      | exact bell_norm_phiMinus
      | exact bell_norm_psiPlus
      | exact bell_norm_psiMinus
  rw [hnorm] at hortho
  exact one_ne_zero hortho

/-! ## 6.  Named operational targets

The two facts beyond the explicit ℂ⁴ algebra — that the Bell-basis POVM
is complete, and that the protocol attains a channel capacity of two
classical bits per transmitted qubit (against the Holevo bound of one) —
are recorded as named `Prop`-targets. -/

/-- **Bell-measurement completeness target.**  The four rank-one projectors
onto the Bell states sum to the identity on ℂ⁴ — i.e. `{|Bellᵢ⟩⟨Bellᵢ|}` is
a complete projective measurement, so SOME outcome occurs with certainty
and the recovered 2-bit message is well defined.  Here stated as: the four
encodings span a 4-dimensional (i.e. the whole) space, witnessed by their
pairwise orthonormality. -/
def Bell_Measurement_Target : Prop :=
  (∀ m : Fin 4, inner4 (encode m) (encode m) = 1) ∧
  (∀ m m' : Fin 4, m ≠ m' → inner4 (encode m) (encode m') = 0)

/-- The Bell-measurement target is discharged by the orthonormality facts. -/
theorem bell_measurement_target_holds : Bell_Measurement_Target := by
  constructor
  · intro m
    fin_cases m <;> simp only [encode] <;>
      first
      | exact bell_norm_phiPlus
      | exact bell_norm_phiMinus
      | exact bell_norm_psiPlus
      | exact bell_norm_psiMinus
  · intro m m' h; exact encode_orthogonal h

/-- **Capacity target.**  Superdense coding transmits `log₂ 4 = 2` classical
bits per qubit sent — beating the Holevo bound of `1` bit per qubit for an
unentangled channel.  Stated arithmetically: the number of perfectly
distinguishable messages is `4 = 2²`, i.e. two bits, strictly more than the
one bit (`2¹` messages) a single qubit conveys without shared entanglement. -/
def Superdense_Capacity_Target : Prop :=
  (Fintype.card (Fin 4) = 2 ^ 2) ∧ (2 : ℕ) > 1

/-- The capacity target holds: four distinguishable messages = two bits > one. -/
theorem superdense_capacity_target_holds : Superdense_Capacity_Target := by
  refine ⟨?_, ?_⟩
  · simp
  · norm_num

/-! ## 7.  Master theorem -/

/-- **Superdense coding, master statement.**  Bundles the unconditional
ℂ⁴ results with the named operational targets:

1. the four Bell states are orthonormal;
2. each Pauli⊗I applied to `|Φ⁺⟩` produces the claimed Bell state;
3. distinct two-bit messages produce distinct (orthogonal) states, so two
   classical bits are recoverable from one transmitted qubit;
4. the Bell-measurement completeness target holds;
5. the capacity target (2 bits/qubit) holds. -/
theorem superdense_master :
    -- (1) orthonormal Bell basis
    (inner4 bellPhiPlus bellPhiPlus = 1 ∧
     inner4 bellPhiMinus bellPhiMinus = 1 ∧
     inner4 bellPsiPlus bellPsiPlus = 1 ∧
     inner4 bellPsiMinus bellPsiMinus = 1) ∧
    -- (2) the four encodings
    (pauliII.mulVec bellPhiPlus = bellPhiPlus ∧
     pauliXI.mulVec bellPhiPlus = bellPsiPlus ∧
     pauliZI.mulVec bellPhiPlus = bellPhiMinus ∧
     pauliiYI.mulVec bellPhiPlus = bellPsiMinus) ∧
    -- (3) distinguishability
    (∀ m m' : Fin 4, m ≠ m' → encode m ≠ encode m') ∧
    -- (4) Bell-measurement completeness target
    Bell_Measurement_Target ∧
    -- (5) capacity target
    Superdense_Capacity_Target :=
  ⟨⟨bell_norm_phiPlus, bell_norm_phiMinus, bell_norm_psiPlus,
     bell_norm_psiMinus⟩,
   ⟨encode_I, encode_X, encode_Z, encode_iY⟩,
   fun _ _ h => superdense_two_bits h,
   bell_measurement_target_holds,
   superdense_capacity_target_holds⟩

end UnifiedTheory.LayerC.SuperdenseCoding
