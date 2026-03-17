/-
  LayerB/NonCommutative.lean — Non-commutativity from matrix multiplication

  The perturbation space Matrix (Fin n) (Fin n) ℝ has a natural
  non-commutative multiplication: matrix multiplication. This is
  NOT an additional postulate — it is intrinsic algebraic structure
  of the perturbation space.

  Key results:
    1. Matrix multiplication is non-commutative for n ≥ 2
    2. The trace is the unique linear functional commuting with
       multiplication: Tr(AB) = Tr(BA) for all A, B
    3. Individual matrix-entry observables do NOT commute with
       multiplication: O_{ij}(AB) ≠ O_{ij}(BA) in general
    4. The trace/charge Q is therefore DISTINGUISHED among all
       observables as the unique commutative one

  This gives the quantum side genuine geometric content:
    - Non-commutativity comes FROM the perturbation space structure
    - The charge Q = Tr is distinguished BY this non-commutativity
    - The non-commuting observables are matrix entries, not postulated
    - This is intrinsic to Matrix, not imported from quantum mechanics

  The connection to quantum mechanics:
    - In QM, observables are operators that don't commute: [A,B] ≠ 0
    - Here, the perturbation space IS an operator algebra (matrices)
    - The "observables" (matrix entry functionals) don't commute
      under the natural multiplication
    - The trace is the unique "classical" (commutative) observable
-/
import UnifiedTheory.LayerB.MetricDefects
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic

namespace UnifiedTheory.LayerB.NonCommutative

open MetricDefects Matrix

variable {m : ℕ}

/-! ## Matrix multiplication is non-commutative -/

/-- **MATRIX MULTIPLICATION IS NON-COMMUTATIVE for n ≥ 2.**
    There exist matrices A, B in the perturbation space such that
    A * B ≠ B * A. This is intrinsic algebraic structure, not a postulate. -/
theorem matrix_mul_noncommutative (hm : 0 < m) :
    ∃ A B : Perturbation (m + 2), A * B ≠ B * A := by
  -- Witness: elementary matrices E_{01} and E_{10}
  -- E_{01} * E_{10} = E_{00}, E_{10} * E_{01} = E_{11}
  -- These differ at position (0,0): 1 vs 0
  let n := m + 2
  have hn : 1 < n := by omega
  let E01 : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let E10 : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = 1 ∧ j = 0 then 1 else 0
  use E01, E10
  intro h
  -- E01 * E10 at (0,0) = Σ_k E01(0,k) * E10(k,0) = E01(0,1) * E10(1,0) = 1
  -- E10 * E01 at (0,0) = Σ_k E10(0,k) * E01(k,0) = 0 (E10(0,k) = 0 for all k)
  have h00 : (E01 * E10) 0 0 = (E10 * E01) 0 0 := by
    have := congr_fun (congr_fun h 0) 0; exact this
  simp only [Matrix.mul_apply] at h00
  -- LHS: Σ_k (if 0=0 ∧ k=1 then 1 else 0) * (if k=1 ∧ 0=0 then 1 else 0)
  -- The only nonzero term is k=1: 1 * 1 = 1
  -- RHS: Σ_k (if 0=1 ∧ k=0 then 1 else 0) * (if k=0 ∧ 0=1 then 1 else 0)
  -- All terms are 0 because 0 ≠ 1
  have lhs : ∑ k : Fin n, (if (0 : Fin n) = 0 ∧ k = 1 then (1 : ℝ) else 0) *
    (if k = 1 ∧ (0 : Fin n) = 0 then (1 : ℝ) else 0) = 1 := by
    have : ∀ k : Fin n, k ≠ (1 : Fin n) →
      (if (0 : Fin n) = 0 ∧ k = 1 then (1 : ℝ) else 0) *
      (if k = 1 ∧ (0 : Fin n) = 0 then (1 : ℝ) else 0) = 0 := by
      intro k hk; simp [hk]
    rw [Finset.sum_eq_single (1 : Fin n) (fun k _ hk => this k hk)
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have rhs : ∑ k : Fin n, (if (0 : Fin n) = 1 ∧ k = 0 then (1 : ℝ) else 0) *
    (if k = 0 ∧ (0 : Fin n) = 1 then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    have : (0 : Fin n) ≠ (1 : Fin n) := by exact Fin.ne_of_lt (by omega : (0 : ℕ) < 1)
    simp [this]
  linarith

/-! ## The trace commutes with multiplication -/

/-- **TRACE COMMUTES WITH MULTIPLICATION: Tr(AB) = Tr(BA).**
    This is a standard fact about matrix trace. It means the charge
    functional Q = Tr is invariant under reordering of multiplication.
    The trace is "classical" — it doesn't see the non-commutativity. -/
theorem trace_commutes (A B : Perturbation (m + 2)) :
    Matrix.trace (A * B) = Matrix.trace (B * A) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-! ## Matrix-entry observables do NOT commute -/

/-- A matrix-entry observable: O_{ij}(h) = h(i,j). -/
def entryObs (i j : Fin (m + 2)) (h : Perturbation (m + 2)) : ℝ := h i j

/-- **ENTRY OBSERVABLES DO NOT COMMUTE WITH MULTIPLICATION.**
    O_{ij}(AB) ≠ O_{ij}(BA) in general. This means measuring
    a specific matrix entry gives different results depending on
    the order of composition — genuine non-commutativity of observables. -/
theorem entry_obs_noncommutative (hm : 0 < m) :
    ∃ (i j : Fin (m + 2)) (A B : Perturbation (m + 2)),
      entryObs i j (A * B) ≠ entryObs i j (B * A) := by
  -- Same witnesses as matrix_mul_noncommutative
  use 0, 0
  let n := m + 2
  let E01 : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let E10 : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = 1 ∧ j = 0 then 1 else 0
  use E01, E10
  simp only [entryObs, Matrix.mul_apply]
  -- Same computation as in matrix_mul_noncommutative
  have lhs : ∑ k : Fin n, (if (0 : Fin n) = 0 ∧ k = 1 then (1 : ℝ) else 0) *
    (if k = 1 ∧ (0 : Fin n) = 0 then (1 : ℝ) else 0) = 1 := by
    have : ∀ k : Fin n, k ≠ (1 : Fin n) →
      (if (0 : Fin n) = 0 ∧ k = 1 then (1 : ℝ) else 0) *
      (if k = 1 ∧ (0 : Fin n) = 0 then (1 : ℝ) else 0) = 0 := by
      intro k hk; simp [hk]
    rw [Finset.sum_eq_single (1 : Fin n) (fun k _ hk => this k hk)
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have rhs : ∑ k : Fin n, (if (0 : Fin n) = 1 ∧ k = 0 then (1 : ℝ) else 0) *
    (if k = 0 ∧ (0 : Fin n) = 1 then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    have : (0 : Fin n) ≠ (1 : Fin n) := by exact Fin.ne_of_lt (by omega : (0 : ℕ) < 1)
    simp [this]
  linarith

/-! ## The trace is distinguished by commutativity -/

/-- **THE TRACE IS A DISTINGUISHED ORDER-INSENSITIVE OBSERVABLE.**

    Among observables on the perturbation space:
    - Matrix-entry observables O_{ij} do NOT commute with multiplication
    - The trace Tr DOES commute: Tr(AB) = Tr(BA)

    This means: the charge functional Q = Tr is a distinguished
    order-insensitive observable. The traceless sector carries
    order-sensitive degrees of freedom not visible to trace.

    Physical interpretation:
    - Q = Tr is an order-insensitive (classical-like) observable
    - Matrix entries detect order-sensitive (quantum-like) structure
    - The K/P split separates order-insensitive content (K = trace)
      from order-sensitive content (P = traceless)

    This is genuine geometric content: the non-commutativity is
    intrinsic to the matrix algebra, not imported from QM. -/
theorem trace_is_distinguished (hm : 0 < m) :
    -- (1) The trace commutes with multiplication
    (∀ A B : Perturbation (m + 2), Matrix.trace (A * B) = Matrix.trace (B * A))
    -- (2) Matrix entries do NOT commute with multiplication
    ∧ (∃ (i j : Fin (m + 2)) (A B : Perturbation (m + 2)),
        entryObs i j (A * B) ≠ entryObs i j (B * A))
    -- (3) Matrix multiplication is genuinely non-commutative
    ∧ (∃ A B : Perturbation (m + 2), A * B ≠ B * A) := by
  exact ⟨trace_commutes, entry_obs_noncommutative hm, matrix_mul_noncommutative hm⟩

/-! ## Trace classification: uniqueness up to scale -/

/-- **Diagonal values of a cyclic functional are all equal.**
    If φ(AB) = φ(BA) for all A, B, then φ(E_{ii}) = φ(E_{jj}) for
    all i, j, where E_{ij} = Matrix.single i j 1. -/
private lemma cyclic_diagonal_eq {n : ℕ} [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h_cyclic : ∀ A B : Matrix (Fin n) (Fin n) ℝ, φ (A * B) = φ (B * A))
    (i j : Fin n) : φ (Matrix.single i i 1) = φ (Matrix.single j j 1) := by
  -- φ(E_{ij} * E_{ji}) = φ(E_{ii}) since j=j in the product
  have h1 : φ (Matrix.single i j 1 * Matrix.single j i 1) =
            φ (Matrix.single i i (1 * 1)) := by
    rw [Matrix.single_mul_single_same]
  -- φ(E_{ji} * E_{ij}) = φ(E_{jj})
  have h2 : φ (Matrix.single j i 1 * Matrix.single i j 1) =
            φ (Matrix.single j j (1 * 1)) := by
    rw [Matrix.single_mul_single_same]
  -- By cyclic property: φ(E_{ij} * E_{ji}) = φ(E_{ji} * E_{ij})
  have h3 := h_cyclic (Matrix.single i j 1) (Matrix.single j i 1)
  simp only [mul_one] at h1 h2
  linarith

/-- **Off-diagonal values of a cyclic functional are zero.**
    If φ(AB) = φ(BA) and i ≠ j, then φ(E_{ij}) = 0. -/
private lemma cyclic_offdiag_zero {n : ℕ} [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h_cyclic : ∀ A B : Matrix (Fin n) (Fin n) ℝ, φ (A * B) = φ (B * A))
    (i j : Fin n) (hij : i ≠ j) : φ (Matrix.single i j 1) = 0 := by
  -- E_{ij} * E_{jj} = E_{ij} (since j=j in the product)
  have h1 : Matrix.single i j (1 : ℝ) * Matrix.single j j 1 =
            Matrix.single i j (1 * 1) :=
    Matrix.single_mul_single_same 1 i j j 1
  -- E_{jj} * E_{ij} = 0 (since j ≠ i)
  have h2 : Matrix.single j j (1 : ℝ) * Matrix.single i j 1 = 0 :=
    Matrix.single_mul_single_of_ne 1 j j i (hij.symm) 1
  -- By cyclic: φ(E_{ij} * E_{jj}) = φ(E_{jj} * E_{ij})
  have h3 := h_cyclic (Matrix.single i j 1) (Matrix.single j j 1)
  simp only [mul_one] at h1
  rw [h1, h2] at h3
  rw [map_zero] at h3
  exact h3

/-- **TRACE CLASSIFICATION THEOREM: uniqueness up to scale.**

    Any linear functional φ on Matrix (Fin n) (Fin n) ℝ satisfying the
    cyclic property φ(AB) = φ(BA) for all A, B must be proportional to
    the trace. That is, there exists c ∈ ℝ such that φ = c · Tr.

    Proof strategy (elementary matrices):
    1. All diagonal values are equal: φ(E_{ii}) = φ(E_{jj}) for all i,j
       (from φ(E_{ij}E_{ji}) = φ(E_{ji}E_{ij}) by cyclic property)
    2. Off-diagonal values vanish: φ(E_{ij}) = 0 for i ≠ j
       (from φ(E_{ij}E_{jj}) = φ(E_{jj}E_{ij}) and E_{jj}E_{ij} = 0)
    3. Any A = Σ_{ij} a_{ij} E_{ij}, so φ(A) = Σ_i a_{ii} φ(E_{11}) = φ(E_{11}) · Tr(A)

    This upgrades `trace_is_distinguished` from "distinguished" to
    "unique up to scale" among cyclic linear functionals. -/
theorem trace_unique_cyclic {n : ℕ} (hn : 0 < n)
    (φ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h_cyclic : ∀ A B : Matrix (Fin n) (Fin n) ℝ, φ (A * B) = φ (B * A)) :
    ∃ c : ℝ, ∀ A : Matrix (Fin n) (Fin n) ℝ, φ A = c * Matrix.trace A := by
  haveI : NeZero n := ⟨by omega⟩
  -- The constant is φ(E_{00})
  use φ (Matrix.single (0 : Fin n) (0 : Fin n) 1)
  intro A
  -- Helper: φ(single i j (r)) = r • φ(single i j 1)
  have φ_single_smul : ∀ (i j : Fin n) (r : ℝ),
      φ (Matrix.single i j r) = r * φ (Matrix.single i j 1) := by
    intro i j r
    have : Matrix.single i j r = r • Matrix.single i j 1 := by
      ext p q; simp [Matrix.single, mul_one]
    rw [this, map_smul, smul_eq_mul]
  -- Key: φ(single i j (A i j)) = if i = j then A i j * φ(E₀₀) else 0
  have key : ∀ (i j : Fin n), φ (Matrix.single i j (A i j)) =
      if i = j then A i j * φ (Matrix.single 0 0 1) else 0 := by
    intro i j
    rw [φ_single_smul]
    split_ifs with h
    · subst h
      rw [cyclic_diagonal_eq φ h_cyclic i 0]
    · rw [cyclic_offdiag_zero φ h_cyclic i j h, mul_zero]
  -- Decompose A = Σ_{i,j} A(i,j) · E_{ij}
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  simp_rw [map_sum, key]
  -- Inner sum: Σ_j (if i=j then ... else 0) = A i i * c
  have inner : ∀ i : Fin n, ∑ j : Fin n, (if i = j then A i j *
      φ (Matrix.single 0 0 1) else 0) = A i i * φ (Matrix.single 0 0 1) := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hji => if_neg (Ne.symm hji))
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  simp_rw [inner]
  -- Σ_i A i i * c = c * Tr(A)
  simp only [Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum]
  congr 1; ext i; ring

end UnifiedTheory.LayerB.NonCommutative
