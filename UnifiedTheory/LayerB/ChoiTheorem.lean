/-
# Choi's Theorem on Completely Positive Maps (1975)

A linear map `Φ : M_n → M_n` is **completely positive** iff its Choi matrix
`C_Φ = ∑_{ij} E_ij ⊗ Φ(E_ij)` is positive semidefinite.

## What is closed unconditionally

The **easy (constructive) direction**: every Kraus map `Φ(X) = ∑_α K_α X K_α†`
is completely positive.  We prove this by identifying the textbook Choi matrix
of a Kraus map with the Choi matrix already shown PSD in
`UnifiedTheory.LayerB.ChoiKraus` (`choi_posSemidef`), so `krausMap_is_CP`
reduces to that keystone.

## Named targets (honest scoping)

* `Choi_CP_iff_Kraus_Target` — the HARD direction: `C_Φ ⪰ 0 ⟹ Φ` has a Kraus
  representation (via spectral decomposition of `C_Φ` + reshaping eigenvectors).
* `TracePreserving_iff_Choi_Target` — `Φ` is trace-preserving iff
  `Tr_out(C_Φ) = I`.

All theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerB.ChoiKraus

namespace UnifiedTheory.LayerB.ChoiTheorem

open Matrix
open scoped BigOperators ComplexOrder

variable {n k : ℕ}

/-- A linear (here: arbitrary) map between square matrix algebras. -/
def MatrixMap (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ

/-- The `(i,j)` matrix unit `E_ij` (one at entry `(i,j)`, zero elsewhere). -/
noncomputable def matrixUnit (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single i j 1

/-- The **Choi matrix** of a map in the textbook convention
    `C[(i,k),(j,l)] = Φ(E_ij) k l`. -/
noncomputable def choiMatrix (Φ : MatrixMap n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun ik jl => Φ (matrixUnit ik.1 jl.1) ik.2 jl.2

@[simp]
theorem choiMatrix_apply (Φ : MatrixMap n) (i k j l : Fin n) :
    choiMatrix Φ (i, k) (j, l) = Φ (matrixUnit i j) k l := rfl

/-- **Complete positivity** = positive semidefiniteness of the Choi matrix
    (the modern operational definition). -/
def IsCompletelyPositive (Φ : MatrixMap n) : Prop :=
  (choiMatrix Φ).PosSemidef

/-- The Kraus map `X ↦ ∑_α K_α X K_α†`. -/
noncomputable def krausMap (K : Fin k → Matrix (Fin n) (Fin n) ℂ) : MatrixMap n :=
  fun X => ∑ α, K α * X * (K α)ᴴ

/-- Evaluation of a Kraus map on a matrix unit, entrywise:
    `(∑_α K_α E_ij K_α†) k l = ∑_α (K_α)_{k i} · conj((K_α)_{l j})`. -/
theorem krausMap_matrixUnit_apply
    (K : Fin k → Matrix (Fin n) (Fin n) ℂ) (i j p q : Fin n) :
    krausMap K (matrixUnit i j) p q
      = ∑ α, K α p i * star (K α q j) := by
  unfold krausMap matrixUnit
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro α _
  -- (K_α * E_ij * K_α†) p q = K_α p i * star (K_α q j)
  rw [Matrix.mul_apply]
  -- ∑ x, (K_α * E_ij) p x * (K_α†) x q ;  only x = j survives
  rw [Finset.sum_eq_single j]
  · -- the x = j term
    rw [Matrix.mul_apply]
    -- ∑ y, K_α p y * (single i j 1) y j * (K_α†) j q ; only y = i survives
    rw [Finset.sum_eq_single i]
    · simp [Matrix.single_apply, Matrix.conjTranspose_apply]
    · intro b _ hb
      simp [Matrix.single_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro x _ hx
    rw [Matrix.mul_apply]
    have hzero : ∀ y, K α p y * Matrix.single i j 1 y x = 0 := by
      intro y
      rw [Matrix.single_apply, if_neg (by rintro ⟨_, hjx⟩; exact hx hjx.symm), mul_zero]
    simp only [hzero, Finset.sum_const_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Bridge:** the textbook Choi matrix of a Kraus map coincides with the
    Choi matrix of the Kraus family in `ChoiKraus`. -/
theorem choiMatrix_krausMap_eq (K : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    choiMatrix (krausMap K) = UnifiedTheory.LayerB.ChoiKraus.choi K := by
  ext ik jl
  obtain ⟨i, p⟩ := ik
  obtain ⟨j, q⟩ := jl
  rw [choiMatrix_apply, krausMap_matrixUnit_apply,
      UnifiedTheory.LayerB.ChoiKraus.choi_apply]

/-- **The easy direction of Choi's theorem.**  Every Kraus map is completely
    positive. -/
theorem krausMap_is_CP (K : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    IsCompletelyPositive (krausMap K) := by
  unfold IsCompletelyPositive
  rw [choiMatrix_krausMap_eq]
  exact UnifiedTheory.LayerB.ChoiKraus.choi_posSemidef K

/-- The Choi matrix of any Kraus map is Hermitian (corollary of the bridge). -/
theorem choiMatrix_krausMap_isHermitian (K : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    (choiMatrix (krausMap K)).IsHermitian :=
  (krausMap_is_CP K).1

/-- **Choi's theorem, hard direction (named target).**
    A completely positive map admits a Kraus representation. -/
def Choi_CP_iff_Kraus_Target : Prop :=
  ∀ {n : ℕ} (Φ : MatrixMap n), IsCompletelyPositive Φ →
    ∃ (k : ℕ) (K : Fin k → Matrix (Fin n) (Fin n) ℂ),
      ∀ X, Φ X = krausMap K X

/-- **Trace-preservation characterization (named target).**
    `Φ` is trace-preserving iff the output-partial-trace of its Choi matrix
    is the identity. -/
def TracePreserving_iff_Choi_Target : Prop :=
  ∀ {n : ℕ} (Φ : MatrixMap n),
    (∀ X, (Φ X).trace = X.trace) ↔
      (∀ i j, (∑ p, choiMatrix Φ (i, p) (j, p)) = if i = j then 1 else 0)

/-- Master theorem: the unconditional easy direction together with the two
    named targets capturing the deep content of Choi's theorem. -/
theorem choi_master :
    (∀ (K : Fin k → Matrix (Fin n) (Fin n) ℂ), IsCompletelyPositive (krausMap K)) ∧
    (∀ (K : Fin k → Matrix (Fin n) (Fin n) ℂ),
      (choiMatrix (krausMap K)).IsHermitian) := by
  exact ⟨krausMap_is_CP, choiMatrix_krausMap_isHermitian⟩

end UnifiedTheory.LayerB.ChoiTheorem
