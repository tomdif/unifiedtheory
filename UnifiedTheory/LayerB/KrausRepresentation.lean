/-
  LayerB/KrausRepresentation.lean
  ────────────────────────────────

  Phase 1 of the Kraus representation theorem: the *engineering form*.

  A Kraus representation of dimension (m → n, with k operators) is a
  finite indexed family {Kᵢ : Matrix n m ℂ} satisfying the completeness
  relation

      Σᵢ Kᵢ† · Kᵢ  =  I_m .

  Every such family induces a map on density matrices

      ρ ↦ Σᵢ Kᵢ · ρ · Kᵢ†

  which is linear, Hermitian-preserving, PSD-preserving, and trace-
  preserving — i.e., a CPTP map in the engineering sense.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `KrausRepresentation m n k` structure (k operators Kᵢ : n×m
       complex matrices with completeness).
    2. `apply K ρ := Σᵢ Kᵢ · ρ · Kᵢ†` is:
         - linear in ρ
         - Hermitian-preserving (Hermitian ρ ↦ Hermitian result)
         - trace-preserving (Tr(apply K ρ) = Tr ρ)
         - PSD-preserving (PSD ρ ↦ PSD result)
    3. `identity_kraus` : the trivial single-operator rep {I} is a
       valid Kraus representation, and its `apply` is the identity.

  WHAT IS NOT IN THIS FILE (Phase 2):
    The existence direction (every CP map has a Kraus representation)
    requires the Choi-Jamiolkowski isomorphism + spectral decomposition
    of the Choi matrix + vec/unvec.  Left for a follow-up.

  SCOPE CAVEAT:
    – Finite-dimensional complex matrices.
    – Trace-preserving (sum-to-identity) form, not subnormalized.
    – Indexed by `Fin k` (not arbitrary `Finset`) for index-handling
      simplicity.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.Star

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Kraus

open Matrix Complex
open scoped ComplexOrder

/-- Local `AddLeftMono ℂ` instance — needed for `Matrix.PosSemidef.add`
    over ℂ.  Mathlib provides `IsOrderedAddMonoid ℂ` via ComplexOrder
    but does not register the corresponding `AddLeftMono` covariant
    class instance globally. -/
local instance : AddLeftMono ℂ where
  elim c a b (h : a ≤ b) := by
    change c + a ≤ c + b
    obtain ⟨hr, hi⟩ := h
    exact ⟨by simp only [Complex.add_re]; linarith,
           by simp only [Complex.add_im]; linarith⟩

/-! ## 1. The Kraus representation structure -/

/-- A Kraus representation with `k` operators mapping `m`-dimensional
    to `n`-dimensional complex matrices.  The operators `K i : Matrix n m ℂ`
    are required to satisfy the completeness relation

        Σ i, (K i)† · (K i)  =  (1 : Matrix m m ℂ) . -/
structure KrausRepresentation (m n k : ℕ) where
  /-- The `k` Kraus operators K i : Matrix n m ℂ. -/
  K : Fin k → Matrix (Fin n) (Fin m) ℂ
  /-- Completeness relation:  Σᵢ Kᵢ† · Kᵢ = I_m. -/
  complete : (∑ i, (K i).conjTranspose * (K i)) = (1 : Matrix (Fin m) (Fin m) ℂ)

namespace KrausRepresentation

variable {m n k : ℕ}

/-- The map induced by a Kraus representation:
    `apply K ρ := Σᵢ Kᵢ · ρ · Kᵢ†`. -/
noncomputable def apply (K : KrausRepresentation m n k)
    (ρ : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, K.K i * ρ * (K.K i).conjTranspose

/-! ## 2. Linearity in ρ -/

theorem apply_add (K : KrausRepresentation m n k)
    (ρ σ : Matrix (Fin m) (Fin m) ℂ) :
    K.apply (ρ + σ) = K.apply ρ + K.apply σ := by
  unfold apply
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_add, Matrix.add_mul]

theorem apply_smul (K : KrausRepresentation m n k)
    (c : ℂ) (ρ : Matrix (Fin m) (Fin m) ℂ) :
    K.apply (c • ρ) = c • K.apply ρ := by
  unfold apply
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem apply_zero (K : KrausRepresentation m n k) :
    K.apply 0 = 0 := by
  unfold apply
  simp

/-! ## 3. Hermitian preservation -/

theorem apply_isHermitian (K : KrausRepresentation m n k)
    {ρ : Matrix (Fin m) (Fin m) ℂ} (hρ : ρ.IsHermitian) :
    (K.apply ρ).IsHermitian := by
  unfold IsHermitian apply
  rw [conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- (Kᵢ ρ Kᵢ†)† = (Kᵢ†)† ρ† Kᵢ† = Kᵢ ρ Kᵢ†   (using ρ Hermitian)
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hρ]
  -- Goal: Kᵢ * ρ * Kᵢ† = Kᵢ† * ρ * (Kᵢ†)† -- wait need to track sides
  rw [Matrix.mul_assoc]

/-! ## 4. Trace preservation -/

/-- Cyclicity helper: `Tr(K · ρ · K†) = Tr(K† · K · ρ)`. -/
private theorem trace_kraus_term (K : Matrix (Fin n) (Fin m) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (K * ρ * K.conjTranspose)
      = Matrix.trace (K.conjTranspose * K * ρ) := by
  -- Tr(K · ρ · K†) = Tr((K · ρ) · K†) = Tr(K† · (K · ρ)) = Tr(K† · K · ρ)
  rw [Matrix.trace_mul_comm (K * ρ) K.conjTranspose, Matrix.mul_assoc]

/-- **Trace preservation.**  For any ρ, `Tr(apply K ρ) = Tr ρ`. -/
theorem trace_apply (K : KrausRepresentation m n k)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (K.apply ρ) = Matrix.trace ρ := by
  unfold apply
  rw [Matrix.trace_sum]
  -- Σ i, Tr(Kᵢ ρ Kᵢ†) = Σ i, Tr(Kᵢ† Kᵢ ρ) = Tr((Σ i, Kᵢ† Kᵢ) · ρ) = Tr(I · ρ) = Tr ρ
  simp_rw [trace_kraus_term]
  rw [← Matrix.trace_sum]
  rw [← Finset.sum_mul]
  rw [K.complete, Matrix.one_mul]

/-! ## 5. PSD preservation -/

/-- **PSD preservation.**  For any PSD ρ, `apply K ρ` is PSD. -/
theorem apply_posSemidef (K : KrausRepresentation m n k)
    {ρ : Matrix (Fin m) (Fin m) ℂ} (hρ : ρ.PosSemidef) :
    (K.apply ρ).PosSemidef := by
  unfold apply
  -- Each term Kᵢ · ρ · Kᵢ† is PSD (PSD conjugated by a matrix),
  -- and sum of PSD is PSD.
  have h_term : ∀ i, (K.K i * ρ * (K.K i).conjTranspose).PosSemidef :=
    fun i => hρ.mul_mul_conjTranspose_same (K.K i)
  -- Induct on the universal finset Fin k.
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact Matrix.PosSemidef.zero
  | insert _ _ h_notin ih =>
    rw [Finset.sum_insert h_notin]
    exact (h_term _).add ih

/-! ## 6. The trivial (identity) Kraus representation -/

/-- The single-operator Kraus representation with `K₀ = I`.  Its
    induced map is the identity on density matrices. -/
def identity (m : ℕ) : KrausRepresentation m m 1 where
  K := fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)
  complete := by
    simp [Matrix.conjTranspose_one]

theorem identity_apply (m : ℕ) (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (identity m).apply ρ = ρ := by
  unfold apply identity
  simp [Matrix.conjTranspose_one]

end KrausRepresentation

end UnifiedTheory.LayerB.Kraus
