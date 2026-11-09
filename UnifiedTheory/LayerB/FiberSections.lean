/-
  LayerB/FiberSections.lean — Coordinate projections and degree-one homogeneity.

  This file proves homogeneity, pairwise distinctness, and the cardinality
  of the coordinate index set. It does not prove linear independence,
  spanning, a holomorphic section-space identification, or a physical
  generation count. Homogeneity alone does not imply complex linearity.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card

namespace UnifiedTheory.LayerB.FiberSections

/-! ## Homogeneous functions on ℂ^{n+1}

  A function f: ℂ^{n+1} → ℂ is homogeneous of degree 1 if
  f(λz) = λ · f(z) for all λ ∈ ℂ, z ∈ ℂ^{n+1}.

  This algebraic condition alone does not identify the holomorphic sections
  of the hyperplane bundle O(1) on CP^n.
-/

/-- A function on ℂ^{n+1} is homogeneous of degree 1. -/
def IsHomogeneous1 {n : ℕ} (f : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ (c : ℂ) (z : Fin n → ℂ), f (fun i => c * z i) = c * f z

/-- The k-th coordinate projection: π_k(z) = z_k. -/
def coordProj {n : ℕ} (k : Fin n) : (Fin n → ℂ) → ℂ :=
  fun z => z k

/-- Each coordinate projection is homogeneous of degree 1. -/
theorem coordProj_homogeneous {n : ℕ} (k : Fin n) :
    IsHomogeneous1 (coordProj k) := by
  intro c z
  simp [coordProj]

/-- Coordinate projections are distinct: π_j ≠ π_k for j ≠ k.
    Proof: the standard basis vectors distinguish them. -/
theorem coordProj_distinct {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    coordProj j ≠ coordProj (n := n) k := by
  intro h
  -- Apply both sides to the basis vector e_j
  let e_j : Fin n → ℂ := fun i => if i = j then 1 else 0
  have h1 : coordProj j e_j = 1 := by simp [coordProj, e_j]
  have h2 : coordProj k e_j = 0 := by simp [coordProj, e_j, hjk.symm]
  rw [h] at h1
  exact absurd (h1.symm.trans h2) one_ne_zero

/- WHAT IS PROVEN HERE about coordinate projections:

    1. coordProj_homogeneous: The n+1 coordinate projections are degree-1
       homogeneous functions on ℂ^{n+1}. (PROVEN)
    2. coordProj_distinct: They are pairwise distinct. (PROVEN)
    3. There are exactly n+1 of them. (TRIVIAL: Fin (n+1) has card n+1)

    WHAT IS NOT PROVEN HERE:
    4. Spanning or a dimension computation for the space of complex linear forms.
       Arbitrary degree-one homogeneous functions need not be linear.
    5. An identification with holomorphic sections of O(1).

    The "key theorem" `n + 1 = n + 1 := rfl` was rightly flagged as a tautology.
    It is replaced below with a reference to Mathlib's dimension computation. -/

/-- The number of coordinate projections on ℂ^{n+1} is n+1.
    This is the cardinality of Fin (n+1), which is a tautology.
    The REAL theorem (that these SPAN the space of linear forms,
    giving dim = n+1) requires Mathlib's Module.finrank. -/
theorem n_coordinate_projections (n : ℕ) : Fintype.card (Fin (n + 1)) = n + 1 :=
  Fintype.card_fin (n + 1)

/-! ## Generation count

  DELETED: The former `generationCount Nc := Nc` was the identity function,
  making `three_generations : generationCount 3 = 3` a tautology (3 = 3 := rfl).

  The REAL generation count is in GenerationsFromFiber.lean:
    noncomputable def generationCount (Nc : ℕ) : ℕ := Module.finrank ℝ (Fin Nc → ℝ)
  which uses Mathlib's vector space dimension computation.

  This file retains the FIBER SECTION proofs:
  - coordProj_homogeneous: coordinate projections are degree-1 homogeneous
  - coordProj_distinct: they are pairwise distinct
  - n_coordinate_projections: there are n+1 of them (Fintype.card_fin)
-/

end UnifiedTheory.LayerB.FiberSections
