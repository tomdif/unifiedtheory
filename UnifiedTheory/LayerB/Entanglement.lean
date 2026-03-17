/-
  LayerB/Entanglement.lean — Tensor product structure and entanglement
  from the matrix perturbation space

  The perturbation space Matrix (Fin n) (Fin n) R naturally admits a
  notion of separability and entanglement:

  - A perturbation h is **separable** (rank 1) if h = v otimes w,
    i.e., h i j = v i * w j for some vectors v, w.
  - A perturbation is **entangled** if it is NOT separable.

  Key results:
    1. Separable matrices exist (vecMulVec v w for any nonzero v, w)
    2. The identity matrix is entangled for n >= 2
    3. Trace of a separable matrix = dot product of the factors
    4. Entangled perturbations cannot be decomposed into independent
       subsystem contributions

  Physical interpretation:
    - Separable perturbations = independent subsystems (row x column)
    - Entangled perturbations = correlated subsystems (cannot factor)
    - The identity matrix (conformal mode) is maximally entangled
    - Rank = entanglement measure
-/
import UnifiedTheory.LayerB.MetricDefects
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic

namespace UnifiedTheory.LayerB.Entanglement

open MetricDefects Matrix

variable {m : ℕ}

/-! ## Separability and entanglement -/

/-- A matrix h is **separable** if it can be written as an outer product
    h i j = v i * w j for some vectors v, w. This is the rank-1 condition. -/
def IsSeparable {n : ℕ} (h : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ v w : Fin n → ℝ, h = Matrix.vecMulVec v w

/-- A matrix is **entangled** if it is NOT separable (not rank 1). -/
def IsEntangled {n : ℕ} (h : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ¬IsSeparable h

/-! ## Separable matrices exist -/

/-- For any vectors v and w, vecMulVec v w is separable. -/
theorem vecMulVec_isSeparable {n : ℕ} (v w : Fin n → ℝ) :
    IsSeparable (Matrix.vecMulVec v w) :=
  ⟨v, w, rfl⟩

/-- Separable perturbations exist in the perturbation space. -/
theorem separable_exists : ∃ h : Perturbation (m + 2), IsSeparable h :=
  ⟨Matrix.vecMulVec (fun _ => 1) (fun _ => 1), vecMulVec_isSeparable _ _⟩

/-! ## The identity matrix is entangled -/

/-- **The identity matrix is entangled for n >= 2.**

    Proof by contradiction: if 1 = vecMulVec v w, then
    - Diagonal: v i * w i = 1 for all i, so v i != 0 and w i != 0
    - Off-diagonal: v i * w j = 0 for i != j
    - But v i != 0 implies w j = 0 for j != i, contradicting w j != 0. -/
theorem identity_isEntangled (_hn : 2 ≤ m + 2) :
    IsEntangled (1 : Perturbation (m + 2)) := by
  intro ⟨v, w, hvw⟩
  -- Extract diagonal entries: v i * w i = 1
  have hdiag : ∀ i : Fin (m + 2), v i * w i = 1 := by
    intro i
    have := congr_fun (congr_fun hvw i) i
    simp [Matrix.vecMulVec_apply, Matrix.one_apply_eq] at this
    linarith
  -- Extract off-diagonal: v i * w j = 0 for i != j
  have hoffdiag : ∀ i j : Fin (m + 2), i ≠ j → v i * w j = 0 := by
    intro i j hij
    have := congr_fun (congr_fun hvw i) j
    simp only [Matrix.vecMulVec_apply, Matrix.one_apply_ne hij] at this
    linarith
  -- v 0 != 0 (from diagonal)
  have hv0 : v 0 ≠ 0 := by
    intro hv0
    have := hdiag 0
    rw [hv0, zero_mul] at this
    exact zero_ne_one this
  -- w 1 != 0 (from diagonal, using 1 < m + 2)
  have hw1 : w (1 : Fin (m + 2)) ≠ 0 := by
    intro hw1
    have := hdiag 1
    rw [hw1, mul_zero] at this
    exact zero_ne_one this
  -- Off-diagonal: v 0 * w 1 = 0
  have h01 : v 0 * w (1 : Fin (m + 2)) = 0 := by
    apply hoffdiag
    exact Fin.ne_of_lt (by omega : (0 : ℕ) < 1)
  -- But v 0 != 0 and w 1 != 0, so v 0 * w 1 != 0 -- contradiction
  exact absurd h01 (mul_ne_zero hv0 hw1)

/-- Entangled perturbations exist in the perturbation space. -/
theorem entangled_exists : ∃ h : Perturbation (m + 2), IsEntangled h :=
  ⟨1, identity_isEntangled (by omega)⟩

/-! ## Trace of a separable matrix -/

/-- **Trace of a separable matrix equals the dot product of its factors.**
    Tr(v (x) w) = sum_i v_i * w_i = v . w (inner product). -/
theorem trace_separable {n : ℕ} (v w : Fin n → ℝ) :
    Matrix.trace (Matrix.vecMulVec v w) = v ⬝ᵥ w :=
  Matrix.trace_vecMulVec v w

/-- The trace of a separable matrix is the dot product,
    expressed as a Finset sum. -/
theorem trace_separable_sum {n : ℕ} (v w : Fin n → ℝ) :
    Matrix.trace (Matrix.vecMulVec v w) = ∑ i : Fin n, v i * w i := by
  rw [trace_separable]
  rfl

/-! ## Entangled perturbations cannot be decomposed -/

/-- **An entangled perturbation cannot be written as an independent
    contribution from row indices and column indices.**

    If h is entangled, there is no decomposition h i j = f i * g j
    for any functions f, g. This means the perturbation encodes
    genuine correlations between the row and column subsystems. -/
theorem entangled_no_factorization {n : ℕ} (h : Matrix (Fin n) (Fin n) ℝ)
    (hent : IsEntangled h) :
    ¬∃ f g : Fin n → ℝ, ∀ i j, h i j = f i * g j := by
  intro ⟨f, g, hfg⟩
  apply hent
  exact ⟨f, g, Matrix.ext (fun i j => by rw [hfg, Matrix.vecMulVec_apply])⟩

/-- **The identity matrix (conformal mode) has no independent subsystem
    decomposition.** This is a direct consequence of identity_isEntangled. -/
theorem conformal_mode_entangled (hn : 2 ≤ m + 2) :
    ¬∃ f g : Fin (m + 2) → ℝ, ∀ i j, (1 : Perturbation (m + 2)) i j = f i * g j :=
  entangled_no_factorization 1 (identity_isEntangled hn)

/-! ## Summary theorem -/

/-- **ENTANGLEMENT FROM THE PERTURBATION SPACE.**

    The matrix perturbation space naturally supports entanglement:
    1. Separable (rank-1) perturbations exist
    2. Entangled (non-rank-1) perturbations exist (the identity)
    3. Trace of separable = dot product (inner product of factors)
    4. Entangled perturbations have no independent subsystem decomposition -/
theorem entanglement_structure :
    -- (1) Separable perturbations exist
    (∃ h : Perturbation (m + 2), IsSeparable h)
    -- (2) Entangled perturbations exist
    ∧ (∃ h : Perturbation (m + 2), IsEntangled h)
    -- (3) Trace of separable = dot product
    ∧ (∀ v w : Fin (m + 2) → ℝ,
        Matrix.trace (Matrix.vecMulVec v w) = v ⬝ᵥ w)
    -- (4) Entangled perturbations have no factorization
    ∧ (∀ h : Perturbation (m + 2), IsEntangled h →
        ¬∃ f g : Fin (m + 2) → ℝ, ∀ i j, h i j = f i * g j) :=
  ⟨separable_exists, entangled_exists,
   fun v w => trace_separable v w,
   fun h hent => entangled_no_factorization h hent⟩

end UnifiedTheory.LayerB.Entanglement
