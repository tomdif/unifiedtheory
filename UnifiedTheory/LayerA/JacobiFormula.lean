/-
  LayerA/JacobiFormula.lean — Jacobi's formula for small matrices

  Proves d/dε det(I + ε·h)|_{ε=0} = tr(h) for 2×2 and 4×4 matrices
  via direct polynomial expansion.

  Key results:
  - `det_one_add_smul_fin2`: det(I + t·h) = 1 + t·tr(h) + t²·(...)
  - `jacobi_formula_fin2`:   d/dt det(I + t·h)|_{t=0} = tr(h)
  - `det4_one_add_smul`:     det₄(I + t·h) = 1 + t·tr₄(h) + O(t²)
  - `jacobi_formula_4`:      d/dt det₄(I + t·h)|_{t=0} = tr₄(h)
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.JacobiFormula

open Matrix Finset

/-! ### 1×1 case -/

/-- **Jacobi's formula for 1×1 matrices.**
    det(I + t·h) = 1 + t·h₀₀ = 1 + t·tr(h). -/
theorem det_one_add_smul_fin1 (h : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ) :
    (1 + t • h).det = 1 + t * h.trace := by
  simp [trace, Matrix.diag, smul_apply, smul_eq_mul]

/-! ### 2×2 case -/

/-- **Jacobi's formula for 2×2 matrices (full expansion).**
    det(I + t·h) = 1 + t·tr(h) + t²·(h₀₀h₁₁ - h₀₁h₁₀). -/
theorem det_one_add_smul_fin2 (h : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    (1 + t • h).det =
      1 + t * h.trace + t ^ 2 * (h 0 0 * h 1 1 - h 0 1 * h 1 0) := by
  simp [det_fin_two, trace, Matrix.diag, smul_apply, smul_eq_mul]
  ring

/-- **Jacobi's formula at the identity (2×2).**
    The derivative of det(I + t·h) with respect to t, evaluated at t = 0, is tr(h).
    Stated as: the remainder after subtracting 1 + t·tr(h) is O(t²). -/
theorem jacobi_formula_fin2 (h : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ t : ℝ, (1 + t • h).det - 1 - t * h.trace =
      t ^ 2 * (h 0 0 * h 1 1 - h 0 1 * h 1 0) := by
  intro t
  rw [det_one_add_smul_fin2]
  ring

/-- det(I + 0·h) = 1 for 2×2. -/
theorem jacobi_formula_fin2_at_zero (h : Matrix (Fin 2) (Fin 2) ℝ) :
    (1 + (0 : ℝ) • h).det = 1 := by
  rw [det_one_add_smul_fin2]; ring

/-! ### 4×4 case — explicit determinant and trace

Mathlib does not provide `det_fin_four`, so we define the 4×4 determinant
and trace as explicit functions on `Fin 4 → Fin 4 → ℝ` and prove the
Jacobi expansion by `ring`. All definitions are fully inlined (no helper
defs) so that `unfold` + `ring` closes the goals. -/

/-- Explicit trace for a 4×4 real-valued function. -/
def trace4 (h : Fin 4 → Fin 4 → ℝ) : ℝ :=
  h 0 0 + h 1 1 + h 2 2 + h 3 3

/-- Explicit 4×4 determinant via cofactor expansion along row 0.
    All 3×3 cofactors are expanded inline. -/
def det4 (m : Fin 4 → Fin 4 → ℝ) : ℝ :=
  m 0 0 * (m 1 1 * (m 2 2 * m 3 3 - m 2 3 * m 3 2)
           - m 1 2 * (m 2 1 * m 3 3 - m 2 3 * m 3 1)
           + m 1 3 * (m 2 1 * m 3 2 - m 2 2 * m 3 1))
  - m 0 1 * (m 1 0 * (m 2 2 * m 3 3 - m 2 3 * m 3 2)
             - m 1 2 * (m 2 0 * m 3 3 - m 2 3 * m 3 0)
             + m 1 3 * (m 2 0 * m 3 2 - m 2 2 * m 3 0))
  + m 0 2 * (m 1 0 * (m 2 1 * m 3 3 - m 2 3 * m 3 1)
             - m 1 1 * (m 2 0 * m 3 3 - m 2 3 * m 3 0)
             + m 1 3 * (m 2 0 * m 3 1 - m 2 1 * m 3 0))
  - m 0 3 * (m 1 0 * (m 2 1 * m 3 2 - m 2 2 * m 3 1)
             - m 1 1 * (m 2 0 * m 3 2 - m 2 2 * m 3 0)
             + m 1 2 * (m 2 0 * m 3 1 - m 2 1 * m 3 0))

/-- det(I + t·h) for 4×4, with (I + th) entries substituted directly. -/
def det4_IplusT (h : Fin 4 → Fin 4 → ℝ) (t : ℝ) : ℝ :=
  (1 + t * h 0 0) *
    ((1 + t * h 1 1) * ((1 + t * h 2 2) * (1 + t * h 3 3) - t * h 2 3 * (t * h 3 2))
     - t * h 1 2 * (t * h 2 1 * (1 + t * h 3 3) - t * h 2 3 * (t * h 3 1))
     + t * h 1 3 * (t * h 2 1 * (t * h 3 2) - (1 + t * h 2 2) * (t * h 3 1)))
  - t * h 0 1 *
    (t * h 1 0 * ((1 + t * h 2 2) * (1 + t * h 3 3) - t * h 2 3 * (t * h 3 2))
     - t * h 1 2 * (t * h 2 0 * (1 + t * h 3 3) - t * h 2 3 * (t * h 3 0))
     + t * h 1 3 * (t * h 2 0 * (t * h 3 2) - (1 + t * h 2 2) * (t * h 3 0)))
  + t * h 0 2 *
    (t * h 1 0 * (t * h 2 1 * (1 + t * h 3 3) - t * h 2 3 * (t * h 3 1))
     - (1 + t * h 1 1) * (t * h 2 0 * (1 + t * h 3 3) - t * h 2 3 * (t * h 3 0))
     + t * h 1 3 * (t * h 2 0 * (t * h 3 1) - t * h 2 1 * (t * h 3 0)))
  - t * h 0 3 *
    (t * h 1 0 * (t * h 2 1 * (t * h 3 2) - (1 + t * h 2 2) * (t * h 3 1))
     - (1 + t * h 1 1) * (t * h 2 0 * (t * h 3 2) - (1 + t * h 2 2) * (t * h 3 0))
     + t * h 1 2 * (t * h 2 0 * (t * h 3 1) - t * h 2 1 * (t * h 3 0)))

/-- Sum of all 2×2 principal minors of h (coefficient of t²). -/
def c2 (h : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (h 0 0 * h 1 1 - h 0 1 * h 1 0)
  + (h 0 0 * h 2 2 - h 0 2 * h 2 0)
  + (h 0 0 * h 3 3 - h 0 3 * h 3 0)
  + (h 1 1 * h 2 2 - h 1 2 * h 2 1)
  + (h 1 1 * h 3 3 - h 1 3 * h 3 1)
  + (h 2 2 * h 3 3 - h 2 3 * h 3 2)

/-- Sum of all 3×3 principal minors of h (coefficient of t³), fully expanded. -/
def c3 (h : Fin 4 → Fin 4 → ℝ) : ℝ :=
  h 0 0 * (h 1 1 * h 2 2 - h 1 2 * h 2 1)
  - h 0 1 * (h 1 0 * h 2 2 - h 1 2 * h 2 0)
  + h 0 2 * (h 1 0 * h 2 1 - h 1 1 * h 2 0)
  + h 0 0 * (h 1 1 * h 3 3 - h 1 3 * h 3 1)
  - h 0 1 * (h 1 0 * h 3 3 - h 1 3 * h 3 0)
  + h 0 3 * (h 1 0 * h 3 1 - h 1 1 * h 3 0)
  + h 0 0 * (h 2 2 * h 3 3 - h 2 3 * h 3 2)
  - h 0 2 * (h 2 0 * h 3 3 - h 2 3 * h 3 0)
  + h 0 3 * (h 2 0 * h 3 2 - h 2 2 * h 3 0)
  + h 1 1 * (h 2 2 * h 3 3 - h 2 3 * h 3 2)
  - h 1 2 * (h 2 1 * h 3 3 - h 2 3 * h 3 1)
  + h 1 3 * (h 2 1 * h 3 2 - h 2 2 * h 3 1)

-- 4x4 polynomial identity requires extended heartbeats for ring
set_option maxHeartbeats 800000 in
set_option linter.style.maxHeartbeats false in
/-- **Jacobi's formula for 4×4 (full expansion).**
    det₄(I + t·h) = 1 + t·tr₄(h) + t²·C₂ + t³·C₃ + t⁴·det₄(h). -/
theorem det4_one_add_smul (h : Fin 4 → Fin 4 → ℝ) (t : ℝ) :
    det4_IplusT h t =
      1 + t * trace4 h + t ^ 2 * c2 h + t ^ 3 * c3 h + t ^ 4 * det4 h := by
  unfold det4_IplusT trace4 c2 c3 det4
  ring

/-- **Jacobi's formula at the identity (4×4).**
    The remainder after 1 + t·tr₄(h) is O(t²). -/
theorem jacobi_formula_4 (h : Fin 4 → Fin 4 → ℝ) :
    ∀ t : ℝ, det4_IplusT h t - 1 - t * trace4 h =
      t ^ 2 * c2 h + t ^ 3 * c3 h + t ^ 4 * det4 h := by
  intro t
  rw [det4_one_add_smul]
  ring

/-- det₄(I + 0·h) = 1. -/
theorem jacobi_formula_4_at_zero (h : Fin 4 → Fin 4 → ℝ) :
    det4_IplusT h 0 = 1 := by
  rw [det4_one_add_smul]; ring

end UnifiedTheory.LayerA.JacobiFormula
