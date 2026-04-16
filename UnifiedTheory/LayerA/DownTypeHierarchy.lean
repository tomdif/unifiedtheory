/-
  LayerA/DownTypeHierarchy.lean — Down-type quark mass hierarchy from J₄ + hypercharge

  The up-type ratio R_up = ln(5-√7)/ln(5+√7) ≈ 0.421 comes from J₄ with
  b₁² = 1/25, b₂² = 1/50.

  For down-type quarks, the off-diagonal couplings are modified by the
  hypercharge ratio:
    |Y(d_R)|²/|Y(u_R)|² = (2/3)²/(4/3)² = 1/4

  So: b₁²(down) = 1/25 · 1/4 = 1/100,  b₂²(down) = 1/50 · 1/4 = 1/200.

  The down-type Jacobi matrix J₄^down has:
    diagonal = {1/3, 2/5, 1/5}  (universal, from Volterra)
    b₁² = 1/100, b₂² = 1/200

  Its characteristic polynomial is 6000λ³ - 5600λ² + 1590λ - 138 = 0,
  which gives different eigenvalues and a different hierarchy shape.

  PREDICTION: R_down ≈ 0.527 vs measured 0.560 (5.9% error, zero free parameters).

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.DownTypeHierarchy

/-! ## The hypercharge modification -/

/-- Hypercharge ratio: |Y(d_R)|²/|Y(u_R)|² = (2/3)²/(4/3)² = 1/4. -/
theorem hypercharge_ratio_down :
    ((2 : ℚ) / 3) ^ 2 / ((4 : ℚ) / 3) ^ 2 = 1 / 4 := by norm_num

/-- Down-type couplings: b₁²(down) = 1/100, b₂²(down) = 1/200. -/
theorem b1_sq_down : (1 : ℚ) / 25 * (1 / 4) = 1 / 100 := by norm_num
theorem b2_sq_down : (1 : ℚ) / 50 * (1 / 4) = 1 / 200 := by norm_num

/-! ## The down-type characteristic polynomial -/

/-- The tridiagonal recurrence for the down-type J₄. -/
noncomputable def p₁_down (x : ℚ) : ℚ := x - 1 / 3
noncomputable def p₂_down (x : ℚ) : ℚ := (x - 2 / 5) * p₁_down x - 1 / 100
noncomputable def charPoly_down (x : ℚ) : ℚ :=
  (x - 1 / 5) * p₂_down x - (1 / 200) * p₁_down x

/-- The down-type characteristic polynomial: 6000x³ - 5600x² + 1590x - 138 = 0. -/
theorem charPoly_down_expanded (x : ℚ) :
    6000 * charPoly_down x = 6000 * x ^ 3 - 5600 * x ^ 2 + 1590 * x - 138 := by
  unfold charPoly_down p₂_down p₁_down; ring

-- The roots are approximately 0.484, 0.279, 0.170 (from Python).
-- The top eigenvalue is NOT 3/5 (unlike the up-type case).

/-- Verification: the up-type polynomial at 3/5 gives 0, but the down-type doesn't. -/
theorem down_type_differs_from_up :
    6000 * charPoly_down (3 / 5) ≠ 0 := by
  unfold charPoly_down p₂_down p₁_down; norm_num

/-! ## The inter-sector ratio (Casimir scaling) -/

/-- The Casimir + hypercharge formula for m_t/m_b:
    m_t/m_b = (1/r) · C₂(SU3)/C₂(SU2) · |Y(t_R)/Y(b_R)|
    where r = m_μ/m_τ (from SU(2) holonomy).

    C₂(SU3) = 4/3, C₂(SU2) = 3/4, ratio = 16/9.
    |Y(t_R)/Y(b_R)| = |(4/3)/(-2/3)| = 2.
    So: m_t/m_b = 32/(9·r). -/
theorem casimir_formula :
    (4 : ℚ) / 3 / (3 / 4) * ((4 : ℚ) / 3 / ((2 : ℚ) / 3)) = 32 / 9 := by
  norm_num

-- At r = m_μ/m_τ ≈ 0.0595: m_t/m_b = 32/(9·0.0595) ≈ 59.7.
-- Measured: m_t/m_b = 41.4.
-- This overpredicts by ~44%, suggesting r_eff ≈ 0.086 (including
-- running corrections not computed here).

/-! ## Summary -/

/-- **DOWN-TYPE HIERARCHY PREDICTION.**

    The framework predicts:
    1. Inter-sector: m_t/m_b = 32/(9·r) from Casimir + hypercharge
    2. Intra-sector shape: R_down ≈ 0.527 from J₄^down with
       b₁² = 1/100, b₂² = 1/200 (5.9% from measured 0.560)
    3. The charged lepton sector (color singlet) requires separate
       treatment — the J₄ mechanism applies only to colored fermions.

    What's proved:
    - hypercharge_ratio_down: |Y(d_R)/Y(u_R)|² = 1/4
    - b1_sq_down, b2_sq_down: modified couplings
    - charPoly_down_expanded: explicit polynomial
    - down_type_differs_from_up: eigenvalues differ from up-type

    What's computed (Python, scripts/down_type_hierarchy.py):
    - R_down = 0.527 ± 0.001 (numerical eigenvalue computation)
    - Measured R_down = 0.560
    - Agreement: 5.9% (zero free parameters) -/
theorem down_type_predictions :
    -- Hypercharge ratio is 1/4
    ((2 : ℚ) / 3) ^ 2 / ((4 : ℚ) / 3) ^ 2 = 1 / 4
    -- Down-type couplings are 4× smaller
    ∧ (1 : ℚ) / 25 * (1 / 4) = 1 / 100
    ∧ (1 : ℚ) / 50 * (1 / 4) = 1 / 200
    -- Down-type polynomial differs from up-type
    ∧ 6000 * charPoly_down (3 / 5) ≠ 0 := by
  exact ⟨hypercharge_ratio_down, b1_sq_down, b2_sq_down, down_type_differs_from_up⟩

end UnifiedTheory.LayerA.DownTypeHierarchy
