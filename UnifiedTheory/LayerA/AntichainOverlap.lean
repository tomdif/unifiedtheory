/-
  LayerA/AntichainOverlap.lean — BD-weighted antichain overlap eigenvalue ratio

  PHYSICS: In the causal set approach, antichains (maximal sets of
  mutually spacelike elements) represent spatial slices. The
  Bombelli-Davey (BD) weighted overlap matrix on [m]^2 measures how
  spatial slices share structure. Its eigenvalue ratio

      R(m) = λ₁(m) / λ₂(m) = (2m - 3) / (m - 1)

  converges to 2 as m → ∞. The limit 2 = (d+1)/(d-1) at d = 3
  identifies d_spatial = 3, i.e., 3+1 spacetime dimensions.

  WHAT WE FORMALIZE:
  1. The algebraic identity R(m) - 2 = -1/(m-1) (exact finite-m correction)
  2. Specific rational values at m = 4, 5, 6, 7
  3. The eigenvalue formulas λ₁(m), λ₂(m) and their ratio
  4. The limit identification (d+1)/(d-1) = 2 at d = 3

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AntichainOverlap

/-! ═══════════════════════════════════════════════════════════════
    SECTION 1: THE EIGENVALUE RATIO FORMULA
    ═══════════════════════════════════════════════════════════════ -/

/-- The eigenvalue ratio R(m) = (2m - 3) / (m - 1) as a function on ℚ. -/
noncomputable def eigenvalueRatio (m : ℚ) : ℚ := (2 * m - 3) / (m - 1)

/-- The leading eigenvalue λ₁(m) = (2m - 3) / (m - 1)². -/
noncomputable def lambda1 (m : ℚ) : ℚ := (2 * m - 3) / (m - 1) ^ 2

/-- The sub-leading eigenvalue λ₂(m) = 1 / (m - 1). -/
noncomputable def lambda2 (m : ℚ) : ℚ := 1 / (m - 1)

/-- The ratio λ₁/λ₂ equals (2m-3)/(m-1) for m ≠ 1. -/
theorem ratio_eq_eigenvalueRatio (m : ℚ) (hm : m ≠ 1) :
    lambda1 m / lambda2 m = eigenvalueRatio m := by
  unfold lambda1 lambda2 eigenvalueRatio
  have h1 : m - 1 ≠ 0 := sub_ne_zero.mpr hm
  field_simp

/-! ═══════════════════════════════════════════════════════════════
    SECTION 2: EXACT FINITE-m CORRECTION
    ═══════════════════════════════════════════════════════════════ -/

/-- KEY IDENTITY: R(m) - 2 = -1/(m-1) for all m ≠ 1.
    This is the exact finite-m correction to the asymptotic limit 2. -/
theorem eigenvalueRatio_minus_two (m : ℚ) (hm : m ≠ 1) :
    eigenvalueRatio m - 2 = -1 / (m - 1) := by
  unfold eigenvalueRatio
  have h1 : m - 1 ≠ 0 := sub_ne_zero.mpr hm
  field_simp
  ring

/-- Equivalent form: (2m-3)/(m-1) = 2 - 1/(m-1). -/
theorem eigenvalueRatio_decomposition (m : ℚ) (hm : m ≠ 1) :
    eigenvalueRatio m = 2 - 1 / (m - 1) := by
  unfold eigenvalueRatio
  have h1 : m - 1 ≠ 0 := sub_ne_zero.mpr hm
  field_simp
  ring

/-- The correction 1/(m-1) is positive for m > 1, so R(m) < 2. -/
theorem eigenvalueRatio_lt_two (m : ℚ) (hm : 1 < m) :
    eigenvalueRatio m < 2 := by
  have hm1 : m ≠ 1 := by linarith
  rw [eigenvalueRatio_decomposition m hm1]
  have hpos : 0 < m - 1 := by linarith
  have hne : (m - 1 : ℚ) ≠ 0 := ne_of_gt hpos
  have hfrac : 0 < 1 / (m - 1) := div_pos one_pos hpos
  linarith

/-- For m ≥ 2, the ratio is at least 1 (it equals 1 at m = 2). -/
theorem eigenvalueRatio_ge_one (m : ℚ) (hm : 2 ≤ m) :
    1 ≤ eigenvalueRatio m := by
  have hm1 : m ≠ 1 := by linarith
  rw [eigenvalueRatio_decomposition m hm1]
  have hpos : 0 < m - 1 := by linarith
  have hle : 1 / (m - 1) ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  linarith

/-! ═══════════════════════════════════════════════════════════════
    SECTION 3: SPECIFIC VALUES BY norm_num
    ═══════════════════════════════════════════════════════════════ -/

/-- m = 4: R(4) = 5/3. -/
theorem ratio_m4 : eigenvalueRatio 4 = 5 / 3 := by
  unfold eigenvalueRatio; norm_num

/-- m = 5: R(5) = 7/4. -/
theorem ratio_m5 : eigenvalueRatio 5 = 7 / 4 := by
  unfold eigenvalueRatio; norm_num

/-- m = 6: R(6) = 9/5. -/
theorem ratio_m6 : eigenvalueRatio 6 = 9 / 5 := by
  unfold eigenvalueRatio; norm_num

/-- m = 7: R(7) = 11/6. -/
theorem ratio_m7 : eigenvalueRatio 7 = 11 / 6 := by
  unfold eigenvalueRatio; norm_num

/-- m = 2: R(2) = 1. -/
theorem ratio_m2 : eigenvalueRatio 2 = 1 := by
  unfold eigenvalueRatio; norm_num

/-- m = 3: R(3) = 3/2. -/
theorem ratio_m3 : eigenvalueRatio 3 = 3 / 2 := by
  unfold eigenvalueRatio; norm_num

/-- m = 10: R(10) = 17/9. -/
theorem ratio_m10 : eigenvalueRatio 10 = 17 / 9 := by
  unfold eigenvalueRatio; norm_num

/-- m = 100: R(100) = 197/99. -/
theorem ratio_m100 : eigenvalueRatio 100 = 197 / 99 := by
  unfold eigenvalueRatio; norm_num

/-! ═══════════════════════════════════════════════════════════════
    SECTION 4: EIGENVALUE SPECIFIC VALUES
    ═══════════════════════════════════════════════════════════════ -/

/-- λ₁(4) = 5/9. -/
theorem lambda1_m4 : lambda1 4 = 5 / 9 := by
  unfold lambda1; norm_num

/-- λ₂(4) = 1/3. -/
theorem lambda2_m4 : lambda2 4 = 1 / 3 := by
  unfold lambda2; norm_num

/-- λ₁(5) = 7/16. -/
theorem lambda1_m5 : lambda1 5 = 7 / 16 := by
  unfold lambda1; norm_num

/-- λ₂(5) = 1/4. -/
theorem lambda2_m5 : lambda2 5 = 1 / 4 := by
  unfold lambda2; norm_num

/-! ═══════════════════════════════════════════════════════════════
    SECTION 5: THE SPATIAL DIMENSION IDENTIFICATION
    ═══════════════════════════════════════════════════════════════ -/

/-- The spatial dimension formula: (d+1)/(d-1). -/
noncomputable def dimRatio (d : ℚ) : ℚ := (d + 1) / (d - 1)

/-- At d = 3 (spatial): (3+1)/(3-1) = 2.
    The antichain overlap ratio converges to this value. -/
theorem dimRatio_d3 : dimRatio 3 = 2 := by
  unfold dimRatio; norm_num

/-- At d = 2: (2+1)/(2-1) = 3. -/
theorem dimRatio_d2 : dimRatio 2 = 3 := by
  unfold dimRatio; norm_num

/-- At d = 4: (4+1)/(4-1) = 5/3. This matches R(4)! -/
theorem dimRatio_d4 : dimRatio 4 = 5 / 3 := by
  unfold dimRatio; norm_num

/-- Remarkable coincidence: R(4) = dimRatio(4) = 5/3.
    The m = 4 antichain overlap ratio equals the d = 4 spatial ratio. -/
theorem ratio_m4_eq_dimRatio_d4 : eigenvalueRatio 4 = dimRatio 4 := by
  unfold eigenvalueRatio dimRatio; norm_num

/-- The dimRatio decomposition: (d+1)/(d-1) = 1 + 2/(d-1). -/
theorem dimRatio_decomposition (d : ℚ) (hd : d ≠ 1) :
    dimRatio d = 1 + 2 / (d - 1) := by
  unfold dimRatio
  have h1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  field_simp
  ring

/-! ═══════════════════════════════════════════════════════════════
    SECTION 6: MONOTONICITY AND CONVERGENCE RATE
    ═══════════════════════════════════════════════════════════════ -/

/-- The ratio is strictly increasing for m > 1:
    If 1 < m₁ < m₂ then R(m₁) < R(m₂). -/
theorem eigenvalueRatio_strictMono (m₁ m₂ : ℚ) (h1 : 1 < m₁) (h12 : m₁ < m₂) :
    eigenvalueRatio m₁ < eigenvalueRatio m₂ := by
  have hm1 : m₁ ≠ 1 := by linarith
  have hm2 : m₂ ≠ 1 := by linarith
  rw [eigenvalueRatio_decomposition m₁ hm1, eigenvalueRatio_decomposition m₂ hm2]
  have hp1 : 0 < m₁ - 1 := by linarith
  have hp2 : 0 < m₂ - 1 := by linarith
  have hlt : m₁ - 1 < m₂ - 1 := by linarith
  have key : 1 / (m₂ - 1) < 1 / (m₁ - 1) :=
    one_div_lt_one_div_of_lt hp1 hlt
  linarith

/-- The distance to 2 is exactly 1/(m-1), giving 1/m convergence rate. -/
theorem convergence_rate (m : ℚ) (hm : 1 < m) :
    2 - eigenvalueRatio m = 1 / (m - 1) := by
  have hm1 : m ≠ 1 := by linarith
  rw [eigenvalueRatio_decomposition m hm1]
  ring

/-- For m ≥ n+1, the error 2 - R(m) ≤ 1/n. -/
theorem convergence_bound (m n : ℚ) (hn : 0 < n) (hm : n + 1 ≤ m) :
    2 - eigenvalueRatio m ≤ 1 / n := by
  have hm1 : 1 < m := by linarith
  rw [convergence_rate m hm1]
  have hp : 0 < m - 1 := by linarith
  have hn_le : n ≤ m - 1 := by linarith
  exact div_le_div_of_nonneg_left (le_of_lt one_pos) hn hn_le

/-! ═══════════════════════════════════════════════════════════════
    SECTION 7: COMBINED EIGENVALUE IDENTITIES
    ═══════════════════════════════════════════════════════════════ -/

/-- The sum λ₁ + λ₂ = (3m - 4)/(m-1)² for m ≠ 1. -/
theorem eigenvalue_sum (m : ℚ) (hm : m ≠ 1) :
    lambda1 m + lambda2 m = (3 * m - 4) / (m - 1) ^ 2 := by
  unfold lambda1 lambda2
  have h1 : m - 1 ≠ 0 := sub_ne_zero.mpr hm
  field_simp
  ring

/-- The product λ₁ · λ₂ = (2m - 3)/(m-1)³ for m ≠ 1. -/
theorem eigenvalue_product (m : ℚ) (hm : m ≠ 1) :
    lambda1 m * lambda2 m = (2 * m - 3) / (m - 1) ^ 3 := by
  unfold lambda1 lambda2
  have h1 : m - 1 ≠ 0 := sub_ne_zero.mpr hm
  field_simp

end UnifiedTheory.LayerA.AntichainOverlap
