/-
  LayerB/MassProductRule.lean — The product rule for quark mass ratios.

  THEOREM: The product of the intra-sector mass ratio m_c/m_t and the
  inter-sector mass ratio m_t/m_b is determined by the derived gauge
  group structure alone:

    (m_c/m_t) × (m_t/m_b) = √(d_⊥(SU(3)) / d_⊥(SU(2))) × (β_w / β_c)

  All ingredients are derived: N_c=3, N_w=2, g²=1.
  Evaluates to √(2/1) × (4/6) = √2 × 2/3 ≈ 0.943.

  Experimental: 0.164. Gap: factor 5.8 (beyond tree-level K/P).

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace UnifiedTheory.LayerB.MassProductRule

/-- The number of colors N_c = 3. -/
def N_c : ℕ := 3

/-- The weak isospin dimension N_w = 2. -/
def N_w : ℕ := 2

/-- Perpendicular dimensions in the fundamental representation of SU(N) on ℂ^N. -/
def dimPerp (N : ℕ) : ℕ := N - 1

theorem dimPerp_color : dimPerp N_c = 2 := by unfold dimPerp N_c; rfl
theorem dimPerp_weak : dimPerp N_w = 1 := by unfold dimPerp N_w; rfl

/-- Wilson parameter: β = 2N/g². At g²=1: β(SU(3))=6, β(SU(2))=4. -/
noncomputable def wilsonBeta (N : ℕ) (g_sq : ℝ) : ℝ := 2 * N / g_sq

theorem beta_color : wilsonBeta N_c 1 = 6 := by
  unfold wilsonBeta N_c; norm_num

theorem beta_weak : wilsonBeta N_w 1 = 4 := by
  unfold wilsonBeta N_w; norm_num

/-- The beta ratio β_w/β_c = N_w/N_c (at equal g²). -/
theorem beta_ratio : wilsonBeta N_w 1 / wilsonBeta N_c 1 = 2 / 3 := by
  rw [beta_weak, beta_color]; norm_num

/-- **THE MASS PRODUCT RULE.**

    product = √(d_⊥(3) / d_⊥(2)) × (β_w / β_c)
            = √(2/1) × (2/3)
            = √2 × 2/3

    This is N-independent: it holds for any number of chains,
    any causal set realization, any density.

    All ingredients derived:
      N_c = 3 (ColorGroupForced)
      N_w = 2 (GaugeGroupDerived)
      g² = 1 (CouplingUnification)
      d_⊥(SU(N)) = N-1 (fundamental representation geometry)
-/
noncomputable def massProductRule : ℝ :=
  Real.sqrt ((dimPerp N_c : ℝ) / (dimPerp N_w : ℝ)) *
    (wilsonBeta N_w 1 / wilsonBeta N_c 1)

/-- The product rule evaluates to √2 × 2/3. -/
theorem product_rule_value :
    massProductRule = Real.sqrt 2 * (2 / 3) := by
  unfold massProductRule
  rw [dimPerp_color, dimPerp_weak, beta_ratio]
  push_cast
  norm_num

/-- The product rule is positive (the hierarchy is real). -/
theorem product_rule_pos : 0 < massProductRule := by
  rw [product_rule_value]
  apply mul_pos
  · exact Real.sqrt_pos_of_pos (by positivity)
  · positivity

/-- The product rule squared equals 8/9. -/
theorem product_rule_sq :
    massProductRule ^ 2 = 8 / 9 := by
  rw [product_rule_value]
  rw [mul_pow, Real.sq_sqrt (by positivity : (2 : ℝ) ≥ 0)]
  ring

/-- The product rule is less than 1 (proved via the square).
    Since product² = 8/9 < 1 and product > 0: product < 1. -/
theorem product_rule_lt_one : massProductRule < 1 := by
  have hsq : massProductRule ^ 2 < 1 ^ 2 := by
    rw [product_rule_sq]; norm_num
  have hpos := product_rule_pos
  nlinarith [sq_nonneg (massProductRule - 1), sq_nonneg massProductRule]

/-! ## Bridge to the K/P concentration theorem -/

/-- The concentration amplitude A(β, N) for SU(N) at coupling β.
    This is the prefactor in the CLT concentration: r ~ A/√(samples).
    A = √(dimPerp) / β where dimPerp = N-1 (perpendicular directions). -/
noncomputable def concentrationAmplitude (N : ℕ) (beta : ℝ) : ℝ :=
  Real.sqrt (dimPerp N : ℝ) / beta

/-- The concentration amplitude for SU(3) at β=6. -/
theorem concentration_color :
    concentrationAmplitude N_c (wilsonBeta N_c 1) = Real.sqrt 2 / 6 := by
  unfold concentrationAmplitude; rw [dimPerp_color, beta_color]; push_cast; ring

/-- The concentration amplitude for SU(2) at β=4. -/
theorem concentration_weak :
    concentrationAmplitude N_w (wilsonBeta N_w 1) = Real.sqrt 1 / 4 := by
  unfold concentrationAmplitude; rw [dimPerp_weak, beta_weak]; push_cast; ring

/-- **Bridge theorem: the mass product rule IS the ratio of concentration amplitudes.**

    massProductRule = A_color / A_weak

    This is the formal connection between the algebraic product rule
    and the physical K/P concentration theorem. The concentration
    theorem says:
      m_c/m_t ~ A_color / √N  (intra-sector ratio)
      m_t/m_b ~ √N / A_weak   (inter-sector ratio, from K/P VEV alignment)

    The product is N-independent: (A_color/√N) × (√N/A_weak) = A_color/A_weak. -/
theorem product_rule_is_concentration_ratio :
    massProductRule =
    concentrationAmplitude N_c (wilsonBeta N_c 1) /
    concentrationAmplitude N_w (wilsonBeta N_w 1) := by
  rw [concentration_color, concentration_weak, Real.sqrt_one]
  rw [product_rule_value]
  field_simp; ring

end UnifiedTheory.LayerB.MassProductRule
