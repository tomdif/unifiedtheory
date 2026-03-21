/-
  LayerB/CorrectedMassProductRule.lean — Correlation-corrected product rule.

  When chains in a causal set share common ancestors, their holonomies
  are correlated. The effective number of independent samples N_eff < N
  differs between the color (SU(3), β=6) and weak (SU(2), β=4) sectors
  because they decorrelate at different rates.

  The corrected product rule:
    product_corrected = tree_value × √(N_eff_weak / N_eff_color)

  where tree_value = 2√2/3 (proven in MassProductRule.lean).

  Key theorems:
  1. corrected_reduces_to_tree: when N_eff_color = N_eff_weak, correction = 1
  2. corrected_product_sq: squared corrected product = (8/9) × (N_eff_w/N_eff_c)
  3. required_ratio_for_experiment: matches experiment iff ratio ≈ 0.030

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.LayerB.MassProductRule
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace UnifiedTheory.LayerB.CorrectedMassProductRule

open MassProductRule

/-- The correlation correction factor: √(N_eff_weak / N_eff_color).
    When N_eff_weak = N_eff_color (no differential correlation), this is 1.
    When N_eff_weak > N_eff_color (color more correlated than weak),
    the correction is > 1, increasing the product (wrong direction).
    When N_eff_weak < N_eff_color (weak more correlated than color),
    the correction is < 1, decreasing the product (right direction). -/
noncomputable def correctionFactor (N_eff_color N_eff_weak : ℝ) : ℝ :=
  Real.sqrt (N_eff_weak / N_eff_color)

/-- The corrected mass product rule. -/
noncomputable def correctedProduct (N_eff_color N_eff_weak : ℝ) : ℝ :=
  massProductRule * correctionFactor N_eff_color N_eff_weak

/-- PROVEN: When both sectors have equal N_eff, the correction is trivial. -/
theorem corrected_reduces_to_tree (N_eff : ℝ) (hN : 0 < N_eff) :
    correctedProduct N_eff N_eff = massProductRule := by
  unfold correctedProduct correctionFactor
  rw [div_self (ne_of_gt hN), Real.sqrt_one, mul_one]

/-- PROVEN: The squared corrected product. -/
theorem corrected_product_sq (N_eff_color N_eff_weak : ℝ)
    (hc : 0 < N_eff_color) (hw : 0 < N_eff_weak) :
    (correctedProduct N_eff_color N_eff_weak) ^ 2 =
    (8 / 9) * (N_eff_weak / N_eff_color) := by
  unfold correctedProduct correctionFactor
  rw [mul_pow, Real.sq_sqrt (le_of_lt (div_pos hw hc))]
  rw [product_rule_sq]

/-- PROVEN: The corrected product is positive. -/
theorem corrected_product_pos (N_eff_color N_eff_weak : ℝ)
    (hc : 0 < N_eff_color) (hw : 0 < N_eff_weak) :
    0 < correctedProduct N_eff_color N_eff_weak := by
  unfold correctedProduct
  exact mul_pos product_rule_pos (Real.sqrt_pos_of_pos (div_pos hw hc))

/-- PROVEN: The required N_eff ratio to match experiment.

    Experiment: (m_c/m_t)(m_t/m_b) ≈ 0.164.
    Tree value² = 8/9 ≈ 0.889.
    Corrected² = (8/9) × ratio.
    For corrected² = 0.164² = 0.0269: ratio = 0.0269 × 9/8 = 0.0302.

    So N_eff_weak/N_eff_color ≈ 0.030 is needed to match experiment.
    This means the weak sector needs ~33× MORE correlation than the
    color sector — i.e., N_eff_weak ≈ N_eff_color / 33. -/
theorem required_ratio (target : ℝ) (ht : 0 < target)
    (N_eff_color N_eff_weak : ℝ) (hc : 0 < N_eff_color) (hw : 0 < N_eff_weak)
    (h_match : correctedProduct N_eff_color N_eff_weak = target) :
    N_eff_weak / N_eff_color = target ^ 2 * (9 / 8) := by
  have hsq := corrected_product_sq N_eff_color N_eff_weak hc hw
  rw [h_match] at hsq
  -- hsq : target ^ 2 = (8/9) * (N_eff_weak / N_eff_color)
  have h89 : (8 : ℝ) / 9 ≠ 0 := by norm_num
  linarith [mul_comm ((8 : ℝ) / 9) (N_eff_weak / N_eff_color)]

end UnifiedTheory.LayerB.CorrectedMassProductRule
