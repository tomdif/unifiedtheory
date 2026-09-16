/-
  Audit/FineStructureIRPrecisionExclusion.lean — the closed form
  α(0) = ln(5/3)/70 is EXCLUDED as an exact identity by CODATA.

  `LayerA.FineStructureIRFromGap.prediction_brackets_PDG` shows that an
  interval containing 70/ln(5/3) also contains CODATA 137.035999. That
  interval (137.028, 137.041) comes from a 12-term Taylor bracket on
  ln(5/3) and is ~6×10⁵ times wider than the CODATA uncertainty, so
  "brackets PDG" is an artifact of bracket width, not agreement.

  With a 14-term bracket, ln(5/3) > 0.510823, hence
      70/ln(5/3) < 137.034 < 137.035999177 − 0.0019.
  CODATA 2022: α⁻¹ = 137.035999177(21), σ = 2.1×10⁻⁸. The miss is
  > 0.0019 ≈ 9×10⁴ σ (true miss 0.00294 ≈ 1.4×10⁵ σ).

  Consequence: γ₄/70 can at best be a LEADING term. Any claim of
  agreement must name the correction (and its origin) that closes a
  2.1×10⁻⁵ relative gap; see ALPHA_GATE.md (2026-09-16 audit) for the chance-coincidence probability of the
  leading term itself.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerA.FineStructureIRFromGap

set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.FineStructureIRPrecisionExclusion

open Real UnifiedTheory.LayerA.FineStructureIRFromGap

/-- **ln(5/3) > 0.510823** — 14-term Taylor bracket at x = 2/5
    (remainder (2/5)^15/(3/5) ≈ 1.8×10⁻⁶). -/
theorem log_5_3_lower_tight : (0.510823 : ℝ) < Real.log (5 / 3) := by
  have hx : |(2 / 5 : ℝ)| = 2 / 5 := by rw [abs_of_pos] <;> norm_num
  have key := Real.abs_log_sub_add_sum_range_le
    (x := (2 / 5 : ℝ)) (by rw [hx]; norm_num) 14
  rw [hx] at key
  have hlog : Real.log (1 - 2 / 5) = - Real.log (5 / 3) := by
    rw [show (1 - 2 / 5 : ℝ) = (5 / 3)⁻¹ by norm_num, Real.log_inv]
  rw [hlog] at key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at key
  rw [abs_le] at key
  obtain ⟨klo, khi⟩ := key
  nlinarith [klo, khi]

/-- **The prediction lies strictly below 137.034.** -/
theorem inv_alphaIR_lt : inv_alphaIR < 137.034 := by
  have hpos : 0 < Real.log (5 / 3) := gamma_4_pos
  unfold inv_alphaIR
  rw [div_lt_iff₀ hpos]
  nlinarith [log_5_3_lower_tight]

/-- CODATA 2022 central value and standard uncertainty of α⁻¹. -/
def codata_inv_alpha : ℝ := 137.035999177
def codata_inv_alpha_sigma : ℝ := 0.000000021

/-- **Exclusion.** The predicted α(0)⁻¹ misses CODATA by more than
    0.0019, i.e. by more than 90 000 standard uncertainties. -/
theorem codata_excludes_exact_closed_form :
    0.0019 < codata_inv_alpha - inv_alphaIR
    ∧ 90000 * codata_inv_alpha_sigma < codata_inv_alpha - inv_alphaIR := by
  have h := inv_alphaIR_lt
  unfold codata_inv_alpha codata_inv_alpha_sigma
  constructor <;> linarith

end UnifiedTheory.Audit.FineStructureIRPrecisionExclusion
