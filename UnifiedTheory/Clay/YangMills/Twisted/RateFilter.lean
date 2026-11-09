/- A one-step spectral deficit smaller than the lattice spacing yields no physical
gap. If the trajectory has spacing at least exp(-κβ) and the deficit is at most
exp(-κ'β) with κ' > κ, the resulting physical lower bound tends to zero. The
scaling of the spacing is a hypothesis here; asymptotic freedom is not proved. -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.RateFilter
open Filter Topology

/-- The physical energy bound from a one-step ratio `1 - δ` at spacing `a`. -/
noncomputable def energyBound (δ a : ℝ) : ℝ := -Real.log (1 - δ) / a

theorem energyBound_nonneg (δ a : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) (ha : 0 < a) :
    0 ≤ energyBound δ a := by
  apply div_nonneg _ ha.le
  have := Real.log_nonpos (by linarith) (by linarith : 1 - δ ≤ 1)
  linarith

theorem energyBound_le (δ a : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) (ha : 0 < a) :
    energyBound δ a ≤ 2 * δ / a := by
  apply div_le_div_of_nonneg_right _ ha.le
  have hpos : 0 < 1 - δ := by linarith
  have hlog : Real.log (1 - δ)⁻¹ ≤ (1 - δ)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hinv : (1 - δ)⁻¹ ≤ 1 + 2 * δ := by
    rw [inv_le_comm₀ hpos (by linarith)]
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  linarith

/-- The filter: a deficit beaten by the spacing gives a vanishing physical bound. -/
theorem energyBound_tendsto_zero (δ a : ℝ → ℝ) (κ κ' : ℝ) (hκ : κ < κ')
    (hδ0 : ∀ᶠ β in atTop, 0 ≤ δ β) (hδ : ∀ᶠ β in atTop, δ β ≤ Real.exp (-κ' * β))
    (ha : ∀ᶠ β in atTop, Real.exp (-κ * β) ≤ a β) (hκ' : 0 < κ') :
    Tendsto (fun β => energyBound (δ β) (a β)) atTop (𝓝 0) := by
  have hdecay : Tendsto (fun β : ℝ => 2 * Real.exp (-(κ' - κ) * β)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun β : ℝ => (κ' - κ) * β) atTop atTop :=
      tendsto_id.const_mul_atTop (sub_pos.mpr hκ)
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 : Tendsto (fun β : ℝ => 2 * Real.exp (-((κ' - κ) * β))) atTop (𝓝 0) := by
      simpa [Function.comp_def] using h2.const_mul 2
    refine h3.congr (fun β => ?_)
    rw [neg_mul]
  have hsmall : ∀ᶠ β in atTop, Real.exp (-κ' * β) ≤ 1 / 2 := by
    have h1 : Tendsto (fun β : ℝ => κ' * β) atTop atTop := tendsto_id.const_mul_atTop hκ'
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1)
    have h3 := h2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h3] with β hβ
    simpa [Function.comp_def, neg_mul] using hβ
  refine squeeze_zero' ?_ ?_ hdecay
  · filter_upwards [hδ0, hδ, ha, hsmall] with β h0 h1 h2 h3
    exact energyBound_nonneg _ _ h0 (by linarith) (lt_of_lt_of_le (Real.exp_pos _) h2)
  · filter_upwards [hδ0, hδ, ha, hsmall] with β h0 h1 h2 h3
    have hapos : 0 < a β := lt_of_lt_of_le (Real.exp_pos _) h2
    refine (energyBound_le _ _ h0 (by linarith) hapos).trans ?_
    have hstep : 2 * δ β / a β ≤ 2 * Real.exp (-κ' * β) / Real.exp (-κ * β) := by
      apply div_le_div₀ (by positivity) (by linarith) (Real.exp_pos _) h2
    refine hstep.trans (le_of_eq ?_)
    rw [mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring

/-- Instance: the existing volume deficit `exp(-24βV)` with `V ≥ 1` cannot produce a
physical gap on any trajectory whose spacing is at least `exp(-κβ)` with `κ < 24`. -/
theorem volume_deficit_filtered (V κ : ℝ) (hV : 1 ≤ V) (hκ : κ < 24) (a : ℝ → ℝ)
    (ha : ∀ᶠ β in atTop, Real.exp (-κ * β) ≤ a β) :
    Tendsto (fun β => energyBound (Real.exp (-24 * β * V)) (a β)) atTop (𝓝 0) := by
  apply energyBound_tendsto_zero _ a κ 24 hκ (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ ha (by norm_num)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  apply Real.exp_le_exp.mpr
  nlinarith

end UnifiedTheory.Clay.YangMills.Twisted.RateFilter
