/- An integrable upper bound on a derivative suffices for a full-line
integral inequality. Endpoint sequences are constructed from integrability
of the primitive; no endpoint limit or absolute derivative bound is assumed. -/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalOneSidedIntegral
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem exists_small_on_interval (B : ℝ → ℝ) (hB : Integrable B volume)
    (a r : ℝ) (hr : 0 < r) :
    ∃ x ∈ Icc a (a+r), ‖B x‖ ≤ (∫ s, ‖B s‖)/r := by
  have hm : volume (Icc a (a+r)) ≠ 0 := by
    rw [Real.volume_Icc]
    simpa using (ENNReal.ofReal_ne_zero_iff.mpr hr)
  obtain ⟨x, hx, hav⟩ := exists_le_setAverage hm isCompact_Icc.measure_ne_top
    (hB.norm.integrableOn (s := Icc a (a+r)))
  refine ⟨x, hx, hav.trans ?_⟩
  rw [setAverage_eq, Real.volume_real_Icc_of_le (by linarith : a ≤ a+r)]
  simp only [add_sub_cancel_left, smul_eq_mul]
  calc
    r⁻¹ * (∫ s in Icc a (a+r), ‖B s‖) ≤ r⁻¹ * (∫ s, ‖B s‖) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hB.norm (ae_of_all _ (fun s => norm_nonneg (B s))))
        (inv_nonneg.mpr hr.le)
    _ = _ := by ring

theorem exists_vanishing_endpoints (B : ℝ → ℝ) (hB : Integrable B volume) :
    ∃ a b : ℕ → ℝ, (∀ n, a n ≤ b n) ∧
      Tendsto a atTop atBot ∧ Tendsto b atTop atTop ∧
      Tendsto (fun n => B (a n)) atTop (𝓝 0) ∧
      Tendsto (fun n => B (b n)) atTop (𝓝 0) := by
  have hr (n : ℕ) : 0 < (n:ℝ)+1 := by positivity
  have ha (n : ℕ) := exists_small_on_interval B hB (-2*((n:ℝ)+1)) ((n:ℝ)+1) (hr n)
  have hb (n : ℕ) := exists_small_on_interval B hB ((n:ℝ)+1) ((n:ℝ)+1) (hr n)
  choose a haI haB using ha
  choose b hbI hbB using hb
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hnneg : Tendsto (fun n : ℕ => -((n:ℝ)+1)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hn
  have hsmall : Tendsto (fun n : ℕ => (∫ s, ‖B s‖)/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hai := (haI n).2
    have hbi := (hbI n).1
    have := hr n
    linarith
  · exact tendsto_atBot_mono (fun n => by have := (haI n).2; linarith) hnneg
  · exact tendsto_atTop_mono (fun n => (hbI n).1) hn
  · exact squeeze_zero_norm haB hsmall
  · exact squeeze_zero_norm hbB hsmall

theorem integral_nonneg_of_derivative_upper (B D G : ℝ → ℝ)
    (hD : ∀ s, HasDerivAt B (D s) s)
    (hB : Integrable B volume) (hG : Integrable G volume)
    (hupper : ∀ s, D s ≤ G s) :
    0 ≤ ∫ s, G s := by
  obtain ⟨a, b, hab, ha, hb, hBa, hBb⟩ := exists_vanishing_endpoints B hB
  have hcont : Continuous B := continuous_iff_continuousAt.mpr
    (fun s => (hD s).continuousAt)
  have hfinite (n : ℕ) : B (b n)-B (a n) ≤ ∫ s in a n..b n, G s :=
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (hab n) hcont.continuousOn
      (fun s _ => (hD s).hasDerivWithinAt) hG.integrableOn
      (fun s _ => hupper s)
  have hzero : Tendsto (fun n => B (b n)-B (a n)) atTop (𝓝 0) := by
    simpa using hBb.sub hBa
  exact le_of_tendsto_of_tendsto hzero (intervalIntegral_tendsto_integral hG ha hb)
    (Eventually.of_forall hfinite)

theorem derivative_integrable_of_upper (B D G : ℝ → ℝ)
    (hD : ∀ s, HasDerivAt B (D s) s) (hDc : Continuous D)
    (hB : Integrable B volume) (hG : Integrable G volume)
    (hupper : ∀ s, D s ≤ G s) :
    Integrable D volume := by
  obtain ⟨a, b, hab, ha, hb, hBa, hBb⟩ := exists_vanishing_endpoints B hB
  have hDi (n : ℕ) : IntervalIntegrable D volume (a n) (b n) :=
    hDc.intervalIntegrable _ _
  have hzero : Tendsto (fun n => B (b n)-B (a n)) atTop (𝓝 0) := by
    simpa using hBb.sub hBa
  apply integrable_of_intervalIntegral_norm_bounded (2*(∫ s, ‖G s‖)+1)
    (fun n => (intervalIntegrable_iff_integrableOn_Ioc_of_le (hab n)).mp (hDi n)) ha hb
  filter_upwards [hzero.eventually (Ioi_mem_nhds (show (-1:ℝ) < 0 by norm_num))] with n hn
  have hpoint (s : ℝ) : ‖D s‖ ≤ 2*‖G s‖-D s := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hu := (hupper s).trans (le_abs_self (G s))
    rcases le_total 0 (D s) with hp | hn
    · rw [abs_of_nonneg hp]
      linarith
    · rw [abs_of_nonpos hn]
      linarith [abs_nonneg (G s)]
  have hGi : IntervalIntegrable (fun s => ‖G s‖) volume (a n) (b n) :=
    hG.norm.intervalIntegrable
  calc
    (∫ s in a n..b n, ‖D s‖) ≤ ∫ s in a n..b n, (2*‖G s‖-D s) :=
      intervalIntegral.integral_mono (hab n) (hDi n).norm
        ((hGi.const_mul 2).sub (hDi n)) hpoint
    _ = 2*(∫ s in a n..b n, ‖G s‖)-(B (b n)-B (a n)) := by
      rw [intervalIntegral.integral_sub (hGi.const_mul 2) (hDi n),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hD s) (hDi n)]
    _ ≤ 2*(∫ s, ‖G s‖)+1 := by
      have hpart : (∫ s in a n..b n, ‖G s‖) ≤ ∫ s, ‖G s‖ := by
        rw [intervalIntegral.integral_of_le (hab n)]
        exact setIntegral_le_integral hG.norm (ae_of_all _ (fun s => norm_nonneg (G s)))
      linarith

#print axioms exists_small_on_interval
#print axioms exists_vanishing_endpoints
#print axioms integral_nonneg_of_derivative_upper
#print axioms derivative_integrable_of_upper
end
end UnifiedTheory.Audit.KFCausalOneSidedIntegral
