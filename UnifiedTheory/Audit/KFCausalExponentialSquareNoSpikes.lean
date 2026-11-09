/- A finite dissipation tail budget excludes revivals under a squared
variation bound. This permits Hilbert curves with only half-order continuity. -/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalExponentialSquareNoSpikes
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

theorem tendsto_zero {E : Type*} [NormedAddCommGroup E]
    (q : ℝ → E) (d : ℝ → ℝ) (hd : Continuous d) (s K : ℝ) (hK : 0 ≤ K)
    (hvar : ∀ a b, s ≤ a → a ≤ b → ‖q b-q a‖^2 ≤ K*Real.exp (2*b)*(b-a))
    (hdetect : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ t, s ≤ t → η ≤ ‖q t‖ → Real.exp (2*t)*δ ≤ d t)
    (htail : ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ a b, R ≤ a → a ≤ b →
      (∫ t in a..b, d t) < η) : Tendsto q atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨δ,hδ,hdet⟩ := hdetect (η/2) (by positivity)
  let α := min 1 (η^2/(16*(K+1)*Real.exp 2))
  have hα : 0 < α := lt_min zero_lt_one (div_pos (sq_pos_of_pos hη) (by positivity))
  have hα1 : α ≤ 1 := min_le_left _ _
  have hαη : K*Real.exp 2*α ≤ η^2/16 := by
    have ha := (le_div_iff₀ (by positivity : 0 < 16*(K+1)*Real.exp 2)).mp (min_le_right 1 (η^2/(16*(K+1)*Real.exp 2)))
    have hp := mul_nonneg (Real.exp_pos 2).le hα.le
    dsimp [α]
    dsimp [α] at hp
    nlinarith only [ha,hp]
  obtain ⟨R,hR⟩ := htail (α*δ) (mul_pos hα hδ)
  filter_upwards [eventually_ge_atTop (max R (max s 0))] with t ht
  have htR : R ≤ t := (le_max_left _ _).trans ht
  have hts : s ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  rw [dist_zero_right]
  by_contra hn
  have hq : η ≤ ‖q t‖ := le_of_not_gt hn
  let L := α*Real.exp (-2*t)
  have hL : 0 < L := mul_pos hα (Real.exp_pos _)
  have hL1 : L ≤ 1 := by
    have he : Real.exp (-2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left he hα.le).trans (by simpa using hα1)
  have hcancel : Real.exp (2*t)*Real.exp (-2*t) = 1 := by
    rw [← Real.exp_add,show 2*t+ -2*t = 0 by ring,Real.exp_zero]
  have hscale : Real.exp (2*t)*L = α := by
    dsimp [L]
    calc
      _ = α*(Real.exp (2*t)*Real.exp (-2*t)) := by ring
      _ = α := by rw [hcancel,mul_one]
  have hlower (z : ℝ) (hz : z ∈ Icc t (t+L)) : Real.exp (2*t)*δ ≤ d z := by
    have hz1 : z ≤ t+1 := by linarith [hz.2]
    have hexp : Real.exp (2*z) ≤ Real.exp (2*t)*Real.exp 2 := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hv := hvar t z hts hz.1
    have hsmallSq : ‖q z-q t‖^2 ≤ η^2/16 := by
      calc
        _ ≤ K*Real.exp (2*z)*(z-t) := hv
        _ ≤ K*(Real.exp (2*t)*Real.exp 2)*L :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hK) (by linarith [hz.2])
            (sub_nonneg.mpr hz.1) (by positivity)
        _ = K*Real.exp 2*(Real.exp (2*t)*L) := by ring
        _ = K*Real.exp 2*α := by rw [hscale]
        _ ≤ _ := hαη
    have hsmall : ‖q z-q t‖ ≤ η/4 := by
      nlinarith [norm_nonneg (q z-q t)]
    have hqz : η/2 ≤ ‖q z‖ := by
      have hh := norm_add_le (q t-q z) (q z)
      rw [sub_add_cancel,norm_sub_rev] at hh
      linarith
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hz.1])) hδ.le).trans
      (hdet z (hts.trans hz.1) hqz)
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := t) (b := t+L)
    (by linarith) (intervalIntegrable_const (c := Real.exp (2*t)*δ))
    (hd.intervalIntegrable t (t+L)) hlower
  have hi' : α*δ ≤ ∫ z in t..t+L, d z := by
    have he : (∫ _ : ℝ in t..t+L, Real.exp (2*t)*δ) = α*δ := by
      rw [intervalIntegral.integral_const,add_sub_cancel_left,smul_eq_mul]
      calc
        _ = (Real.exp (2*t)*L)*δ := by ring
        _ = _ := by rw [hscale]
    exact he.symm.le.trans hi
  exact (hR t (t+L) htR (by linarith)).not_ge hi'

#print axioms tendsto_zero
end
end UnifiedTheory.Audit.KFCausalExponentialSquareNoSpikes
