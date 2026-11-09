/- Quantitative convergence to a normalized fixed vacuum at a fixed cutoff. -/
import UnifiedTheory.Clay.YangMills.TransferPhysicalRatio
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.VacuumPowerConvergence
noncomputable section
open Filter TransferEnergySurvival

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Subtracting the unit-vacuum component leaves an orthogonal vector. -/
theorem residual_orthogonal (Omega w : H) (hn : ‖Omega‖ = 1) :
    inner ℂ Omega (w - inner ℂ Omega w • Omega) = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_one_of_norm_eq_one hn]
  ring

/-- Powers preserve the fixed-vacuum subtraction exactly. -/
theorem iterate_residual (A : H →L[ℂ] H) (Omega w : H) (hf : A Omega = Omega)
    (k : ℕ) :
    iterate A k (w - inner ℂ Omega w • Omega) =
      iterate A k w - inner ℂ Omega w • Omega := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate_succ, ih, map_sub, map_smul, hf]

/-- The entire vector converges at the orthogonal contraction rate. -/
theorem power_error (A : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (Omega : H) (hn : ‖Omega‖ = 1) (hf : A Omega = Omega)
    (q : ℝ) (hq : 0 ≤ q)
    (hc : ∀ v, inner ℂ Omega v = 0 → ‖A v‖ ≤ q * ‖v‖) (w : H) (k : ℕ) :
    ‖iterate A k w - inner ℂ Omega w • Omega‖ ≤
      q ^ k * ‖w - inner ℂ Omega w • Omega‖ := by
  have hb : ∀ v, inner ℂ Omega v = 0 → ‖iterate A 1 v‖ ≤ q * ‖v‖ := by
    simpa only [iterate_succ, iterate_zero] using hc
  simpa only [Nat.mul_one, iterate_residual A Omega w hf] using
    TransferPhysicalRatio.iterate_blocks_norm A hs Omega hf q hq 1 hb
      (w - inner ℂ Omega w • Omega) (residual_orthogonal Omega w hn) k

/-- A strict contraction on the orthogonal complement makes every fixed
vector a multiple of the vacuum, without an extra simplicity premise. -/
theorem fixed_proportional (A : H →L[ℂ] H) (Omega : H)
    (hn : ‖Omega‖ = 1) (hf : A Omega = Omega) (q : ℝ) (hq : q < 1)
    (hc : ∀ v, inner ℂ Omega v = 0 → ‖A v‖ ≤ q * ‖v‖)
    (w : H) (hw : A w = w) : w = inner ℂ Omega w • Omega := by
  have h := hc (w - inner ℂ Omega w • Omega) (residual_orthogonal Omega w hn)
  rw [map_sub, map_smul, hf, hw] at h
  have hz : ‖w - inner ℂ Omega w • Omega‖ = 0 := by
    nlinarith [norm_nonneg (w - inner ℂ Omega w • Omega)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The contraction applies around any nonzero fixed vector. -/
theorem rebase_contraction (A : H →L[ℂ] H) (Omega : H)
    (hn : ‖Omega‖ = 1) (hf : A Omega = Omega) (q : ℝ) (hq : q < 1)
    (hc : ∀ v, inner ℂ Omega v = 0 → ‖A v‖ ≤ q * ‖v‖)
    (Psi : H) (hPsi : Psi ≠ 0) (hfix : A Psi = Psi)
    (v : H) (hv : inner ℂ Psi v = 0) : ‖A v‖ ≤ q * ‖v‖ := by
  have he := fixed_proportional A Omega hn hf q hq hc Psi hfix
  have hcoef : inner ℂ Omega Psi ≠ 0 := by
    intro h
    rw [h, zero_smul] at he
    exact hPsi he
  rw [he, inner_smul_left] at hv
  exact hc v ((mul_eq_zero.mp hv).resolve_left (star_ne_zero.mpr hcoef))

/-- Fixed-cutoff convergence needs only the proved strict ratio cap. -/
theorem power_tendsto (A : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (Omega : H) (hn : ‖Omega‖ = 1) (hf : A Omega = Omega)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hc : ∀ v, inner ℂ Omega v = 0 → ‖A v‖ ≤ q * ‖v‖) (w : H) :
    Tendsto (fun k => iterate A k w) atTop (nhds (inner ℂ Omega w • Omega)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => power_error A hs Omega hn hf q hq hc w k)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const
    ‖w - inner ℂ Omega w • Omega‖

end
end UnifiedTheory.Clay.YangMills.VacuumPowerConvergence
