/- Actual imaginary-clock phase control for negative clock frequencies.
For positive hbar the inverse clock lies strictly below the real axis.
The frequency phase is contractive for nonpositive frequencies, monotone
in frequency, and tends pointwise to zero along negative integer frequencies.
These are pointwise phase statements: a full Hamiltonian-energy comparison
and pure-momentum domain obstruction are not asserted here. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockVelocity
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
namespace UnifiedTheory.Audit.KFCausalNegativeClockFrequency
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorClockVelocity

theorem inverse_im_negative (ε h : ℝ) (hε : 0 < ε) (hp : 0 < h)
    (hb : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) : (inversePoint ε h x).im < 0 := by
  have hv := inverse_im_ne_zero ε hε h hp.ne' hb x
  have hr := inverse_ratio_bounds ε hε h hp.ne' hb x
  have he := imaginary_equation ε hε h hb x
  have hd : 0 < Real.exp (inversePoint ε h x).re *
      (Real.sin (inversePoint ε h x).im/(inversePoint ε h x).im)+ε :=
    add_pos (mul_pos (Real.exp_pos _) (by linarith only [hr.1])) hε
  have ht : Real.exp (inversePoint ε h x).re*Real.sin (inversePoint ε h x).im+
      ε*(inversePoint ε h x).im = (inversePoint ε h x).im *
      (Real.exp (inversePoint ε h x).re *
      (Real.sin (inversePoint ε h x).im/(inversePoint ε h x).im)+ε) := by
    field_simp [hv]
  rw [ht] at he
  by_contra hn
  have hm := mul_nonneg (le_of_not_gt hn) hd.le
  linarith only [hm,he,hp]

def frequencyPhase (ε h p : ℝ) (x : Configuration) : ℂ :=
  Complex.exp (Complex.I*(p:ℂ)*inversePoint ε h x)

theorem frequencyPhase_norm (ε h p : ℝ) (x : Configuration) :
    ‖frequencyPhase ε h p x‖ = Real.exp (-p*(inversePoint ε h x).im) := by
  unfold frequencyPhase
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]

theorem frequencyPhase_contraction (ε h p : ℝ) (hε : 0 < ε) (hh : 0 < h)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hp : p ≤ 0) (x : Configuration) :
    ‖frequencyPhase ε h p x‖ ≤ 1 := by
  rw [frequencyPhase_norm]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hp)
      (inverse_im_negative ε h hε hh hb x).le)

theorem frequencyPhase_mono (ε h p q : ℝ) (hε : 0 < ε) (hh : 0 < h)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hpq : p ≤ q) (x : Configuration) :
    ‖frequencyPhase ε h p x‖ ≤ ‖frequencyPhase ε h q x‖ := by
  rw [frequencyPhase_norm,frequencyPhase_norm]
  apply Real.exp_le_exp.mpr
  have hi := inverse_im_negative ε h hε hh hb x
  nlinarith only [mul_nonneg (sub_nonneg.mpr hpq) (neg_nonneg.mpr hi.le)]

theorem frequencyPhase_tendsto_zero (ε h : ℝ) (hε : 0 < ε) (hh : 0 < h)
    (hb : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    Tendsto (fun n : ℕ => ‖frequencyPhase ε h (-(n:ℝ)) x‖) atTop (𝓝 0) := by
  simp_rw [frequencyPhase_norm,neg_neg]
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_atBot.comp
    (hn.atTop_mul_const_of_neg (inverse_im_negative ε h hε hh hb x))

#print axioms frequencyPhase_tendsto_zero
#print axioms inverse_im_negative
#print axioms frequencyPhase_norm
#print axioms frequencyPhase_contraction
#print axioms frequencyPhase_mono
end
end UnifiedTheory.Audit.KFCausalNegativeClockFrequency
