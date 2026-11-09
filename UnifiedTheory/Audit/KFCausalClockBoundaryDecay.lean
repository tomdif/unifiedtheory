/- Actual Gaussian clock cross-pair boundaries have a Gaussian majorant.
The constants depend on the packet widths/frequencies; no state-uniform
response estimate or integration over transverse position is asserted. -/
import UnifiedTheory.Audit.KFCausalClockResponseTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockBoundaryDecay
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock pair)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument inverse)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (amplitude amplitude_positive amplitude_square)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase clockPhase_bound)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor clockFactor_norm)

def boundary (ε a b p q y s : ℝ) : ℂ := pair ε a b p q y s/(clock ε s:ℂ)
def decay (ε a b : ℝ) : ℝ := (a+b)*ε^2/4
def constant (ε a b p q y : ℝ) : ℝ :=
  Real.exp ((a+b)*(1+y^2)+1/decay ε a b+(|p|+|q|)*Real.pi/3)

theorem chart_square_lower (ε s : ℝ) (hε : 0 < ε) :
    ε^2*s^2/2-1 ≤ (chart ε s)^2 := by
  have he := Real.exp_pos s
  by_cases hs : s ≤ 0
  · have hb : Real.exp s ≤ 1 := by simpa using Real.exp_le_exp.mpr hs
    have hsq : (Real.exp s)^2 ≤ 1 := by nlinarith
    unfold chart
    nlinarith [sq_nonneg (2*Real.exp s+ε*s)]
  · have hp : 0 ≤ ε*s := mul_nonneg hε.le (le_of_not_ge hs)
    unfold chart
    nlinarith [mul_nonneg he.le hp,sq_nonneg (ε*s)]

theorem boundary_norm (ε a b p q y s : ℝ) (hε : 0 < ε) :
    ‖boundary ε a b p q y s‖ =
      Real.exp (-2*s-(a+b)*((chart ε s)^2-y^2))*
        ‖clockPhase p (inverse ε y s)‖*‖clockPhase q (inverse ε y s)‖ := by
  have hc : 0 < clock ε s := by unfold clock; positivity
  have ha := amplitude_positive ε s hε
  simp only [boundary,pair,norm_div,norm_mul,norm_star,clockAmplitude,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc,abs_of_pos ha,
    argument,clockFactor_norm]
  calc
    _ = (amplitude ε s)^2/clock ε s*
        (Real.exp (-a*((chart ε s)^2-y^2))*Real.exp (-b*((chart ε s)^2-y^2)))*
        ‖clockPhase p (inverse ε y s)‖*‖clockPhase q (inverse ε y s)‖ := by ring
    _ = _ := by
      rw [amplitude_square ε s hε]
      change (clock ε s*Real.exp (-2*s))/clock ε s*_ *_ *_ = _
      rw [mul_div_cancel_left₀ _ hc.ne',← Real.exp_add,← Real.exp_add]
      congr 3
      ring

theorem boundary_bound (ε a b p q y s : ℝ) (hε : 0 < ε)
    (hab : 0 < a+b) (hy : |y| ≤ Real.pi*ε/3) :
    ‖boundary ε a b p q y s‖ ≤ constant ε a b p q y*Real.exp (-decay ε a b*s^2) := by
  have hz : |(inverse ε y s).im| ≤ Real.pi/3 :=
    KFCausalClockInverseStripBounds.inverse_im_third_strip ε hε (argument ε y s)
      (by simpa [argument] using hy)
  have hphase := mul_le_mul (clockPhase_bound p _ hz) (clockPhase_bound q _ hz)
    (norm_nonneg _) (Real.exp_pos _).le
  have hd : 0 < decay ε a b := by unfold decay; positivity
  have hyoung : -2*s-decay ε a b*s^2 ≤ 1/decay ε a b := by
    apply (mul_le_mul_iff_right₀ hd).mp
    have he : decay ε a b*(1/decay ε a b) = 1 := by field_simp
    rw [he]
    nlinarith [sq_nonneg (decay ε a b*s+1)]
  have hquad := mul_le_mul_of_nonneg_left (chart_square_lower ε s hε) hab.le
  have hexp : -2*s-(a+b)*((chart ε s)^2-y^2) ≤
      (a+b)*(1+y^2)+1/decay ε a b-decay ε a b*s^2 := by
    dsimp only [decay] at *
    nlinarith
  rw [boundary_norm ε a b p q y s hε]
  calc
    _ = Real.exp (-2*s-(a+b)*((chart ε s)^2-y^2))*
      (‖clockPhase p (inverse ε y s)‖*‖clockPhase q (inverse ε y s)‖) := by ring
    _ ≤ Real.exp ((a+b)*(1+y^2)+1/decay ε a b-decay ε a b*s^2)*
      (Real.exp (|p| *Real.pi/3)*Real.exp (|q| *Real.pi/3)) :=
        mul_le_mul (Real.exp_le_exp.mpr hexp) hphase (by positivity) (Real.exp_pos _).le
    _ = _ := by
      unfold constant
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
      congr 1
      ring

theorem boundary_atTop (ε a b p q y : ℝ) (hε : 0 < ε)
    (hab : 0 < a+b) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (boundary ε a b p q y) atTop (𝓝 0) := by
  have hd : 0 < decay ε a b := by unfold decay; positivity
  have hsq : Tendsto (fun s : ℝ => s^2) atTop atTop := tendsto_pow_atTop (by decide)
  have ht := Real.tendsto_exp_atBot.comp (hsq.const_mul_atTop_of_neg (neg_lt_zero.mpr hd))
  apply squeeze_zero_norm (boundary_bound ε a b p q y · hε hab hy)
  simpa using ht.const_mul (constant ε a b p q y)

theorem boundary_atBot (ε a b p q y : ℝ) (hε : 0 < ε)
    (hab : 0 < a+b) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (boundary ε a b p q y) atBot (𝓝 0) := by
  have hd : 0 < decay ε a b := by unfold decay; positivity
  have hsq : Tendsto (fun s : ℝ => s^2) atBot atTop := by
    simpa only [Function.comp_def,neg_sq] using
      (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0) :
        Tendsto (fun s : ℝ => s^2) atTop atTop).comp tendsto_neg_atBot_atTop
  have ht := Real.tendsto_exp_atBot.comp (hsq.const_mul_atTop_of_neg (neg_lt_zero.mpr hd))
  apply squeeze_zero_norm (boundary_bound ε a b p q y · hε hab hy)
  simpa using ht.const_mul (constant ε a b p q y)

#print axioms chart_square_lower
#print axioms boundary_norm
#print axioms boundary_bound
#print axioms boundary_atTop
#print axioms boundary_atBot
end
end UnifiedTheory.Audit.KFCausalClockBoundaryDecay
