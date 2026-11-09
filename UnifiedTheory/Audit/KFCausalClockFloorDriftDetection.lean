/- The classical drift multiplier detects every nonzero physical vector.
Its squared output norm is controlled by its nonnegative dissipation
pairing, without a uniform lower bound on the multiplier. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectProductionCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorDriftDetection
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator (driftOperator driftOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
open UnifiedTheory.Audit.KFCausalClockFloorDefectProductionCoercivity

variable (ε : ℝ) (hε : 0 < ε)
local notation "B" => driftOperator ε hε

def detection (f : Hilbert) : ℝ := -(inner ℂ f (B f)).re

include hε in
theorem drift_negative (s : ℝ) : drift ε (defect ε s) < 0 := by
  have hd := defect_positive ε s hε
  have hr := (response_bounds ε s hε).1
  have he := response_add_defect ε s hε.le
  unfold drift
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (sq_pos_of_pos hd) (by linarith))) hε

theorem drift_injective : Function.Injective B := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have he := (Lp.eq_zero_iff_ae_eq_zero).mp hf
  filter_upwards [he,driftOperator_coe ε hε f] with x hx hb
  have hm : (drift ε (defect ε x.1):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (drift_negative ε hε x.1).ne
  exact (mul_eq_zero.mp (hb.symm.trans hx)).resolve_left hm

theorem detection_nonnegative (f : Hilbert) : 0 ≤ detection ε hε f :=
  neg_nonneg.mpr (physical_classical_nonpositive ε hε f)

theorem detection_smul (c : ℂ) (f : Hilbert) :
    detection ε hε (c • f) = ‖c‖^2*detection ε hε f := by
  unfold detection
  rw [map_smul,inner_smul_left,inner_smul_right,← mul_assoc,
    Complex.conj_mul',← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem drift_norm_sq_bound (f : Hilbert) : ‖B f‖^2 ≤ (1/ε)*detection ε hε f := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) f (B f)).re
  have he : (fun x : Configuration => (inner ℂ (f x) (B f x)).re) =ᵐ[volume]
      fun x => drift ε (defect ε x.1)*‖f x‖^2 := by
    filter_upwards [driftOperator_coe ε hε f] with x hx
    rw [hx,scalar_real_pairing]
  have hd := hi.congr he
  rw [KFCausalAveragedEnergyGraph.l2_norm_square,detection,
    real_multiplier_pairing volume _ _ _ (driftOperator_coe ε hε f),
    ← integral_neg,← integral_const_mul]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (B f))).mp (Lp.memLp (B f)))
    (hd.neg.const_mul (1/ε))
  filter_upwards [driftOperator_coe ε hε f] with x hx
  change ‖B f x‖^2 ≤ (1/ε)*(-(drift ε (defect ε x.1)*‖f x‖^2))
  have hn := (drift_negative ε hε x.1).le
  have hb := drift_clock_bound ε hε x.1
  rw [abs_of_nonpos hn] at hb
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos hn,mul_pow]
  have hm := mul_le_mul_of_nonneg_right hb (neg_nonneg.mpr hn)
  have hs := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖f x‖)
  nlinarith only [hs]

theorem drift_tendsto_zero (f : ℕ → Hilbert)
    (hf : Tendsto (fun n => detection ε hε (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => B (f n)) atTop (𝓝 0) := by
  have hs := squeeze_zero (fun n => sq_nonneg ‖B (f n)‖)
    (fun n => drift_norm_sq_bound ε hε (f n))
    (show Tendsto (fun n => (1/ε)*detection ε hε (f n)) atTop (𝓝 0) by
      simpa only [mul_zero] using hf.const_mul (1/ε))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

#print axioms drift_negative
#print axioms drift_injective
#print axioms detection_nonnegative
#print axioms detection_smul
#print axioms drift_norm_sq_bound
#print axioms drift_tendsto_zero
end
end UnifiedTheory.Audit.KFCausalClockFloorDriftDetection
