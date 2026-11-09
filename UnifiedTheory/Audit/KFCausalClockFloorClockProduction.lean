/- Physical L2 clock production: exact multiplier integral, strict sign,
and quantitative comparison with the classical clock-response energy. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockVelocity
import UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm
import UnifiedTheory.Audit.KFCausalStrictMultiplierPairing
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockProduction
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorClockVelocity
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response response_bounds response_add_defect)
open UnifiedTheory.Audit.KFCausalStrictMultiplierPairing

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)

def production (f : Hilbert) : ℝ := (2/h)*(inner ℂ f (differenceOperator ε hε h hh f)).im

def responseAction : Hilbert →L[ℂ] Hilbert := ContinuousLinearMap.id ℂ Hilbert-defectOperator ε hε

def responseEnergy (f : Hilbert) : ℝ := (inner ℂ f (responseAction ε hε f)).re

theorem responseAction_coe (f : Hilbert) : responseAction ε hε f =ᵐ[volume]
    fun x => (response ε x.1:ℂ)*f x := by
  filter_upwards [Lp.coeFn_sub f (defectOperator ε hε f),defectOperator_coe ε hε f] with x hs hd
  change (f-defectOperator ε hε f) x = _
  rw [hs]
  simp only [Pi.sub_apply,hd]
  have hr : (response ε x.1:ℂ) = 1-(KFCausalClockFloorCanonicalDefect.defect ε x.1:ℂ) := by
    exact_mod_cast (show response ε x.1 = 1-KFCausalClockFloorCanonicalDefect.defect ε x.1 by
      linarith [response_add_defect ε x.1 hε.le])
  rw [hr]
  ring

theorem responseEnergy_integral (f : Hilbert) : responseEnergy ε hε f = ∫ x, response ε x.1*‖f x‖^2 :=
  KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing volume _ _ _ (responseAction_coe ε hε f)

include hε in
theorem response_density_integrable (f : Hilbert) : Integrable (fun x => response ε x.1*‖f x‖^2) volume := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hm : Measurable (fun x : Configuration => response ε x.1) := by
    unfold response KFCausalClockFloorFlow.clock
    fun_prop
  apply hi.mono' (hm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).norm.pow 2))
  exact Eventually.of_forall (fun x => by
    change ‖response ε x.1*‖f x‖^2‖ ≤ ‖f x‖^2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (response_bounds ε x.1 hε).1.le (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (response_bounds ε x.1 hε).2.le)

theorem responseEnergy_bounds (f : Hilbert) : 0 ≤ responseEnergy ε hε f ∧ responseEnergy ε hε f ≤ ‖f‖^2 := by
  rw [responseEnergy_integral,KFCausalAveragedEnergyGraph.l2_norm_square volume f]
  refine ⟨integral_nonneg (fun x => mul_nonneg (response_bounds ε x.1 hε).1.le (sq_nonneg _)),?_⟩
  apply integral_mono_ae (response_density_integrable ε hε f)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
  exact Eventually.of_forall (fun x => mul_le_of_le_one_left (sq_nonneg _) (response_bounds ε x.1 hε).2.le)

theorem production_integral (f : Hilbert) : production ε hε h hh f = ∫ x, velocity ε h x*‖f x‖^2 := by
  rw [production,imaginary_pairing_integral]
  apply integral_congr_ae
  filter_upwards [differenceOperator_coe ε hε h hh f] with x hx
  rw [hx,scalar_imaginary_pairing]
  exact (mul_assoc _ _ _).symm

include hε hh in
theorem production_density_integrable (f : Hilbert) : Integrable (fun x => velocity ε h x*‖f x‖^2) volume := by
  have hi := ((L2.integrable_inner (𝕜 := ℂ) f (differenceOperator ε hε h hh f)).im).const_mul (2/h)
  apply hi.congr
  filter_upwards [differenceOperator_coe ε hε h hh f] with x hx
  change (2/h)*(inner ℂ (f x) (differenceOperator ε hε h hh f x)).im = _
  rw [hx,scalar_imaginary_pairing]
  exact (mul_assoc _ _ _).symm

include hne in
theorem production_nonnegative (f : Hilbert) : 0 ≤ production ε hε h hh f := by
  rw [production_integral]
  exact integral_nonneg (fun x => mul_nonneg (velocity_positive ε hε h hne hh x).le (sq_nonneg _))

include hne in
theorem production_positive (f : Hilbert) (hf : f ≠ 0) : 0 < production ε hε h hh f := by
  have hn (x : Configuration) : (-2/h)*(difference ε h x).im < 0 := by
    have hp := velocity_positive ε hε h hne hh x
    unfold velocity at hp
    simpa only [neg_div,neg_mul] using neg_neg_of_pos hp
  have ht := multiplier_pairing_negative volume (difference ε h) (-2/h) f _
    (differenceOperator_coe ε hε h hh f) hn hf
  unfold production
  simpa only [neg_div,neg_mul,neg_lt_zero] using ht

include hne in
theorem production_bounds (f : Hilbert) :
    (1/2)*responseEnergy ε hε f ≤ production ε hε h hh f ∧ production ε hε h hh f ≤ ‖f‖^2 := by
  rw [production_integral,responseEnergy_integral,← integral_const_mul,
    KFCausalAveragedEnergyGraph.l2_norm_square volume f]
  constructor
  · apply integral_mono_ae ((response_density_integrable ε hε f).const_mul (1/2))
      (production_density_integrable ε hε h hh f)
    exact Eventually.of_forall (fun x => by
      dsimp only
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (velocity_bounds ε hε h hne hh x).1 (sq_nonneg _))
  · apply integral_mono_ae (production_density_integrable ε hε h hh f)
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
    exact Eventually.of_forall (fun x => mul_le_of_le_one_left (sq_nonneg _) (velocity_bounds ε hε h hne hh x).2.le)

theorem production_continuous : Continuous (production ε hε h hh) :=
  continuous_const.mul (Complex.continuous_im.comp (continuous_id.inner (differenceOperator ε hε h hh).continuous))

theorem responseEnergy_continuous : Continuous (responseEnergy ε hε) :=
  Complex.continuous_re.comp (continuous_id.inner (responseAction ε hε).continuous)

#print axioms responseAction_coe
#print axioms responseEnergy_integral
#print axioms response_density_integrable
#print axioms responseEnergy_bounds
#print axioms production_integral
#print axioms production_density_integrable
#print axioms production_nonnegative
#print axioms production_positive
#print axioms production_bounds
#print axioms production_continuous
#print axioms responseEnergy_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorClockProduction
