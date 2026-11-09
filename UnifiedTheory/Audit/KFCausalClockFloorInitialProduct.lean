/- The previously constructed physical energy-form family has an exact
normalized clock/transverse product representation. No replacement family
or extra energy assumption is introduced here. -/
import UnifiedTheory.Audit.KFCausalGaussianPhaseSpaceLimit
import UnifiedTheory.Audit.KFCausalProductPhaseTranslation
import UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialProduct
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalGaussianPhaseSpaceLimit
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalProductPhaseTranslation
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)

abbrev ClockHilbert := Lp ℂ 2 (volume : Measure ℝ)

def clockState (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) : ClockHilbert :=
  (clockFunction_memLp ε a hε ha).toLp (clockFunction ε a)

theorem clockState_norm_square (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    ‖clockState ε a hε ha‖^2 = clockMass ε a :=
  toLp_square_integral _ (clockFunction_memLp ε a hε ha)

theorem clockState_ne_zero (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    clockState ε a hε ha ≠ 0 := by
  intro hz
  have he := clockState_norm_square ε a hε ha
  rw [hz,norm_zero,zero_pow (by norm_num)] at he
  exact (clockMass_positive ε a hε ha).ne' he.symm

def unitClock (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) : ClockHilbert :=
  (‖clockState ε a hε ha‖⁻¹:ℝ) • clockState ε a hε ha

theorem unitClock_norm (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    ‖unitClock ε a hε ha‖ = 1 := by
  rw [unitClock,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (clockState_ne_zero ε a hε ha))

theorem trialState_product (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    trialState ε a hbar hε ha hh = productState volume volume (clockState ε a hε ha)
      (gaussian (groundWidth hbar) (neutralWidth hbar)
        (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)) := by
  apply Lp.ext
  filter_upwards [trialState_coe ε a hbar hε ha hh,
    productState_coe volume volume (clockState ε a hε ha)
      (gaussian (groundWidth hbar) (neutralWidth hbar)
        (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)),
    quasiMeasurePreserving_fst.ae (clockFunction_memLp ε a hε ha).coeFn_toLp,
    quasiMeasurePreserving_snd.ae (physicalGaussian_memLp _ _
      (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)).coeFn_toLp] with z hz hp hc hg
  change clockState ε a hε ha z.1 = clockFunction ε a z.1 at hc
  change gaussian (groundWidth hbar) (neutralWidth hbar)
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) z.2 = _ at hg
  rw [hz,hp,hc,hg]
  rfl

theorem unitTrial_product (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    unitTrial ε a hbar hε ha hh =
      productState volume volume (unitClock ε a hε ha) (unitGaussian hbar hh) := by
  rw [unitTrial,unitClock,unitGaussian,product_real_smul_left,product_real_smul_right,
    smul_smul,trialState_product,product_norm,mul_inv_rev]
  rw [mul_comm]

#print axioms clockState_norm_square
#print axioms clockState_ne_zero
#print axioms unitClock_norm
#print axioms trialState_product
#print axioms unitTrial_product

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialProduct
