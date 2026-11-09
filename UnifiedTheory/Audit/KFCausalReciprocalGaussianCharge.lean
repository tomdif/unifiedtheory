/- The reciprocal-width generating family consists of actual nonzero
zero-charge Hilbert states. Finite complex superpositions retain zero
charge. Ordered-energy domains and bounds for this family remain separate. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianStates
import UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianCharge
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive clockFunction clockFunction_continuous
   clockFunction_memLp clockFunction_ne_zero trialState)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalStandingChargeOperator (zeroSector standingCharge standingCharge_zero_iff)
open KFCausalReciprocalGaussianStates (configurationDensity coordinateDensity)

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 0 < w)

def state : Hilbert :=
  KFCausalReciprocalGaussianStates.state (groundWidth h) (neutralWidth h) w
    (groundWidth_positive h hh) (neutralWidth_positive h hh) hw
    (clockFunction ε a) (clockFunction_continuous ε a) (clockFunction_memLp ε a hε ha)

theorem state_configuration_coe :
    state ε a h w hε ha hh hw =ᵐ[volume]
      configurationDensity (groundWidth h) (neutralWidth h) w (clockFunction ε a) :=
  KFCausalReciprocalGaussianStates.state_configuration_coe _ _ _ _ _ _ _ _ _

theorem state_coordinates_coe :
    chargeCoordinates (state ε a h w hε ha hh hw) =ᵐ[volume]
      coordinateDensity (groundWidth h) (neutralWidth h) w (momentumScale h) (clockFunction ε a) :=
  KFCausalReciprocalGaussianStates.state_coordinates_coe _ _ _ _ _ _ _ _ _ _
    (groundWidth_matching h hh)

theorem state_zeroSector : state ε a h w hε ha hh hw ∈ zeroSector h hh := by
  apply (KFCausalContinuousChargeDetection.fixed_iff_pointwise h hh _ _
    (state_coordinates_coe ε a h w hε ha hh hw)
    (KFCausalReciprocalGaussianStates.coordinateDensity_continuous _ _ _ _ _
      (clockFunction_continuous ε a))).mpr
  intro θ x
  exact KFCausalReciprocalGaussianStates.coordinateDensity_flow _ _ _ _
    (KFCausalNormalizedChargeFlow.momentumScale_ne_zero h hh) _ θ x

theorem state_charge_zero :
    (state ε a h w hε ha hh hw,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh _).mpr (state_zeroSector ε a h w hε ha hh hw)

theorem state_ne_zero : state ε a h w hε ha hh hw ≠ 0 :=
  KFCausalReciprocalGaussianStates.state_ne_zero _ _ _ _ _ _ _ _ _
    (clockFunction_ne_zero ε a hε.le 0)

omit w hw in
theorem state_one : state ε a h 1 hε ha hh (by norm_num) = trialState ε a h hε ha hh := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [state_coordinates_coe ε a h 1 hε ha hh (by norm_num),
    KFCausalClockFloorCoherentStates.weight_coe ε a h hε ha hh] with x hx hy
  rw [hx,hy]
  simp [coordinateDensity,KFCausalReciprocalGaussianStates.coordinateQuadratic,
    KFCausalClockFloorCoherentStates.weight,KFCausalChargeGaussianGeometry.profile,mul_assoc]

omit w hw in
def superposition {ι : Type*} [Fintype ι] (widths : ι → ℝ) (hwidths : ∀ i, 0 < widths i)
    (c : ι → ℂ) : Hilbert := ∑ i, c i • state ε a h (widths i) hε ha hh (hwidths i)

omit w hw in
theorem superposition_zeroSector {ι : Type*} [Fintype ι]
    (widths : ι → ℝ) (hwidths : ∀ i, 0 < widths i) (c : ι → ℂ) :
    superposition ε a h hε ha hh widths hwidths c ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem (fun i _ => (zeroSector h hh).smul_mem (c i)
    (state_zeroSector ε a h (widths i) hε ha hh (hwidths i)))

omit w hw in
theorem superposition_configuration_coe {ι : Type*} [Fintype ι]
    (widths : ι → ℝ) (hwidths : ∀ i, 0 < widths i) (c : ι → ℂ) :
    superposition ε a h hε ha hh widths hwidths c =ᵐ[volume]
      fun x => ∑ i, c i*configurationDensity (groundWidth h) (neutralWidth h)
        (widths i) (clockFunction ε a) x := by
  classical
  exact KFCausalFiniteLpRepresentatives.weighted_sum_coe volume c _ _
    (fun i => state_configuration_coe ε a h (widths i) hε ha hh (hwidths i))

def ratio (t : ℝ) : ℝ := (1+t)/(1-t)

theorem ratio_positive (t : ℝ) (ht : |t| < 1) : 0 < ratio t := by
  have hb := abs_lt.mp ht
  exact div_pos (by linarith) (by linarith)

def generatingState (t : ℝ) (ht : |t| < 1) : Hilbert :=
  ((1/(1-t^2):ℝ):ℂ) • state ε a h (ratio t) hε ha hh (ratio_positive t ht)

omit w hw in
theorem generatingState_zeroSector (t : ℝ) (ht : |t| < 1) :
    generatingState ε a h hε ha hh t ht ∈ zeroSector h hh :=
  (zeroSector h hh).smul_mem _ (state_zeroSector ε a h _ hε ha hh (ratio_positive t ht))

omit w hw in
theorem generatingState_ne_zero (t : ℝ) (ht : |t| < 1) :
    generatingState ε a h hε ha hh t ht ≠ 0 := by
  have hd : 1-t^2 ≠ 0 := by nlinarith [sq_abs t, abs_nonneg t]
  exact smul_ne_zero (Complex.ofReal_ne_zero.mpr (one_div_ne_zero hd))
    (state_ne_zero ε a h _ hε ha hh (ratio_positive t ht))

omit w hw in
theorem generatingState_initial :
    generatingState ε a h hε ha hh 0 (by norm_num) = trialState ε a h hε ha hh := by
  simpa [generatingState,ratio] using state_one ε a h hε ha hh

#print axioms state_configuration_coe
#print axioms state_coordinates_coe
#print axioms state_zeroSector
#print axioms state_charge_zero
#print axioms state_ne_zero
#print axioms state_one
#print axioms superposition_zeroSector
#print axioms superposition_configuration_coe
#print axioms ratio_positive
#print axioms generatingState_zeroSector
#print axioms generatingState_ne_zero
#print axioms generatingState_initial
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianCharge
