/- The scalar quantum-to-classical velocity estimate on the actual
physical L2 multipliers, with a cubic defect-weighted error bound. -/
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar
import UnifiedTheory.Audit.KFCausalMultiplierVelocityPairing
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
import UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm (defect_inner)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar
open UnifiedTheory.Audit.KFCausalMultiplierVelocityPairing

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3)
local notation "D" => defectOperator ε hε
local notation "B" => shiftedDefect ε hε hbar hh
local notation "P" => driftOperator ε hε

theorem realDefect_chart (s : ℝ) : realDefect ε hε (chart ε s) = defect ε s := by
  unfold realDefect
  rw [← chartIso_apply ε hε,(chartIso ε hε).symm_apply_apply]

theorem defect_cube_coe (f : Hilbert) :
    D (D (D f)) =ᵐ[volume] fun x => ((defect ε x.1)^3:ℝ)*f x := by
  filter_upwards [defectOperator_coe ε hε (D (D f)),defectOperator_coe ε hε (D f),
    defectOperator_coe ε hε f] with x h3 h2 h1
  rw [h3,h2,h1,Complex.ofReal_pow]
  ring

include hne in
theorem velocity_pairing_weighted_error (f : Hilbert) :
    |(-2/hbar)*(inner ℂ f (B f)).im-(inner ℂ f (P f)).re| ≤
      (20*|hbar|/ε^2)*(inner ℂ (D f) (D (D f))).re := by
  have hb := velocity_pairing_bound (physicalSymbol ε hbar)
    (fun x => drift ε (defect ε x.1)) (fun x => (defect ε x.1)^3)
    (-2/hbar) (20*|hbar|/ε^2) f (B f) (P f) (D (D (D f)))
    (shiftedDefect_physical_coe ε hε hbar hh f) (driftOperator_coe ε hε f)
    (defect_cube_coe ε hε f) (fun x => by
      have hs := quantumVelocity_error ε hε hbar hne hh (chart ε x.1)
      rw [realDefect_chart ε hε] at hs
      exact hs)
  rwa [← defect_inner ε hε f (D (D f))] at hb

include hne in
theorem velocity_pairing_norm_error (f : Hilbert) :
    |(-2/hbar)*(inner ℂ f (B f)).im-(inner ℂ f (P f)).re| ≤
      (20*|hbar|/ε^2)*‖f‖^2 := by
  apply (velocity_pairing_weighted_error ε hε hbar hne hh f).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ‖D f‖*‖D (D f)‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖f‖*‖f‖ := mul_le_mul (defectOperator_norm_le ε hε f)
      ((defectOperator_norm_le ε hε (D f)).trans (defectOperator_norm_le ε hε f))
      (norm_nonneg _) (norm_nonneg _)
    _ = _ := (pow_two _).symm

theorem defect_inner_im_zero (f : Hilbert) : (inner ℂ f (D f)).im = 0 := by
  have h := inner_im_symm (𝕜 := ℂ) (D f) f
  rw [defect_inner ε hε f f] at h
  change (inner ℂ f (D f)).im = -(inner ℂ f (D f)).im at h
  linarith

#print axioms realDefect_chart
#print axioms defect_cube_coe
#print axioms velocity_pairing_weighted_error
#print axioms velocity_pairing_norm_error
#print axioms defect_inner_im_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityPairing
