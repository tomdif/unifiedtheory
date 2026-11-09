/- Quantitative comparison of the actual clock-production quadratic form
with the classical-response form, through all physical output components
and charge averaging. This does not identify an evolved phase-space law. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockVelocityApproximation
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockProduction
import UnifiedTheory.Audit.KFCausalMultiplierVelocityPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockProductionApproximation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm (defect_inner)
open UnifiedTheory.Audit.KFCausalClockFloorClockProduction
open UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm (deltaOutput deltaLp)
open UnifiedTheory.Audit.KFCausalClockFloorClockOutputProduction (responseOutput)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect response)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "D" => defectOperator ε hε

theorem defect_square_coe (f : Hilbert) : D (D f) =ᵐ[volume] fun x => ((defect ε x.1)^2:ℝ)*f x := by
  filter_upwards [defectOperator_coe ε hε (D f),defectOperator_coe ε hε f] with x h2 h1
  rw [h2,h1,Complex.ofReal_pow]
  ring

include hne in
theorem physical_weighted_error (f : Hilbert) :
    |production ε hε h hh f-responseEnergy ε hε f| ≤ (2*|h|/ε)*‖D f‖^2 := by
  have he := KFCausalMultiplierVelocityPairing.velocity_pairing_bound (difference ε h)
    (fun x => response ε x.1) (fun x => (defect ε x.1)^2) (2/h) (2*|h|/ε)
    f (differenceOperator ε hε h hh f) (responseAction ε hε f) (D (D f))
    (differenceOperator_coe ε hε h hh f) (responseAction_coe ε hε f)
    (defect_square_coe ε hε f) (KFCausalClockFloorClockVelocityApproximation.velocity_error ε hε h hne hh)
  have hs : (inner ℂ (D f) (D f)).re = ‖D f‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [← defect_inner ε hε f (D f),hs] at he
  exact he

include hne in
theorem physical_error (f : Hilbert) :
    |production ε hε h hh f-responseEnergy ε hε f| ≤ (2*|h|/ε)*‖f‖^2 :=
  (physical_weighted_error ε hε h hne hh f).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (defectOperator_norm_le ε hε f) 2) (by positivity))

include hne in
theorem output_error (g : Output (Fin 8) Hilbert) :
    |KFCausalClockFloorClockOutputProduction.production ε hε h hh g-
      KFCausalClockFloorClockOutputProduction.classicalProduction ε hε g| ≤ (2*|h|/ε)*‖g‖^2 := by
  rw [KFCausalClockFloorClockOutputProduction.production_sum,
    KFCausalClockFloorClockOutputProduction.classicalProduction,← Finset.sum_sub_distrib,
    PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · simp only [sub_self,abs_zero]
    positivity
  · exact physical_error ε hε h hne hh (g i)

include hne in
theorem averaged_error (g : KFCausalAveragedOutputRescaling.EnergyOutputSpace) :
    |KFCausalClockFloorAveragedClockProduction.production ε hε h hh g-
      KFCausalClockFloorAveragedClockProduction.classicalProduction ε hε g| ≤ (2*|h|/ε)*‖g‖^2 := by
  apply KFCausalMultiplierVelocityPairing.integrated_velocity_bound (2/h) (2*|h|/ε)
    g (deltaLp ε hε h hh g) ((responseOutput ε hε).compLp g)
  filter_upwards [(deltaOutput ε hε h hh).coeFn_compLp g,(responseOutput ε hε).coeFn_compLp g] with θ hd hr
  change |(2/h)*(inner ℂ (g θ) ((deltaOutput ε hε h hh).compLp g θ)).im-
    (inner ℂ (g θ) ((responseOutput ε hε).compLp g θ)).re| ≤ _
  rw [hd,hr,← KFCausalClockFloorClockOutputProduction.classicalProduction_pairing]
  exact output_error ε hε h hne hh (g θ)

#print axioms defect_square_coe
#print axioms physical_weighted_error
#print axioms physical_error
#print axioms output_error
#print axioms averaged_error
end
end UnifiedTheory.Audit.KFCausalClockFloorClockProductionApproximation
