/- The uniform relative quantum dissipation bound passes to the actual
physical L2 pairings, all energy components and charge averaging. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectVelocityCoercivity
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
import UnifiedTheory.Audit.KFCausalStrictMultiplierPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectProductionCoercivity
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorDefectVelocityCoercivity
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator (driftOperator driftOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect response response_bounds)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shiftedDefect)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem integrated_pairing_order {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (μ : Measure X) (c d : ℝ) (f g k : Lp E 2 μ)
    (hb : ∀ᵐ x ∂μ, c*(inner ℂ (f x) (g x)).im ≤ d*(inner ℂ (f x) (k x)).re) :
    c*(inner ℂ f g).im ≤ d*(inner ℂ f k).re := by
  have hi1 := L2.integrable_inner (𝕜 := ℂ) f g
  have hi2 := L2.integrable_inner (𝕜 := ℂ) f k
  have e1 := integral_im hi1
  have e2 := integral_re hi2
  change (∫ x, (inner ℂ (f x) (g x)).im ∂μ) = (∫ x, inner ℂ (f x) (g x) ∂μ).im at e1
  change (∫ x, (inner ℂ (f x) (k x)).re ∂μ) = (∫ x, inner ℂ (f x) (k x) ∂μ).re at e2
  rw [L2.inner_def,L2.inner_def,← e1,← e2,← integral_const_mul,← integral_const_mul]
  exact integral_mono_ae (hi1.im.const_mul c) (hi2.re.const_mul d) hb

theorem scalar_real_pairing (z : ℂ) (r : ℝ) : (inner ℂ z ((r:ℂ)*z)).re = r*‖z‖^2 := by
  change (inner ℂ z ((r:ℂ) • z)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change ((r:ℂ)*(‖z‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "R" => outputAction ε hε h hh
local notation "Q" => classicalOutput ε hε

include hne in
theorem physical_coercivity (f : Hilbert) :
    (-2/h)*(inner ℂ f (shiftedDefect ε hε h hh f)).im ≤ (1/32)*(inner ℂ f (driftOperator ε hε f)).re := by
  apply integrated_pairing_order volume (-2/h) (1/32) f _ _
  filter_upwards [shiftedDefect_physical_coe ε hε h hh f,driftOperator_coe ε hε f] with x hx hy
  change (-2/h)*(inner ℂ (f x) (shiftedDefect ε hε h hh f x)).im ≤
    (1/32)*(inner ℂ (f x) (driftOperator ε hε f x)).re
  rw [hx,hy,KFCausalStrictMultiplierPairing.scalar_imaginary_pairing,scalar_real_pairing]
  have hp := neg_le_neg (dissipation_lower ε hε h hne hh x)
  have hb : (-2/h)*(physicalSymbol ε h x).im ≤ (1/32)*drift ε (defect ε x.1) := by
    simpa only [dissipation,neg_div,neg_mul,mul_neg,neg_neg] using hp
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb (sq_nonneg ‖f x‖)

theorem physical_classical_nonpositive (f : Hilbert) : (inner ℂ f (driftOperator ε hε f)).re ≤ 0 := by
  rw [KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing volume _ _ _ (driftOperator_coe ε hε f)]
  apply integral_nonpos
  intro x
  have he := classical_dissipation_identity ε hε x.1
  have hp : 0 ≤ (ε/(KFCausalClockFloorFlow.clock ε x.1)^2)*response ε x.1 :=
    mul_nonneg (div_nonneg hε.le (sq_nonneg _)) (response_bounds ε x.1 hε).1.le
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

include hne in
theorem output_coercivity (g : Output (Fin 8) Hilbert) :
    (-2/h)*(inner ℂ g (R g)).im ≤ (1/32)*(inner ℂ g (Q g)).re := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Complex.im_sum,Complex.re_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val<5
  · simp only [outputAction_apply,factorAction,classicalOutput_apply,classicalFactor,hi,if_true,
      KFCausalClockFloorQuantumVelocityPairing.defect_inner_im_zero,ContinuousLinearMap.zero_apply,
      inner_zero_right,Complex.zero_re,mul_zero,le_refl]
  · simpa only [outputAction_apply,factorAction,classicalOutput_apply,classicalFactor,hi,if_false] using
      physical_coercivity ε hε h hne hh (g i)

theorem output_classical_nonpositive (g : Output (Fin 8) Hilbert) : (inner ℂ g (Q g)).re ≤ 0 := by
  rw [PiLp.inner_apply,Complex.re_sum]
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : i.val<5
  · simp only [classicalOutput_apply,classicalFactor,hi,if_true,ContinuousLinearMap.zero_apply,inner_zero_right,Complex.zero_re,le_refl]
  · simpa only [classicalOutput_apply,classicalFactor,hi,if_false] using physical_classical_nonpositive ε hε (g i)

include hne in
theorem averaged_coercivity (g : KFCausalAveragedOutputRescaling.EnergyOutputSpace) :
    (-2/h)*(inner ℂ g ((R).compLp g)).im ≤ (1/32)*(inner ℂ g ((Q).compLp g)).re := by
  apply integrated_pairing_order angleMeasure (-2/h) (1/32) g _ _
  filter_upwards [(R).coeFn_compLp g,(Q).coeFn_compLp g] with θ hr hq
  rw [hr,hq]
  exact output_coercivity ε hε h hne hh (g θ)

theorem averaged_classical_nonpositive (g : KFCausalAveragedOutputRescaling.EnergyOutputSpace) :
    (inner ℂ g ((Q).compLp g)).re ≤ 0 := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) g ((Q).compLp g))
  change (∫ θ, (inner ℂ (g θ) ((Q).compLp g θ)).re ∂angleMeasure) =
    (∫ θ, inner ℂ (g θ) ((Q).compLp g θ) ∂angleMeasure).re at he
  rw [L2.inner_def,← he]
  apply integral_nonpos_of_ae
  filter_upwards [(Q).coeFn_compLp g] with θ hq
  rw [hq]
  exact output_classical_nonpositive ε hε (g θ)

#print axioms integrated_pairing_order
#print axioms scalar_real_pairing
#print axioms physical_coercivity
#print axioms physical_classical_nonpositive
#print axioms output_coercivity
#print axioms output_classical_nonpositive
#print axioms averaged_coercivity
#print axioms averaged_classical_nonpositive
end
end UnifiedTheory.Audit.KFCausalClockFloorDefectProductionCoercivity
