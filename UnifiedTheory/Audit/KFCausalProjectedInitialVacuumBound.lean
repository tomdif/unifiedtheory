/- Actual initial-mean norm control by the final projected vacuum factor,
including bounded clock weights. Positive vacuum coupling gives a full
Hamiltonian bound for the unweighted initial norm, not its field moments. -/
import UnifiedTheory.Audit.KFCausalProjectedInitialClockCancellation
import UnifiedTheory.Audit.KFCausalShearNormEndpointMean
import UnifiedTheory.Audit.KFCausalClockSecantMultiplier

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedInitialVacuumBound
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalStructuredShearInterpolation (input shear)
open UnifiedTheory.Audit.KFCausalStructuredShearMean
  (meanInputAt meanShearAt angle_continuous endpointValues endpoint_sum endpoint_continuous mean_input_one)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalShearEndpointMean (endpoint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator)
open UnifiedTheory.Audit.KFCausalProjectedInitialClockCancellation (initial_clock_tangent_zero)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian
  (meanInput projectedEnergy physical_energy factorEnergy)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)
local notation "C" => coefficientOperator ε h hε hb hh
local notation "G0" => meanInputAt ε h hε hh hb S 0
local notation "G1" => meanInput ε h hε hh hb S 7

theorem mean_initial_tangent_lower (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x) :
    ‖W G0‖^2+2*(inner ℂ (W G0) (C (W (meanShearAt ε h hε hh hb S 0)))).re ≤
      ‖W (meanInputAt ε h hε hh hb S 1)‖^2 := by
  have hi (t : Interval) : Integrable (fun θ => input ε h hε hh hb S (2*Real.pi*θ) t) angleMeasure := (continuous_angle_memLp _
    ((angle_continuous ε h hε hh hb S t).1.comp (continuous_const.mul continuous_id))).integrable (by norm_num)
  have hj (t : Interval) : Integrable (fun θ => shear ε h hε hh hb S (2*Real.pi*θ) t) angleMeasure := (continuous_angle_memLp _
    ((angle_continuous ε h hε hh hb S t).2.comp (continuous_const.mul continuous_id))).integrable (by norm_num)
  have hc : Continuous (fun θ => endpointValues ε h hε hh hb S (2*Real.pi*θ)) :=
    (endpoint_continuous ε h hε hh hb S).comp (continuous_const.mul continuous_id)
  have hm : ∀ θ, endpointValues ε h hε hh hb S (2*Real.pi*θ) ∈
      Submodule.span ℂ (Set.range (endpoint ε h hε hb)) := by
    intro θ
    rw [endpoint_sum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self _)))
  have he := KFCausalShearNormEndpointMean.mean_gap ε h hε hb hh W w hW _
    ((continuous_angle_memLp _ hc).integrable (by norm_num)) hm
  let zero : Interval := ⟨0,by constructor <;> norm_num⟩
  let one : Interval := ⟨1,by constructor <;> norm_num⟩
  have hmval : (∫ θ, endpointValues ε h hε hh hb S (2*Real.pi*θ) ∂angleMeasure) =
      ((meanInputAt ε h hε hh hb S 0,meanShearAt ε h hε hh hb S 0),
       (meanInputAt ε h hε hh hb S 1,meanShearAt ε h hε hh hb S 1)) := by
    unfold endpointValues
    rw [integral_pair ((hi zero).prodMk (hj zero)) ((hi one).prodMk (hj one)),
      integral_pair (hi zero) (hj zero),integral_pair (hi one) (hj one)]
    rfl
  rw [hmval] at he
  change 0 ≤ ‖W (meanInputAt ε h hε hh hb S 1)‖^2-‖W (meanInputAt ε h hε hh hb S 0)‖^2-
    2*(inner ℂ (W (meanInputAt ε h hε hh hb S 0))
      (C (W (meanShearAt ε h hε hh hb S 0)))).re at he
  linarith only [he]

theorem weighted_initial_le_final (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)
    (hQ : ∀ θ f, W (action h hh θ f) = action h hh θ (W f)) :
    ‖W G0‖^2 ≤ ‖W G1‖^2 := by
  have he := mean_initial_tangent_lower ε h hε hh hb S W w hW
  rw [initial_clock_tangent_zero ε h hε hh hb S W hQ,mean_input_one] at he
  simpa only [mul_zero,add_zero] using he

theorem initial_le_final : ‖G0‖^2 ≤ ‖G1‖^2 :=
  weighted_initial_le_final ε h hε hh hb S (ContinuousLinearMap.id ℂ Hilbert) (fun _ => 1)
    (fun f => Filter.Eventually.of_forall (fun x => (one_mul (f x)).symm)) (fun _ _ => rfl)

theorem secant_initial_le_final :
    ‖KFCausalClockSecantMultiplier.operator ε h hε hb hh G0‖^2 ≤
      ‖KFCausalClockSecantMultiplier.operator ε h hε hb hh G1‖^2 := by
  apply weighted_initial_le_final ε h hε hh hb S _
    (fun s => (KFCausalClockSecantMultiplier.value ε h s:ℂ))
    (KFCausalClockSecantMultiplier.operator_coe ε h hε hb hh)
  exact KFCausalBoundedClockCharge.multiplier_charge _ _ _ _ _ h hh

variable (mass2 quartic vacuum t : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic)
include hm hq

theorem initial_vacuum_energy (hv : 0 ≤ vacuum) :
    Real.exp (2*t)*vacuum*‖G0‖^2 ≤ projectedEnergy ε h hε hh hb S mass2 quartic vacuum t := by
  have he := mul_le_mul_of_nonneg_left (initial_le_final ε h hε hh hb S)
    (mul_nonneg (Real.exp_pos (2*t)).le hv)
  rw [physical_energy ε h hε hh hb S mass2 quartic vacuum t hm hq hv]
  have hs : 0 ≤ (factorEnergy ε h hε hh hb S 0+factorEnergy ε h hε hh hb S 1+
      factorEnergy ε h hε hh hb S 2)/2 := by unfold factorEnergy; positivity
  have hg : 0 ≤ (factorEnergy ε h hε hh hb S 3+factorEnergy ε h hε hh hb S 4)/2+
      mass2/2*factorEnergy ε h hε hh hb S 5+quartic/4*factorEnergy ε h hε hh hb S 6 := by
    unfold factorEnergy
    positivity
  have hp := mul_nonneg (Real.exp_pos (2*t)).le hg
  change _ ≤ Real.exp (2*t)*vacuum*factorEnergy ε h hε hh hb S 7 at he
  nlinarith only [he,hs,hp]

theorem positive_vacuum_energy_bound (hv : 0 < vacuum) :
    ‖G0‖^2 ≤ projectedEnergy ε h hε hh hb S mass2 quartic vacuum t/(Real.exp (2*t)*vacuum) := by
  apply (le_div_iff₀ (mul_pos (Real.exp_pos _) hv)).mpr
  simpa only [mul_comm (‖G0‖^2)] using initial_vacuum_energy ε h hε hh hb S mass2 quartic vacuum t hm hq hv.le

theorem secant_vacuum_energy_bound (hv : 0 < vacuum) :
    ‖KFCausalClockSecantMultiplier.operator ε h hε hb hh G0‖^2 ≤
      (ε/4)*(projectedEnergy ε h hε hh hb S mass2 quartic vacuum t/(Real.exp (2*t)*vacuum)) := by
  exact (KFCausalClockSecantMultiplier.operator_norm_sq ε h hε hb hh G0).trans
    (mul_le_mul_of_nonneg_left (positive_vacuum_energy_bound ε h hε hh hb S mass2 quartic vacuum t hm hq hv)
      (by positivity))

#print axioms mean_initial_tangent_lower
#print axioms weighted_initial_le_final
#print axioms initial_le_final
#print axioms secant_initial_le_final
#print axioms initial_vacuum_energy
#print axioms positive_vacuum_energy_bound
#print axioms secant_vacuum_energy_bound
end
end UnifiedTheory.Audit.KFCausalProjectedInitialVacuumBound
