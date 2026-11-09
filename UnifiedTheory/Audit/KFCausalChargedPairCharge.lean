/- The previously constructed paired state has actual standing charge
zero and is odd under charged-plane interchange. It is orthogonal to the
entire restricted neutral closure. -/
import UnifiedTheory.Audit.KFCausalPairedQuadraticChargeCoordinates
import UnifiedTheory.Audit.KFCausalChargedPairDomain
import UnifiedTheory.Audit.KFCausalNeutralSwapConstraint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedPairCharge
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargedPairDomain (state state_coe state_ne_zero)
open KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalClockFloorInvariantTrial
  (clockFunction clockFunction_continuous clockFunction_memLp neutralWidth neutralWidth_positive)
open KFCausalClockFloorCoherentStates (weight weight_flow)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero flow_preserves_volume)
open KFCausalChargeZeroSwapWitness (imbalance imbalance_flow imbalance_swap)
open KFCausalChargedPlaneSwap
open KFCausalStandingChargeOperator
  (zeroSector standingCharge standingCharge_zero_iff zeroProjection zeroProjection_fixes)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hc" => clockFunction_continuous ε a
local notation "hg" => clockFunction_memLp ε a hε ha
local notation "ψ" => state ε a h hε ha hh

theorem tensor_state_eq :
    KFCausalPairedQuadraticStates.state α β hα hβ (clockFunction ε a) hc hg = ψ := by
  apply Lp.ext
  filter_upwards [KFCausalPairedQuadraticStates.state_configuration_coe
    α β hα hβ (clockFunction ε a) hc hg,state_coe ε a h hε ha hh] with x hx hy
  rw [hx,hy]
  unfold KFCausalPairedQuadraticStates.pairedConfigurationProfile
    KFCausalChargedPairDomain.pairedProfile KFCausalChargeGaussianIdentities.configurationProfile
  ring

theorem state_chargeCoordinates :
    chargeCoordinates ψ =ᵐ[volume] fun x => (imbalance (momentumScale h) x:ℂ)/2*weight ε a h x := by
  have he := KFCausalPairedQuadraticChargeCoordinates.state_coordinates_coe
    α β hα hβ (clockFunction ε a) hc hg (momentumScale h) (groundWidth_matching h hh)
  rw [tensor_state_eq] at he
  exact he

theorem state_zeroSector : ψ ∈ zeroSector h hh := by
  intro θ
  change action h hh θ ψ = ψ
  apply chargeCoordinates.injective
  rw [action_coordinates]
  apply Lp.ext
  filter_upwards [KFCausalMixedCircleAction.action_coe _ (momentumScale_ne_zero h hh) θ
    (chargeCoordinates ψ),
    (flow_preserves_volume _ (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae
      (state_chargeCoordinates ε a h hε ha hh),
    state_chargeCoordinates ε a h hε ha hh] with x hx hy hz
  simp only [Function.comp_apply] at hx
  rw [hx,hy,hz,imbalance_flow,weight_flow ε a h hh]

theorem state_charge_zero : (ψ,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh ψ).mpr (state_zeroSector ε a h hε ha hh)

theorem state_projection : zeroProjection h hh ψ = ψ :=
  zeroProjection_fixes h hh ψ (state_zeroSector ε a h hε ha hh)

theorem state_odd : operator ψ = -ψ := by
  apply chargeCoordinates.injective
  rw [coordinates_operator,map_neg]
  apply Lp.ext
  filter_upwards [mixed_coe (chargeCoordinates ψ),
    swapIsometry.measurePreserving.quasiMeasurePreserving.ae
      (state_chargeCoordinates ε a h hε ha hh),
    state_chargeCoordinates ε a h hε ha hh,Lp.coeFn_neg (chargeCoordinates ψ)] with x hx hy hz hn
  change chargeCoordinates ψ (swap x) =
    (imbalance (momentumScale h) (swap x):ℂ)/2*weight ε a h (swap x) at hy
  rw [hx,hy,hn,Pi.neg_apply,hz,imbalance_swap,weight_swap,Complex.ofReal_neg]
  ring

theorem state_orthogonal_fixed (f : Hilbert) (hf : f ∈ fixedSpace) :
    inner ℂ f ψ = 0 := by
  have he := operator.inner_map_map f ψ
  rw [show operator f = f from hf,state_odd,inner_neg_right] at he
  linear_combination -he/2

theorem state_neutralClosure_orthogonal (f : Hilbert)
    (hf : f ∈ closure (KFCausalNeutralSwapConstraint.neutralStates ε h hε hh)) :
    inner ℂ f ψ = 0 :=
  state_orthogonal_fixed ε a h hε ha hh f
    (KFCausalNeutralSwapConstraint.closure_subset_fixed ε h hε hh hf)

theorem state_outside_neutralClosure :
    ψ ∉ closure (KFCausalNeutralSwapConstraint.neutralStates ε h hε hh) := by
  intro hf
  have hz := state_neutralClosure_orthogonal ε a h hε ha hh ψ hf
  exact state_ne_zero ε a h hε ha hh ((inner_self_eq_zero).mp hz)

#print axioms tensor_state_eq
#print axioms state_chargeCoordinates
#print axioms state_zeroSector
#print axioms state_charge_zero
#print axioms state_projection
#print axioms state_odd
#print axioms state_orthogonal_fixed
#print axioms state_neutralClosure_orthogonal
#print axioms state_outside_neutralClosure
end
end UnifiedTheory.Audit.KFCausalChargedPairCharge
