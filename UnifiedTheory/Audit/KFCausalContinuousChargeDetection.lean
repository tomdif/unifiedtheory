/- Continuous representatives detect actual standing charge invariance
pointwise, after applying the established unitary charge coordinates. -/
import UnifiedTheory.Audit.KFCausalChargedPairCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalContinuousChargeDetection
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open KFCausalNormalizedChargeFlow
open KFCausalStandingChargeOperator (zeroSector)

theorem fixed_iff_pointwise (h : ℝ) (hh : h ≠ 0) (f : Hilbert)
    (F : Joint 2 4 → ℂ) (hF : chargeCoordinates f =ᵐ[volume] F)
    (hcont : Continuous F) :
    f ∈ zeroSector h hh ↔
      ∀ θ x, F (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ x) = F x := by
  constructor
  · intro hf θ
    have hfix : action h hh θ f = f := hf θ
    have hmix := congrArg chargeCoordinates hfix
    rw [action_coordinates] at hmix
    have he : (fun x => F (flowEquiv (momentumScale h)
        (momentumScale_ne_zero h hh) θ x)) =ᵐ[volume] F := by
      filter_upwards [KFCausalMixedCircleAction.action_coe _
        (momentumScale_ne_zero h hh) θ (chargeCoordinates f),
        (flow_preserves_volume _ (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae hF,
        hF] with x hx hy hz
      simp only [Function.comp_apply] at hx
      rw [hmix] at hx
      exact hy.symm.trans (hx.symm.trans hz)
    have hp : Continuous (fun x : Joint 2 4 => (θ,x)) :=
      continuous_const.prodMk continuous_id
    have hflow := (flow_continuous (momentumScale h) (momentumScale_ne_zero h hh)).comp hp
    exact congrFun (Measure.eq_of_ae_eq he (hcont.comp hflow) hcont)
  · intro hf θ
    change action h hh θ f = f
    apply chargeCoordinates.injective
    rw [action_coordinates]
    apply Lp.ext
    filter_upwards [KFCausalMixedCircleAction.action_coe _
      (momentumScale_ne_zero h hh) θ (chargeCoordinates f),
      (flow_preserves_volume _ (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae hF,
      hF] with x hx hy hz
    simp only [Function.comp_apply] at hx
    rw [hx,hy,hz,hf]

theorem nonzero_of_pointwise (f : Hilbert) (F : Joint 2 4 → ℂ)
    (hF : chargeCoordinates f =ᵐ[volume] F) (hcont : Continuous F)
    (x : Joint 2 4) (hx : F x ≠ 0) : f ≠ 0 := by
  intro hz
  have he : F =ᵐ[volume] fun _ => (0:ℂ) := by
    filter_upwards [hF,Lp.coeFn_zero ℂ 2 (volume : Measure (Joint 2 4))] with y hy h0
    rw [hz,map_zero] at hy
    exact hy.symm.trans h0
  exact hx (congrFun (Measure.eq_of_ae_eq he hcont continuous_const) x)

#print axioms fixed_iff_pointwise
#print axioms nonzero_of_pointwise
end
end UnifiedTheory.Audit.KFCausalContinuousChargeDetection
