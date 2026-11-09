/- The relative coupled/pure clock chart is an actual transverse shear
unitary. Its all-L2 formula is independent of the positive clock floor. -/
import UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorPureClockLpCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTransverseShearCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph (flow_joint_continuous)
open UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets (flow_joint_differentiable homeomorph_quasiMeasurePreserving)

-- This chart contains no floor parameter.
def shearChart : Configuration ≃ₜ Configuration where
  toFun x := (x.1,flow (-x.1) x.2)
  invFun x := (x.1,flow x.1 x.2)
  left_inv x := by simp only [flow_compose,neg_add_cancel,flow_initial,Prod.mk.eta]
  right_inv x := by simp only [flow_compose,add_neg_cancel,flow_initial,Prod.mk.eta]
  continuous_toFun := continuous_fst.prodMk
    (flow_joint_continuous.comp (continuous_fst.neg.prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (flow_joint_continuous.comp (continuous_fst.prodMk continuous_snd))

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem shearChart_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving shearChart volume volume :=
  homeomorph_quasiMeasurePreserving volume shearChart
    (differentiable_fst.prodMk
      (flow_joint_differentiable.comp (differentiable_fst.prodMk differentiable_snd)))

theorem shearChart_inverse_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving shearChart.symm volume volume :=
  homeomorph_quasiMeasurePreserving volume shearChart.symm
    (differentiable_fst.prodMk
      (flow_joint_differentiable.comp (differentiable_fst.neg.prodMk differentiable_snd)))

def relativeCoordinates (ε : ℝ) (hε : 0 < ε) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  (KFCausalClockFloorPureClockCoordinates.coordinates ε hε).symm.trans
    (KFCausalClockFloorUnitaryCoordinates.coordinates ε hε)

theorem chart_cancellation (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    (KFCausalClockFloorPureClockCoordinates.chartHomeomorph ε hε).symm
      (KFCausalClockFloorFlow.coordinateHomeomorph ε hε x) = shearChart x := by
  change ((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm
    (KFCausalRegularizedLongitudinalChart.chartIso ε hε x.1),flow (-x.1) x.2) = _
  rw [OrderIso.symm_apply_apply]
  rfl

theorem weight_cancellation (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    KFCausalClockFloorTestPullback.weight ε x *
      (KFCausalClockFloorPureClockCoordinates.weight ε (shearChart x))⁻¹ =
        (Real.exp (-x.1):ℂ) := by
  have hn : (Real.sqrt (Real.exp x.1+ε):ℂ) ≠ 0 :=
    KFCausalClockFloorPureClockCoordinates.weight_ne_zero ε hε x
  change ((Real.sqrt (Real.exp x.1+ε)*Real.exp (-x.1):ℝ):ℂ) *
    (Real.sqrt (Real.exp x.1+ε):ℂ)⁻¹ = _
  rw [Complex.ofReal_mul,mul_comm _ (Real.exp (-x.1):ℂ),mul_assoc,mul_inv_cancel₀ hn,mul_one]

theorem relativeCoordinates_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    relativeCoordinates ε hε f =ᵐ[volume]
      fun x => (Real.exp (-x.1):ℂ)*f (shearChart x) := by
  filter_upwards [KFCausalClockFloorLpCoordinates.coordinates_coe ε hε
    ((KFCausalClockFloorPureClockCoordinates.coordinates ε hε).symm f),
    (KFCausalClockFloorLpCoordinates.coordinate_quasiMeasurePreserving ε hε).ae
      (KFCausalClockFloorPureClockLpCoordinates.coordinates_inverse_coe ε hε f)] with x hx hf
  change (KFCausalClockFloorUnitaryCoordinates.coordinates ε hε
    ((KFCausalClockFloorPureClockCoordinates.coordinates ε hε).symm f)) x = _
  rw [hx]
  change KFCausalClockFloorTestPullback.weight ε x *
    ((KFCausalClockFloorPureClockCoordinates.coordinates ε hε).symm f)
      (KFCausalClockFloorFlow.coordinateHomeomorph ε hε x) = _
  rw [hf]
  simp only [KFCausalClockFloorPureClockLpCoordinates.inverseFunction,chart_cancellation]
  rw [← mul_assoc,weight_cancellation ε hε]

def coordinates : Hilbert ≃ₗᵢ[ℂ] Hilbert := relativeCoordinates 1 (by norm_num)

theorem coordinates_coe (f : Hilbert) :
    coordinates f =ᵐ[volume] fun x => (Real.exp (-x.1):ℂ)*f (shearChart x) :=
  relativeCoordinates_coe 1 (by norm_num) f

theorem relativeCoordinates_eq (ε : ℝ) (hε : 0 < ε) :
    relativeCoordinates ε hε = coordinates := by
  apply LinearIsometryEquiv.ext
  intro f
  exact Lp.ext ((relativeCoordinates_coe ε hε f).trans (coordinates_coe f).symm)

theorem coordinates_inverse_coe (f : Hilbert) :
    coordinates.symm f =ᵐ[volume] fun x => (Real.exp x.1:ℂ)*f (shearChart.symm x) := by
  have he := KFCausalWeightedLpRepresentative.inverse_weighted_representative coordinates
    shearChart.toMeasurableEquiv shearChart_inverse_quasiMeasurePreserving
    (fun x => (Real.exp (-x.1):ℂ))
    (fun x => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) coordinates_coe f
  filter_upwards [he] with x hx
  change coordinates.symm f x = (Real.exp (-x.1):ℂ)⁻¹*f (shearChart.symm x) at hx
  simpa only [Real.exp_neg,Complex.ofReal_inv,inv_inv] using hx

#print axioms shearChart_quasiMeasurePreserving
#print axioms shearChart_inverse_quasiMeasurePreserving
#print axioms chart_cancellation
#print axioms weight_cancellation
#print axioms relativeCoordinates_coe
#print axioms coordinates_coe
#print axioms relativeCoordinates_eq
#print axioms coordinates_inverse_coe
end
end UnifiedTheory.Audit.KFCausalTransverseShearCoordinates
