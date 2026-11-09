/- Whole-L2 representative of the existing physical clock straightening
in paired position coordinates. Its clock-dependent dilation, spectator
chart and weight are derived from the preceding physical unitary. -/
import UnifiedTheory.Audit.KFCausalClockFloorPairedChart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates (pairedCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPairedChart
open UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart (backward backward_continuous backward_compact)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chartIso)
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (amplitude amplitude_positive)
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback (amplitude_continuous)

variable (ε : ℝ) (hε : 0 < ε)

def clockInverse (y : Block 4) : ℝ := (chartIso ε hε).symm (y 0)
def dilation (y : Block 4) : ℝ := Real.exp (clockInverse ε hε y/2)
def inverseWeight (y : Block 4) : ℂ := (amplitude ε (clockInverse ε hε y):ℂ)⁻¹

theorem clockInverse_continuous : Continuous (clockInverse ε hε) :=
  (chartIso ε hε).symm.toHomeomorph.continuous.comp (by fun_prop)

theorem dilation_continuous : Continuous (dilation ε hε) :=
  Real.continuous_exp.comp ((clockInverse_continuous ε hε).div_const 2)

theorem dilation_positive (y : Block 4) : 0 < dilation ε hε y := Real.exp_pos _

theorem inverseWeight_continuous : Continuous (inverseWeight ε hε) := by
  apply (Complex.continuous_ofReal.comp ((amplitude_continuous ε).comp (clockInverse_continuous ε hε))).inv₀
  intro y
  exact Complex.ofReal_ne_zero.mpr (amplitude_positive ε _ hε).ne'

theorem pair_symm_clock (x : Block 2 × Block 4) : (pair.symm x).1 = x.2 0 := by
  have he := congrArg (fun w : Block 2 × Block 4 => w.2 0) (pair.apply_symm_apply x)
  exact he

def inverseMap (x : Block 2 × Block 4) : Block 2 × Block 4 :=
  pair ((coordinateHomeomorph ε hε).symm (pair.symm x))

theorem inverseMap_apply (x : Block 2 × Block 4) :
    inverseMap ε hε x = (dilation ε hε x.2 • x.1,backward ε hε x.2) := by
  have he := pair_coordinate_inverse ε hε (pair.symm x)
  simpa only [MeasurableEquiv.apply_symm_apply,pair_symm_clock] using he

theorem inverseMap_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (inverseMap ε hε) volume volume :=
  pair_preserves_volume.quasiMeasurePreserving.comp
    ((coordinate_inverse_quasiMeasurePreserving ε hε).comp pair_preserves_volume.symm.quasiMeasurePreserving)

def straighten : ProductHilbert 2 4 ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  pairedCoordinates.symm.trans ((coordinates ε hε).symm.trans pairedCoordinates)

theorem straighten_coe (f : ProductHilbert 2 4) :
    straighten ε hε f =ᵐ[volume] fun x => inverseWeight ε hε x.2*f (inverseMap ε hε x) := by
  filter_upwards [paired_coe ((coordinates ε hε).symm (pairedCoordinates.symm f)),
    pair_preserves_volume.symm.quasiMeasurePreserving.ae
      (coordinates_inverse_coe ε hε (pairedCoordinates.symm f)),
    ((coordinate_inverse_quasiMeasurePreserving ε hε).comp
      pair_preserves_volume.symm.quasiMeasurePreserving).ae (paired_inverse_coe f)] with x hp hw hf
  change pairedCoordinates ((coordinates ε hε).symm (pairedCoordinates.symm f)) x = _
  rw [hp,hw]
  unfold inverseFunction
  simp only [Function.comp_apply] at hf
  rw [hf]
  change ((amplitude ε ((chartIso ε hε).symm (pair.symm x).1):ℂ)⁻¹)*f (inverseMap ε hε x) = _
  rw [pair_symm_clock]
  rfl

def weightedSpectator (b : Block 4 → ℂ) (y : Block 4) : ℂ :=
  inverseWeight ε hε y*b (backward ε hε y)

theorem weightedSpectator_continuous (b : Block 4 → ℂ) (hb : Continuous b) :
    Continuous (weightedSpectator ε hε b) :=
  (inverseWeight_continuous ε hε).mul (hb.comp (backward_continuous ε hε))

theorem weightedSpectator_compact (b : Block 4 → ℂ) (hb : HasCompactSupport b) :
    HasCompactSupport (weightedSpectator ε hε b) := (backward_compact ε hε b hb).mul_left

theorem jacobian_cancel (y : Block 4) :
    (((dilation ε hε y)^2)⁻¹:ℝ) • inverseWeight ε hε y =
      (Real.sqrt (Real.exp (clockInverse ε hε y)+ε):ℂ)⁻¹ := by
  have he : (dilation ε hε y)^2 = Real.exp (clockInverse ε hε y) := by
    rw [dilation,pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he,inverseWeight,amplitude,Real.exp_neg,Complex.ofReal_mul,Complex.ofReal_inv,Complex.real_smul]
  have hn : (Real.exp (clockInverse ε hε y):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  simp only [Complex.ofReal_inv,mul_inv_rev,inv_inv]
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

#print axioms clockInverse_continuous
#print axioms dilation_continuous
#print axioms dilation_positive
#print axioms inverseWeight_continuous
#print axioms pair_symm_clock
#print axioms inverseMap_apply
#print axioms inverseMap_quasiMeasurePreserving
#print axioms straighten_coe
#print axioms weightedSpectator_continuous
#print axioms weightedSpectator_compact
#print axioms jacobian_cancel

end
end UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
