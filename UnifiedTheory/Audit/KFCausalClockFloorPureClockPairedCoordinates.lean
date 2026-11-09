/- The actual pure-clock unitary in paired position coordinates. Only the
spectator clock coordinate changes; the antisymmetric block is untouched. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockLpCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
import UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockPairedCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates (pairedCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPairedChart
open UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening (pair_symm_clock)
open UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart
  (changeClock changeClock_clock changeClock_compose changeClock_self)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates (chartHomeomorph coordinates weight)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockLpCoordinates
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso chart_continuous)

variable (ε : ℝ) (hε : 0 < ε)

def rightForward (y : Block 4) : Block 4 := changeClock (chart ε (y 0)) y
def rightBackward (y : Block 4) : Block 4 := changeClock ((chartIso ε hε).symm (y 0)) y

theorem rightBackward_forward (y : Block 4) : rightBackward ε hε (rightForward ε y) = y := by
  have hc : (chartIso ε hε).symm (chart ε (y 0)) = y 0 := (chartIso ε hε).symm_apply_apply _
  simp only [rightBackward,rightForward,changeClock_clock,hc,changeClock_compose,changeClock_self]

theorem rightForward_backward (y : Block 4) : rightForward ε (rightBackward ε hε y) = y := by
  have hc : chart ε ((chartIso ε hε).symm (y 0)) = y 0 := (chartIso ε hε).apply_symm_apply _
  simp only [rightBackward,rightForward,changeClock_clock,hc,changeClock_compose,changeClock_self]

theorem rightForward_continuous : Continuous (rightForward ε) := by
  have hc := chart_continuous ε
  unfold rightForward changeClock
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun x : Block 4 => chart ε (x 0))
    fun_prop
  · change Continuous (fun x : Block 4 => x 1)
    fun_prop
  · change Continuous (fun x : Block 4 => x 2)
    fun_prop
  · change Continuous (fun x : Block 4 => x 3)
    fun_prop

theorem rightBackward_continuous : Continuous (rightBackward ε hε) := by
  have hc : Continuous ((chartIso ε hε).symm : ℝ → ℝ) := (chartIso ε hε).symm.toHomeomorph.continuous
  unfold rightBackward changeClock
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun x : Block 4 => (chartIso ε hε).symm (x 0))
    fun_prop
  · change Continuous (fun x : Block 4 => x 1)
    fun_prop
  · change Continuous (fun x : Block 4 => x 2)
    fun_prop
  · change Continuous (fun x : Block 4 => x 3)
    fun_prop

def rightHomeomorph : Block 4 ≃ₜ Block 4 where
  toFun := rightForward ε
  invFun := rightBackward ε hε
  left_inv := rightBackward_forward ε hε
  right_inv := rightForward_backward ε hε
  continuous_toFun := rightForward_continuous ε
  continuous_invFun := rightBackward_continuous ε hε

def pairedMap (x : Block 2 × Block 4) : Block 2 × Block 4 :=
  pair (chartHomeomorph ε hε (pair.symm x))

theorem pairedMap_apply (x : Block 2 × Block 4) :
    pairedMap ε hε x = (x.1,rightForward ε x.2) := by
  change pair (chart ε (pair.symm x).1,(pair.symm x).2) = _
  rw [pair_changeClock _ (pair.symm x),MeasurableEquiv.apply_symm_apply,pair_symm_clock]
  rfl

theorem pairedMap_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (pairedMap ε hε) volume volume :=
  pair_preserves_volume.quasiMeasurePreserving.comp
    ((coordinate_quasiMeasurePreserving ε hε).comp pair_preserves_volume.symm.quasiMeasurePreserving)

def pairedUnitary : ProductHilbert 2 4 ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  pairedCoordinates.symm.trans ((coordinates ε hε).trans pairedCoordinates)

def rightWeight (y : Block 4) : ℂ := Real.sqrt (Real.exp (y 0)+ε)

theorem pairedUnitary_coe (f : ProductHilbert 2 4) :
    pairedUnitary ε hε f =ᵐ[volume] fun x => rightWeight ε x.2*f (pairedMap ε hε x) := by
  filter_upwards [paired_coe (coordinates ε hε (pairedCoordinates.symm f)),
    pair_preserves_volume.symm.quasiMeasurePreserving.ae
      (coordinates_coe ε hε (pairedCoordinates.symm f)),
    ((coordinate_quasiMeasurePreserving ε hε).comp
      pair_preserves_volume.symm.quasiMeasurePreserving).ae (paired_inverse_coe f)] with x hp hw hf
  change pairedCoordinates (coordinates ε hε (pairedCoordinates.symm f)) x = _
  rw [hp,hw]
  unfold weightedFunction
  simp only [Function.comp_apply] at hf
  rw [hf]
  change (Real.sqrt (Real.exp (pair.symm x).1+ε):ℂ)*f (pairedMap ε hε x) = _
  rw [pair_symm_clock]
  rfl

def weightedRight (b : Block 4 → ℂ) (y : Block 4) : ℂ := rightWeight ε y*b (rightForward ε y)

theorem weightedRight_continuous (b : Block 4 → ℂ) (hb : Continuous b) :
    Continuous (weightedRight ε b) := by
  have hw : Continuous (rightWeight ε) := by unfold rightWeight; fun_prop
  exact hw.mul (hb.comp (rightForward_continuous ε))

include hε in
theorem weightedRight_compact (b : Block 4 → ℂ) (hb : HasCompactSupport b) :
    HasCompactSupport (weightedRight ε b) := (hb.comp_homeomorph (rightHomeomorph ε hε)).mul_left

#print axioms rightBackward_forward
#print axioms rightForward_backward
#print axioms rightForward_continuous
#print axioms rightBackward_continuous
#print axioms pairedMap_apply
#print axioms pairedMap_quasiMeasurePreserving
#print axioms pairedUnitary_coe
#print axioms weightedRight_continuous
#print axioms weightedRight_compact
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockPairedCoordinates
