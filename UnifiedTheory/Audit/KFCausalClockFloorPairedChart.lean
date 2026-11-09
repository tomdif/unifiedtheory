/- The existing physical clock coordinate map in paired position
coordinates. This identifies its antisymmetric dilation and its spectator
homeomorphism, with whole-L2 paired-coordinate representatives. -/
import UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart
import UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorPairedChart
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block ProductHilbert coordinates split split_preserves_volume)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square modeIsometry modePullback mode_preserves_volume)
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates (pairedCoordinates)
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates (positionCoordinates_coe)
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback (unitaryPullback_symm_coe)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso)

def pair : Configuration ≃ᵐ (Block 2 × Block 4) :=
  KFCausalEuclideanConfiguration.split.symm.trans
    (modeIsometry.toMeasurableEquiv.trans (split 2 4))

theorem pair_preserves_volume : MeasurePreserving pair :=
  ((split_preserves_volume 2 4).comp mode_preserves_volume).comp
    KFCausalEuclideanConfiguration.split_preserves_volume.symm

theorem pair_apply (x : Configuration) : pair x =
    (WithLp.toLp 2 ![scale*(x.2 0-x.2 1),scale*(x.2 2-x.2 3)],
      WithLp.toLp 2 ![x.1,scale*(x.2 0+x.2 1),scale*(x.2 2+x.2 3),x.2 4]) := rfl

theorem pair_clock (x : Configuration) : (pair x).2 0 = x.1 := rfl

theorem paired_inverse_coe (f : ProductHilbert 2 4) :
    pairedCoordinates.symm f =ᵐ[volume] fun x => f (pair x) := by
  have he : pairedCoordinates.symm f = euclideanPullback.symm (modePullback (coordinates 2 4 f)) := rfl
  rw [he]
  filter_upwards [unitaryPullback_symm_coe KFCausalEuclideanConfiguration.split
    KFCausalEuclideanConfiguration.split_preserves_volume (modePullback (coordinates 2 4 f)),
    KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae
      (positionCoordinates_coe f)] with x hx hp
  exact hx.trans hp

theorem paired_coe (f : Hilbert) : pairedCoordinates f =ᵐ[volume] fun x => f (pair.symm x) := by
  have he := paired_inverse_coe (pairedCoordinates f)
  rw [LinearIsometryEquiv.symm_apply_apply] at he
  filter_upwards [pair_preserves_volume.symm.quasiMeasurePreserving.ae he] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx.symm

theorem pair_changeClock (q : ℝ) (x : Configuration) :
    pair (q,x.2) = ((pair x).1,KFCausalClockFloorSpectatorChart.changeClock q (pair x).2) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem pair_flow (t : ℝ) (x : Configuration) :
    pair (x.1,KFCausalTransverseDilationFlow.flow t x.2) =
      (Real.exp (t/2) • (pair x).1,KFCausalClockFloorSpectatorChart.flow t (pair x).2) := by
  rw [pair_apply,pair_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [KFCausalTransverseDilationFlow.flow,KFCausalTransverseDilationFlow.scale] <;> ring
  · ext i
    fin_cases i <;> simp [KFCausalTransverseDilationFlow.flow,KFCausalTransverseDilationFlow.scale,
      KFCausalClockFloorSpectatorChart.flow] <;> ring_nf
    rw [scale_square]
    ring

theorem pair_coordinate (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    pair (coordinateHomeomorph ε hε x) =
      (Real.exp (-x.1/2) • (pair x).1,KFCausalClockFloorSpectatorChart.forward ε (pair x).2) := by
  change pair (chart ε x.1,KFCausalTransverseDilationFlow.flow (-x.1) x.2) = _
  rw [pair_changeClock (chart ε x.1) (x.1,KFCausalTransverseDilationFlow.flow (-x.1) x.2),pair_flow]
  rfl

theorem pair_coordinate_inverse (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    pair ((coordinateHomeomorph ε hε).symm x) =
      (Real.exp ((chartIso ε hε).symm x.1/2) • (pair x).1,
        KFCausalClockFloorSpectatorChart.backward ε hε (pair x).2) := by
  change pair ((chartIso ε hε).symm x.1,
    KFCausalTransverseDilationFlow.flow ((chartIso ε hε).symm x.1) x.2) = _
  rw [pair_changeClock ((chartIso ε hε).symm x.1)
    (x.1,KFCausalTransverseDilationFlow.flow ((chartIso ε hε).symm x.1) x.2),pair_flow]
  rfl

#print axioms pair_preserves_volume
#print axioms pair_apply
#print axioms pair_clock
#print axioms paired_inverse_coe
#print axioms paired_coe
#print axioms pair_changeClock
#print axioms pair_flow
#print axioms pair_coordinate
#print axioms pair_coordinate_inverse

end
end UnifiedTheory.Audit.KFCausalClockFloorPairedChart
