/- The actual physical heat factor and radial neutral-position test in
clock-straightened mixed coordinates, on every L2 state. The coordinate
intertwining and transformed symbols are derived from the original
operators. No clock-exponential graph identity is assumed here. -/
import UnifiedTheory.Audit.KFCausalClockFloorMixedCoordinates
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalClockFloorMixedRadial
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening (straighten)
open UnifiedTheory.Audit.KFCausalClockFloorMixedChart
open UnifiedTheory.Audit.KFCausalClockFloorMixedCoordinates

variable (ε : ℝ) (hε : 0 < ε)

def clockMixed : Hilbert ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  (KFCausalClockFloorUnitaryCoordinates.coordinates ε hε).symm.trans mixedCoordinates

theorem clockMixed_eq (f : Hilbert) :
    clockMixed ε hε f = mixedStraighten ε hε (mixedCoordinates f) := by
  change KFCausalPartialFourier.leftFourier 2 4
    (pairedCoordinates ((KFCausalClockFloorUnitaryCoordinates.coordinates ε hε).symm f)) =
      mixedStraighten ε hε (KFCausalPartialFourier.leftFourier 2 4 (pairedCoordinates f))
  rw [mixedStraighten_leftFourier]
  exact congrArg (fun g => KFCausalPartialFourier.leftFourier 2 4
    (pairedCoordinates ((KFCausalClockFloorUnitaryCoordinates.coordinates ε hε).symm g)))
      (pairedCoordinates.symm_apply_apply f).symm

theorem clockMixed_coe (f : Hilbert) : clockMixed ε hε f =ᵐ[volume]
    fun x => mixedWeight ε hε x*(mixedCoordinates f) (mixedMap ε hε x) := by
  rw [clockMixed_eq]
  exact mixedStraighten_coe ε hε _

theorem charge_relation (m : Joint 2 4 → ℂ) (f g : Hilbert)
    (hfg : chargeCoordinates g =ᵐ[volume] fun x => m x*(chargeCoordinates f) x) :
    mixedCoordinates g =ᵐ[volume] fun x => m ((split 2 4).symm x)*(mixedCoordinates f) x := by
  have he : ∀ᵐ x ∂volume, (mixedCoordinates g) (split 2 4 x) =
      m x*(mixedCoordinates f) (split 2 4 x) := by
    filter_upwards [hfg,coordinates_coe 2 4 (mixedCoordinates f),
      coordinates_coe 2 4 (mixedCoordinates g)] with x hx hf hg
    change (coordinates 2 4 (mixedCoordinates g)) x = m x*(coordinates 2 4 (mixedCoordinates f)) x at hx
    rw [hf,hg] at hx
    exact hx
  have hr := (split_preserves_volume 2 4).symm.quasiMeasurePreserving.ae he
  simpa only [MeasurableEquiv.apply_symm_apply] using hr

theorem clockMixed_relation (m : Joint 2 4 → ℂ) (f g : Hilbert)
    (hfg : chargeCoordinates g =ᵐ[volume] fun x => m x*(chargeCoordinates f) x) :
    clockMixed ε hε g =ᵐ[volume] fun x =>
      m ((split 2 4).symm (mixedMap ε hε x))*(clockMixed ε hε f) x := by
  filter_upwards [clockMixed_coe ε hε f,clockMixed_coe ε hε g,
    (mixedMap_quasiMeasurePreserving ε hε).ae (charge_relation m f g hfg)] with x hf hg hr
  rw [hg,hf,hr]
  ring

open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff

theorem heat_transformed (h δ : ℝ) (hδ : 0 < δ) (f : Hilbert) :
    clockMixed ε hε (heat h δ hδ f) =ᵐ[volume] fun x =>
      heatSymbol h δ ((split 2 4).symm (mixedMap ε hε x))*(clockMixed ε hε f) x :=
  clockMixed_relation ε hε _ f _ (heat_coe h δ hδ f)

theorem radial_transformed (h δ v : ℝ) (hδ : 0 < δ) (f : Hilbert) :
    clockMixed ε hε (action h δ v hδ f) =ᵐ[volume] fun x =>
      symbol h δ v ((split 2 4).symm (mixedMap ε hε x))*(clockMixed ε hε f) x :=
  clockMixed_relation ε hε _ f _ (action_coe h δ v hδ f)

#print axioms clockMixed_eq
#print axioms clockMixed_coe
#print axioms charge_relation
#print axioms clockMixed_relation
#print axioms heat_transformed
#print axioms radial_transformed

end
end UnifiedTheory.Audit.KFCausalClockFloorMixedRadial
