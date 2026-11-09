/- A volume-preserving regrouping of the five transverse coordinates
identifies the actual physical L2 space with the space used in the full
clock-floor Gaussian estimates. -/
import UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Charged Grouped)
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

def transverseGrouping : Transverse ≃ᵐ Grouped :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) (Fin.last 4)).trans
    MeasurableEquiv.prodComm

theorem transverseGrouping_apply (x : Transverse) :
    transverseGrouping x = (fun i : Fin 4 => x i.castSucc,x 4) := by
  change (fun i : Fin 4 => x ((Fin.last 4).succAbove i),x 4) = _
  rw [Fin.succAbove_last]

theorem transverseGrouping_symm_apply (x : Grouped) :
    transverseGrouping.symm x = ![x.1 0,x.1 1,x.1 2,x.1 3,x.2] := by
  apply transverseGrouping.injective
  rw [MeasurableEquiv.apply_symm_apply,transverseGrouping_apply]
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem transverseGrouping_preserves_volume : MeasurePreserving transverseGrouping := by
  exact measurePreserving_swap.comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 5 => ℝ) (Fin.last 4))

def grouping : Configuration ≃ᵐ (ℝ × Grouped) :=
  (MeasurableEquiv.refl ℝ).prodCongr transverseGrouping

theorem grouping_preserves_volume : MeasurePreserving grouping :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod transverseGrouping_preserves_volume

theorem grouping_symm_apply (z : ℝ × Grouped) :
    grouping.symm z = (z.1,![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]) := by
  change (z.1,transverseGrouping.symm z.2) = _
  rw [transverseGrouping_symm_apply]

abbrev GroupedHilbert := Lp ℂ 2 (volume : Measure (ℝ × Grouped))

def groupedCoordinates : Hilbert ≃ₗᵢ[ℂ] GroupedHilbert :=
  (unitaryPullback grouping grouping_preserves_volume).symm

theorem groupedCoordinates_coe (f : Hilbert) :
    groupedCoordinates f =ᵐ[volume] f ∘ grouping.symm :=
  unitaryPullback_symm_coe grouping grouping_preserves_volume f

theorem groupedCoordinates_norm (f : Hilbert) : ‖groupedCoordinates f‖ = ‖f‖ :=
  groupedCoordinates.norm_map f

#print axioms transverseGrouping_apply
#print axioms transverseGrouping_symm_apply
#print axioms transverseGrouping_preserves_volume
#print axioms grouping_preserves_volume
#print axioms grouping_symm_apply
#print axioms groupedCoordinates_coe
#print axioms groupedCoordinates_norm

end
end UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
