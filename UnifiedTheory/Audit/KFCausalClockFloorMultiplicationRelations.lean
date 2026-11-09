/- Arbitrary multiplication relations, including unbounded ones, are
preserved and reflected by the actual weighted clock straightening.
Both directions use proved representatives and preservation of null sets. -/
import UnifiedTheory.Audit.KFCausalStripFamilyPhysicalMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalClockFloorMultiplicationRelations
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates (straightening)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback (weight)
open UnifiedTheory.Audit.KFCausalStripFamilyPhysicalMultiplier (straightening_symm_coe)

variable (ε : ℝ) (hε : 0 < ε)

def symbol (b : Configuration → ℂ) (x : Space) : ℂ :=
  b ((coordinateHomeomorph ε hε).symm (split x))

theorem straightening_coe (f : Hilbert) :
    straightening ε hε f =ᵐ[volume] fun x =>
      (weight ε ((coordinateHomeomorph ε hε).symm (split x)))⁻¹*
        f ((coordinateHomeomorph ε hε).symm (split x)) := by
  filter_upwards [euclideanPullback_coe ((coordinates ε hε).symm f),
    split_preserves_volume.quasiMeasurePreserving.ae (coordinates_inverse_coe ε hε f)] with x hx hy
  exact hx.trans hy

theorem straightening_relation (b : Configuration → ℂ) (f g : Hilbert) :
    (g =ᵐ[volume] fun x => b x*f x) ↔
      straightening ε hε g =ᵐ[volume] fun x => symbol ε hε b x*(straightening ε hε f) x := by
  constructor
  · intro hfg
    filter_upwards [straightening_coe ε hε f,straightening_coe ε hε g,
      ((coordinate_inverse_quasiMeasurePreserving ε hε).comp
        split_preserves_volume.quasiMeasurePreserving).ae hfg] with x hf hg hr
    simp only [Function.comp_apply] at hr
    rw [hf,hg,hr]
    unfold symbol
    ring
  · intro hfg
    filter_upwards [straightening_symm_coe ε hε (straightening ε hε f),
      straightening_symm_coe ε hε (straightening ε hε g),
      (split_preserves_volume.symm.quasiMeasurePreserving.comp
        (coordinate_quasiMeasurePreserving ε hε)).ae hfg] with x hf hg hr
    rw [LinearIsometryEquiv.symm_apply_apply] at hf hg
    simp only [Function.comp_apply,symbol,MeasurableEquiv.apply_symm_apply,Homeomorph.symm_apply_apply] at hr
    rw [hf,hg,hr]
    ring

#print axioms straightening_coe
#print axioms straightening_relation

end
end UnifiedTheory.Audit.KFCausalClockFloorMultiplicationRelations
