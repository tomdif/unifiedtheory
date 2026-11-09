/- The strip-family operator is actual physical multiplication, after the
proved weighted coordinate change. It therefore preserves every physical
multiplication graph, including unbounded field and clock factors. -/
import UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalStripFamilyPhysicalMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback (weight)
open UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph

variable (ε : ℝ) (hε : 0 < ε)

def physicalSymbol (F : ℂ → TailSpace → ℂ) (y : ℝ) (x : Configuration) : ℂ :=
  symbol F y (split.symm (coordinateHomeomorph ε hε x))

theorem straightening_symm_coe (f : FrequencyHilbert) :
    (straightening ε hε).symm f =ᵐ[volume]
      fun x => weight ε x*f (split.symm (coordinateHomeomorph ε hε x)) := by
  filter_upwards [coordinates_coe ε hε (euclideanPullback.symm f),
    (coordinate_quasiMeasurePreserving ε hε).ae
      (KFCausalMeasureUnitaryPullback.unitaryPullback_symm_coe split split_preserves_volume f)] with x hx hy
  change (coordinates ε hε (euclideanPullback.symm f)) x = _
  rw [hx]
  change weight ε x*(euclideanPullback.symm f) (coordinateHomeomorph ε hε x) = _
  change (euclideanPullback.symm f) (coordinateHomeomorph ε hε x) =
    f (split.symm (coordinateHomeomorph ε hε x)) at hy
  rw [hy]

variable (F : ℂ → TailSpace → ℂ) (d M : ℝ)
  (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace => F ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2))
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ∀ z, ‖F q z‖ ≤ M)

theorem physicalMultiplier_representative (y : ℝ) (hy : |y| ≤ d) (f : Hilbert) :
    physicalMultiplier F d M hC hM hB ε hε y hy f =ᵐ[volume]
      fun x => physicalSymbol ε hε F y x*f x := by
  have hξ := split_preserves_volume.symm.quasiMeasurePreserving.comp
    (coordinate_quasiMeasurePreserving ε hε)
  filter_upwards [straightening_symm_coe ε hε
      (frequencyOperator F d M hC hM hB y hy (straightening ε hε f)),
    straightening_symm_coe ε hε (straightening ε hε f),
    hξ.ae (frequencyOperator_coe F d M hC hM hB y hy (straightening ε hε f))] with x hx hf hm
  change ((straightening ε hε).symm (frequencyOperator F d M hC hM hB y hy (straightening ε hε f))) x = _
  dsimp only [Function.comp_apply] at hm
  rw [hx,hm]
  rw [LinearIsometryEquiv.symm_apply_apply] at hf
  rw [hf]
  unfold physicalSymbol
  ring

theorem preserves_relation (y : ℝ) (hy : |y| ≤ d) (a : Configuration → ℂ) (f g : Hilbert)
    (hfg : g =ᵐ[volume] fun x => a x*f x) :
    physicalMultiplier F d M hC hM hB ε hε y hy g =ᵐ[volume]
      fun x => a x*physicalMultiplier F d M hC hM hB ε hε y hy f x := by
  filter_upwards [physicalMultiplier_representative ε hε F d M hC hM hB y hy f,
    physicalMultiplier_representative ε hε F d M hC hM hB y hy g,hfg] with x hf hg hx
  rw [hf,hg,hx]
  ring

#print axioms straightening_symm_coe
#print axioms physicalMultiplier_representative
#print axioms preserves_relation

end
end UnifiedTheory.Audit.KFCausalStripFamilyPhysicalMultiplier
