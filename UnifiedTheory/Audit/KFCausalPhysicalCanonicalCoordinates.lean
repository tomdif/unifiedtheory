/- The existing volume-preserving flattening intertwines every physical
canonical Weyl test with its six-dimensional Euclidean counterpart. -/
import UnifiedTheory.Audit.KFCausalEuclideanConfiguration
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPhysicalCanonicalCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def coordinateMap : Space →L[ℝ] Configuration where
  toFun := split
  map_add' x y := by
    apply Prod.ext
    · rfl
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · rfl
  cont := by
    change Continuous (fun x : Space => (x 0,fun i : Fin 5 => x i.succ))
    fun_prop

def frequency (z : Frequency (X := Configuration)) : Frequency (X := Space) :=
  (z.1.comp coordinateMap,split.symm z.2)

theorem split_translated (x : Space) (h : ℝ) (v : Configuration) :
    split (x+h • split.symm v) = split x+h • v := by
  change coordinateMap (x+h • split.symm v) = coordinateMap x+h • v
  rw [map_add,map_smul]
  change coordinateMap x+h • split (split.symm v) = _
  rw [split.apply_symm_apply]

theorem operator_coordinates (h : ℝ) (z : Frequency (X := Configuration)) (f : Hilbert) :
    operator volume h (frequency z) (euclideanPullback f) = euclideanPullback (operator volume h z f) := by
  apply Lp.ext
  filter_upwards [operator_coe volume h (frequency z) (euclideanPullback f),
    (KFCausalLpPhaseTranslation.shift_preserves volume (h • (frequency z).2)).quasiMeasurePreserving.ae (euclideanPullback_coe f),
    euclideanPullback_coe (operator volume h z f),
    split_preserves_volume.quasiMeasurePreserving.ae (operator_coe volume h z f)] with x hw hf hp ho
  change euclideanPullback f (x+h • (frequency z).2) = f (split (x+h • (frequency z).2)) at hf
  change operator volume h z f (split x) = _ at ho
  rw [hw,hf,hp]
  simp only [Function.comp_apply]
  rw [ho]
  change scalar (z.1 (split x))*f (split (x+h • split.symm z.2)) = _
  rw [split_translated]

theorem characteristic_coordinates (h : ℝ) (z : Frequency (X := Configuration)) (f : Hilbert) :
    characteristic volume h (euclideanPullback f) (frequency z) = characteristic volume h f z := by
  unfold characteristic
  rw [operator_coordinates,euclideanPullback.inner_map_map]

#print axioms split_translated
#print axioms operator_coordinates
#print axioms characteristic_coordinates

end
end UnifiedTheory.Audit.KFCausalPhysicalCanonicalCoordinates
