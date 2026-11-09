/- Separate the clock coordinate from the five transverse Euclidean
coordinates, preserving the actual volume and splitting the Fourier phase. -/
import UnifiedTheory.Audit.KFCausalEuclideanConfiguration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalEuclideanClockSplit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration

abbrev TailSpace := EuclideanSpace ℝ (Fin 5)

def transverseCoordinates : Transverse ≃ᵐ TailSpace := MeasurableEquiv.toLp 2 (Fin 5 → ℝ)

theorem transverse_preserves_volume : MeasurePreserving transverseCoordinates :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 5)).symm

def euclideanSplit : Space ≃ᵐ (ℝ × TailSpace) :=
  split.trans ((MeasurableEquiv.refl ℝ).prodCongr transverseCoordinates)

theorem euclideanSplit_preserves_volume : MeasurePreserving euclideanSplit :=
  ((MeasurePreserving.id (volume : Measure ℝ)).prod transverse_preserves_volume).comp split_preserves_volume

def tail (x : Space) : TailSpace := WithLp.toLp 2 (fun i : Fin 5 => x i.succ)

theorem euclideanSplit_apply (x : Space) : euclideanSplit x = (x 0,tail x) := rfl

theorem euclideanSplit_symm_apply (q : ℝ) (y : TailSpace) :
    ((euclideanSplit.symm (q,y)) 0,tail (euclideanSplit.symm (q,y))) = (q,y) :=
  euclideanSplit.apply_symm_apply (q,y)

theorem inner_split (x k : Space) :
    inner ℝ x k = x 0*k 0+inner ℝ (tail x) (tail k) := by
  rw [PiLp.inner_apply,Fin.sum_univ_succ]
  simp only [PiLp.inner_apply,tail,RCLike.inner_apply,conj_trivial]
  congr 1
  exact mul_comm _ _

#print axioms transverse_preserves_volume
#print axioms euclideanSplit_preserves_volume
#print axioms euclideanSplit_apply
#print axioms euclideanSplit_symm_apply
#print axioms inner_split

end
end UnifiedTheory.Audit.KFCausalEuclideanClockSplit
