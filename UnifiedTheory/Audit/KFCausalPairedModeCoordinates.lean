/- An explicit volume-preserving change from the six real mode coordinates
to two antisymmetric coordinates and four spectator/symmetric coordinates.
Clock and neutral matter coordinates are retained exactly. -/
import UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
import UnifiedTheory.Audit.KFCausalEuclideanConfiguration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPairedModeCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

def scale : ℝ := (Real.sqrt 2)⁻¹

theorem scale_square : scale ^ 2 = 1/2 := by
  rw [scale, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

def forward (x : Space) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl i => ![scale * (x 1-x 2), scale * (x 3-x 4)] i
  | .inr i => ![x 0, scale * (x 1+x 2), scale * (x 3+x 4), x 5] i

def backward (y : Joint 2 4) : Space :=
  WithLp.toLp 2 ![y (.inr 0), scale * (y (.inr 1)+y (.inl 0)),
    scale * (y (.inr 1)-y (.inl 0)), scale * (y (.inr 2)+y (.inl 1)),
    scale * (y (.inr 2)-y (.inl 1)), y (.inr 3)]

theorem backward_forward (x : Space) : backward (forward x) = x := by
  ext i
  fin_cases i <;> simp [backward, forward]
  all_goals ring_nf; rw [scale_square]; ring

theorem forward_backward (y : Joint 2 4) : forward (backward y) = y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [backward, forward]
  all_goals ring_nf; rw [scale_square]; ring

def modeEquiv : Space ≃ₗ[ℝ] Joint 2 4 where
  toFun := forward
  invFun := backward
  left_inv := backward_forward
  right_inv := forward_backward
  map_add' x y := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [forward] <;> ring
  map_smul' c x := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [forward] <;> ring

theorem modeEquiv_inner (x y : Space) : inner ℝ (modeEquiv x) (modeEquiv y) = inner ℝ x y := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
  simp [modeEquiv, forward, RCLike.inner_apply]
  ring_nf
  rw [scale_square]
  ring

def modeIsometry : Space ≃ₗᵢ[ℝ] Joint 2 4 where
  toLinearEquiv := modeEquiv
  norm_map' := (modeEquiv.toLinearMap.isometryOfInner modeEquiv_inner).norm_map

theorem mode_preserves_volume : MeasurePreserving modeIsometry := modeIsometry.measurePreserving

theorem antisymmetric_coordinates (x : Space) :
    (split 2 4 (modeIsometry x)).1 =
      WithLp.toLp 2 ![scale * (x 1-x 2), scale * (x 3-x 4)] := rfl

theorem symmetric_coordinates (x : Space) :
    (split 2 4 (modeIsometry x)).2 =
      WithLp.toLp 2 ![x 0, scale * (x 1+x 2), scale * (x 3+x 4), x 5] := rfl

def modePullback : JointHilbert 2 4 ≃ₗᵢ[ℂ] FrequencyHilbert :=
  unitaryPullback modeIsometry.toMeasurableEquiv mode_preserves_volume

theorem modePullback_coe (f : JointHilbert 2 4) :
    modePullback f =ᵐ[volume] f ∘ modeIsometry :=
  unitaryPullback_coe _ _ _

#print axioms scale_square
#print axioms backward_forward
#print axioms forward_backward
#print axioms modeEquiv_inner
#print axioms modeIsometry
#print axioms mode_preserves_volume
#print axioms antisymmetric_coordinates
#print axioms symmetric_coordinates
#print axioms modePullback
#print axioms modePullback_coe

end
end UnifiedTheory.Audit.KFCausalPairedModeCoordinates
