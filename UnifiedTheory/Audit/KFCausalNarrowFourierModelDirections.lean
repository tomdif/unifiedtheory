/- The actual four model momentum directions in narrow Fourier coordinates,
and proved linear-growth bounds for their frequency and position factors. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierPackets
import UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierModelDirections
noncomputable section
open KFCausalEuclideanProductCoordinates (Block split)
open KFCausalNarrowFourierCoordinates (modeIsometry narrow_coordinates spectator_coordinates)
open KFCausalNarrowFourierPackets (chargedRadius chargedRadius_nonnegative)
open KFCausalPairedModeCoordinates (scale)
open KFCausalPhysicalTransverseMomentum (transverseVector)
open KFCausalPhysicalEnergyFactors (modelDirections)

def leftDirection (j : Fin 4) : Block 2 := WithLp.toLp 2
  (![![2*scale,0],![0,0],![0,0],![0,2*scale]] j)
def rightDirection (j : Fin 4) : Block 4 := WithLp.toLp 2
  (![![0,0,0,0],![0,0,2*scale,1],![0,2*scale,0,0],![0,0,0,0]] j)

theorem model_direction (j : Fin 4) :
    split 2 4 (modeIsometry (transverseVector (modelDirections j))) =
      (leftDirection j,rightDirection j) := by
  have hv (v : KFCausalTransverseDilationFlow.Transverse) :
      transverseVector v = WithLp.toLp 2 ![0,v 0,v 1,v 2,v 3,v 4] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  apply Prod.ext
  · rw [narrow_coordinates]
    ext i
    fin_cases j <;> fin_cases i <;> simp [leftDirection,modelDirections] <;> ring
  · rw [spectator_coordinates]
    ext i
    fin_cases j <;> fin_cases i <;> simp [rightDirection,modelDirections] <;> ring

theorem left_square_le (α : ℝ) (hα : 0 < α) (z : Block 2 × Block 4) (i : Fin 2) :
    (Real.pi^2/α)*(z.1 i)^2 ≤ chargedRadius α z := by
  have h0 := mul_nonneg (show 0 ≤ Real.pi^2/α by positivity) (sq_nonneg (z.1 0))
  have h1 := mul_nonneg (show 0 ≤ Real.pi^2/α by positivity) (sq_nonneg (z.1 1))
  have h2 := mul_nonneg hα.le (sq_nonneg (z.2 1))
  have h3 := mul_nonneg hα.le (sq_nonneg (z.2 2))
  fin_cases i
  · change (Real.pi^2/α)*(z.1 0)^2 ≤ _
    unfold chargedRadius
    nlinarith
  · change (Real.pi^2/α)*(z.1 1)^2 ≤ _
    unfold chargedRadius
    nlinarith

theorem right_square_le (α : ℝ) (hα : 0 < α) (z : Block 2 × Block 4) (i : Fin 2) :
    α*(z.2 i.castSucc.succ)^2 ≤ chargedRadius α z := by
  have h0 := mul_nonneg (show 0 ≤ Real.pi^2/α by positivity) (sq_nonneg (z.1 0))
  have h1 := mul_nonneg (show 0 ≤ Real.pi^2/α by positivity) (sq_nonneg (z.1 1))
  have h2 := mul_nonneg hα.le (sq_nonneg (z.2 1))
  have h3 := mul_nonneg hα.le (sq_nonneg (z.2 2))
  fin_cases i
  · change α*(z.2 1)^2 ≤ _
    unfold chargedRadius
    nlinarith
  · change α*(z.2 2)^2 ≤ _
    unfold chargedRadius
    nlinarith

theorem coordinate_growth (a x t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hx : a*x^2 ≤ t) :
    |x| ≤ (1+1/a)*(1+t) := by
  have h1 : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have h2 : x^2 ≤ t/a := (le_div_iff₀ ha).mpr (by nlinarith only [hx])
  have h3 : 0 ≤ 1/a := by positivity
  rw [div_eq_mul_one_div] at h2
  nlinarith

theorem left_coordinate_bound (α : ℝ) (hα : 0 < α) (z : Block 2 × Block 4) (i : Fin 2) :
    ‖(z.1 i:ℂ)‖ ≤ (1+1/(Real.pi^2/α))*(1+chargedRadius α z) := by
  simpa only [Complex.norm_real,Real.norm_eq_abs] using coordinate_growth (Real.pi^2/α) (z.1 i)
    (chargedRadius α z) (by positivity) (chargedRadius_nonnegative α hα z) (left_square_le α hα z i)

theorem right_coordinate_bound (α : ℝ) (hα : 0 < α) (z : Block 2 × Block 4) (i : Fin 2) :
    ‖(z.2 i.castSucc.succ:ℂ)‖ ≤ (1+1/α)*(1+chargedRadius α z) := by
  simpa only [Complex.norm_real,Real.norm_eq_abs] using coordinate_growth α (z.2 i.castSucc.succ)
    (chargedRadius α z) hα (chargedRadius_nonnegative α hα z) (right_square_le α hα z i)

#print axioms model_direction
#print axioms left_square_le
#print axioms right_square_le
#print axioms coordinate_growth
#print axioms left_coordinate_bound
#print axioms right_coordinate_bound
end
end UnifiedTheory.Audit.KFCausalNarrowFourierModelDirections
