/- Fixed-width Gaussian estimates for the actual four charged and one
neutral directions. These control the shear without discarding the
displaced centre or the neutral momentum. -/
import UnifiedTheory.Audit.KFCausalClockFloorCenteredDensityLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredGaussian (realQuadratic weight)
open UnifiedTheory.Audit.KFCausalClockFloorRescaledDisplacement (shearVector)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase (shear)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)

def energy (X : Transverse) : ℝ := realQuadratic (groundWidth 1) (neutralWidth 1) X

theorem energy_eq (X : Transverse) :
    energy X = (X 0^2+X 1^2+X 2^2+X 3^2)/2+X 4^2/64 := by
  simp [energy,realQuadratic,weight,groundWidth,neutralWidth,Fin.sum_univ_succ]
  ring

theorem energy_nonnegative (X : Transverse) : 0 ≤ energy X := by rw [energy_eq]; positivity

theorem energy_lower (X : Transverse) : (∑ i, X i^2)/64 ≤ energy X := by
  rw [energy_eq]
  simp [Fin.sum_univ_succ]
  nlinarith only [sq_nonneg (X 0),sq_nonneg (X 1),sq_nonneg (X 2),sq_nonneg (X 3)]

theorem energy_shearVector (X : Transverse) : energy (shearVector X) ≤ 2*energy X := by
  simp [energy_eq,shearVector]
  nlinarith [sq_nonneg (X 0),sq_nonneg (X 1),sq_nonneg (X 4),sq_nonneg (X 2-X 3)]

theorem energy_add_scale (Q ξ : Transverse) (σ : ℝ) :
    energy (fun i => Q i+σ*ξ i) ≤ 2*energy Q+2*σ^2*energy ξ := by
  simp only [energy_eq]
  nlinarith only [sq_nonneg (Q 0-σ*ξ 0),sq_nonneg (Q 1-σ*ξ 1),
    sq_nonneg (Q 2-σ*ξ 2),sq_nonneg (Q 3-σ*ξ 3),sq_nonneg (Q 4-σ*ξ 4)]

def coefficients (P : Transverse) : Transverse := ![P 0/2,P 1/2,P 2/2+P 4,P 3/2+P 4,0]
def momentumBound (P : Transverse) : ℝ := 64*∑ i, (coefficients P i)^2

theorem momentumBound_nonnegative (P : Transverse) : 0 ≤ momentumBound P := by
  unfold momentumBound
  positivity

theorem shear_coefficients (X P : Transverse) : shear X P = ∑ i, coefficients P i*X i := by
  simp [shear,velocity,coefficients,Fin.sum_univ_succ]
  ring

theorem shear_square_bound (X P : Transverse) : (shear X P)^2 ≤ momentumBound P*energy X := by
  rw [shear_coefficients]
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (coefficients P) X
  have hn : 0 ≤ ∑ i, (coefficients P i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have he := mul_le_mul_of_nonneg_left (energy_lower X) hn
  unfold momentumBound
  nlinarith

theorem phase_young (D σ : ℝ) (X P : Transverse) :
    4*D*σ*|shear X P| ≤ energy X/4+16*D^2*σ^2*momentumBound P := by
  have hG := energy_nonnegative X
  have hA := momentumBound_nonnegative P
  have hb := mul_le_mul_of_nonneg_left (shear_square_bound X P) (sq_nonneg (4*D*σ))
  have he : (4*D*σ*|shear X P|)^2 ≤ (16*D^2*σ^2*momentumBound P)*energy X := by
    simpa only [mul_pow,sq_abs,show (4:ℝ)^2 = 16 by norm_num,mul_assoc] using hb
  have hK : 0 ≤ 16*D^2*σ^2*momentumBound P := by positivity
  nlinarith only [he,hG,hK,sq_nonneg (energy X/4-16*D^2*σ^2*momentumBound P)]

theorem shear_add_scale (Q ξ P : Transverse) (σ : ℝ) :
    shear (fun i => Q i+σ*ξ i) P = shear Q P+σ*shear ξ P := by
  simp [shear,velocity,Fin.sum_univ_succ]
  ring

#print axioms energy_eq
#print axioms energy_nonnegative
#print axioms energy_lower
#print axioms energy_shearVector
#print axioms energy_add_scale
#print axioms momentumBound_nonnegative
#print axioms shear_coefficients
#print axioms shear_square_bound
#print axioms phase_young
#print axioms shear_add_scale

end
end UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates
