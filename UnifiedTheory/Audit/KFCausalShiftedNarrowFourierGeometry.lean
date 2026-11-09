/- Narrow charged coordinates at a complex clock shift. The neutral
coordinate and mixed field are spectators; their shear is retained. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierPackets
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredNeutralPowers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowFourierGeometry
noncomputable section
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalReciprocalGaussianStates (quadratic)

def reconstruct (u : Block 2) (v : Block 4) : Transverse :=
  ![scale*(u 0+v 1),scale*(u 0-v 1),scale*(u 1+v 2),scale*(v 2-u 1),v 3]

def neutral (r : ℂ) (v : Block 4) : ℂ :=
  (v 3:ℂ)+4*(scale:ℂ)*(r-1)*(v 2:ℂ)

def mixedField (t : ℂ) (v : Block 4) : ℂ :=
  (v 3:ℂ)+2*(scale:ℂ)*(3*t-2)*(v 2:ℂ)

def broadRadius (v : Block 4) : ℝ := (v 1)^2+(v 2)^2

def radius (A : ℂ) (u : Block 2) (v : Block 4) : ℂ :=
  (Real.pi:ℂ)^2/A*(‖u‖:ℂ)^2+A*(broadRadius v:ℂ)

theorem narrow_norm_square (u : Block 2) : ‖u‖^2 = (u 0)^2+(u 1)^2 := by
  simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]

theorem reconstruct_quadratic (w : ℝ) (u : Block 2) (v : Block 4) :
    quadratic w (reconstruct u v) = ‖u‖^2/w+w*broadRadius v := by
  rw [narrow_norm_square]
  dsimp [quadratic,KFCausalQuarticChargeProfiles.chargedRadius,
    KFCausalChargedPairCoordinates.pairPolynomial,reconstruct,broadRadius]
  ring_nf
  rw [scale_square]
  ring

theorem reconstruct_neutral (r : ℂ) (u : Block 2) (v : Block 4) :
    KFCausalRelativeGaussianDifferential.position r (reconstruct u v) 4 = neutral r v := by
  dsimp [KFCausalRelativeGaussianDifferential.position,reconstruct,neutral]
  push_cast
  ring

theorem reconstruct_field (t : ℂ) (u : Block 2) (v : Block 4) :
    KFCausalMixedFieldClockBounds.field t (reconstruct u v) = mixedField t v := by
  dsimp [KFCausalMixedFieldClockBounds.field,reconstruct,mixedField]
  push_cast
  ring

theorem broadRadius_nonnegative (v : Block 4) : 0 ≤ broadRadius v := by
  unfold broadRadius
  positivity

theorem radius_re (A : ℂ) (u : Block 2) (v : Block 4) :
    (radius A u v).re = (Real.pi^2*A.re/Complex.normSq A)*‖u‖^2+A.re*broadRadius v := by
  simp only [radius,div_eq_mul_inv,← Complex.ofReal_pow,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.inv_re,
    zero_mul,mul_zero,sub_zero]
  ring

theorem radius_re_nonnegative (A : ℂ) (hA : 0 ≤ A.re) (u : Block 2) (v : Block 4) :
    0 ≤ (radius A u v).re := by
  rw [radius_re]
  have := broadRadius_nonnegative v
  have := Complex.normSq_nonneg A
  positivity

theorem shifted_coefficient_positive (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) :
    0 < ((α:ℂ)*(KFCausalClockFloorRelativeShift.scale ε y s)^2).re := by
  have hs := KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy
  simpa only [pow_two,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using mul_pos hα hs

#print axioms narrow_norm_square
#print axioms reconstruct_quadratic
#print axioms reconstruct_neutral
#print axioms reconstruct_field
#print axioms broadRadius_nonnegative
#print axioms radius_re
#print axioms radius_re_nonnegative
#print axioms shifted_coefficient_positive
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowFourierGeometry
