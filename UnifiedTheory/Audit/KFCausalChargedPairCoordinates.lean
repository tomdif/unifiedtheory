/- Real sum/difference coordinates for the paired quadratic excitation
of the actual complex shifted Gaussian. The real shear has determinant
minus two, including at zero imaginary shift. -/
import UnifiedTheory.Audit.KFCausalChargedPairIntegral
import UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
import UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalChargedPairCoordinates
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalRelativeGaussianDifferential (position exponent)
open KFCausalMatterOrderedDomain (pointField)

def coordinates (r : ℂ) (q : Transverse) : Transverse :=
  ![q 0,q 1,q 2+q 3,q 2-q 3,q 4+2*(r.re-1)*(q 2+q 3)]

def reconstruct (r : ℂ) (u : Transverse) : Transverse :=
  ![u 0,u 1,(u 2+u 3)/2,(u 2-u 3)/2,u 4-2*(r.re-1)*u 2]

def narrowWidth (α β : ℝ) (r : ℂ) : ℝ := α*(r.re^2-r.im^2)-8*β*r.im^2
def wideWidth (α : ℝ) (r : ℂ) : ℝ := α*(r.re^2-r.im^2)
def fieldSlope (r : ℂ) : ℝ := 3-2*r.re
def pairPolynomial (q : Transverse) : ℝ := q 0*q 1-q 2*q 3
def quadratic (α β : ℝ) (r : ℂ) (u : Transverse) : ℝ :=
  2*wideWidth α r*((u 0)^2+(u 1)^2)+narrowWidth α β r*(u 2)^2+
    wideWidth α r*(u 3)^2+2*β*(u 4)^2

theorem reconstruct_coordinates (r : ℂ) (q : Transverse) :
    reconstruct r (coordinates r q) = q := by
  funext i
  fin_cases i <;> simp [reconstruct,coordinates]

theorem coordinates_reconstruct (r : ℂ) (u : Transverse) :
    coordinates r (reconstruct r u) = u := by
  funext i
  fin_cases i <;> simp [reconstruct,coordinates] <;> ring

theorem field_reconstruct (r : ℂ) (u : Transverse) :
    pointField (reconstruct r u) = u 4+fieldSlope r*u 2 := by
  change (u 2+u 3)/2+(u 2-u 3)/2+(u 4-2*(r.re-1)*u 2) = _
  unfold fieldSlope
  ring

theorem pair_reconstruct (r : ℂ) (u : Transverse) :
    pairPolynomial (reconstruct r u) = u 0*u 1-((u 2)^2-(u 3)^2)/4 := by
  change u 0*u 1-((u 2+u 3)/2)*((u 2-u 3)/2) =
    u 0*u 1-((u 2)^2-(u 3)^2)/4
  ring

theorem shifted_pair (r : ℂ) (q : Transverse) :
    position r q 0*position r q 1-position r q 2*position r q 3 =
      r^2*(pairPolynomial q:ℂ) := by
  change (r*(q 0:ℂ))*(r*(q 1:ℂ))-(r*(q 2:ℂ))*(r*(q 3:ℂ)) =
    r^2*((q 0*q 1-q 2*q 3:ℝ):ℂ)
  push_cast
  ring

theorem exponent_reconstruct (α β : ℝ) (r : ℂ) (u : Transverse) :
    2*(exponent α β 0 r (reconstruct r u)).re = -quadratic α β r u := by
  simp only [exponent,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_sub,Fin.sum_univ_succ]
  change 2*(-((α:ℂ)*(r*(u 0:ℂ))^2+
    ((α:ℂ)*(r*(u 1:ℂ))^2+
    ((α:ℂ)*(r*(((u 2+u 3)/2:ℝ):ℂ))^2+
    ((α:ℂ)*(r*(((u 2-u 3)/2:ℝ):ℂ))^2+
    ((β:ℂ)*(((u 4-2*(r.re-1)*u 2:ℝ):ℂ)+
      2*(r-1)*((((u 2+u 3)/2:ℝ):ℂ)+(((u 2-u 3)/2:ℝ):ℂ)))^2+0)))))).re =
    -quadratic α β r u
  simp only [quadratic,narrowWidth,wideWidth,pow_two,
    Complex.neg_re,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.one_im,Complex.re_ofNat,Complex.im_ofNat,Complex.zero_re]
  ring

theorem gaussian_norm_reconstruct (α β : ℝ) (r : ℂ) (u : Transverse) :
    ‖Complex.exp (exponent α β 0 r (reconstruct r u))‖^2 =
      Real.exp (-quadratic α β r u) := by
  rw [Complex.norm_exp,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [exponent_reconstruct]

def coordinateMatrix (r : ℂ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1,0,0,0,0; 0,1,0,0,0; 0,0,1,1,0; 0,0,1,-1,0;
    0,0,2*(r.re-1),2*(r.re-1),1]

def coordinateMap (r : ℂ) : Transverse →ₗ[ℝ] Transverse :=
  (coordinateMatrix r).toLin'

theorem coordinateMap_apply (r : ℂ) (q : Transverse) :
    coordinateMap r q = coordinates r q := by
  funext i
  fin_cases i <;> simp [coordinateMap,coordinateMatrix,coordinates,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

def coordinateEquiv (r : ℂ) : Transverse ≃ₗ[ℝ] Transverse :=
  { coordinateMap r with
    invFun := reconstruct r
    left_inv := fun q => by
      change reconstruct r (coordinateMap r q) = q
      rw [coordinateMap_apply,reconstruct_coordinates]
    right_inv := fun u => by
      change coordinateMap r (reconstruct r u) = u
      rw [coordinateMap_apply,coordinates_reconstruct] }

theorem coordinateMap_det (r : ℂ) : LinearMap.det (coordinateMap r) = -2 := by
  rw [coordinateMap,LinearMap.det_toLin']
  norm_num [coordinateMatrix,Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Matrix.cons_val_two]

theorem coordinates_volume (r : ℂ) :
    Measure.map (coordinates r) volume =
      ENNReal.ofReal (1/2) • (volume : Measure Transverse) := by
  have hd : LinearMap.det (coordinateMap r) ≠ 0 := by rw [coordinateMap_det]; norm_num
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi hd
  simpa only [coordinateMap_det,show |(-2:ℝ)⁻¹|=1/2 by norm_num,
    show (coordinateMap r : Transverse → Transverse) = coordinates r
      from funext (coordinateMap_apply r)] using hm

theorem integral_coordinates (r : ℂ) (f : Transverse → ℝ) :
    ∫ q, f q = (1/2:ℝ)*∫ u, f (reconstruct r u) := by
  have hm := (coordinateEquiv r).toContinuousLinearEquiv.toHomeomorph
    |>.measurableEmbedding.integral_map (μ := volume) (fun u => f (reconstruct r u))
  have hfun : ((coordinateEquiv r).toContinuousLinearEquiv.toHomeomorph :
      Transverse → Transverse) = coordinates r := funext (coordinateMap_apply r)
  rw [hfun,coordinates_volume,integral_smul_measure] at hm
  simp only [reconstruct_coordinates,ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/2:ℝ)),
    smul_eq_mul] at hm
  exact hm.symm

theorem widths_strict (α β : ℝ) (r : ℂ) (hβ : 0 < β) (hi : r.im ≠ 0) :
    narrowWidth α β r < wideWidth α r := by
  have hp : 0 < 8*β*r.im^2 := by positivity
  unfold narrowWidth wideWidth
  linarith

theorem actual_narrowWidth_positive (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    0 < narrowWidth α β (KFCausalClockFloorRelativeShift.scale ε y s) := by
  have hp := KFCausalNeutralPlaneClockGeometry.actual_planeWidth_positive
    α β ε y s hα hβ hw hε hy hy0
  have hi := KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy hy0
  have hm := mul_pos hp (show 0 < 4*(KFCausalClockFloorRelativeShift.scale ε y s).im^2
    by positivity)
  convert hm using 1
  unfold narrowWidth KFCausalNeutralPlaneCoordinates.planeWidth
  field_simp
  ring

#print axioms reconstruct_coordinates
#print axioms coordinates_reconstruct
#print axioms field_reconstruct
#print axioms pair_reconstruct
#print axioms shifted_pair
#print axioms exponent_reconstruct
#print axioms gaussian_norm_reconstruct
#print axioms coordinateMap_apply
#print axioms coordinateMap_det
#print axioms coordinates_volume
#print axioms integral_coordinates
#print axioms widths_strict
#print axioms actual_narrowWidth_positive
end
end UnifiedTheory.Audit.KFCausalChargedPairCoordinates
