/- Real coordinates in which the complex shifted neutral argument is
X+iY. This retains the exact field shear and diagonalizes the centered
Gaussian exponent, before any integral or Jacobian identification. -/
import UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position exponent)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

def coordinates (r : ℂ) (q : Transverse) : Transverse :=
  ![q 0,q 1,q 2-q 3,q 4+2*(r.re-1)*(q 2+q 3),2*r.im*(q 2+q 3)]

def reconstruct (r : ℂ) (u : Transverse) : Transverse :=
  ![u 0,u 1,(u 4/(2*r.im)+u 2)/2,(u 4/(2*r.im)-u 2)/2,
    u 3-(r.re-1)*u 4/r.im]

def planeWidth (α β : ℝ) (r : ℂ) : ℝ := α*(r.re^2-r.im^2)/(4*r.im^2)-2*β
def fieldSlope (r : ℂ) : ℝ := (3-2*r.re)/(2*r.im)
def quadratic (α β : ℝ) (r : ℂ) (u : Transverse) : ℝ :=
  2*α*(r.re^2-r.im^2)*((u 0)^2+(u 1)^2)+
    α*(r.re^2-r.im^2)*(u 2)^2+2*β*(u 3)^2+planeWidth α β r*(u 4)^2

theorem reconstruct_coordinates (r : ℂ) (hr : r.im ≠ 0) (q : Transverse) :
    reconstruct r (coordinates r q) = q := by
  funext i
  fin_cases i <;> simp [reconstruct,coordinates] <;> field_simp <;> ring

theorem coordinates_reconstruct (r : ℂ) (hr : r.im ≠ 0) (u : Transverse) :
    coordinates r (reconstruct r u) = u := by
  funext i
  fin_cases i <;> simp [reconstruct,coordinates] <;> field_simp <;> ring

theorem neutral_position (r : ℂ) (hr : r.im ≠ 0) (u : Transverse) :
    position r (reconstruct r u) 4 = (u 3:ℂ)+(u 4:ℂ)*Complex.I := by
  change (↑(u 3-(r.re-1)*u 4/r.im):ℂ) +
      2*(r-1)*(↑((u 4/(2*r.im)+u 2)/2)+↑((u 4/(2*r.im)-u 2)/2)) =
    (u 3:ℂ)+(u 4:ℂ)*Complex.I
  apply Complex.ext <;>
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,
      Complex.re_ofNat,Complex.im_ofNat] <;> field_simp <;> ring

theorem field_reconstruct (r : ℂ) (hr : r.im ≠ 0) (u : Transverse) :
    pointField (reconstruct r u) = u 3+fieldSlope r*u 4 := by
  change (u 4/(2*r.im)+u 2)/2+(u 4/(2*r.im)-u 2)/2+
    (u 3-(r.re-1)*u 4/r.im) = u 3+fieldSlope r*u 4
  unfold fieldSlope
  field_simp
  ring

theorem exponent_reconstruct (α β : ℝ) (r : ℂ) (hr : r.im ≠ 0) (u : Transverse) :
    2*(exponent α β 0 r (reconstruct r u)).re = -quadratic α β r u := by
  unfold exponent
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_sub]
  rw [show (∑ i : Fin 5, (KFCausalPhysicalGaussianMoments.widths α β i:ℂ)*
      (position r (reconstruct r u) i)^2) =
    (α:ℂ)*(r*(u 0:ℂ))^2+(α:ℂ)*(r*(u 1:ℂ))^2+
      (α:ℂ)*(r*((reconstruct r u 2):ℂ))^2+
      (α:ℂ)*(r*((reconstruct r u 3):ℂ))^2+
      (β:ℂ)*((u 3:ℂ)+(u 4:ℂ)*Complex.I)^2 by
    simp only [Fin.sum_univ_succ]
    change (α:ℂ)*position r (reconstruct r u) 0^2+
      ((α:ℂ)*position r (reconstruct r u) 1^2+
      ((α:ℂ)*position r (reconstruct r u) 2^2+
      ((α:ℂ)*position r (reconstruct r u) 3^2+
      ((β:ℂ)*position r (reconstruct r u) 4^2+0)))) = _
    rw [neutral_position r hr]
    change (α:ℂ)*(r*(u 0:ℂ))^2+((α:ℂ)*(r*(u 1:ℂ))^2+
      ((α:ℂ)*(r*((reconstruct r u 2):ℂ))^2+
      ((α:ℂ)*(r*((reconstruct r u 3):ℂ))^2+
      ((β:ℂ)*((u 3:ℂ)+(u 4:ℂ)*Complex.I)^2+0)))) = _
    ring]
  change 2*(-((α:ℂ)*(r*(u 0:ℂ))^2+(α:ℂ)*(r*(u 1:ℂ))^2+
    (α:ℂ)*(r*(↑((u 4/(2*r.im)+u 2)/2):ℂ))^2+
    (α:ℂ)*(r*(↑((u 4/(2*r.im)-u 2)/2):ℂ))^2+
    (β:ℂ)*((u 3:ℂ)+(u 4:ℂ)*Complex.I)^2)).re = _
  simp only [quadratic,planeWidth,pow_two,
    Complex.neg_re,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im]
  field_simp
  ring

theorem planeWidth_positive (α β : ℝ) (r : ℂ) (hr : r.im ≠ 0)
    (hwidth : 8*β*r.im^2 < α*(r.re^2-r.im^2)) : 0 < planeWidth α β r := by
  unfold planeWidth
  have hd : 0 < 4*r.im^2 := by positivity
  apply sub_pos.mpr
  exact (lt_div_iff₀ hd).mpr (by nlinarith)

#print axioms reconstruct_coordinates
#print axioms coordinates_reconstruct
#print axioms neutral_position
#print axioms field_reconstruct
#print axioms exponent_reconstruct
#print axioms planeWidth_positive
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
