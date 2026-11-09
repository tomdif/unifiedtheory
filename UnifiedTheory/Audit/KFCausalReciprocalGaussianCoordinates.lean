/- Diagonalize the actual reciprocal Gaussian after a complex clock shift.
The parameter k = 1/sqrt(w) has a regular endpoint k=0 in the marginal
formula, although k=0 itself does not define a finite-width Hilbert state. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianCharge
import UnifiedTheory.Audit.KFCausalChargedPairCompactGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianCoordinates
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalReciprocalGaussianStates (quadratic)
open KFCausalChargedPairCoordinates (fieldSlope)

def area (r : ℂ) : ℝ := r.re^2-r.im^2
def narrow (α β k : ℝ) (r : ℂ) : ℝ := α*area r-8*β*k^2*r.im^2

def exponent (α β w : ℝ) (r : ℂ) (q : Transverse) : ℂ :=
  -(α:ℂ)*r^2*(quadratic w q:ℂ)-
    (β:ℂ)*((q 4:ℂ)+2*(r-1)*((q 2+q 3:ℝ):ℂ))^2

def coordinates (k : ℝ) (r : ℂ) (q : Transverse) : Transverse :=
  ![k*(q 0+q 1),(q 0-q 1)/k,(q 2+q 3)/k,k*(q 2-q 3),
    q 4+2*(r.re-1)*(q 2+q 3)]
def reconstruct (k : ℝ) (r : ℂ) (u : Transverse) : Transverse :=
  ![(u 0/k+k*u 1)/2,(u 0/k-k*u 1)/2,(k*u 2+u 3/k)/2,
    (k*u 2-u 3/k)/2,u 4-2*(r.re-1)*k*u 2]

theorem reconstruct_coordinates (k : ℝ) (hk : k ≠ 0) (r : ℂ) (q : Transverse) :
    reconstruct k r (coordinates k r q) = q := by
  funext i
  fin_cases i <;> simp [reconstruct,coordinates] <;> field_simp <;> ring

theorem coordinates_reconstruct (k : ℝ) (hk : k ≠ 0) (r : ℂ) (u : Transverse) :
    coordinates k r (reconstruct k r u) = u := by
  funext i
  fin_cases i <;> simp [reconstruct,coordinates] <;> field_simp <;> ring

theorem field_reconstruct (k : ℝ) (r : ℂ) (u : Transverse) :
    pointField (reconstruct k r u) = u 4+(k*fieldSlope r)*u 2 := by
  change (k*u 2+u 3/k)/2+(k*u 2-u 3/k)/2+
    (u 4-2*(r.re-1)*k*u 2) = _
  unfold fieldSlope
  ring

def diagonalQuadratic (α β k : ℝ) (r : ℂ) (u : Transverse) : ℝ :=
  α*area r*((u 0)^2+(u 1)^2+(u 3)^2)+narrow α β k r*(u 2)^2+2*β*(u 4)^2

theorem exponent_reconstruct (α β k : ℝ) (hk : k ≠ 0) (r : ℂ) (u : Transverse) :
    2*(exponent α β (1/k^2) r (reconstruct k r u)).re =
      -diagonalQuadratic α β k r u := by
  dsimp [exponent,quadratic,KFCausalQuarticChargeProfiles.chargedRadius,
    KFCausalChargedPairCoordinates.pairPolynomial,reconstruct]
  simp only [diagonalQuadratic,area,narrow,pow_two,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.one_im,Complex.re_ofNat,Complex.im_ofNat]
  field_simp
  ring

theorem gaussian_norm_reconstruct (α β k : ℝ) (hk : k ≠ 0) (r : ℂ) (u : Transverse) :
    ‖Complex.exp (exponent α β (1/k^2) r (reconstruct k r u))‖^2 =
      Real.exp (-diagonalQuadratic α β k r u) := by
  rw [Complex.norm_exp,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [exponent_reconstruct α β k hk]

def coordinateMatrix (k : ℝ) (r : ℂ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![k,k,0,0,0; 1/k,-1/k,0,0,0; 0,0,1/k,1/k,0; 0,0,k,-k,0;
    0,0,2*(r.re-1),2*(r.re-1),1]
def coordinateMap (k : ℝ) (r : ℂ) : Transverse →ₗ[ℝ] Transverse :=
  (coordinateMatrix k r).toLin'

theorem coordinateMap_apply (k : ℝ) (r : ℂ) (q : Transverse) :
    coordinateMap k r q = coordinates k r q := by
  funext i
  fin_cases i <;> simp [coordinateMap,coordinateMatrix,coordinates,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

def coordinateEquiv (k : ℝ) (hk : k ≠ 0) (r : ℂ) : Transverse ≃ₗ[ℝ] Transverse :=
  { coordinateMap k r with
    invFun := reconstruct k r
    left_inv := fun q => by
      change reconstruct k r (coordinateMap k r q) = q
      rw [coordinateMap_apply,reconstruct_coordinates k hk]
    right_inv := fun u => by
      change coordinateMap k r (reconstruct k r u) = u
      rw [coordinateMap_apply,coordinates_reconstruct k hk] }

theorem coordinateMap_det (k : ℝ) (hk : k ≠ 0) (r : ℂ) :
    LinearMap.det (coordinateMap k r) = 4 := by
  rw [coordinateMap,LinearMap.det_toLin']
  simp [coordinateMatrix,Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove]
  field_simp
  ring

theorem coordinates_volume (k : ℝ) (hk : k ≠ 0) (r : ℂ) :
    Measure.map (coordinates k r) volume =
      ENNReal.ofReal (1/4) • (volume : Measure Transverse) := by
  have hd : LinearMap.det (coordinateMap k r) ≠ 0 := by rw [coordinateMap_det k hk]; norm_num
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi hd
  simpa only [coordinateMap_det k hk,show |(4:ℝ)⁻¹|=1/4 by norm_num,
    show (coordinateMap k r : Transverse → Transverse) = coordinates k r
      from funext (coordinateMap_apply k r)] using hm

theorem integral_coordinates (k : ℝ) (hk : k ≠ 0) (r : ℂ) (f : Transverse → ℝ) :
    ∫ q, f q = (1/4:ℝ)*∫ u, f (reconstruct k r u) := by
  have hm := (coordinateEquiv k hk r).toContinuousLinearEquiv.toHomeomorph
    |>.measurableEmbedding.integral_map (μ := volume) (fun u => f (reconstruct k r u))
  have hfun : ((coordinateEquiv k hk r).toContinuousLinearEquiv.toHomeomorph :
      Transverse → Transverse) = coordinates k r := funext (coordinateMap_apply k r)
  rw [hfun,coordinates_volume k hk,integral_smul_measure] at hm
  simp only [reconstruct_coordinates k hk,ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/4:ℝ)),
    smul_eq_mul] at hm
  exact hm.symm

#print axioms reconstruct_coordinates
#print axioms coordinates_reconstruct
#print axioms field_reconstruct
#print axioms exponent_reconstruct
#print axioms gaussian_norm_reconstruct
#print axioms coordinateMap_apply
#print axioms coordinateMap_det
#print axioms coordinates_volume
#print axioms integral_coordinates
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianCoordinates
