/- Exact real change of variables for the centered transverse polynomial
energy. The determinant and Gaussian identity are proved, without a
numerical Gaussian integration or a spectral cutoff. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
import UnifiedTheory.Audit.KFCausalQuarticPlaneDomination
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position exponent)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
open UnifiedTheory.Audit.KFCausalQuarticPlaneDomination (potential)

def coordinateMatrix (r : ℂ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1,0,0,0,0; 0,1,0,0,0; 0,0,1,-1,0;
    0,0,2*(r.re-1),2*(r.re-1),1; 0,0,2*r.im,2*r.im,0]

def coordinateMap (r : ℂ) : Transverse →ₗ[ℝ] Transverse :=
  (coordinateMatrix r).toLin'

theorem coordinateMap_apply (r : ℂ) (q : Transverse) :
    coordinateMap r q = coordinates r q := by
  funext i
  fin_cases i <;> simp [coordinateMap,coordinateMatrix,coordinates,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

def coordinateEquiv (r : ℂ) (hr : r.im ≠ 0) : Transverse ≃ₗ[ℝ] Transverse :=
  { coordinateMap r with
    invFun := reconstruct r
    left_inv := fun q => by
      change reconstruct r (coordinateMap r q) = q
      rw [coordinateMap_apply,reconstruct_coordinates r hr]
    right_inv := fun u => by
      change coordinateMap r (reconstruct r u) = u
      rw [coordinateMap_apply,coordinates_reconstruct r hr] }

theorem coordinateMap_det (r : ℂ) : LinearMap.det (coordinateMap r) = -4*r.im := by
  rw [coordinateMap,LinearMap.det_toLin']
  norm_num [coordinateMatrix,Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,
    Matrix.cons_val_two]
  ring

theorem coordinates_volume (r : ℂ) (hr : r.im ≠ 0) :
    Measure.map (coordinates r) volume =
      ENNReal.ofReal (1/(4*|r.im|)) • (volume : Measure Transverse) := by
  have hd : LinearMap.det (coordinateMap r) ≠ 0 := by
    rw [coordinateMap_det]
    exact mul_ne_zero (by norm_num) hr
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi hd
  simp only [coordinateMap_det,abs_inv,abs_mul,abs_neg,show |(4:ℝ)|=4 by norm_num] at hm
  simpa only [one_div,show (coordinateMap r : Transverse → Transverse) =
    coordinates r from funext (coordinateMap_apply r)] using hm

theorem integral_coordinates (r : ℂ) (hr : r.im ≠ 0) (f : Transverse → ℝ) :
    ∫ q, f q = (1/(4*|r.im|)) * ∫ u, f (reconstruct r u) := by
  have hm := (coordinateEquiv r hr).toContinuousLinearEquiv.toHomeomorph
    |>.measurableEmbedding.integral_map (μ := volume) (fun u => f (reconstruct r u))
  have hfun : ((coordinateEquiv r hr).toContinuousLinearEquiv.toHomeomorph :
      Transverse → Transverse) = coordinates r :=
    funext (coordinateMap_apply r)
  rw [hfun,coordinates_volume r hr,integral_smul_measure] at hm
  simp only [reconstruct_coordinates r hr,ENNReal.toReal_ofReal
    (by positivity : 0 ≤ 1/(4*|r.im|)),smul_eq_mul] at hm
  exact hm.symm

theorem gaussian_norm_reconstruct (α β : ℝ) (r : ℂ) (hr : r.im ≠ 0) (u : Transverse) :
    ‖Complex.exp (exponent α β 0 r (reconstruct r u))‖^2 =
      Real.exp (-quadratic α β r u) := by
  rw [Complex.norm_exp,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [exponent_reconstruct α β r hr]

def centeredEnergyDensity (α β : ℝ) (r : ℂ) (P : Polynomial ℂ) (q : Transverse) : ℝ :=
  ‖Complex.exp (exponent α β 0 r q)‖^2 *
    potential (pointField q) * ‖P.eval (position r q 4)‖^2

theorem centeredEnergy_change_variables (α β : ℝ) (r : ℂ) (hr : r.im ≠ 0)
    (P : Polynomial ℂ) :
    ∫ q, centeredEnergyDensity α β r P q =
      (1/(4*|r.im|)) * ∫ u : Transverse,
        Real.exp (-quadratic α β r u) * potential (u 3+fieldSlope r*u 4) *
          ‖P.eval ((u 3:ℂ)+(u 4:ℂ)*Complex.I)‖^2 := by
  rw [integral_coordinates r hr]
  simp only [centeredEnergyDensity,gaussian_norm_reconstruct α β r hr,
    field_reconstruct r hr,neutral_position r hr]

#print axioms coordinateMap_apply
#print axioms coordinateMap_det
#print axioms coordinates_volume
#print axioms integral_coordinates
#print axioms gaussian_norm_reconstruct
#print axioms centeredEnergy_change_variables
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure
