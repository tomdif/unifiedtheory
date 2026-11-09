/- The integrated temporal conformal first-variation kernel has the actual
normalized limit -6. The density and interval corrections use the same
compact cutoff. The curved operator at fixed nonzero curvature, and the
identification of the parameter integral with geometric volume, are separate. -/
import UnifiedTheory.Audit.KFCausalBDG4DQuadraticVariationLimit
import UnifiedTheory.Audit.KFCausalBDG4DCompactPhysicalTest
import UnifiedTheory.Audit.KFCausalConformal4DConnection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalBDG4DTemporalCurvatureLimit
noncomputable section
open Real Filter Topology
open KFCausalMinkowski4DVariationCone (coneIntegral)
open KFCausalMinkowski4DMoments (f4D)
open KFCausalBDG4DQuadraticVariationLimit
open KFCausalBDG4DQuadraticEulerProfiles (profile profile_formula)
open KFCausalBDG4DCompactPhysicalTest (densityParameter densityParameter_tendsto)

def densityProfile : ℝ × ℝ → ℝ := Function.uncurry (profile 1 2)
def intervalProfile : ℝ × ℝ → ℝ := Function.uncurry (profile (3/10) (7/15))
def cutoff (t r : ℝ) : ℝ :=
  KFCausalBDG4DCompactProfile.profile (-t-r)*KFCausalBDG4DCompactProfile.profile (-t+r)

theorem density_profile_formula (t r : ℝ) :
    densityProfile (-t-r,-t+r)=4*t^2*cutoff t r := by
  simp only [densityProfile,Function.uncurry_apply_pair,profile_formula,cutoff]
  ring

theorem interval_profile_formula (t r : ℝ) :
    intervalProfile (-t-r,-t+r)=(6/5*t^2-2/15*(t^2-r^2))*cutoff t r := by
  simp only [intervalProfile,Function.uncurry_apply_pair,profile_formula,cutoff]
  ring

def correctionIntegral (a : ℝ) : ℝ :=
  coneIntegral f4D a densityProfile+
    coneIntegral (fun x => x*deriv f4D x) a intervalProfile

def normalizedCorrection (a : ℝ) : ℝ :=
  (48/sqrt π)*(sqrt a*(16*a*correctionIntegral a))

theorem normalized_correction_tendsto :
    Tendsto normalizedCorrection atTop (𝓝 (-6)) := by
  have h := ((ordinary_cone_tendsto 1 2).add
    (variation_cone_tendsto (3/10) (7/15))).const_mul (48/sqrt π)
  have hv : (48/sqrt π)*(sqrt π*((1:ℝ)-2)/6-
      (sqrt π*((3:ℝ)/10-7/15))/4) = -6 := by
    field_simp [ne_of_gt (sqrt_pos.mpr pi_pos)]
    ring
  rw [show sqrt π*((1:ℝ)-2)/6+(-(sqrt π*((3:ℝ)/10-7/15))/4) =
    sqrt π*((1:ℝ)-2)/6-(sqrt π*((3:ℝ)/10-7/15))/4 by ring,hv] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun a => by
    dsimp [normalizedCorrection,correctionIntegral,densityProfile,intervalProfile]
    ring)

def physicalCorrection (rho : ℝ) : ℝ :=
  (4/sqrt 6)*sqrt rho*(rho*(4*π)*correctionIntegral (densityParameter rho))

theorem physical_normalization (rho : ℝ) (hrho : 0 ≤ rho) :
    physicalCorrection rho=normalizedCorrection (densityParameter rho) := by
  have hs : sqrt (π*rho/24)=sqrt π*sqrt rho/(2*sqrt 6) := by
    rw [sqrt_div (mul_nonneg pi_pos.le hrho),sqrt_mul pi_pos.le,
      show (24:ℝ)=2^2*6 by norm_num,sqrt_mul (by norm_num : (0:ℝ)≤2^2),
      sqrt_sq (by norm_num : (0:ℝ)≤2)]
  unfold physicalCorrection normalizedCorrection densityParameter
  rw [hs]
  field_simp [ne_of_gt (sqrt_pos.mpr pi_pos),ne_of_gt (sqrt_pos.mpr (by norm_num : (0:ℝ)<6))]
  ring

theorem physical_correction_tendsto : Tendsto physicalCorrection atTop (𝓝 (-6)) := by
  apply (normalized_correction_tendsto.comp densityParameter_tendsto).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with rho hrho
  exact (physical_normalization rho hrho).symm

theorem scalar_curvature_derivative :
    HasDerivAt (fun c => KFCausalConformal4DDiamondBenchmark.scalar (2*c) 0) 12 0 := by
  simp_rw [KFCausalConformal4DDiamondBenchmark.scalar_curvature]
  convert (hasDerivAt_id (0:ℝ)).const_mul 12 using 1
  · funext c; dsimp only [id_eq]; ring
  · ring

theorem physical_limit_matches_curvature :
    Tendsto physicalCorrection atTop (𝓝 (-(1/2)*
      deriv (fun c => KFCausalConformal4DDiamondBenchmark.scalar (2*c) 0) 0)) := by
  rw [scalar_curvature_derivative.deriv]
  convert physical_correction_tendsto using 1
  norm_num

#print axioms density_profile_formula
#print axioms interval_profile_formula
#print axioms normalized_correction_tendsto
#print axioms physical_normalization
#print axioms physical_correction_tendsto
#print axioms scalar_curvature_derivative
#print axioms physical_limit_matches_curvature
end
end UnifiedTheory.Audit.KFCausalBDG4DTemporalCurvatureLimit
