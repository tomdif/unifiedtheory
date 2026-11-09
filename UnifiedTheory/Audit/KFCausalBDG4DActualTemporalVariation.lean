/- The first derivative of the actual compact finite-density cone operator
has the temporal conformal curvature limit. This is a limit of derivatives;
it does not interchange a derivative with a continuum limit or identify the
explicit parameter volume with a geometric chronological-diamond volume. -/
import UnifiedTheory.Audit.KFCausalConformal4DCompactKernelDerivative
import UnifiedTheory.Audit.KFCausalBDG4DTemporalCurvatureLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalBDG4DActualTemporalVariation
noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology
open KFCausalConformal4DTemporalVariation KFCausalConformal4DRegularVolumeSmoothness
open KFCausalConformal4DCompactKernelDerivative
open KFCausalMinkowski4DMoments (f4D)
open KFCausalMinkowski4DVariationCone (coneIntegral)
open KFCausalBDG4DCompactPhysicalTest (densityParameter field)
open KFCausalBDG4DTemporalCurvatureLimit

theorem slope_integral_eq_correction (rho : ℝ) :
    (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), slope rho 0 (t,r)) =
      correctionIntegral (densityParameter rho) := by
  let D : ℝ × ℝ → ℝ := fun p =>
    (p.2^2*(4*p.1^2)*f4D (rho*(π*(p.1^2-p.2^2)^2/24)))*
      KFCausalConformal4DCompactKernelDerivative.cutoff p
  let V : ℝ × ℝ → ℝ := fun p =>
    (p.2^2*(6/5*p.1^2-2/15*(p.1^2-p.2^2))*(rho*(π*(p.1^2-p.2^2)^2/24))*
      deriv f4D (rho*(π*(p.1^2-p.2^2)^2/24)))*
      KFCausalConformal4DCompactKernelDerivative.cutoff p
  have hD : Integrable D := by
    apply weighted_cutoff_integrable (fun p =>
      p.2^2*(4*p.1^2)*f4D (rho*(π*(p.1^2-p.2^2)^2/24)))
    unfold f4D
    fun_prop
  have hV : Integrable V := by
    apply weighted_cutoff_integrable (fun p =>
      p.2^2*(6/5*p.1^2-2/15*(p.1^2-p.2^2))*(rho*(π*(p.1^2-p.2^2)^2/24))*
        deriv f4D (rho*(π*(p.1^2-p.2^2)^2/24)))
    simp_rw [(KFCausalMinkowski4DSecondOrder.f4D_hasDerivAt _).deriv]
    fun_prop
  have he : slope rho 0 = fun p => D p+V p := by
    funext p
    dsimp [KFCausalConformal4DCompactKernelDerivative.slope,D,V]
    rw [kernel_slope_zero]
    ring
  have hD' : (∫ p in cone, D p) = coneIntegral f4D (densityParameter rho) densityProfile := by
    rw [cone_integral_eq_iterated _ hD]
    apply setIntegral_congr_fun measurableSet_Iio
    intro t _
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    dsimp only
    rw [density_profile_formula]
    dsimp [D,KFCausalConformal4DCompactKernelDerivative.cutoff,
      KFCausalBDG4DTemporalCurvatureLimit.cutoff,densityParameter]
    rw [show rho*(π*(t^2-r^2)^2/24)=(π*rho/24)*(t^2-r^2)^2 from by ring]
    ring
  have hV' : (∫ p in cone, V p) =
      coneIntegral (fun x => x*deriv f4D x) (densityParameter rho) intervalProfile := by
    rw [cone_integral_eq_iterated _ hV]
    apply setIntegral_congr_fun measurableSet_Iio
    intro t _
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    dsimp only
    rw [interval_profile_formula]
    dsimp [V,KFCausalConformal4DCompactKernelDerivative.cutoff,
      KFCausalBDG4DTemporalCurvatureLimit.cutoff,densityParameter]
    rw [show rho*(π*(t^2-r^2)^2/24)=(π*rho/24)*(t^2-r^2)^2 from by ring]
    ring
  rw [← cone_integral_eq_iterated _ (slope_integrable rho 0),he,
    integral_add hD.integrableOn hV.integrableOn,hD',hV']
  rfl

theorem outer_derivative (rho : ℝ) :
    HasDerivAt (outerIntegral rho) (correctionIntegral (densityParameter rho)) 0 := by
  rw [← slope_integral_eq_correction]
  exact outer_integral_hasDerivAt rho

def operator (rho c : ℝ) : ℝ :=
  (4/sqrt 6)*sqrt rho*(rho*(4*π)*outerIntegral rho c-field 0)

theorem operator_zero (rho : ℝ) :
    operator rho 0=KFCausalBDG4DCompactPhysicalTest.densityOperator rho := by
  have he : outerIntegral rho 0 = ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
      r^2*f4D (densityParameter rho*(t^2-r^2)^2)*
        KFCausalBDG4DNonzeroCompactKernel.functions.mbar t r := by
    unfold outerIntegral
    apply setIntegral_congr_fun measurableSet_Iio
    intro t ht
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have hq : 0<t^2-r^2 := by
      have ht' : t<0 := ht
      have hr' : 0<r ∧ r< -t := hr
      nlinarith
    dsimp only
    rw [timelike_volume_zero t r hq,density_polynomial]
    dsimp [densityParameter,KFCausalBDG4DNonzeroCompactKernel.functions,
      KFCausalConformal4DCompactKernelDerivative.cutoff]
    rw [show rho*(π*(t^2-r^2)^2/24)=(π*rho/24)*(t^2-r^2)^2 from by ring]
    ring
  unfold operator KFCausalBDG4DCompactPhysicalTest.densityOperator
  rw [he]

theorem operator_hasDerivAt (rho : ℝ) :
    HasDerivAt (operator rho) (physicalCorrection rho) 0 := by
  convert (((outer_derivative rho).const_mul (rho*(4*π))).sub_const (field 0)).const_mul
    ((4/sqrt 6)*sqrt rho) using 1

theorem actual_derivative_tendsto :
    Tendsto (fun rho => deriv (operator rho) 0) atTop (𝓝 (-6)) := by
  have he : (fun rho => deriv (operator rho) 0)=physicalCorrection :=
    funext (fun rho => (operator_hasDerivAt rho).deriv)
  rw [he]
  exact physical_correction_tendsto

theorem actual_derivative_matches_curvature :
    Tendsto (fun rho => deriv (operator rho) 0) atTop
      (𝓝 (-(1/2)*deriv
        (fun c => KFCausalConformal4DDiamondBenchmark.scalar (2*c) 0) 0)) := by
  have he : (fun rho => deriv (operator rho) 0)=physicalCorrection :=
    funext (fun rho => (operator_hasDerivAt rho).deriv)
  rw [he]
  exact physical_limit_matches_curvature

#print axioms slope_integral_eq_correction
#print axioms outer_derivative
#print axioms operator_zero
#print axioms operator_hasDerivAt
#print axioms actual_derivative_tendsto
#print axioms actual_derivative_matches_curvature
end
end UnifiedTheory.Audit.KFCausalBDG4DActualTemporalVariation
