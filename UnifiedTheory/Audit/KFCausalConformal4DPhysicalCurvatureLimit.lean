/- Actual metric-density diamond integrals and the coordinate covariant wave
operator are attached to the fixed temporal-conformal continuum limit.
The diamond remains the explicit Minkowski chronological-cone domain;
conformal curve chronology and general curved dynamics are separate tasks. -/
import UnifiedTheory.Audit.KFCausalConformal4DTransformedProfileJets
import UnifiedTheory.Audit.KFCausalConformal4DCovariantWaveTest
import UnifiedTheory.Audit.KFCausalConformal4DCoordinateVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DPhysicalCurvatureLimit
noncomputable section
open Real Set MeasureTheory Filter Topology
open KFCausalConformal4DDiamondBenchmark (metric)
open KFCausalConformal4DDiamondAffine (diamond endpoint)
open KFCausalConformal4DCoordinateVolume
open KFCausalConformal4DTemporalVariation (density)
open KFCausalConformal4DCompactKernelDerivative (outerIntegral cutoff)
open KFCausalBDG4DCompactPhysicalTest (field)
open KFCausalMinkowski4DMoments (f4D)
open KFCausalConformal4DCovariantWaveTest

def coordinateOuter (rho c : ℝ) : ℝ :=
  ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
    r^2*sqrt |Matrix.det (metric (2*c) 0 (endpoint t r))| *
      f4D (rho*(∫ x in diamond (endpoint t r) 0, sqrt |Matrix.det (metric (2*c) 0 x)|))*
      field (endpoint t r)

def coordinateOperator (rho c : ℝ) : ℝ :=
  (4/sqrt 6)*sqrt rho*(rho*(4*π)*coordinateOuter rho c-field 0)

theorem coordinate_outer_eq (rho c : ℝ) : coordinateOuter rho c=outerIntegral rho c := by
  unfold coordinateOuter outerIntegral
  apply setIntegral_congr_fun measurableSet_Iio
  intro t ht
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have ht' : t<0 := ht
  have hr' : 0<r ∧ r< -t := hr
  have hq : 0<t^2-r^2 := by nlinarith
  dsimp only
  rw [← timelike_volume_eq_coordinate_integral c t r ht' hq,
    KFCausalConformal4DTemporalVariation.density_at_point c (endpoint t r)]
  have hf : field (endpoint t r)=cutoff (t,r) := by
    exact KFCausalBDG4DCompactPhysicalTest.radial_profile t r hr'.1.le
  rw [hf]
  rfl

theorem coordinate_operator_eq (rho c : ℝ) :
    coordinateOperator rho c=KFCausalBDG4DActualTemporalVariation.operator rho c := by
  unfold coordinateOperator KFCausalBDG4DActualTemporalVariation.operator
  rw [coordinate_outer_eq]

theorem actual_operator_covariant_limit (c : ℝ) (hc : |c|≤1/54) :
    Tendsto (fun rho => KFCausalBDG4DActualTemporalVariation.operator rho c) atTop
      (𝓝 (covariantWave (2*c) 0 field 0-scalarCurvature (2*c) 0/2*field 0)) := by
  rw [temporal_wave_curvature]
  exact KFCausalConformal4DTransformedProfileJets.operator_tendsto c hc

theorem coordinate_operator_covariant_limit (c : ℝ) (hc : |c|≤1/54) :
    Tendsto (fun rho => coordinateOperator rho c) atTop
      (𝓝 (covariantWave (2*c) 0 field 0-scalarCurvature (2*c) 0/2*field 0)) := by
  simp_rw [coordinate_operator_eq]
  exact actual_operator_covariant_limit c hc

#print axioms coordinate_outer_eq
#print axioms coordinate_operator_eq
#print axioms actual_operator_covariant_limit
#print axioms coordinate_operator_covariant_limit
end
end UnifiedTheory.Audit.KFCausalConformal4DPhysicalCurvatureLimit
