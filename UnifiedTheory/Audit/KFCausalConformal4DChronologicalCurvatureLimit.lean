/- The fixed-parameter operator now uses diamonds defined by actual smooth
future-timelike curves of the conformal metric. Equality with the explicit
cone domain is derived on the original compact support. -/
import UnifiedTheory.Audit.KFCausalConformal4DChronology
import UnifiedTheory.Audit.KFCausalConformal4DPhysicalCurvatureLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DChronologicalCurvatureLimit
noncomputable section
open Real Set MeasureTheory Filter Topology
open KFCausalConformal4DDiamondBenchmark (metric)
open KFCausalConformal4DDiamondAffine (endpoint)
open KFCausalConformal4DChronology KFCausalConformal4DPhysicalCurvatureLimit
open KFCausalConformal4DCompactKernelDerivative (cutoff)
open KFCausalConformal4DTransformedProfile (cutoff_nonzero_bound)
open KFCausalBDG4DCompactPhysicalTest (field)
open KFCausalMinkowski4DMoments (f4D)
open KFCausalConformal4DCovariantWaveTest

def chronologicalVolume (c t r : ℝ) : ℝ :=
  ∫ x in chronologicalDiamondIn (2*c) 0 univ (endpoint t r) 0,
    sqrt |Matrix.det (metric (2*c) 0 x)|

def chronologicalOuter (rho c : ℝ) : ℝ :=
  ∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
    r^2*sqrt |Matrix.det (metric (2*c) 0 (endpoint t r))| *
      f4D (rho*chronologicalVolume c t r)*field (endpoint t r)

def chronologicalOperator (rho c : ℝ) : ℝ :=
  (4/sqrt 6)*sqrt rho*(rho*(4*π)*chronologicalOuter rho c-field 0)

theorem chronological_volume_eq (c : ℝ) (hc : |c|≤1/54) (t r : ℝ)
    (ht : t<0) (htb : |t|≤2) (hq : 0<t^2-r^2) :
    chronologicalVolume c t r=KFCausalConformal4DTemporalVariation.timelikeVolume c t r := by
  unfold chronologicalVolume
  rw [retarded_global_diamond c hc t r ht htb]
  exact (KFCausalConformal4DCoordinateVolume.timelike_volume_eq_coordinate_integral c t r ht hq).symm

theorem chronological_outer_eq (rho c : ℝ) (hc : |c|≤1/54) :
    chronologicalOuter rho c=coordinateOuter rho c := by
  unfold chronologicalOuter coordinateOuter
  apply setIntegral_congr_fun measurableSet_Iio
  intro t ht
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  by_cases hz : field (endpoint t r)=0
  · rw [hz,mul_zero,mul_zero]
  · have hfield : field (endpoint t r)=cutoff (t,r) :=
      KFCausalBDG4DCompactPhysicalTest.radial_profile t r (show 0<r from hr.1).le
    have hn : cutoff (t,r)≠0 := by rwa [hfield] at hz
    have htb := (cutoff_nonzero_bound (t,r) hn).1
    unfold chronologicalVolume
    rw [retarded_global_diamond c hc t r ht htb]

theorem chronological_operator_eq (rho c : ℝ) (hc : |c|≤1/54) :
    chronologicalOperator rho c=KFCausalBDG4DActualTemporalVariation.operator rho c := by
  rw [← coordinate_operator_eq]
  unfold chronologicalOperator coordinateOperator
  rw [chronological_outer_eq rho c hc]

theorem chronological_operator_covariant_limit (c : ℝ) (hc : |c|≤1/54) :
    Tendsto (fun rho => chronologicalOperator rho c) atTop
      (𝓝 (covariantWave (2*c) 0 field 0-scalarCurvature (2*c) 0/2*field 0)) := by
  simp_rw [chronological_operator_eq _ c hc]
  exact actual_operator_covariant_limit c hc

#print axioms chronological_volume_eq
#print axioms chronological_outer_eq
#print axioms chronological_operator_eq
#print axioms chronological_operator_covariant_limit
end
end UnifiedTheory.Audit.KFCausalConformal4DChronologicalCurvatureLimit
