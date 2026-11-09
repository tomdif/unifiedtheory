import UnifiedTheory.Audit.KFCausalConformal4DEndpointVolume
import UnifiedTheory.Audit.KFCausalConformal4DSpatialRadialMeasureProduct

/-! Literal four-coordinate outer integration for the actual chronological
volume operator. The past is defined by actual timelike curves on the positive
temporal slab. The original compact field permits this support localization.
All L1 and angular integration obligations are derived; no radial reduction or
desired continuum limit is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DFullCoordinateOperator
noncomputable section
open Set MeasureTheory Real Filter Topology
open KFCausalConformal4DDiamondBenchmark (Point)
open KFCausalConformal4DDiamondAffine (future)
open KFCausalConformal4DDiamondMeasure (spatialRadius future_iff_radius)
open KFCausalConformal4DChronology
open KFCausalConformal4DEndpointVolume
open KFCausalConformal4DSpatialRadialMeasureProduct
open KFCausalConformal4DChronologicalCurvatureLimit
open KFCausalConformal4DCompactKernelDerivative (cutoff)
open KFCausalConformal4DRegularVolumeSmoothness (kernel)
open KFCausalConformal4DCovariantWaveTest
open KFCausalBDG4DCompactPhysicalTest (field)
open KFCausalMinkowski4DMoments (f4D)

def pastPatch (c : ℝ) : Set Point :=
  {p | chronologicalIn (2 * c) 0 (timeSlab (-2) 0) p 0}

def actualIntegrand (rho c : ℝ) (p : Point) : ℝ :=
  volumeDensity c p * f4D (rho * endpointVolume c p) * field p

def fullOuter (rho c : ℝ) : ℝ := ∫ p in pastPatch c, actualIntegrand rho c p

def fullOperator (rho c : ℝ) : ℝ :=
  (4 / sqrt 6) * sqrt rho * (rho * fullOuter rho c - field 0)

private def radialProfile (rho c : ℝ) (p : ℝ × ℝ) : ℝ :=
  kernel rho c p.1 p.2 * cutoff p

theorem past_patch_eq (c : ℝ) (hc : |c| ≤ 1 / 54) :
    pastPatch c = {p : Point | -2 ≤ p 0} ∩ pointPastCone := by
  ext p
  constructor
  · intro hp
    have hfuture := chronological_implies_future (2 * c) 0 _ p 0 hp
    have ht : p 0 < 0 := by have h := hfuture.1; change 0 < 0 - p 0 at h; linarith
    have hr : spatialRadius p < -p 0 := by
      have h := (future_iff_radius (0 - p)).mp hfuture
      simpa [spatialRadius] using h
    obtain ⟨γ, _, h0, _, hv⟩ := hp
    have hm := (hv 0 (by norm_num)).1
    rw [h0] at hm
    exact ⟨hm.1, ht, hr⟩
  · rintro ⟨hlo, ht, hr⟩
    apply (time_slab_chronology_iff c hc (-2) 0 (by norm_num) (by norm_num)
      p 0 ⟨hlo, ht.le⟩ (by constructor <;> norm_num)).mpr
    apply (future_iff_radius (0 - p)).mpr
    simpa [spatialRadius] using hr

private theorem cone_measurable : MeasurableSet pointPastCone := by
  apply (isOpen_lt (continuous_apply 0) continuous_const).measurableSet.inter
  apply IsOpen.measurableSet
  apply isOpen_lt _ (continuous_apply 0).neg
  unfold spatialRadius
  fun_prop

theorem past_patch_measurable (c : ℝ) (hc : |c| ≤ 1 / 54) : MeasurableSet (pastPatch c) := by
  rw [past_patch_eq c hc]
  exact (measurableSet_le measurable_const (measurable_pi_apply 0)).inter cone_measurable

private theorem profile_continuous (rho c : ℝ) : Continuous (radialProfile rho c) := by
  have hp : Continuous (fun p : ℝ × ℝ => (c, p)) := continuous_const.prodMk continuous_id
  have hk := (KFCausalConformal4DRegularVolumeSmoothness.kernel_continuous rho).comp hp
  have hcut : Continuous cutoff := by
    unfold cutoff
    exact (KFCausalBDG4DCompactProfile.smooth.continuous.comp (by fun_prop)).mul
      (KFCausalBDG4DCompactProfile.smooth.continuous.comp (by fun_prop))
  exact hk.mul hcut

private theorem profile_compact (rho c : ℝ) : HasCompactSupport (radialProfile rho c) := by
  apply HasCompactSupport.intro (K := Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2)
    (isCompact_Icc.prod isCompact_Icc)
  intro p hp
  have hz : cutoff p = 0 := by
    by_contra hn
    obtain ⟨ht, hr⟩ := KFCausalConformal4DTransformedProfile.cutoff_nonzero_bound p hn
    exact hp ⟨abs_le.mp ht, abs_le.mp hr⟩
  simp only [radialProfile, hz, mul_zero]

private theorem field_cutoff (p : Point) : field p = cutoff (p 0, spatialRadius p) := rfl

private theorem actual_eq_profile (rho c : ℝ) (hc : |c| ≤ 1 / 54)
    (p : Point) (hp : p ∈ pastPatch c) :
    actualIntegrand rho c p = pointLift (radialProfile rho c) p := by
  have hmem : -2 ≤ p 0 ∧ p ∈ pointPastCone := by
    have h := hp
    rwa [past_patch_eq c hc] at h
  have hf : future (-p) := by
    apply (future_iff_radius (-p)).mpr
    simpa [spatialRadius] using hmem.2.2
  have hb : |p 0| ≤ 2 := abs_le.mpr ⟨hmem.1, by linarith [hmem.2.1]⟩
  unfold actualIntegrand pointLift radialProfile kernel volumeDensity
  rw [KFCausalConformal4DTemporalVariation.density_at_point,
    endpoint_volume_regular c hc p hf hb, field_cutoff]

private theorem indicator_eq (rho c : ℝ) (hc : |c| ≤ 1 / 54) :
    (pastPatch c).indicator (actualIntegrand rho c) =
      pointPastCone.indicator (pointLift (radialProfile rho c)) := by
  funext p
  by_cases hp : p ∈ pastPatch c
  · have hm : p ∈ pointPastCone := by
      have h := hp
      rw [past_patch_eq c hc] at h
      exact h.2
    rw [indicator_of_mem hp, indicator_of_mem hm, actual_eq_profile rho c hc p hp]
  · rw [indicator_of_notMem hp]
    by_cases hm : p ∈ pointPastCone
    · rw [indicator_of_mem hm]
      have hlow : p 0 < -2 := by
        by_contra hn
        apply hp
        rw [past_patch_eq c hc]
        exact ⟨le_of_not_gt hn, hm⟩
      have hz : cutoff (p 0, spatialRadius p) = 0 := by
        by_contra hn
        have hb := (KFCausalConformal4DTransformedProfile.cutoff_nonzero_bound _ hn).1
        have ht := (abs_le.mp hb).1
        linarith
      simp only [pointLift, radialProfile, hz, mul_zero]
    · rw [indicator_of_notMem hm]

theorem actual_integrable (rho c : ℝ) (hc : |c| ≤ 1 / 54) :
    IntegrableOn (actualIntegrand rho c) (pastPatch c) := by
  exact (pointLift_integrable (radialProfile rho c) (profile_continuous rho c)
    (profile_compact rho c)).integrableOn.congr_fun
      (fun p hp => (actual_eq_profile rho c hc p hp).symm) (past_patch_measurable c hc)

private theorem radial_integral_eq (rho c : ℝ) (hc : |c| ≤ 1 / 54) :
    (∫ t in Iio (0 : ℝ), ∫ r in Ioo (0 : ℝ) (-t), r ^ 2 * radialProfile rho c (t, r)) =
      chronologicalOuter rho c := by
  rw [chronological_outer_eq rho c hc,
    KFCausalConformal4DPhysicalCurvatureLimit.coordinate_outer_eq,
    KFCausalConformal4DCompactKernelDerivative.outer_integral_eq_regular,
    KFCausalConformal4DCompactKernelDerivative.cone_integral_eq_iterated _
      (KFCausalConformal4DCompactKernelDerivative.integrand_integrable rho c)]
  apply setIntegral_congr_fun measurableSet_Iio
  intro t _
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  dsimp [radialProfile, KFCausalConformal4DCompactKernelDerivative.integrand]
  ring

theorem full_outer_eq (rho c : ℝ) (hc : |c| ≤ 1 / 54) :
    fullOuter rho c = 4 * π * chronologicalOuter rho c := by
  unfold fullOuter
  rw [← integral_indicator (past_patch_measurable c hc), indicator_eq rho c hc,
    integral_indicator cone_measurable,
    point_past_integral (radialProfile rho c) (profile_continuous rho c) (profile_compact rho c),
    radial_integral_eq rho c hc]

theorem full_operator_eq (rho c : ℝ) (hc : |c| ≤ 1 / 54) :
    fullOperator rho c = chronologicalOperator rho c := by
  rw [fullOperator, full_outer_eq rho c hc]
  unfold chronologicalOperator
  ring

theorem full_operator_covariant_limit (c : ℝ) (hc : |c| ≤ 1 / 54) :
    Tendsto (fun rho => fullOperator rho c) atTop
      (𝓝 (covariantWave (2 * c) 0 field 0 - scalarCurvature (2 * c) 0 / 2 * field 0)) := by
  simp_rw [full_operator_eq _ c hc]
  exact chronological_operator_covariant_limit c hc

#print axioms past_patch_eq
#print axioms past_patch_measurable
#print axioms actual_integrable
#print axioms full_outer_eq
#print axioms full_operator_eq
#print axioms full_operator_covariant_limit
end
end UnifiedTheory.Audit.KFCausalConformal4DFullCoordinateOperator
