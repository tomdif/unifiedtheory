import UnifiedTheory.Audit.KFCausalConformal4DSpatialIsometry
import UnifiedTheory.Audit.KFCausalConformal4DChronologicalCurvatureLimit

/-! Actual chronological diamond volume at an arbitrary endpoint. Spatial
isometries transport both genuine curve-defined diamonds and Lebesgue measure.
A constructed reflection reduces every endpoint to the radial representative.
All inner volume integrals are proved integrable, for arbitrary endpoints. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DEndpointVolume
noncomputable section
open Set MeasureTheory Real Metric WithLp
open KFCausalConformal4DDiamondBenchmark (Point metric)
open KFCausalConformal4DDiamondAffine (future endpoint)
open KFCausalConformal4DDiamondMeasure (spatialRadius future_iff_radius)
open KFCausalConformal4DChronology
open KFCausalConformal4DSpatialIsometry
open KFCausalConformal4DChronologicalCurvatureLimit (chronologicalVolume)

def volumeDensity (c : ℝ) (x : Point) : ℝ := sqrt |Matrix.det (metric (2 * c) 0 x)|

def endpointVolume (c : ℝ) (p : Point) : ℝ :=
  ∫ x in chronologicalDiamondIn (2 * c) 0 univ p 0, volumeDensity c x

theorem density_lift (c : ℝ) (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (x : Point) :
    volumeDensity c (lift e x) = volumeDensity c x := by
  simp only [volumeDensity, KFCausalConformal4DTemporalVariation.density_at_point, lift_time]

theorem diamond_bounded (att spatial : ℝ) (p : Point) :
    chronologicalDiamondIn att spatial univ p 0 ⊆ closedBall (0 : Point) |p 0| := by
  intro x hx
  have hleft := chronological_implies_future att spatial univ p x hx.1
  have hright := chronological_implies_future att spatial univ x 0 hx.2
  have ht : p 0 < x 0 := by have h := hleft.1; change 0 < x 0 - p 0 at h; linarith
  have hx0 : x 0 < 0 := by have h := hright.1; change 0 < 0 - x 0 at h; linarith
  have hR : spatialRadius x < -x 0 := by
    have h := (future_iff_radius (0 - x)).mp hright
    simpa [spatialRadius] using h
  have hRb : spatialRadius x ≤ |p 0| := by linarith [neg_le_abs (p 0)]
  have hRn : 0 ≤ spatialRadius x := sqrt_nonneg _
  have hRsq : spatialRadius x ^ 2 = x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 :=
    sq_sqrt (by positivity)
  have hb : ∀ z : ℝ, z ^ 2 ≤ |p 0| ^ 2 → |z| ≤ |p 0| := by
    intro z hz
    exact (sq_le_sq₀ (abs_nonneg z) (abs_nonneg (p 0))).mp (by simpa only [sq_abs] using hz)
  have hsq := (sq_le_sq₀ hRn (abs_nonneg (p 0))).mpr hRb
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg (p 0))]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |x 0| ≤ |p 0|
    rw [abs_of_neg hx0]
    linarith [neg_le_abs (p 0)]
  · change |x 1| ≤ |p 0|
    exact hb _ (by nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)])
  · change |x 2| ≤ |p 0|
    exact hb _ (by nlinarith [sq_nonneg (x 1), sq_nonneg (x 3)])
  · change |x 3| ≤ |p 0|
    exact hb _ (by nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)])

theorem endpoint_integrable (c : ℝ) (p : Point) :
    IntegrableOn (volumeDensity c) (chronologicalDiamondIn (2 * c) 0 univ p 0) := by
  have hc : Continuous (volumeDensity c) := by
    have he : volumeDensity c = fun x : Point => (1 + c * x 0 ^ 2) ^ 4 := by
      funext x
      exact (KFCausalConformal4DTemporalVariation.density_at_point c x).trans
        (KFCausalConformal4DTemporalVariation.density_polynomial c (x 0))
    rw [he]
    fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Point) |p 0|)).mono_set
    (diamond_bounded (2 * c) 0 p)

theorem endpoint_volume_lift (c : ℝ) (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (p : Point) :
    endpointVolume c (lift e p) = endpointVolume c p := by
  have hz : lift e (0 : Point) = 0 := (liftEquiv e).map_zero
  have hi := (lift_measurePreserving e).setIntegral_image_emb
    (liftEquiv e).toHomeomorph.measurableEmbedding (volumeDensity c)
    (chronologicalDiamondIn (2 * c) 0 univ p 0)
  rw [chronological_diamond_image, hz] at hi
  simpa only [endpointVolume, density_lift] using hi

private def axisVector (r : ℝ) : Euclidean := toLp 2 ![r, 0, 0]

private theorem axisVector_norm (r : ℝ) : ‖axisVector r‖ = |r| := by
  simp [axisVector, EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.norm_eq_abs,
    Real.sqrt_sq_eq_abs]

def radialIsometry (p : Point) : Euclidean ≃ₗᵢ[ℝ] Euclidean :=
  (ℝ ∙ (spatialPart p - axisVector (spatialRadius p)))ᗮ.reflection

private theorem radialIsometry_apply (p : Point) :
    radialIsometry p (spatialPart p) = axisVector (spatialRadius p) := by
  apply Submodule.reflection_sub
  have hR : 0 ≤ spatialRadius p := sqrt_nonneg _
  rw [spatialPart_norm, axisVector_norm, abs_of_nonneg hR]

theorem radial_endpoint (p : Point) :
    lift (radialIsometry p) p = endpoint (p 0) (spatialRadius p) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change radialIsometry p (spatialPart p) j = endpoint (p 0) (spatialRadius p) j.succ
    rw [radialIsometry_apply]
    fin_cases j <;> rfl

theorem endpoint_volume_eq (c : ℝ) (p : Point) :
    endpointVolume c p = chronologicalVolume c (p 0) (spatialRadius p) := by
  rw [← endpoint_volume_lift c (radialIsometry p) p, radial_endpoint]
  rfl

theorem endpoint_volume_regular (c : ℝ) (hc : |c| ≤ 1 / 54) (p : Point)
    (hp : future (-p)) (hpb : |p 0| ≤ 2) :
    endpointVolume c p = KFCausalConformal4DRegularVolume.regularVolume c (p 0) (spatialRadius p) := by
  have ht : p 0 < 0 := by have h := hp.1; change 0 < -p 0 at h; linarith
  have hr : spatialRadius p < -p 0 := by
    have h := (future_iff_radius (-p)).mp hp
    simpa [spatialRadius] using h
  have hq : 0 < p 0 ^ 2 - spatialRadius p ^ 2 := by
    have hR : 0 ≤ spatialRadius p := sqrt_nonneg _
    nlinarith
  rw [endpoint_volume_eq,
    KFCausalConformal4DChronologicalCurvatureLimit.chronological_volume_eq c hc _ _ ht hpb hq,
    KFCausalConformal4DRegularVolume.timelike_eq_regular c _ _ hq]

#print axioms density_lift
#print axioms diamond_bounded
#print axioms endpoint_integrable
#print axioms endpoint_volume_lift
#print axioms radial_endpoint
#print axioms endpoint_volume_eq
#print axioms endpoint_volume_regular
end
end UnifiedTheory.Audit.KFCausalConformal4DEndpointVolume
