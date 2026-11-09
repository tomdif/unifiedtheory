/- The nonzero local equipartition variance is removed-link noise.
The actual retained response converges to a constant in L2 under the original
Wilson laws, while its orthogonal conditional residual has limiting norm
squared 3/2. This concerns this microscopic observable, not a continuum no-go. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonLocalSecondMoment
import UnifiedTheory.Clay.YangMills.SU2RetainedCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2WilsonEquipartitionNoise
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2HaarTilt SU2StarEnergy SU2WilsonConditionalSource
open SU2WilsonLocalEquipartition SU2WilsonLocalSecondMoment

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance law_probability (β : ℝ) : IsProbabilityMeasure (wilsonLaw n Q character β 2) :=
  wilsonLaw_probability n Q character character_continuous β 2

/-- The actual one-link conditional mean, evaluated on its original exterior. -/
def retained (x : Vertex n) (μ : Fin 4) (β : ℝ) (U : Configuration (Vertex n) Q) : ℝ :=
  conditionalMean n x μ β (exterior n x μ U)

/-- The actual local excess minus that same conditional mean. -/
def noise (x : Vertex n) (μ : Fin 4) (β : ℝ) (U : Configuration (Vertex n) Q) : ℝ :=
  localExcess n x μ β U - retained n x μ β U

omit [Fact (1 < n)] in
theorem retained_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (retained n x μ β) :=
  (conditionalMean_continuous n x μ β).comp (exterior_continuous n x μ)

omit [Fact (1 < n)] in
theorem noise_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (noise n x μ β) :=
  (localExcess_continuous n x μ β).sub (retained_continuous n x μ β)

omit [Fact (1 < n)] in
theorem retained_mean (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    (∫ U, retained n x μ β U ∂wilsonLaw n Q character β 2) =
      ∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2 :=
  (mean_eq_conditionalMean n x μ β).symm

theorem retained_bounds (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 ≤ β)
    (U : Configuration (Vertex n) Q) :
    0 ≤ retained n x μ β U ∧ retained n x μ β U ≤ 3 / 2 :=
  conditionalMean_bounds n x μ β hβ _

/-- Saturation of a bounded mean forces its actual retained response to be constant in L2. -/
theorem retained_square_error_bound (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 ≤ β) :
    (∫ U, (retained n x μ β U - 3 / 2)^2 ∂wilsonLaw n Q character β 2) ≤
      (3 / 2) * (3 / 2 - ∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2) := by
  let ν := wilsonLaw n Q character β 2
  have hc := retained_continuous n x μ β
  have hi : Integrable (retained n x μ β) ν :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hL : Integrable (fun U => (retained n x μ β U - (3 / 2 : ℝ))^2) ν :=
    ((hc.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (fun U => (3 / 2 : ℝ) * (3 / 2 - retained n x μ β U)) ν :=
    ((integrable_const _).sub hi).const_mul _
  have h := integral_mono hL hR (fun U => by
    obtain ⟨h0, h1⟩ := retained_bounds n x μ β hβ U
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)])
  rw [integral_const_mul, integral_sub (integrable_const _) hi] at h
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, retained_mean, ν] using h

/-- A corresponding direct bound on the retained second moment. -/
theorem retained_second_error_bound (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ 9 / 4 - (∫ U, (retained n x μ β U)^2 ∂wilsonLaw n Q character β 2) ∧
      9 / 4 - (∫ U, (retained n x μ β U)^2 ∂wilsonLaw n Q character β 2) ≤
        3 * (3 / 2 - ∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2) := by
  let ν := wilsonLaw n Q character β 2
  have hc := retained_continuous n x μ β
  have hi : Integrable (retained n x μ β) ν :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun U => (retained n x μ β U)^2) ν :=
    (hc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ U, (9 / 4 : ℝ) - (retained n x μ β U)^2 ∂ν) =
      9 / 4 - ∫ U, (retained n x μ β U)^2 ∂ν := by
    rw [integral_sub (integrable_const _) hi2]
    simp
  constructor
  · rw [← he]
    apply integral_nonneg
    intro U
    change 0 ≤ (9 / 4 : ℝ) - (retained n x μ β U)^2
    obtain ⟨h0, h1⟩ := retained_bounds n x μ β hβ U
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  · have hL : Integrable (fun U => (9 / 4 : ℝ) - (retained n x μ β U)^2) ν :=
      (integrable_const _).sub hi2
    have hR : Integrable (fun U => 3 * ((3 / 2 : ℝ) - retained n x μ β U)) ν :=
      ((integrable_const _).sub hi).const_mul _
    have h := integral_mono hL hR (fun U => by
      nlinarith [sq_nonneg (retained n x μ β U - 3 / 2)])
    rw [he, integral_const_mul, integral_sub (integrable_const _) hi] at h
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, retained_mean, ν] using h

omit [Fact (1 < n)] in
theorem retained_assemble (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (z : Exterior n Q x μ × Q) :
    retained n x μ β (SingleCoordinateProduct.assemble (selectedLink n x μ) z) =
      conditionalMean n x μ β z.1 := by
  unfold retained
  rw [show exterior n x μ (SingleCoordinateProduct.assemble (selectedLink n x μ) z) = z.1 from
    SU2WilsonMarginalTransport.exteriorProjection_assemble n x μ z]

omit [Fact (1 < n)] in
theorem noise_assemble (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (z : Exterior n Q x μ × Q) :
    noise n x μ β (SingleCoordinateProduct.assemble (selectedLink n x μ) z) =
      GibbsCrossCovariance.removed haar (splitAction n x μ β) (splitExcess n x μ β) z := by
  simp only [noise, localExcess_assemble, retained_assemble]
  rfl

omit [Fact (1 < n)] in
/-- Exact conditional centering, with the actual normalized Wilson fiber. -/
theorem noise_conditional_mean (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    (∫ q, noise n x μ β (SingleCoordinateProduct.assemble (selectedLink n x μ) (r,q))
      ∂conditionalLaw n x μ β r) = 0 := by
  simp_rw [noise_assemble]
  exact (GibbsMarginalTower.response_eq_expectation haar _ _
    (splitAction_continuous n x μ β) r).symm.trans
      (GibbsCrossCovariance.removed_response haar _ _ (splitAction_continuous n x μ β)
        (splitExcess_continuous n x μ β) r)

omit [Fact (1 < n)] in
/-- The removed noise is exactly orthogonal to every continuous observable of the exterior. -/
theorem noise_exterior_orthogonal (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (G : Exterior n Q x μ → ℝ) (hG : Continuous G) :
    (∫ U, noise n x μ β U * G (exterior n x μ U) ∂wilsonLaw n Q character β 2) = 0 := by
  rw [SU2RetainedCovariance.integral_coordinates n x μ β]
  have hR := GibbsCrossCovariance.removed_continuous haar _ _
    (splitAction_continuous n x μ β) (splitExcess_continuous n x μ β)
  have he (z : Exterior n Q x μ × Q) :
      noise n x μ β (SingleCoordinateProduct.assemble (selectedLink n x μ) z) *
        G (exterior n x μ (SingleCoordinateProduct.assemble (selectedLink n x μ) z)) =
      GibbsCrossCovariance.removed haar (splitAction n x μ β) (splitExcess n x μ β) z * G z.1 := by
    rw [noise_assemble]
    rw [show exterior n x μ (SingleCoordinateProduct.assemble (selectedLink n x μ) z) = z.1 from
      SU2WilsonMarginalTransport.exteriorProjection_assemble n x μ z]
  simp_rw [he]
  have hr := GibbsMarginalTower.response_expectation (exteriorMeasure n Q x μ) haar
    (splitAction n x μ β)
    (fun z => GibbsCrossCovariance.removed haar (splitAction n x μ β)
      (splitExcess n x μ β) z * G z.1)
    (splitAction_continuous n x μ β) (hR.mul (hG.comp continuous_fst))
  rw [← hr]
  have hz (r : Exterior n Q x μ) :
      GibbsMarginalTower.response haar (splitAction n x μ β)
        (fun z => GibbsCrossCovariance.removed haar (splitAction n x μ β)
          (splitExcess n x μ β) z * G z.1) r = 0 := by
    rw [GibbsMarginalTower.response_eq_expectation haar _ _ (splitAction_continuous n x μ β) r]
    dsimp only
    rw [integral_mul_const]
    have hr := GibbsCrossCovariance.removed_response haar _ _ (splitAction_continuous n x μ β)
      (splitExcess_continuous n x μ β) r
    rw [GibbsMarginalTower.response_eq_expectation haar _ _
      (splitAction_continuous n x μ β) r] at hr
    rw [hr, zero_mul]
  simp only [hz, integral_zero]

omit [Fact (1 < n)] in
theorem noise_mean_zero (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    (∫ U, noise n x μ β U ∂wilsonLaw n Q character β 2) = 0 := by
  simpa only [mul_one] using noise_exterior_orthogonal n x μ β (fun _ => 1) continuous_const

/-- The retained variance is centered by its own actual mean. -/
def retainedVariance (x : Vertex n) (μ : Fin 4) (β : ℝ) : ℝ :=
  ∫ U, (retained n x μ β U -
    ∫ V, retained n x μ β V ∂wilsonLaw n Q character β 2)^2 ∂wilsonLaw n Q character β 2

/-- The actual mean square of the removed conditional fluctuation. -/
def noiseEnergy (x : Vertex n) (μ : Fin 4) (β : ℝ) : ℝ :=
  ∫ U, (noise n x μ β U)^2 ∂wilsonLaw n Q character β 2

omit [Fact (1 < n)] in
theorem retainedVariance_eq (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    retainedVariance n x μ β =
      (∫ U, (retained n x μ β U)^2 ∂wilsonLaw n Q character β 2) -
        (∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2)^2 := by
  have h := GibbsCrossCovariance.centered_product (wilsonLaw n Q character β 2)
    (retained n x μ β) (retained n x μ β) (retained_continuous n x μ β)
    (retained_continuous n x μ β)
    (∫ U, retained n x μ β U ∂wilsonLaw n Q character β 2)
    (∫ U, retained n x μ β U ∂wilsonLaw n Q character β 2)
  simp only [← pow_two] at h
  unfold retainedVariance
  rw [h, retained_mean]
  ring

omit [Fact (1 < n)] in
/-- Exact original-law Pythagoras; no approximation or variance bound is supplied. -/
theorem secondMoment_split (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    (∫ U, (localExcess n x μ β U)^2 ∂wilsonLaw n Q character β 2) =
      noiseEnergy n x μ β + ∫ U, (retained n x μ β U)^2 ∂wilsonLaw n Q character β 2 := by
  let ν := wilsonLaw n Q character β 2
  have hn := noise_continuous n x μ β
  have hr := retained_continuous n x μ β
  have hin : Integrable (fun U => (noise n x μ β U)^2) ν :=
    (hn.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hir : Integrable (fun U => (retained n x μ β U)^2) ν :=
    (hr.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hic : Integrable (fun U => 2 * (noise n x μ β U * retained n x μ β U)) ν :=
    (continuous_const.mul (hn.mul hr)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (U : Configuration (Vertex n) Q) : (localExcess n x μ β U)^2 =
      ((noise n x μ β U)^2 + (retained n x μ β U)^2) +
        2 * (noise n x μ β U * retained n x μ β U) := by unfold noise; ring
  simp_rw [he]
  have his : Integrable (fun U => (noise n x μ β U)^2 + (retained n x μ β U)^2) ν :=
    hin.add hir
  rw [integral_add his hic, integral_add hin hir, integral_const_mul]
  have hz := noise_exterior_orthogonal n x μ β (conditionalMean n x μ β)
    (conditionalMean_continuous n x μ β)
  change (∫ U, noise n x μ β U * retained n x μ β U ∂ν) = 0 at hz
  rw [hz, mul_zero, add_zero]
  rfl

omit [Fact (1 < n)] in
theorem total_variance_split (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    localVariance n x μ β = noiseEnergy n x μ β + retainedVariance n x μ β := by
  rw [localVariance_eq, retainedVariance_eq, secondMoment_split]
  ring


omit [Fact (1 < n)] in
/-- The L2 collapse is literally under the actual retained marginal as well. -/
theorem retained_law_square_error_eq (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    (∫ r, (conditionalMean n x μ β r - 3 / 2)^2
      ∂SU2WilsonSourceApproximation.retainedLaw n x μ β) =
      ∫ U, (retained n x μ β U - 3 / 2)^2 ∂wilsonLaw n Q character β 2 :=
  SU2WilsonMarginalTransport.retained_integral_eq_wilson n x μ β _
    (((conditionalMean_continuous n x μ β).sub continuous_const).pow 2)

omit n [NeZero n] [Fact (1 < n)] in
/-- The actual retained response converges in mean square to the constant 3/2. -/
theorem retained_square_error_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Filter.Tendsto (fun i => ∫ U, (retained (period i) (x i) (μ i) (β i) U - 3 / 2)^2
      ∂wilsonLaw (period i) Q character (β i) 2) l (nhds 0) := by
  have h := ((tendsto_const_nhds : Filter.Tendsto (fun _ : ι => (3 / 2 : ℝ)) l
    (nhds (3 / 2))).sub (mean_tendsto period β hβ x μ)).const_mul (3 / 2)
  norm_num only [sub_self, mul_zero] at h
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) _ h
  filter_upwards [hβ.eventually_ge_atTop 0] with i hi
  exact retained_square_error_bound (period i) (x i) (μ i) (β i) hi

omit n [NeZero n] [Fact (1 < n)] in
/-- The second retained moment tends to the square of its constant limit. -/
theorem retained_second_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Filter.Tendsto (fun i => ∫ U, (retained (period i) (x i) (μ i) (β i) U)^2
      ∂wilsonLaw (period i) Q character (β i) 2) l (nhds (9 / 4)) := by
  have h := ((tendsto_const_nhds : Filter.Tendsto (fun _ : ι => (3 / 2 : ℝ)) l
    (nhds (3 / 2))).sub (mean_tendsto period β hβ x μ)).const_mul 3
  norm_num only [sub_self, mul_zero] at h
  have hz : Filter.Tendsto (fun i => (9 / 4 : ℝ) -
      ∫ U, (retained (period i) (x i) (μ i) (β i) U)^2
        ∂wilsonLaw (period i) Q character (β i) 2) l (nhds 0) := by
    apply squeeze_zero' _ _ h
    · filter_upwards [hβ.eventually_ge_atTop 0] with i hi
      exact (retained_second_error_bound (period i) (x i) (μ i) (β i) hi).1
    · filter_upwards [hβ.eventually_ge_atTop 0] with i hi
      exact (retained_second_error_bound (period i) (x i) (μ i) (β i) hi).2
  have ht := (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => (9 / 4 : ℝ)) l
    (nhds (9 / 4))).sub hz
  simpa only [sub_sub_cancel, sub_zero] using ht

omit n [NeZero n] [Fact (1 < n)] in
/-- No nonzero variance of this observable survives the actual one-link conditional averaging. -/
theorem retainedVariance_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Filter.Tendsto (fun i => retainedVariance (period i) (x i) (μ i) (β i)) l (nhds 0) := by
  have h := (retained_second_tendsto period β hβ x μ).sub ((mean_tendsto period β hβ x μ).pow 2)
  norm_num at h
  simpa only [retainedVariance_eq] using h

omit n [NeZero n] [Fact (1 < n)] in
/-- The entire limiting variance 3/2 is in the actual orthogonal removed fluctuation. -/
theorem noiseEnergy_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Filter.Tendsto (fun i => noiseEnergy (period i) (x i) (μ i) (β i)) l (nhds (3 / 2)) := by
  have h := (localVariance_tendsto period β hβ x μ).sub
    (retainedVariance_tendsto period β hβ x μ)
  have he (i : ι) : noiseEnergy (period i) (x i) (μ i) (β i) =
      localVariance (period i) (x i) (μ i) (β i) -
        retainedVariance (period i) (x i) (μ i) (β i) := by
    rw [total_variance_split]
    ring
  simpa only [he, sub_zero] using h

end
end UnifiedTheory.Clay.YangMills.SU2WilsonEquipartitionNoise
