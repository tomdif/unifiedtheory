/- A valid replacement for loss-only exceptional-source absorption. The
localized source and the cutoff variation cost are both retained explicitly. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialSourceObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSourceLocalization
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge WilsonTemporalInfluence
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonVariancePair WilsonEndpointSupport
open CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def cutoffPair (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ))
    (u : Slice n) (z : Slice n × Slice n) : ℝ :=
  rawTransition n β hβ u z.1*rawTransition n β hβ u z.2*
    (χ z.1-χ z.2)^2*(f z.2)^2

theorem cutoffPair_nonneg (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ))
    (u : Slice n) (z : Slice n × Slice n) : 0 ≤ cutoffPair n β hβ χ f u z := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (rawTransition_pos n β hβ u z.1).le
      (rawTransition_pos n β hβ u z.2).le) (sq_nonneg _)) (sq_nonneg _)

theorem cutoffPair_continuous (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ)) :
    Continuous (fun z : Slice n × (Slice n × Slice n) => cutoffPair n β hβ χ f z.1 z.2) := by
  have hp := rawTransition_continuous n β hβ
  unfold cutoffPair
  have h1 := hp.comp (f := fun z : Slice n × (Slice n × Slice n) => (z.1,z.2.1))
    (by fun_prop)
  have h2 := hp.comp (f := fun z : Slice n × (Slice n × Slice n) => (z.1,z.2.2))
    (by fun_prop)
  exact (((h1.mul h2).mul (by fun_prop)).mul (by fun_prop))

/-- Ground weighting gives the same actual correlated pair density J. -/
theorem cutoffPair_ground (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ))
    (u v w : Slice n) :
    (WilsonGroundLocalComparison.ground n β hβ u)^2*cutoffPair n β hβ χ f u (v,w) =
      pairWeight n β hβ u v w*(χ v-χ w)^2*(f w)^2 := by
  unfold cutoffPair
  rw [← ground_cancel]
  ring

def cutoffRow (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ)) (u : Slice n) : ℝ :=
  ∫ z, cutoffPair n β hβ χ f u z
    ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)

theorem cutoffRow_continuous (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ)) :
    Continuous (cutoffRow n β hβ χ f) :=
  GibbsMarginalTower.fiber_integral_continuous
    ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))
    (fun z : Slice n × (Slice n × Slice n) => cutoffPair n β hβ χ f z.1 z.2)
    (cutoffPair_continuous n β hβ χ f)

theorem cutoffRow_nonneg (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ)) (u : Slice n) :
    0 ≤ cutoffRow n β hβ χ f u := integral_nonneg (cutoffPair_nonneg n β hβ χ f u)

def cutoffCost (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ)) : ℝ :=
  ∫ u, cutoffRow n β hβ χ f u ∂groundLaw n β hβ

/-- Restricting an endpoint is paid by a localized variance and the actual
two-endpoint cutoff variation. No small probability coefficient is inserted. -/
theorem row_localization (E : Set (Slice n)) (hE : MeasurableSet E)
    (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ)) (hχ : ∀ v ∈ E, χ v = 1)
    (u : Slice n) :
    rowMass n E β hβ f u ≤ 2*rowVariance n β hβ (χ*f) u+cutoffRow n β hβ χ f u := by
  let p := density n β hβ u
  let μ := WilsonSlabOperator.measure n
  have hi := continuous_integrable (μ.prod μ) _ (CompactEndpointSupport.pair_continuous p f)
  have hj := continuous_integrable (μ.prod μ) _
    (CompactEndpointSupport.pair_continuous p (χ*f))
  have hk := continuous_integrable (μ.prod μ) _
    ((cutoffPair_continuous n β hβ χ f).comp
      (f := fun z : Slice n × Slice n => (u,z)) (continuous_const.prodMk continuous_id))
  have hp (z : Slice n × Slice n) :
      (Prod.fst ⁻¹' E).indicator (CompactEndpointSupport.pair p f) z ≤
        2*CompactEndpointSupport.pair p (χ*f) z+2*cutoffPair n β hβ χ f u z := by
    by_cases hz : z.1 ∈ E
    · rw [Set.indicator_of_mem (show z ∈ Prod.fst ⁻¹' E from hz)]
      have hs : (f z.1-f z.2)^2 ≤
          2*(χ z.1*f z.1-χ z.2*f z.2)^2+2*(χ z.1-χ z.2)^2*(f z.2)^2 := by
        rw [hχ z.1 hz]
        nlinarith [sq_nonneg (f z.1-2*χ z.2*f z.2+f z.2)]
      have hm := mul_le_mul_of_nonneg_left hs
        (mul_nonneg (rawTransition_pos n β hβ u z.1).le
          (rawTransition_pos n β hβ u z.2).le)
      change rawTransition n β hβ u z.1*rawTransition n β hβ u z.2*(f z.1-f z.2)^2 ≤
        2*(rawTransition n β hβ u z.1*rawTransition n β hβ u z.2*
          (χ z.1*f z.1-χ z.2*f z.2)^2)+2*cutoffPair n β hβ χ f u z
      unfold cutoffPair
      nlinarith [hm]
    · rw [Set.indicator_of_notMem (show z ∉ Prod.fst ⁻¹' E from hz)]
      exact add_nonneg
        (mul_nonneg (by norm_num) (CompactEndpointSupport.pair_nonneg p (χ*f)
          (fun v => (rawTransition_pos n β hβ u v).le) z))
        (mul_nonneg (by norm_num) (cutoffPair_nonneg n β hβ χ f u z))
  have h := integral_mono (hi.indicator (hE.preimage measurable_fst))
    ((hj.const_mul 2).add (hk.const_mul 2)) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (hj.const_mul 2) (hk.const_mul 2),
    integral_const_mul, integral_const_mul] at h
  have hv : CompactVariancePair.pairMoment μ p (χ*f)/2 =
      rowVariance n β hβ (χ*f) u := rowVariance_pair n β hβ u (χ*f)
  rw [CompactVariancePair.pair_prod] at hv
  change (∫ z, CompactEndpointSupport.pair p (χ*f) z ∂μ.prod μ)/2 =
    rowVariance n β hβ (χ*f) u at hv
  rw [rowMass_pair n E hE]
  change CompactEndpointSupport.restricted μ E p f/2 ≤ _
  change CompactEndpointSupport.restricted μ E p f ≤
    2*(∫ z, CompactEndpointSupport.pair p (χ*f) z ∂μ.prod μ)+2*cutoffRow n β hβ χ f u at h
  linarith

theorem mean_localization (E : Set (Slice n)) (hE : MeasurableSet E)
    (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ)) (hχ : ∀ v ∈ E, χ v = 1) :
    meanMass n E β hβ f ≤ 2*loss n β hβ (χ*f)+cutoffCost n β hβ χ f := by
  letI := groundLaw_probability n β hβ
  have hv := continuous_integrable (groundLaw n β hβ) _ (rowVariance_continuous n β hβ (χ*f))
  have hc := continuous_integrable (groundLaw n β hβ) _ (cutoffRow_continuous n β hβ χ f)
  have h := integral_mono (rowMass_integrable n E hE β hβ f)
    ((hv.const_mul 2).add hc) (row_localization n E hE β hβ χ f hχ)
  simp only [Pi.add_apply] at h
  rw [integral_add (hv.const_mul 2) hc, integral_const_mul, mean_rowVariance_eq_loss] at h
  exact h

/-- A concrete physical cutoff equals one above defect t and vanishes below t / 2. -/
def spatialCutoff (t : ℝ) : C(Slice n, ℝ) :=
  ⟨fun u => min 1 (max 0 ((WilsonSpatialSourceObstruction.defect n u-t / 2)/(t / 2))),
    continuous_const.min (continuous_const.max
      (((WilsonSpatialSourceObstruction.defect n).continuous.sub continuous_const).div_const _))⟩

omit [NeZero n] in
theorem spatialCutoff_gauge (t : ℝ) (h : SliceGauge n Q) (u : Slice n) :
    spatialCutoff n t (gaugeSlice h u) = spatialCutoff n t u := by
  change min 1 (max 0
    ((WilsonSpatialSourceObstruction.defect n (gaugeSlice h u)-t / 2)/(t / 2))) = _
  rw [WilsonSpatialSourceObstruction.defect_gauge]
  rfl

omit [NeZero n] in
theorem spatialCutoff_range (t : ℝ) (u : Slice n) : spatialCutoff n t u ∈ Set.Icc 0 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

omit [NeZero n] in
theorem spatialCutoff_on_bad (t : ℝ) (ht : 0 < t) (u : Slice n)
    (hu : u ∈ WilsonSpatialSourceObstruction.bad n t) : spatialCutoff n t u = 1 := by
  apply min_eq_left
  apply (le_max_right _ _).trans'
  apply (le_div_iff₀ (half_pos ht)).mpr
  change t < WilsonSpatialSourceObstruction.defect n u at hu
  linarith

omit [NeZero n] in
theorem spatialCutoff_supported (t : ℝ) (ht : 0 < t) (u : Slice n)
    (hu : u ∉ WilsonSpatialSourceObstruction.bad n (t / 2)) : spatialCutoff n t u = 0 := by
  have hd : WilsonSpatialSourceObstruction.defect n u-t / 2 ≤ 0 := sub_nonpos.mpr (not_lt.mp hu)
  have hh := div_nonpos_of_nonpos_of_nonneg hd (half_pos ht).le
  change min 1 (max 0 ((WilsonSpatialSourceObstruction.defect n u-t / 2)/(t / 2))) = 0
  rw [max_eq_left hh]
  norm_num

omit [NeZero n] in
theorem spatialCutoff_mul_gauge (t : ℝ) (f : C(Slice n, ℝ))
    (hF : ∀ h u, f (gaugeSlice h u) = f u) (h : SliceGauge n Q) (u : Slice n) :
    (spatialCutoff n t*f) (gaugeSlice h u) = (spatialCutoff n t*f) u := by
  simp only [ContinuousMap.mul_apply, spatialCutoff_gauge, hF]

/-- A concrete spatial-large-field estimate, with both required costs visible. -/
theorem spatial_localization (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (ht : 0 < t)
    (f : C(Slice n, ℝ)) :
    meanMass n (WilsonSpatialSourceObstruction.bad n t) β hβ f ≤
      2*loss n β hβ (spatialCutoff n t*f)+cutoffCost n β hβ (spatialCutoff n t) f :=
  mean_localization n _ (WilsonSpatialSourceObstruction.bad_measurable n t) β hβ _ f
    (spatialCutoff_on_bad n t ht)

end
end UnifiedTheory.Clay.YangMills.WilsonSourceLocalization
