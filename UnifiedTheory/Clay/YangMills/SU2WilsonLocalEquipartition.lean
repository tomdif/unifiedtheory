/- Nonzero one-link excess-energy scaling in the actual weak-coupling Wilson
law, uniformly in the finite lattice period. This is a local conditional
fluctuation limit, not a nonzero continuum field or physical mass gap. -/
import UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability
import UnifiedTheory.Clay.YangMills.SU2WilsonMarginalTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2WilsonLocalEquipartition
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2HaarTilt SU2StarEnergy SU2WilsonConditionalSource
open scoped Quaternion RealInnerProductSpace

/-- The actual beta-scaled excess above the minimum of the conditional link action. -/
def excess (β : ℝ) (A : ℍ) (q : Q) : ℝ := 2 * β * (‖A‖ - ⟪(q : ℍ), A⟫)

theorem excess_nonneg (β : ℝ) (hβ : 0 ≤ β) (A : ℍ) (q : Q) : 0 ≤ excess β A q := by
  have h := real_inner_le_norm (q : ℍ) A
  rw [CStarRing.norm_of_mem_unitary q.property, one_mul] at h
  exact mul_nonneg (by positivity) (sub_nonneg.mpr h)

/-- Exact tilted-Haar mean, including the zero-staple endpoint. -/
theorem excess_mean (β : ℝ) (A : ℍ) :
    (∫ q, excess β A q ∂tiltLaw β A) = axisExcess (2 * β * ‖A‖) := by
  letI := tiltLaw_probability β A
  have hi : Integrable (fun q : Q => ⟪(q : ℍ), A⟫) (tiltLaw β A) :=
    (continuous_subtype_val.inner continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [excess, integral_const_mul]
  rw [integral_sub (integrable_const _) hi, tiltLaw_inner_mean]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [tiltMean_rotational, real_inner_self_eq_norm_sq, axisExcess_identity]
  by_cases hA : A = 0
  · simp [hA]
  · have hn : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
    field_simp

theorem axisExcess_nonneg (κ : ℝ) (hκ : 0 ≤ κ) : 0 ≤ axisExcess κ := by
  unfold axisExcess
  apply div_nonneg _ (axisPartition_pos κ).le
  apply integral_nonneg
  intro q
  have hq : (q : ℍ).re ≤ 1 := by
    have h := real_inner_le_norm (q : ℍ) (1 : ℍ)
    simpa only [Quaternion.inner_def, star_one, mul_one, norm_one,
      CStarRing.norm_of_mem_unitary q.property] using h
  exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hκ (by linarith))

/-- The normalized excess never exceeds its three-dimensional Gamma mean. -/
theorem axisExcess_bounds (κ : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ axisExcess κ ∧ axisExcess κ ≤ 3 / 2 := by
  refine ⟨axisExcess_nonneg κ hκ, ?_⟩
  rcases eq_or_lt_of_le hκ with h | h
  · rw [← h, axisExcess_zero]; norm_num
  · exact SU2HaarCovariance.axisExcess_le h

/-- The previously proved actual Gamma quotient supplies an explicit first-order limit. -/
theorem axisExcess_error {κ : ℝ} (hκ : 3 / 2 ≤ κ) :
    |axisExcess κ - 3 / 2| ≤ 33 / κ := by
  rw [SU2HaarScalarBridge.axisExcess_eq_scalar SU2SemicircleSlice.firstCoordinateFormula]
  have h := SU2ScalarTilt.excessMean_remainder hκ 1 (by omega)
  norm_num [SU2QuotientRemainder.sourceTruncation, SU2SourceCoefficients.coefficient_zero] at h
  convert h using 1; ring

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The local observable is evaluated on the full original Wilson configuration. -/
def localExcess (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (U : Configuration (Vertex n) Q) : ℝ :=
  excess β (stapleField n x μ U) (U (selectedLink n x μ))

omit [Fact (1 < n)] in
theorem localExcess_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (localExcess n x μ β) := by
  unfold localExcess excess
  exact continuous_const.mul ((stapleField_continuous n x μ).norm.sub
    ((continuous_subtype_val.comp (continuous_apply _)).inner (stapleField_continuous n x μ)))

/-- The subtracted quantity is the true minimum of the six-plaquette action. -/
theorem localExcess_eq_starEnergy (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (U : Configuration (Vertex n) Q) :
    localExcess n x μ β U = β * starEnergy n x μ U -
      2 * β * (6 - ‖stapleField n x μ U‖) := by
  rw [starEnergy_eq]
  unfold localExcess excess
  ring

omit [NeZero n] [Fact (1 < n)] in
theorem localExcess_nonneg (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 ≤ β)
    (U : Configuration (Vertex n) Q) : 0 ≤ localExcess n x μ β U :=
  excess_nonneg β hβ _ _

theorem localExcess_le_starEnergy (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 ≤ β)
    (U : Configuration (Vertex n) Q) : localExcess n x μ β U ≤ β * starEnergy n x μ U := by
  rw [localExcess_eq_starEnergy]
  have h := stapleField_norm_le_six n x μ U
  have hp : 0 ≤ 2 * β * (6 - ‖stapleField n x μ U‖) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr h)
  linarith

/-- The same actual observable in the proved exterior/link product coordinates. -/
def splitExcess (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (z : Exterior n Q x μ × Q) : ℝ := excess β (exteriorStaple n x μ z.1) z.2

omit [Fact (1 < n)] in
theorem splitExcess_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (splitExcess n x μ β) := by
  unfold splitExcess excess
  exact continuous_const.mul (((exteriorStaple_continuous n x μ).comp continuous_fst).norm.sub
    ((continuous_subtype_val.comp continuous_snd).inner
      ((exteriorStaple_continuous n x μ).comp continuous_fst)))

omit [Fact (1 < n)] in
theorem localExcess_assemble (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (z : Exterior n Q x μ × Q) :
    localExcess n x μ β (SingleCoordinateProduct.assemble (selectedLink n x μ) z) =
      splitExcess n x μ β z := by
  have he : exterior n x μ (SingleCoordinateProduct.assemble (selectedLink n x μ) z) = z.1 :=
    SU2WilsonMarginalTransport.exteriorProjection_assemble n x μ z
  simp only [localExcess, stapleField, he, SingleCoordinateProduct.assemble_self, splitExcess]

/-- An actual conditional response, not a prescribed exterior approximation. -/
def conditionalMean (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) : ℝ :=
  GibbsMarginalTower.response haar (splitAction n x μ β) (splitExcess n x μ β) r

omit [Fact (1 < n)] in
theorem conditionalMean_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (conditionalMean n x μ β) :=
  GibbsMarginalTower.response_continuous haar _ _ (splitAction_continuous n x μ β)
    (splitExcess_continuous n x μ β)

theorem conditionalMean_eq_axis (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    conditionalMean n x μ β r = axisExcess (2 * β * ‖exteriorStaple n x μ r‖) := by
  rw [conditionalMean, GibbsMarginalTower.response_eq_expectation haar _ _
    (splitAction_continuous n x μ β) r]
  change (∫ q, excess β (exteriorStaple n x μ r) q ∂conditionalLaw n x μ β r) = _
  rw [conditionalLaw_eq_tiltLaw, excess_mean]


omit [Fact (1 < n)] in
/-- Exact disintegration identifies the conditional response with the original Wilson mean. -/
theorem mean_eq_conditionalMean (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    (∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2) =
      ∫ U, conditionalMean n x μ β (exterior n x μ U) ∂wilsonLaw n Q character β 2 := by
  have ht := (SU2WilsonMarginalTransport.wilson_coordinates_preserving n x μ β).integral_comp
    (SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm.measurableEmbedding
    (splitExcess n x μ β)
  have he (U : Configuration (Vertex n) Q) :
      localExcess n x μ β U = splitExcess n x μ β
        ((SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm U) := by
    simpa only [MeasurableEquiv.apply_symm_apply] using
      localExcess_assemble n x μ β
        ((SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm U)
  simp_rw [he]
  rw [ht]
  have hr := GibbsMarginalTower.response_expectation (exteriorMeasure n Q x μ) haar
    (splitAction n x μ β) (splitExcess n x μ β)
    (splitAction_continuous n x μ β) (splitExcess_continuous n x μ β)
  rw [← hr]
  exact SU2WilsonMarginalTransport.retained_integral_eq_wilson n x μ β
    (conditionalMean n x μ β) (conditionalMean_continuous n x μ β)

theorem conditionalMean_bounds (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 ≤ β)
    (r : Exterior n Q x μ) :
    0 ≤ conditionalMean n x μ β r ∧ conditionalMean n x μ β r ≤ 3 / 2 := by
  rw [conditionalMean_eq_axis]
  exact axisExcess_bounds _ (by positivity)

/-- A bound on the genuine conditional response, charged only to the actual small-staple event. -/
theorem conditional_deficit_bound (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hβr : 3 / 4 ≤ β * r₀)
    (U : Configuration (Vertex n) Q) :
    3 / 2 - conditionalMean n x μ β (exterior n x μ U) ≤
      33 / (2 * β * r₀) + (badEvent n x μ r₀).indicator (fun _ => (3 / 2 : ℝ)) U := by
  classical
  by_cases hU : U ∈ badEvent n x μ r₀
  · rw [Set.indicator_of_mem hU]
    have h := (conditionalMean_bounds n x μ β hβ.le (exterior n x μ U)).1
    have hc : 0 ≤ 33 / (2 * β * r₀) := by positivity
    linarith
  · rw [Set.indicator_of_notMem hU, add_zero, conditionalMean_eq_axis]
    have hr : r₀ ≤ ‖stapleField n x μ U‖ := le_of_lt (lt_of_not_ge hU)
    have hk : 3 / 2 ≤ 2 * β * ‖stapleField n x μ U‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hr hβ.le]
    have hh := (abs_le.mp (axisExcess_error hk)).1
    change 3 / 2 - axisExcess (2 * β * ‖stapleField n x μ U‖) ≤ _
    have hi : 33 / (2 * β * ‖stapleField n x μ U‖) ≤ 33 / (2 * β * r₀) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hr (by positivity))
    linarith

/-- The normalized original Wilson mean is bounded on every volume and exterior. -/
theorem mean_bounds (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2) ∧
      (∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2) ≤ 3 / 2 := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  refine ⟨integral_nonneg (localExcess_nonneg n x μ β hβ), ?_⟩
  rw [mean_eq_conditionalMean]
  have hc := (conditionalMean_continuous n x μ β).comp (exterior_continuous n x μ)
  have h := integral_mono (hc.integrable_of_hasCompactSupport
      (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _))
    (integrable_const (3 / 2 : ℝ))
    (fun U => (conditionalMean_bounds n x μ β hβ (exterior n x μ U)).2)
  simpa using h

/-- An actual volume-independent weak-coupling estimate, with no continuum scaling premise. -/
theorem mean_error_bound (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hr₆ : r₀ < 6) (hβr : 3 / 4 ≤ β * r₀) :
    0 ≤ 3 / 2 - (∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2) ∧
      3 / 2 - (∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2) ≤
        33 / (2 * β * r₀) + 27 * WilsonEnergyDensity.energyEnvelope β / (6 - r₀) := by
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  refine ⟨sub_nonneg.mpr (mean_bounds n x μ β hβ.le).2, ?_⟩
  rw [mean_eq_conditionalMean]
  have hc := (conditionalMean_continuous n x μ β).comp (exterior_continuous n x μ)
  have hi : Integrable (fun U => conditionalMean n x μ β (exterior n x μ U)) ν :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := badEvent_measurable n x μ r₀
  have hind : Integrable ((badEvent n x μ r₀).indicator (fun _ => (3 / 2 : ℝ))) ν :=
    (integrable_const _).indicator hs
  have h := integral_mono ((integrable_const (3 / 2 : ℝ)).sub hi)
    ((integrable_const (33 / (2 * β * r₀))).add hind)
    (conditional_deficit_bound n x μ β r₀ hβ hr₀ hβr)
  simp only [Pi.sub_apply, Pi.add_apply] at h
  rw [integral_sub (integrable_const _) hi,
    integral_add (integrable_const _) hind, integral_indicator_const _ hs] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have hp := WilsonBadStapleProbability.bad_probability_bound n β hβ x μ r₀ hr₆
  change ν.real (badEvent n x μ r₀) ≤ _ at hp
  have hm := mul_le_mul_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 3 / 2)
  change 3 / 2 - (∫ U, conditionalMean n x μ β (exterior n x μ U) ∂ν) ≤ _
  calc
    _ ≤ 33 / (2 * β * r₀) + ν.real (badEvent n x μ r₀) * (3 / 2) := h
    _ ≤ 33 / (2 * β * r₀) +
        (18 * WilsonEnergyDensity.energyEnvelope β / (6 - r₀)) * (3 / 2) :=
      add_le_add_right hm _
    _ = _ := by ring

omit n [NeZero n] [Fact (1 < n)] in
/-- A nonzero local scaling limit under the actual full Wilson laws, allowing arbitrary
changing lattice volumes. This does not assert a fixed-smear continuum field limit. -/
theorem mean_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Filter.Tendsto
      (fun i => ∫ U, localExcess (period i) (x i) (μ i) (β i) U
        ∂wilsonLaw (period i) Q character (β i) 2) l (nhds (3 / 2)) := by
  have hi : Filter.Tendsto (fun i => 33 / (2 * β i * 3)) l (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp hβ).const_mul (33 / 6 : ℝ)
    convert h using 1
    · funext i; dsimp only [Function.comp_apply]; ring
    · norm_num
  have he := ((WilsonEnergyDensity.energyEnvelope_tendsto.comp hβ).const_mul 27).div_const (6 - 3)
  simp only [mul_zero, zero_div] at he
  have hz := hi.add he
  simp only [add_zero] at hz
  have hd : Filter.Tendsto (fun i => (3 / 2 : ℝ) -
      ∫ U, localExcess (period i) (x i) (μ i) (β i) U
        ∂wilsonLaw (period i) Q character (β i) 2) l (nhds 0) := by
    apply squeeze_zero' _ _ hz
    · filter_upwards [hβ.eventually_gt_atTop 0] with i hi
      exact sub_nonneg.mpr (mean_bounds (period i) (x i) (μ i) (β i) hi.le).2
    · filter_upwards [hβ.eventually_ge_atTop 1] with i hi
      exact (mean_error_bound (period i) (x i) (μ i) (β i) 3 (by linarith)
        (by norm_num) (by norm_num) (by nlinarith)).2
  have ht := (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ι => (3 / 2 : ℝ)) l (nhds (3 / 2))).sub hd
  simpa only [sub_sub_cancel, sub_zero] using ht

end
end UnifiedTheory.Clay.YangMills.SU2WilsonLocalEquipartition
