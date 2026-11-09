/- Nondegenerate local excess-energy fluctuations in the actual Wilson law.
These are microscopic conditional observables, not continuum fields at separated points. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonLocalEquipartition

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2WilsonLocalSecondMoment
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2HaarTilt SU2StarEnergy SU2WilsonConditionalSource
open SU2WilsonLocalEquipartition SU2HaarCovariance SqrtSourceRemainder
open scoped Quaternion RealInnerProductSpace

@[simp] theorem axisExcessSquare_zero : axisExcessSquare 0 = 0 := by
  simp [axisExcessSquare]

theorem axisExcessSquare_nonneg (κ : ℝ) : 0 ≤ axisExcessSquare κ := by
  unfold axisExcessSquare
  apply div_nonneg _ (axisPartition_pos κ).le
  exact integral_nonneg (fun q => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

theorem axisExcessSquare_bounds (κ : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ axisExcessSquare κ ∧ axisExcessSquare κ ≤ 15 / 4 := by
  refine ⟨axisExcessSquare_nonneg κ, ?_⟩
  rcases eq_or_lt_of_le hκ with h | h
  · rw [← h, axisExcessSquare_zero]; norm_num
  · exact axisExcessSquare_le h

/-- The actual Haar square moment is the second-moment Gamma quotient. -/
theorem axisExcessSquare_eq_gamma {κ : ℝ} (hκ : 0 < κ) :
    axisExcessSquare κ =
      gammaAverage (3 / 2) (fun u => u ^ 2 * cutoffSqrt κ u) /
        gammaAverage (3 / 2) (cutoffSqrt κ) := by
  unfold axisExcessSquare
  rw [SU2HaarScalarBridge.weighted_coordinate_formula
    SU2SemicircleSlice.firstCoordinateFormula κ (fun t => (κ * (1 - t)) ^ 2) (by fun_prop),
    SU2HaarScalarBridge.axisPartition_eq_scalar SU2SemicircleSlice.firstCoordinateFormula,
    div_div_div_cancel_right₀ (SU2ScalarTilt.partition_pos 0).ne',
    SU2ScalarTilt.excess_transform hκ (fun u => u ^ 2), SU2ScalarTilt.partition_transform hκ,
    mul_div_mul_left _ _ (SU2ScalarTilt.changeFactor_pos hκ).ne']
  have he : (fun u : ℝ => cutoffSqrt κ u * u ^ 2) =
      (fun u : ℝ => u ^ 2 * cutoffSqrt κ u) := by funext u; ring
  rw [he]
  unfold gammaAverage
  rw [div_div_div_cancel_right₀ (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).ne']

/-- An explicit first-order error derived from the exact Gamma moment expansion. -/
theorem axisExcessSquare_error {κ : ℝ} (hκ : 3 / 2 ≤ κ) :
    |axisExcessSquare κ - 15 / 4| ≤ 75 / (2 * κ) := by
  have hk : 0 < κ := by linarith
  let D := gammaAverage (3 / 2) (cutoffSqrt κ)
  let N := gammaAverage (3 / 2) (fun u => u ^ 2 * cutoffSqrt κ u)
  have hd : 1 / 2 ≤ D := su2_denominator_ge_half hκ
  have hD : 0 < D := by linarith
  have hn : |N - 15 / 4| ≤ 105 / (8 * κ) := by
    have h := gamma_average_moment_expansion_product
      (by norm_num : (0 : ℝ) < 3 / 2) hk 2 1
    norm_num [Finset.prod_range_succ, coefficient_zero] at h
    convert h using 1; ring
  have hd' : |D - 1| ≤ 3 / (2 * κ) := by
    have h := su2_denominator_expansion hk 1
    norm_num [Finset.prod_range_succ, coefficient_zero] at h
    exact h
  rw [axisExcessSquare_eq_gamma hk]
  change |N / D - 15 / 4| ≤ _
  have he : |N - (15 / 4) * D| ≤ 75 / (4 * κ) := by
    calc
      _ = |(N - 15 / 4) - (15 / 4) * (D - 1)| := by congr 1; ring
      _ ≤ |N - 15 / 4| + |(15 / 4) * (D - 1)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (N - 15 / 4) (-(15 / 4 * (D - 1)))
      _ ≤ 105 / (8 * κ) + (15 / 4) * (3 / (2 * κ)) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 15 / 4)]
        exact add_le_add hn (mul_le_mul_of_nonneg_left hd' (by norm_num))
      _ = _ := by ring
  have hq : 0 ≤ 75 / (2 * κ) := by positivity
  calc
    _ = |N - (15 / 4) * D| / D := by
      have hh : N / D - 15 / 4 = (N - (15 / 4) * D) / D := by
        field_simp
      rw [hh, abs_div, abs_of_pos hD]
    _ ≤ (75 / (4 * κ)) / D := div_le_div_of_nonneg_right he hD.le
    _ ≤ 75 / (2 * κ) := by
      apply (div_le_iff₀ hD).mpr
      have h := mul_le_mul_of_nonneg_left hd hq
      have hh : 75 / (2 * κ) * (1 / 2) = 75 / (4 * κ) := by ring
      rw [hh] at h
      exact h

/-- Exact actual one-link second moment, including a cancelling staple. -/
theorem excess_square_mean (β : ℝ) (hβ : 0 < β) (A : ℍ) :
    (∫ q, (excess β A q) ^ 2 ∂tiltLaw β A) = axisExcessSquare (2 * β * ‖A‖) := by
  by_cases hA : A = 0
  · subst A
    simp [excess]
  · have he (q : Q) : (excess β A q) ^ 2 =
        (2 * β) ^ 2 * (⟪(q : ℍ), A⟫ - ‖A‖) ^ 2 := by unfold excess; ring
    simp_rw [he]
    rw [integral_const_mul, radial_square_deviation β A hβ hA]
    have hn : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
    field_simp


variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The second conditional moment is taken under the actual Wilson fiber. -/
def conditionalSecondMoment (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) : ℝ :=
  GibbsMarginalTower.response haar (splitAction n x μ β)
    (fun z => (splitExcess n x μ β z) ^ 2) r

omit [Fact (1 < n)] in
theorem conditionalSecondMoment_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (conditionalSecondMoment n x μ β) :=
  GibbsMarginalTower.response_continuous haar _ _ (splitAction_continuous n x μ β)
    ((splitExcess_continuous n x μ β).pow 2)

theorem conditionalSecondMoment_eq_axis (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (hβ : 0 < β) (r : Exterior n Q x μ) :
    conditionalSecondMoment n x μ β r =
      axisExcessSquare (2 * β * ‖exteriorStaple n x μ r‖) := by
  rw [conditionalSecondMoment, GibbsMarginalTower.response_eq_expectation haar _ _
    (splitAction_continuous n x μ β) r]
  change (∫ q, (excess β (exteriorStaple n x μ r) q) ^ 2 ∂conditionalLaw n x μ β r) = _
  rw [conditionalLaw_eq_tiltLaw, excess_square_mean β hβ]

omit [Fact (1 < n)] in
/-- Exact Wilson disintegration, without an independent-exterior substitution. -/
theorem secondMoment_eq_conditional (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    (∫ U, (localExcess n x μ β U) ^ 2 ∂wilsonLaw n Q character β 2) =
      ∫ U, conditionalSecondMoment n x μ β (exterior n x μ U)
        ∂wilsonLaw n Q character β 2 := by
  have ht := (SU2WilsonMarginalTransport.wilson_coordinates_preserving n x μ β).integral_comp
    (SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm.measurableEmbedding
    (fun z => (splitExcess n x μ β z) ^ 2)
  have he (U : Configuration (Vertex n) Q) :
      localExcess n x μ β U = splitExcess n x μ β
        ((SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm U) := by
    simpa only [MeasurableEquiv.apply_symm_apply] using
      localExcess_assemble n x μ β
        ((SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm U)
  simp_rw [he]
  rw [ht]
  have hr := GibbsMarginalTower.response_expectation (exteriorMeasure n Q x μ) haar
    (splitAction n x μ β) (fun z => (splitExcess n x μ β z) ^ 2)
    (splitAction_continuous n x μ β) ((splitExcess_continuous n x μ β).pow 2)
  rw [← hr]
  exact SU2WilsonMarginalTransport.retained_integral_eq_wilson n x μ β
    (conditionalSecondMoment n x μ β) (conditionalSecondMoment_continuous n x μ β)

theorem conditionalSecondMoment_bounds (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 < β)
    (r : Exterior n Q x μ) :
    0 ≤ conditionalSecondMoment n x μ β r ∧
      conditionalSecondMoment n x μ β r ≤ 15 / 4 := by
  rw [conditionalSecondMoment_eq_axis n x μ β hβ]
  exact axisExcessSquare_bounds _ (by positivity)

theorem secondMoment_bounds (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 < β) :
    0 ≤ (∫ U, (localExcess n x μ β U) ^ 2 ∂wilsonLaw n Q character β 2) ∧
      (∫ U, (localExcess n x μ β U) ^ 2 ∂wilsonLaw n Q character β 2) ≤ 15 / 4 := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  rw [secondMoment_eq_conditional]
  have hc := (conditionalSecondMoment_continuous n x μ β).comp (exterior_continuous n x μ)
  have h := integral_mono (hc.integrable_of_hasCompactSupport
      (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _))
    (integrable_const (15 / 4 : ℝ))
    (fun U => (conditionalSecondMoment_bounds n x μ β hβ (exterior n x μ U)).2)
  simpa using h

theorem conditional_second_deficit_bound (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hβr : 3 / 4 ≤ β * r₀)
    (U : Configuration (Vertex n) Q) :
    15 / 4 - conditionalSecondMoment n x μ β (exterior n x μ U) ≤
      75 / (4 * β * r₀) + (badEvent n x μ r₀).indicator (fun _ => (15 / 4 : ℝ)) U := by
  classical
  by_cases hU : U ∈ badEvent n x μ r₀
  · rw [Set.indicator_of_mem hU]
    have h := (conditionalSecondMoment_bounds n x μ β hβ (exterior n x μ U)).1
    have hc : 0 ≤ 75 / (4 * β * r₀) := by positivity
    linarith
  · rw [Set.indicator_of_notMem hU, add_zero, conditionalSecondMoment_eq_axis n x μ β hβ]
    have hr : r₀ ≤ ‖stapleField n x μ U‖ := le_of_lt (lt_of_not_ge hU)
    have hk : 3 / 2 ≤ 2 * β * ‖stapleField n x μ U‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hr hβ.le]
    have hh := (abs_le.mp (axisExcessSquare_error hk)).1
    change 15 / 4 - axisExcessSquare (2 * β * ‖stapleField n x μ U‖) ≤ _
    have hi : 75 / (2 * (2 * β * ‖stapleField n x μ U‖)) ≤ 75 / (4 * β * r₀) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hr hβ.le]
    linarith

/-- A uniform second-moment estimate under the original interacting Wilson law. -/
theorem secondMoment_error_bound (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hr₆ : r₀ < 6) (hβr : 3 / 4 ≤ β * r₀) :
    0 ≤ 15 / 4 - (∫ U, (localExcess n x μ β U) ^ 2 ∂wilsonLaw n Q character β 2) ∧
      15 / 4 - (∫ U, (localExcess n x μ β U) ^ 2 ∂wilsonLaw n Q character β 2) ≤
        75 / (4 * β * r₀) + (135 / 2) * WilsonEnergyDensity.energyEnvelope β / (6 - r₀) := by
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  refine ⟨sub_nonneg.mpr (secondMoment_bounds n x μ β hβ).2, ?_⟩
  rw [secondMoment_eq_conditional]
  have hc := (conditionalSecondMoment_continuous n x μ β).comp (exterior_continuous n x μ)
  have hi : Integrable (fun U => conditionalSecondMoment n x μ β (exterior n x μ U)) ν :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := badEvent_measurable n x μ r₀
  have hind : Integrable ((badEvent n x μ r₀).indicator (fun _ => (15 / 4 : ℝ))) ν :=
    (integrable_const _).indicator hs
  have h := integral_mono ((integrable_const (15 / 4 : ℝ)).sub hi)
    ((integrable_const (75 / (4 * β * r₀))).add hind)
    (conditional_second_deficit_bound n x μ β r₀ hβ hr₀ hβr)
  simp only [Pi.sub_apply, Pi.add_apply] at h
  rw [integral_sub (integrable_const _) hi,
    integral_add (integrable_const _) hind, integral_indicator_const _ hs] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have hp := WilsonBadStapleProbability.bad_probability_bound n β hβ x μ r₀ hr₆
  change ν.real (badEvent n x μ r₀) ≤ _ at hp
  have hm := mul_le_mul_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 15 / 4)
  change 15 / 4 - (∫ U, conditionalSecondMoment n x μ β (exterior n x μ U) ∂ν) ≤ _
  calc
    _ ≤ 75 / (4 * β * r₀) + ν.real (badEvent n x μ r₀) * (15 / 4) := h
    _ ≤ 75 / (4 * β * r₀) +
        (18 * WilsonEnergyDensity.energyEnvelope β / (6 - r₀)) * (15 / 4) :=
      add_le_add_right hm _
    _ = _ := by ring

omit n [NeZero n] [Fact (1 < n)] in
/-- The actual second moment has the Gamma limit even when the lattice periods vary. -/
theorem secondMoment_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Filter.Tendsto
      (fun i => ∫ U, (localExcess (period i) (x i) (μ i) (β i) U) ^ 2
        ∂wilsonLaw (period i) Q character (β i) 2) l (nhds (15 / 4)) := by
  have hi : Filter.Tendsto (fun i => 75 / (4 * β i * 3)) l (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp hβ).const_mul (75 / 12 : ℝ)
    convert h using 1
    · funext i; dsimp only [Function.comp_apply]; ring
    · norm_num
  have he := ((WilsonEnergyDensity.energyEnvelope_tendsto.comp hβ).const_mul
    (135 / 2)).div_const (6 - 3)
  simp only [mul_zero, zero_div] at he
  have hz := hi.add he
  simp only [add_zero] at hz
  have hd : Filter.Tendsto (fun i => (15 / 4 : ℝ) -
      ∫ U, (localExcess (period i) (x i) (μ i) (β i) U) ^ 2
        ∂wilsonLaw (period i) Q character (β i) 2) l (nhds 0) := by
    apply squeeze_zero' _ _ hz
    · filter_upwards [hβ.eventually_gt_atTop 0] with i hi
      exact sub_nonneg.mpr (secondMoment_bounds (period i) (x i) (μ i) (β i) hi).2
    · filter_upwards [hβ.eventually_ge_atTop 1] with i hi
      exact (secondMoment_error_bound (period i) (x i) (μ i) (β i) 3 (by linarith)
        (by norm_num) (by norm_num) (by nlinarith)).2
  have ht := (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ι => (15 / 4 : ℝ)) l (nhds (15 / 4))).sub hd
  simpa only [sub_sub_cancel, sub_zero] using ht

/-- The centered variance of the actual local excess observable. -/
def localVariance (x : Vertex n) (μ : Fin 4) (β : ℝ) : ℝ :=
  ∫ U, (localExcess n x μ β U -
    ∫ V, localExcess n x μ β V ∂wilsonLaw n Q character β 2) ^ 2
      ∂wilsonLaw n Q character β 2

omit [Fact (1 < n)] in
theorem localVariance_eq (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    localVariance n x μ β =
      (∫ U, (localExcess n x μ β U) ^ 2 ∂wilsonLaw n Q character β 2) -
        (∫ U, localExcess n x μ β U ∂wilsonLaw n Q character β 2) ^ 2 := by
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  let m := ∫ U, localExcess n x μ β U ∂ν
  have hi : Integrable (localExcess n x μ β) ν :=
    (localExcess_continuous n x μ β).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun U => (localExcess n x μ β U) ^ 2) ν :=
    ((localExcess_continuous n x μ β).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (U : Configuration (Vertex n) Q) : (localExcess n x μ β U - m) ^ 2 =
      ((localExcess n x μ β U) ^ 2 - (2 * m) * localExcess n x μ β U) + m ^ 2 := by ring
  change (∫ U, (localExcess n x μ β U - m) ^ 2 ∂ν) = _
  simp_rw [he]
  have hisub : Integrable (fun U => (localExcess n x μ β U) ^ 2 -
      (2 * m) * localExcess n x μ β U) ν := hi2.sub (hi.const_mul (2 * m))
  rw [integral_add hisub (integrable_const _),
    integral_sub hi2 (hi.const_mul (2 * m)), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  change _ = (∫ U, (localExcess n x μ β U) ^ 2 ∂ν) - m ^ 2
  ring

omit n [NeZero n] [Fact (1 < n)] in
/-- Nondegenerate local fluctuations survive weak coupling uniformly in volume.
This is not a separated continuum covariance or a physical mass-gap estimate. -/
theorem localVariance_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (β : ι → ℝ) (hβ : Filter.Tendsto β l Filter.atTop)
    (x : ∀ i, Vertex (period i)) (μ : ι → Fin 4) :
    Filter.Tendsto (fun i => localVariance (period i) (x i) (μ i) (β i))
      l (nhds (3 / 2)) := by
  have h := (secondMoment_tendsto period β hβ x μ).sub
    ((mean_tendsto period β hβ x μ).pow 2)
  norm_num at h
  simpa only [localVariance_eq] using h

end
end UnifiedTheory.Clay.YangMills.SU2WilsonLocalSecondMoment
