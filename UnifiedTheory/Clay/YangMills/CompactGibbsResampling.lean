/- Conditional Gibbs resampling as an actual stationary selfadjoint projection.
The density and its conditional averages are constructed from the action.
No mixing, spectral gap or physical-clock identification is assumed. -/
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactGibbsResampling
noncomputable section
open MeasureTheory GibbsMarginalTower

variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

/-- Resampling the inside variable while keeping the actual exterior fixed. -/
def average (A F : C(B × X, ℝ)) : C(B × X, ℝ) :=
  ⟨fun z => response μX A F z.1,
    (response_continuous μX A F A.continuous F.continuous).comp continuous_fst⟩

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem average_apply (A F : C(B × X, ℝ)) (z : B × X) :
    average μX A F z =
      ∫ x, F (z.1, x) ∂CompactGibbsContinuity.law μX (fun x => A (z.1, x)) :=
  response_eq_expectation μX A F A.continuous z.1

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem average_const (A : C(B × X, ℝ)) (c : ℝ) :
    average μX A (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
  ext z
  exact response_boundary μX A A.continuous (fun _ => c) z.1

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem average_sub (A F G : C(B × X, ℝ)) :
    average μX A (F - G) = average μX A F - average μX A G := by
  ext z
  exact response_sub μX A F G A.continuous F.continuous G.continuous z.1

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem average_smul (A F : C(B × X, ℝ)) (c : ℝ) :
    average μX A (c • F) = c • average μX A F := by
  ext z
  simp only [average_apply, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
/-- Conditional averaging is idempotent because the first average depends
only on the retained exterior. -/
theorem average_idempotent (A F : C(B × X, ℝ)) :
    average μX A (average μX A F) = average μX A F := by
  ext z
  exact response_boundary μX A A.continuous (response μX A F) z.1

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem average_nonnegative (A F : C(B × X, ℝ)) (hF : ∀ z, 0 ≤ F z) (z : B × X) :
    0 ≤ average μX A F z := by
  rw [average_apply]
  exact integral_nonneg (fun x => hF (z.1, x))

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem average_norm_le (A F : C(B × X, ℝ)) : ‖average μX A F‖ ≤ ‖F‖ := by
  apply ContinuousMap.norm_le _ (norm_nonneg F) |>.mpr
  intro z
  rw [average_apply]
  letI := CompactGibbsContinuity.law_probability μX (fun x => A (z.1, x))
    (A.continuous.comp (continuous_const.prodMk continuous_id))
  simpa using (norm_integral_le_of_norm_le_const
    (μ := CompactGibbsContinuity.law μX (fun x => A (z.1, x)))
    (Filter.Eventually.of_forall (fun x => F.norm_coe_le_norm (z.1, x))))

/-- The actual Gibbs measure is stationary for its constructed resampling. -/
theorem average_stationary (A F : C(B × X, ℝ)) :
    (∫ z, average μX A F z ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      ∫ z, F z ∂CompactGibbsContinuity.law (μB.prod μX) A := by
  have hm : (∫ b, response μX A F b ∂marginal μB μX A) =
      ∫ z, response μX A F z.1 ∂CompactGibbsContinuity.law (μB.prod μX) A :=
    integral_map measurable_fst.aemeasurable
      (response_continuous μX A F A.continuous F.continuous).aestronglyMeasurable
  exact hm.symm.trans (response_expectation μB μX A F A.continuous F.continuous)

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem response_mul_average (A F G : C(B × X, ℝ)) (b : B) :
    response μX A (fun z => F z * average μX A G z) b =
      response μX A F b * response μX A G b := by
  rw [response_eq_expectation μX _ _ A.continuous]
  change (∫ x, F (b, x) * response μX A G b
    ∂CompactGibbsContinuity.law μX (fun x => A (b, x))) = _
  rw [integral_mul_const, ← response_eq_expectation μX A F A.continuous b]

/-- Exact selfadjointness under the actual interacting Gibbs law. -/
theorem average_reversible (A F G : C(B × X, ℝ)) :
    (∫ z, F z * average μX A G z ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      ∫ z, average μX A F z * G z ∂CompactGibbsContinuity.law (μB.prod μX) A := by
  rw [← response_expectation μB μX A (fun z => F z * average μX A G z) A.continuous
    (F.continuous.mul (average μX A G).continuous)]
  simp_rw [response_mul_average]
  rw [← response_expectation μB μX A (fun z => average μX A F z * G z) A.continuous
    ((average μX A F).continuous.mul G.continuous)]
  apply integral_congr_ae
  filter_upwards [] with b
  have he : (fun z => average μX A F z * G z) = (fun z => G z * average μX A F z) := by
    funext z
    exact mul_comm _ _
  rw [he, response_mul_average, mul_comm]

theorem average_square_bound (A F : C(B × X, ℝ)) :
    (∫ z, (average μX A F z)^2 ∂CompactGibbsContinuity.law (μB.prod μX) A) ≤
      ∫ z, (F z)^2 ∂CompactGibbsContinuity.law (μB.prod μX) A := by
  have hm : (∫ b, (response μX A F b)^2 ∂marginal μB μX A) =
      ∫ z, (response μX A F z.1)^2 ∂CompactGibbsContinuity.law (μB.prod μX) A :=
    integral_map measurable_fst.aemeasurable
      ((response_continuous μX A F A.continuous F.continuous).pow 2).aestronglyMeasurable
  exact hm.symm.le.trans (response_l2_bound μB μX A F A.continuous F.continuous)

/-- The exact Dirichlet form is the squared conditional-averaging residual. -/
theorem dirichlet_eq_residual (A F : C(B × X, ℝ)) :
    (∫ z, F z * (F z - average μX A F z)
      ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      ∫ z, (F z - average μX A F z)^2
        ∂CompactGibbsContinuity.law (μB.prod μX) A := by
  let ν := CompactGibbsContinuity.law (μB.prod μX) A
  letI := CompactGibbsContinuity.law_probability (μB.prod μX) A A.continuous
  have horth : (∫ z, average μX A F z * (F z - average μX A F z) ∂ν) = 0 := by
    have h := average_reversible μB μX A F (F - average μX A F)
    rw [average_sub, average_idempotent, sub_self] at h
    simpa only [ContinuousMap.zero_apply, mul_zero, integral_zero,
      ContinuousMap.sub_apply] using h.symm
  have he (z : B × X) : F z * (F z - average μX A F z) =
      (F z - average μX A F z)^2 + average μX A F z * (F z - average μX A F z) := by
    ring
  simp_rw [he]
  have hi : Integrable (fun z => (F z - average μX A F z)^2) ν :=
    ((F.continuous.sub (average μX A F).continuous).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun z => average μX A F z * (F z - average μX A F z)) ν :=
    ((average μX A F).continuous.mul (F.continuous.sub (average μX A F).continuous))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add hi hj, horth, add_zero]

end
end UnifiedTheory.Clay.YangMills.CompactGibbsResampling
