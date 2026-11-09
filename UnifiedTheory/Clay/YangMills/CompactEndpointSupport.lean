/- A source supported in a measurable endpoint region places at least half
of its variance-pair mass on that endpoint region, regardless of its rarity. -/
import UnifiedTheory.Clay.YangMills.CompactVariancePair
import UnifiedTheory.Clay.YangMills.HaarCenteredFluctuation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactEndpointSupport
noncomputable section
open MeasureTheory CompactDensityEntropy CompactVariancePair

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def pair (p f : C(X, ℝ)) (z : X × X) : ℝ := p z.1*p z.2*(f z.1-f z.2)^2

omit μ [IsProbabilityMeasure μ] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem pair_continuous (p f : C(X, ℝ)) : Continuous (pair p f) := by
  unfold pair
  fun_prop

omit μ [IsProbabilityMeasure μ] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem pair_nonneg (p f : C(X, ℝ)) (hp : ∀ x, 0 ≤ p x) (z : X × X) :
    0 ≤ pair p f z := mul_nonneg (mul_nonneg (hp _) (hp _)) (sq_nonneg _)

omit μ [IsProbabilityMeasure μ] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem pair_swap (p f : C(X, ℝ)) (z : X × X) : pair p f z.swap = pair p f z := by
  unfold pair
  simp only [Prod.swap]
  ring

def restricted (E : Set X) (p f : C(X, ℝ)) : ℝ :=
  ∫ z : X × X, (Prod.fst ⁻¹' E).indicator (pair p f) z ∂μ.prod μ

theorem restricted_iterated (E : Set X) (hE : MeasurableSet E) (p f : C(X, ℝ)) :
    restricted μ E p f = ∫ v, E.indicator (fun v => ∫ w, pair p f (v,w) ∂μ) v ∂μ := by
  rw [restricted, integral_prod _
    ((continuous_integrable (μ.prod μ) _ (pair_continuous p f)).indicator
      (hE.preimage measurable_fst))]
  apply integral_congr_ae
  filter_upwards with v
  by_cases hv : v ∈ E <;> simp [Set.indicator, hv]

omit [CompactSpace X] [BorelSpace X] in
theorem second_endpoint (E : Set X) (p f : C(X, ℝ)) :
    (∫ z : X × X, (Prod.snd ⁻¹' E).indicator (pair p f) z ∂μ.prod μ) =
      restricted μ E p f := by
  conv_rhs => rw [restricted, ← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z.2 ∈ E <;> simp [Set.indicator, pair_swap, hz]

/-- This support bound prevents a uniform small exceptional-source constant
for regions on which the observable itself can be supported. -/
theorem pair_le_twice_restricted (E : Set X) (hE : MeasurableSet E)
    (p f : C(X, ℝ)) (hp : ∀ x, 0 ≤ p x) (hf : ∀ x, x ∉ E → f x = 0) :
    pairMoment μ p f ≤ 2*restricted μ E p f := by
  have hi := continuous_integrable (μ.prod μ) _ (pair_continuous p f)
  have hl := hi.indicator (hE.preimage measurable_fst)
  have hr := hi.indicator (hE.preimage measurable_snd)
  have hpoint (z : X × X) : pair p f z ≤
      (Prod.fst ⁻¹' E).indicator (pair p f) z+
        (Prod.snd ⁻¹' E).indicator (pair p f) z := by
    have hn := pair_nonneg p f hp z
    by_cases hv : z.1 ∈ E <;> by_cases hw : z.2 ∈ E
    · simp only [Set.indicator, Set.mem_preimage, hv, hw, ↓reduceIte]
      linarith
    · simp only [Set.indicator, Set.mem_preimage, hv, hw, ↓reduceIte, add_zero, le_refl]
    · simp only [Set.indicator, Set.mem_preimage, hv, hw, ↓reduceIte, zero_add, le_refl]
    · simp only [Set.indicator, Set.mem_preimage, hv, hw, ↓reduceIte, add_zero]
      simp only [pair, hf _ hv, hf _ hw, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero,
        le_refl]
  have h := integral_mono hi (hl.add hr) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hl hr] at h
  rw [second_endpoint] at h
  rw [pair_prod]
  change (∫ z, pair p f z ∂μ.prod μ) ≤ _
  change (∫ z, pair p f z ∂μ.prod μ) ≤ restricted μ E p f+restricted μ E p f at h
  linarith

theorem pair_positive [Measure.IsOpenPosMeasure μ] (p f : C(X, ℝ))
    (hp : ∀ x, 0 < p x) (x y : X) (hne : f x ≠ f y) : 0 < pairMoment μ p f := by
  rw [pair_prod]
  have hc := pair_continuous p f
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (continuous_integrable (μ.prod μ) _ hc) (pair_nonneg p f (fun z => (hp z).le))
    (show pair p f (x,y) ≠ 0 from
      (mul_pos (mul_pos (hp x) (hp y)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))).ne')

end
end UnifiedTheory.Clay.YangMills.CompactEndpointSupport
