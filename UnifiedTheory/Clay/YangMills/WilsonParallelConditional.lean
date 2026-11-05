/- Exact normalized product densities and product moments for simultaneous
updates of independent links in the actual 4D Wilson action. The eight-color
specialization has volume-independent coverage, but no mixing or physical
transfer comparison is asserted here. -/
import UnifiedTheory.Clay.YangMills.WilsonBlockIntegration
import UnifiedTheory.Clay.YangMills.WilsonParallelColors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonParallelConditional
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks
open WilsonBlockIntegration WilsonParallelColors

section Product
variable {I X : Type*} [Fintype I] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def normalizedDensity (A : X → ℝ) (x : X) : ℝ :=
  Real.exp (-A x) / (∫ y, Real.exp (-A y) ∂μ)

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem affine_product_weight (A : I → X → ℝ) (c : ℝ) (V : I → X) :
    Real.exp (-(c + ∑ i, A i (V i))) =
      Real.exp (-c) * ∏ i, Real.exp (-A i (V i)) := by
  rw [neg_add, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum]

omit [CompactSpace X] [BorelSpace X] in
theorem affine_product_partition (A : I → X → ℝ) (c : ℝ) :
    (∫ V, Real.exp (-(c + ∑ i, A i (V i))) ∂Measure.pi (fun _ : I => μ)) =
      Real.exp (-c) * ∏ i, ∫ x, Real.exp (-A i x) ∂μ := by
  simp_rw [affine_product_weight]
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (μ := fun _ : I => μ)
    (fun i x => Real.exp (-A i x))

omit [CompactSpace X] [BorelSpace X] in
/-- The exterior-dependent constant cancels from the actual normalized
density. The remaining factors are the normalized one-coordinate densities. -/
theorem normalizedDensity_product (A : I → X → ℝ) (c : ℝ) (V : I → X) :
    normalizedDensity (Measure.pi (fun _ : I => μ))
      (fun W => c + ∑ i, A i (W i)) V =
      ∏ i, normalizedDensity μ (A i) (V i) := by
  unfold normalizedDensity
  rw [affine_product_weight, affine_product_partition, Finset.prod_div_distrib]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

/-- Every product test has the product of the genuine normalized marginal
expectations under the fixed-exterior Gibbs probability law. -/
theorem affine_product_expectation (A : I → X → ℝ) (hA : ∀ i, Continuous (A i))
    (c : ℝ) (F : I → X → ℝ) :
    (∫ V, ∏ i, F i (V i) ∂CompactGibbsContinuity.law
      (Measure.pi (fun _ : I => μ)) (fun W => c + ∑ i, A i (W i))) =
      ∏ i, ∫ x, F i x ∂CompactGibbsContinuity.law μ (A i) := by
  have hs : Continuous (fun W : I → X => c + ∑ i, A i (W i)) :=
    continuous_const.add (continuous_finset_sum _ (fun i _ => (hA i).comp (continuous_apply i)))
  have hi : (∫ V, ∏ i, F i (V i) ∂CompactGibbsContinuity.law
      (Measure.pi (fun _ : I => μ)) (fun W => c + ∑ i, A i (W i))) =
      (∫ V, Real.exp (-(c + ∑ i, A i (V i))) * ∏ i, F i (V i)
        ∂Measure.pi (fun _ : I => μ)) /
      (∫ V, Real.exp (-(c + ∑ i, A i (V i))) ∂Measure.pi (fun _ : I => μ)) :=
    LocalGibbsComparison.weighted_integral _ _
    (Real.continuous_exp.comp hs.neg).measurable (fun _ => (Real.exp_pos _).le)
    (CompactGibbsContinuity.partition_positive _ _ hs) _
  rw [hi]
  simp_rw [affine_product_weight]
  have he (V : I → X) :
      (Real.exp (-c) * ∏ i, Real.exp (-A i (V i))) * ∏ i, F i (V i) =
      Real.exp (-c) * ∏ i, (Real.exp (-A i (V i)) * F i (V i)) := by
    rw [Finset.prod_mul_distrib, mul_assoc]
  simp_rw [he]
  rw [integral_const_mul,
    integral_fintype_prod_eq_prod (μ := fun _ : I => μ)
      (fun i x => Real.exp (-A i x) * F i x),
    integral_const_mul,
    integral_fintype_prod_eq_prod (μ := fun _ : I => μ)
      (fun i x => Real.exp (-A i x)),
    mul_div_mul_left _ _ (Real.exp_ne_zero _), ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (LocalGibbsComparison.weighted_integral μ _
    (Real.continuous_exp.comp (hA i).neg).measurable
    (fun _ => (Real.exp_pos _).le)
    (CompactGibbsContinuity.partition_positive μ _ (hA i)) _).symm

/-- Equality of probability measures, proved on all measurable rectangles,
not merely a formal product of unnormalized partition functions. -/
theorem affine_product_law (A : I → X → ℝ) (hA : ∀ i, Continuous (A i)) (c : ℝ) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ))
      (fun W => c + ∑ i, A i (W i)) =
      Measure.pi (fun i => CompactGibbsContinuity.law μ (A i)) := by
  classical
  have hsA : Continuous (fun W : I → X => c + ∑ i, A i (W i)) :=
    continuous_const.add (continuous_finset_sum _ (fun i _ => (hA i).comp (continuous_apply i)))
  letI : IsProbabilityMeasure (CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ))
      (fun W => c + ∑ i, A i (W i))) :=
    CompactGibbsContinuity.law_probability _ _ hsA
  letI (i : I) : IsProbabilityMeasure (CompactGibbsContinuity.law μ (A i)) :=
    CompactGibbsContinuity.law_probability _ _ (hA i)
  symm
  apply Measure.pi_eq
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top (fun i _ => measure_ne_top _ _))).mp
  rw [ENNReal.toReal_prod]
  have he := affine_product_expectation μ A hA c (fun i => (s i).indicator 1)
  have hp (V : I → X) : (∏ i, (s i).indicator (1 : X → ℝ) (V i)) =
      (Set.pi Set.univ s).indicator 1 V := by
    simpa only [Finset.coe_univ] using
      (Set.indicator_pi_one_apply (M₀ := ℝ) Finset.univ s V).symm
  simp_rw [hp, integral_indicator_one (MeasurableSet.pi (Set.to_countable _) (fun i _ => hs i)),
    integral_indicator_one (hs _)] at he
  exact he

end Product

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- Actual normalized fixed-exterior Wilson block density, with the
unselected auxiliary coordinates retaining normalized Haar density one. -/
theorem wilson_block_density (χ : G → ℂ) (β c : ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (hS : Independent n S)
    (V : Link n → G) :
    normalizedDensity (Measure.pi (fun _ : Link n => compactHaar G))
      (fun W => action n G χ β c (blockUpdate n G U S W)) V =
      ∏ a, normalizedDensity (compactHaar G) (localAction n G χ β c U S a) (V a) := by
  have he := funext (action_sum n G χ β c U S hS)
  rw [he]
  exact normalizedDensity_product _ _ _ _

theorem wilson_block_product_moments (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (hS : Independent n S)
    (F : Link n → G → ℝ) :
    (∫ V, ∏ a, F a (V a) ∂CompactGibbsContinuity.law
      (Measure.pi (fun _ : Link n => compactHaar G))
      (fun W => action n G χ β c (blockUpdate n G U S W))) =
      ∏ a, ∫ g, F a g ∂CompactGibbsContinuity.law (compactHaar G)
        (localAction n G χ β c U S a) := by
  rw [funext (action_sum n G χ β c U S hS)]
  exact affine_product_expectation _ _ (localAction_continuous n G χ hχ β c U S) _ _

theorem wilson_color_density (χ : G → ℂ) (β c : ℝ)
    (U : Configuration (Vertex n) G) (heven : 2 ∣ n) (d : Color) (V : Link n → G) :
    normalizedDensity (Measure.pi (fun _ : Link n => compactHaar G))
      (fun W => action n G χ β c (blockUpdate n G U (colorBlock n heven d) W)) V =
      ∏ a, normalizedDensity (compactHaar G)
        (localAction n G χ β c U (colorBlock n heven d) a) (V a) :=
  wilson_block_density n G χ β c U _ (colorBlock_independent n heven d) V

/-- Exact factorization of the actual fixed-exterior Wilson probability
measure; the statement includes arbitrary measurable events. -/
theorem wilson_block_law (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (hS : Independent n S) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar G))
      (fun W => action n G χ β c (blockUpdate n G U S W)) =
      Measure.pi (fun a => CompactGibbsContinuity.law (compactHaar G)
        (localAction n G χ β c U S a)) := by
  rw [funext (action_sum n G χ β c U S hS)]
  exact affine_product_law _ _ (localAction_continuous n G χ hχ β c U S) _

/-- All links of a color can be sampled simultaneously from independent
one-link conditional laws, for the original four-dimensional Wilson law. -/
theorem wilson_color_law (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (U : Configuration (Vertex n) G) (heven : 2 ∣ n) (d : Color) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar G))
      (fun W => action n G χ β c (blockUpdate n G U (colorBlock n heven d) W)) =
      Measure.pi (fun a => CompactGibbsContinuity.law (compactHaar G)
        (localAction n G χ β c U (colorBlock n heven d) a)) :=
  wilson_block_law n G χ hχ β c U _ (colorBlock_independent n heven d)

theorem wilson_color_product_moments (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (U : Configuration (Vertex n) G) (heven : 2 ∣ n) (d : Color)
    (F : Link n → G → ℝ) :
    (∫ V, ∏ a, F a (V a) ∂CompactGibbsContinuity.law
      (Measure.pi (fun _ : Link n => compactHaar G))
      (fun W => action n G χ β c (blockUpdate n G U (colorBlock n heven d) W))) =
      ∏ a, ∫ g, F a g ∂CompactGibbsContinuity.law (compactHaar G)
        (localAction n G χ β c U (colorBlock n heven d) a) :=
  wilson_block_product_moments n G χ hχ β c U _ (colorBlock_independent n heven d) F

end
end UnifiedTheory.Clay.YangMills.WilsonParallelConditional
