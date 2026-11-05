/- Actual independent-block integration and continuous hybrid source approximation.
Disjoint affected plaquettes give a single global source-weight budget. This is
one exact finite-cutoff elimination, not closure of generated interactions or
control of the remaining source through infinitely many scales. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonSourceTheorem
import UnifiedTheory.Clay.YangMills.WilsonBlockWeightBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonBlockApproximation
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonIndependentBlocks WilsonSingleLinkStaples

section Product
variable {I X : Type*} [Fintype I] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Mean additivity is derived from the actual source partition factorization. -/
theorem affine_product_mean (A F : I → X → ℝ)
    (hA : ∀ i, Continuous (A i)) (hF : ∀ i, Continuous (F i)) (a f : ℝ) :
    (∫ V, f + ∑ i, F i (V i) ∂CompactGibbsContinuity.law
      (Measure.pi (fun _ : I => μ)) (fun V => a + ∑ i, A i (V i))) =
      f + ∑ i, ∫ q, F i q ∂CompactGibbsContinuity.law μ (A i) := by
  have hcA : Continuous (fun V : I → X => a + ∑ i, A i (V i)) :=
    continuous_const.add (continuous_finset_sum _ (fun i _ =>
      (hA i).comp (continuous_apply i)))
  have hcF : Continuous (fun V : I → X => f + ∑ i, F i (V i)) :=
    continuous_const.add (continuous_finset_sum _ (fun i _ =>
      (hF i).comp (continuous_apply i)))
  have hd : HasDerivAt (fun s => Real.log
      (CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
        (fun V => a + ∑ i, A i (V i)) (fun V => f + ∑ i, F i (V i)) s))
      (f + ∑ i, CompactGibbsSource.expectation μ (A i) (F i) (F i) 0) 0 := by
    rw [funext (WilsonSeparatedSources.affine_log_partition_product μ A F hA hF a f)]
    convert ((hasDerivAt_const 0 (-a)).add ((hasDerivAt_id 0).mul_const f)).add
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        CompactGibbsSource.log_partition_hasDerivAt μ (A i) (F i) (hA i) (hF i) 0)) using 1
    simp
  have he := (CompactGibbsSource.log_partition_hasDerivAt
    (Measure.pi (fun _ : I => μ)) _ _ hcA hcF 0).unique hd
  have hz : CompactGibbsSource.action (fun V : I → X => a + ∑ i, A i (V i))
      (fun V : I → X => f + ∑ i, F i (V i)) 0 =
        (fun V : I → X => a + ∑ i, A i (V i)) := by
    funext V
    simp [CompactGibbsSource.action]
  have hzi (i : I) : CompactGibbsSource.action (A i) (F i) 0 = A i := by
    funext q
    simp [CompactGibbsSource.action]
  simpa only [CompactGibbsSource.expectation, CompactGibbsSource.action,
    hz, hzi] using he
end Product

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

def baseConfiguration (S : Finset (Edge (Vertex n)))
    (b : WilsonBlockMarginal.Outside (G := Q) S) : Configuration (Vertex n) Q :=
  WilsonBlockMarginal.assemble S (b, fun _ => 1)

def linkExterior (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∈ S}) (b : WilsonBlockMarginal.Outside (G := Q) S) :
    Exterior n Q (edgeCoord n e.val).1 (edgeCoord n e.val).2 :=
  SU2WilsonMarginalTransport.exteriorProjection n (edgeCoord n e.val).1
    (edgeCoord n e.val).2 (baseConfiguration n S b)

/-- Response under the original action and true selected-edge Haar fiber. -/
def response (S : Finset (Edge (Vertex n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) : ℝ :=
  GibbsMarginalTower.response (WilsonBlockMarginal.insideMeasure S (compactHaar Q))
    (WilsonBlockMarginal.splitAction n Q character β 2 S)
    (WilsonSeparatedSources.splitSource n Q character 2 S f) b

def oneLinkResponse (S : Finset (Edge (Vertex n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (e : {e : Edge (Vertex n) // e ∈ S}) (b : WilsonBlockMarginal.Outside (G := Q) S) : ℝ :=
  SU2WilsonConditionalSource.conditionalSource n (edgeCoord n e.val).1
    (edgeCoord n e.val).2 β f (linkExterior n S e b)

omit [NeZero n] in
theorem baseConfiguration_continuous (S : Finset (Edge (Vertex n))) :
    Continuous (baseConfiguration n S) :=
  (WilsonBlockMarginal.assemble_continuous S).comp (continuous_id.prodMk continuous_const)

omit [NeZero n] in
theorem linkExterior_continuous (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (linkExterior n S e) :=
  (SU2WilsonMarginalTransport.exteriorProjection_continuous n _ _).comp
    (baseConfiguration_continuous n S)

theorem link_assemble_eq_update (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∈ S}) (b : WilsonBlockMarginal.Outside (G := Q) S)
    (q : Q) :
    SingleCoordinateProduct.assemble
      (selectedLink n (edgeCoord n e.val).1 (edgeCoord n e.val).2)
      (linkExterior n S e b, q) = Function.update (baseConfiguration n S b) e.val q := by
  funext j
  have he := selected_edgeCoord n e.val
  by_cases hj : j = selectedLink n (edgeCoord n e.val).1 (edgeCoord n e.val).2
  · subst j
    rw [SingleCoordinateProduct.assemble_self]
    change q = _
    rw [he, Function.update_self]
  · rw [SingleCoordinateProduct.assemble_other _ _ hj,
      Function.update_of_ne (fun h => hj (h.trans he.symm))]
    rfl

set_option maxHeartbeats 800000 in
-- Elaborating the two dependent coordinate splits requires extra reduction steps.
/-- The additive action constant cancels in each actual one-link law. -/
theorem link_increment_integral (S : Finset (Edge (Vertex n))) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (e : {e : Edge (Vertex n) // e ∈ S})
    (b : WilsonBlockMarginal.Outside (G := Q) S) :
    (∫ q, (WilsonBlockIntegration.source n Q character 2 f
      (Function.update (baseConfiguration n S b) e.val q) -
      WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b))
      ∂CompactGibbsContinuity.law (compactHaar Q) (fun q =>
        WilsonBlockIntegration.action n Q character β 2
          (Function.update (baseConfiguration n S b) e.val q) -
        WilsonBlockIntegration.action n Q character β 2 (baseConfiguration n S b))) =
      oneLinkResponse n S β f e b -
        WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b) := by
  let A : Q → ℝ := fun q => WilsonBlockIntegration.action n Q character β 2
    (Function.update (baseConfiguration n S b) e.val q)
  have hA : Continuous A :=
    (continuous_orientedWilsonAction _ Q character character_continuous
      (base n) (loops n) β 2).comp
        (WilsonSeparatedSources.edge_update_continuous n Q _ e.val)
  have hl : CompactGibbsContinuity.law (compactHaar Q) (fun q => A q -
      WilsonBlockIntegration.action n Q character β 2 (baseConfiguration n S b)) =
      SU2WilsonConditionalSource.conditionalLaw n (edgeCoord n e.val).1
        (edgeCoord n e.val).2 β (linkExterior n S e b) := by
    have he : (fun q => A q - WilsonBlockIntegration.action n Q character β 2
        (baseConfiguration n S b)) =
        (fun q => -WilsonBlockIntegration.action n Q character β 2
          (baseConfiguration n S b) + A q) := by funext q; ring
    rw [he, GibbsConstantShift.law_const_add _ A hA]
    unfold SU2WilsonConditionalSource.conditionalLaw
    congr 1
    funext q
    simp only [SU2WilsonConditionalSource.splitAction, link_assemble_eq_update]
    rfl
  rw [show (fun q => WilsonBlockIntegration.action n Q character β 2
      (Function.update (baseConfiguration n S b) e.val q) -
      WilsonBlockIntegration.action n Q character β 2 (baseConfiguration n S b)) =
        (fun q => A q - WilsonBlockIntegration.action n Q character β 2
          (baseConfiguration n S b)) from rfl, hl]
  letI := SU2WilsonConditionalSource.conditionalLaw_probability n (edgeCoord n e.val).1
    (edgeCoord n e.val).2 β (linkExterior n S e b)
  have hc := (WilsonBlockIntegration.source_continuous n Q character character_continuous
    2 f).comp (WilsonSeparatedSources.edge_update_continuous n Q (baseConfiguration n S b) e.val)
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := SU2WilsonConditionalSource.conditionalLaw n (edgeCoord n e.val).1
      (edgeCoord n e.val).2 β (linkExterior n S e b))
  change Integrable (fun q : Q => WilsonBlockIntegration.source n Q character 2 f
    (Function.update (baseConfiguration n S b) e.val q)) _ at hi
  rw [integral_sub hi (integrable_const _)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  congr 1
  rw [oneLinkResponse, SU2WilsonConditionalSource.conditionalSource_eq_integral]
  apply integral_congr_ae
  filter_upwards with q
  simp only [SU2WilsonConditionalSource.splitSource, link_assemble_eq_update]

/-- Exact independent-block conditional source, including the reference-source correction. -/
theorem response_eq_sum (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) :
    response n S β f b = WilsonBlockIntegration.source n Q character 2 f
      (baseConfiguration n S b) + ∑ e : {e : Edge (Vertex n) // e ∈ S},
        (oneLinkResponse n S β f e b -
          WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b)) := by
  let U := baseConfiguration n S b
  let A : {e : Edge (Vertex n) // e ∈ S} → Q → ℝ := fun e q =>
    WilsonBlockIntegration.action n Q character β 2 (Function.update U e.val q) -
      WilsonBlockIntegration.action n Q character β 2 U
  let F : {e : Edge (Vertex n) // e ∈ S} → Q → ℝ := fun e q =>
    WilsonBlockIntegration.source n Q character 2 f (Function.update U e.val q) -
      WilsonBlockIntegration.source n Q character 2 f U
  have hA (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (A e) :=
    ((continuous_orientedWilsonAction _ Q character character_continuous
      (base n) (loops n) β 2).comp
        (WilsonSeparatedSources.edge_update_continuous n Q U e.val)).sub continuous_const
  have hF (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (F e) :=
    ((WilsonBlockIntegration.source_continuous n Q character character_continuous 2 f).comp
      (WilsonSeparatedSources.edge_update_continuous n Q U e.val)).sub continuous_const
  have hact (V : WilsonBlockMarginal.Inside (G := Q) S) :
      WilsonBlockMarginal.splitAction n Q character β 2 S (b, V) =
        WilsonBlockIntegration.action n Q character β 2 U + ∑ e, A e (V e) :=
    WilsonSeparatedSources.inside_action_sum n Q character β 2 S hS b V
  have hsrc (V : WilsonBlockMarginal.Inside (G := Q) S) :
      WilsonSeparatedSources.splitSource n Q character 2 S f (b, V) =
        WilsonBlockIntegration.source n Q character 2 f U + ∑ e, F e (V e) :=
    WilsonSeparatedSources.inside_source_sum n Q character 2 f S hS b V
  rw [response, GibbsMarginalTower.response_eq_expectation _ _ _
    (WilsonBlockMarginal.splitAction_continuous n Q character character_continuous β 2 S)]
  simp_rw [hact, hsrc]
  rw [affine_product_mean (compactHaar Q) A F hA hF]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact link_increment_integral n S β f e b

variable [Fact (1 < n)]

def oneLinkHybrid (S : Finset (Edge (Vertex n))) (β r₀ r₁ : ℝ)
    (f : PlaquetteIndex n → ℝ) (e : {e : Edge (Vertex n) // e ∈ S})
    (b : WilsonBlockMarginal.Outside (G := Q) S) : ℝ :=
  SU2WilsonSourceApproximation.hybridSource n (edgeCoord n e.val).1
    (edgeCoord n e.val).2 β r₀ r₁ f (linkExterior n S e b)

/-- Only the single-link responses are approximated; the reference source
correction is kept exactly. Each low-staple sector is retained exactly. -/
def hybridSource (S : Finset (Edge (Vertex n))) (β r₀ r₁ : ℝ)
    (f : PlaquetteIndex n → ℝ) (b : WilsonBlockMarginal.Outside (G := Q) S) : ℝ :=
  WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b) +
    ∑ e : {e : Edge (Vertex n) // e ∈ S}, (oneLinkHybrid n S β r₀ r₁ f e b -
      WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b))

/-- The coefficient depends on total plaquette weight, not the number of selected links. -/
def errorEnvelope (β r₀ : ℝ) (f : PlaquetteIndex n → ℝ) : ℝ :=
  1280 * Real.exp 2 * r₀^2 * β^2 * Real.exp (-4 * β * r₀) * ∑ p, |f p|

omit [Fact (1 < n)] in
theorem errorEnvelope_nonneg (β r₀ : ℝ) (f : PlaquetteIndex n → ℝ) :
    0 ≤ errorEnvelope n β r₀ f := by unfold errorEnvelope; positivity

omit [Fact (1 < n)] in
theorem response_continuous (S : Finset (Edge (Vertex n))) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) : Continuous (response n S β f) :=
  GibbsMarginalTower.response_continuous _ _ _
    (WilsonBlockMarginal.splitAction_continuous n Q character character_continuous β 2 S)
    ((WilsonBlockIntegration.source_continuous n Q character character_continuous 2 f).comp
      (WilsonBlockMarginal.assemble_continuous S))

theorem hybridSource_continuous (S : Finset (Edge (Vertex n))) (β r₀ r₁ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (f : PlaquetteIndex n → ℝ) :
    Continuous (hybridSource n S β r₀ r₁ f) := by
  have hc := (WilsonBlockIntegration.source_continuous n Q character character_continuous 2 f).comp
    (baseConfiguration_continuous n S)
  apply hc.add
  apply continuous_finset_sum
  intro e _
  exact ((SU2WilsonSourceApproximation.hybridSource_continuous n (edgeCoord n e.val).1
    (edgeCoord n e.val).2 β r₀ r₁ hβ hr₀ f).comp (linkExterior_continuous n S e)).sub hc

/-- Actual block error with the geometric weight budget and no assumed remainder bound. -/
theorem hybrid_error_bound (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) (b : WilsonBlockMarginal.Outside (G := Q) S) :
    |response n S β f b - hybridSource n S β r₀ r₁ f b| ≤ errorEnvelope n β r₀ f := by
  have he : response n S β f b - hybridSource n S β r₀ r₁ f b =
      ∑ e : {e : Edge (Vertex n) // e ∈ S},
        (oneLinkResponse n S β f e b - oneLinkHybrid n S β r₀ r₁ f e b) := by
    rw [response_eq_sum n S hS β f b]
    simp only [hybridSource, Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ e : {e : Edge (Vertex n) // e ∈ S},
        |oneLinkResponse n S β f e b - oneLinkHybrid n S β r₀ r₁ f e b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : {e : Edge (Vertex n) // e ∈ S},
        SU2WilsonSourceApproximation.errorEnvelope n (edgeCoord n e.val).1
          (edgeCoord n e.val).2 β r₀ f := by
      apply Finset.sum_le_sum
      intro e _
      exact SU2WilsonSourceTheorem.hybrid_error_bound n (edgeCoord n e.val).1
        (edgeCoord n e.val).2 β r₀ r₁ hr₀ hcut hβr f (linkExterior n S e b)
    _ = (1280 * Real.exp 2 * r₀^2 * β^2 * Real.exp (-4 * β * r₀)) *
        ∑ e : {e : Edge (Vertex n) // e ∈ S},
          ∑ p ∈ SingleLinkWilsonOscillation.affected n
            (edgeCoord n e.val).1 (edgeCoord n e.val).2, |f p| := by
      simp only [SU2WilsonSourceApproximation.errorEnvelope, Finset.mul_sum]
    _ ≤ errorEnvelope n β r₀ f :=
      mul_le_mul_of_nonneg_left (WilsonBlockWeightBudget.inside_weight_budget n S
        (by
          intro a ha a' ha' haa'
          exact hS a (by simpa only [Finset.mem_image] using ha)
            a' (by simpa only [Finset.mem_image] using ha') haa') f) (by positivity)

/-- The retained probability uses the original interacting split action. -/
def retainedLaw (S : Finset (Edge (Vertex n))) (β : ℝ) :
    Measure (WilsonBlockMarginal.Outside (G := Q) S) :=
  GibbsMarginalTower.marginal (WilsonBlockMarginal.outsideMeasure S (compactHaar Q))
    (WilsonBlockMarginal.insideMeasure S (compactHaar Q))
    (WilsonBlockMarginal.splitAction n Q character β 2 S)

omit [Fact (1 < n)] in
theorem retainedLaw_probability (S : Finset (Edge (Vertex n))) (β : ℝ) :
    IsProbabilityMeasure (retainedLaw n S β) :=
  GibbsMarginalTower.marginal_probability _ _ _
    (WilsonBlockMarginal.splitAction_continuous n Q character character_continuous β 2 S)

/-- Mean-square approximation control under the true correlated block marginal.
The removed block fluctuation is not part of this approximation residual. -/
theorem retained_error_l2_bound (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β r₀ r₁ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) :
    (∫ b, (response n S β f b - hybridSource n S β r₀ r₁ f b)^2
      ∂retainedLaw n S β) ≤ (errorEnvelope n β r₀ f)^2 := by
  letI := retainedLaw_probability n S β
  have hc := ((response_continuous n S β f).sub
    (hybridSource_continuous n S β r₀ r₁ hβ hr₀ f)).pow 2
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := retainedLaw n S β)
  calc
    _ ≤ ∫ _b, (errorEnvelope n β r₀ f)^2 ∂retainedLaw n S β := by
      apply integral_mono hi (integrable_const _)
      intro b
      have h := hybrid_error_bound n S hS β r₀ r₁ hr₀ hcut hβr f b
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (errorEnvelope_nonneg n β r₀ f)).2 h
    _ = _ := by simp

omit [Fact (1 < n)] in
/-- The full interacting probability is transported to the actual block split. -/
theorem wilson_coordinates_preserving (S : Finset (Edge (Vertex n))) (β : ℝ) :
    MeasurePreserving (WilsonBlockMarginal.assemble (G := Q) S).symm
      (wilsonLaw n Q character β 2)
      (CompactGibbsContinuity.law
        ((WilsonBlockMarginal.outsideMeasure S (compactHaar Q)).prod
          (WilsonBlockMarginal.insideMeasure S (compactHaar Q)))
        (WilsonBlockMarginal.splitAction n Q character β 2 S)) := by
  have h := WilsonBlockMarginal.weightedLaw_preserving _ _
    (WilsonBlockMarginal.assemble (G := Q) S)
    (WilsonBlockMarginal.assemble_preserving S (compactHaar Q))
    (fun U => Real.exp (-WilsonBlockIntegration.action n Q character β 2 U))
    (Real.continuous_exp.comp
      (continuous_orientedWilsonAction _ Q character character_continuous
        (base n) (loops n) β 2).neg).measurable
  have hg := GibbsCoordinateTransport.gibbs_eq_weightedLaw (Vertex n) Q
    (orientedWilsonAction (Vertex n) Q character (base n) (loops n) β 2)
    (continuous_orientedWilsonAction _ Q character character_continuous
      (base n) (loops n) β 2)
  change wilsonLaw n Q character β 2 = LocalGibbsComparison.weightedLaw
    (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
    (fun U => Real.exp (-WilsonBlockIntegration.action n Q character β 2 U)) at hg
  rw [← hg] at h
  exact h.symm (WilsonBlockMarginal.assemble S)

omit [Fact (1 < n)] in
/-- Literal equality to the original Wilson marginal, including every retained event. -/
theorem retainedLaw_eq_map (S : Finset (Edge (Vertex n))) (β : ℝ) :
    retainedLaw n S β = (wilsonLaw n Q character β 2).map
      (fun U => ((WilsonBlockMarginal.assemble (G := Q) S).symm U).1) := by
  unfold retainedLaw GibbsMarginalTower.marginal
  rw [← (wilson_coordinates_preserving n S β).map_eq,
    Measure.map_map measurable_fst (WilsonBlockMarginal.assemble S).symm.measurable]
  rfl

/-- The same block approximation error under the original Wilson probability. -/
theorem wilson_error_l2_bound (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β r₀ r₁ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) :
    (∫ U, (response n S β f ((WilsonBlockMarginal.assemble (G := Q) S).symm U).1 -
      hybridSource n S β r₀ r₁ f ((WilsonBlockMarginal.assemble (G := Q) S).symm U).1)^2
        ∂wilsonLaw n Q character β 2) ≤ (errorEnvelope n β r₀ f)^2 := by
  have h := retained_error_l2_bound n S hS β r₀ r₁ hβ hr₀ hcut hβr f
  have hc := ((response_continuous n S β f).sub
    (hybridSource_continuous n S β r₀ r₁ hβ hr₀ f)).pow 2
  have hm : Measurable (fun U : Configuration (Vertex n) Q =>
      ((WilsonBlockMarginal.assemble (G := Q) S).symm U).1) :=
    measurable_fst.comp (WilsonBlockMarginal.assemble S).symm.measurable
  rw [retainedLaw_eq_map, integral_map hm.aemeasurable hc.aestronglyMeasurable] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.SU2WilsonBlockApproximation
