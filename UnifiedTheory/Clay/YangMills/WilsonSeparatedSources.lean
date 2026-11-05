/- Separated plaquette sources have zero mixed conditional covariance after
integrating an actual independent Wilson link block. The integration uses
the selected-edge subtype Haar measure of WilsonBlockMarginal, not redundant
auxiliary link variables. No nonzero or continuum lower bound is claimed. -/
import UnifiedTheory.Clay.YangMills.WilsonBlockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSeparatedSources
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonIndependentBlocks SingleLinkWilsonOscillation

def quadratic {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) : ℝ :=
  (∫ x, (F x)^2 ∂μ)-(∫ x, F x ∂μ)^2

theorem quadratic_neg {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) :
    quadratic μ (fun x => -F x) = quadratic μ F := by
  simp only [quadratic, neg_sq, integral_neg]

theorem quadratic_polarization {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F H : X → ℝ) (hF : Continuous F) (hH : Continuous H) :
    quadratic μ (fun x => F x+H x)-quadratic μ (fun x => F x-H x) =
      4*((∫ x, F x*H x ∂μ)-(∫ x, F x ∂μ)*(∫ x, H x ∂μ)) := by
  have hiF := hF.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hiH := hH.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hiP : Integrable (fun x => (F x+H x)^2) μ :=
    ((hF.add hH).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiM : Integrable (fun x => (F x-H x)^2) μ :=
    ((hF.sub hH).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hq : (∫ x, (F x+H x)^2 ∂μ)-(∫ x, (F x-H x)^2 ∂μ) =
      4*∫ x, F x*H x ∂μ := by
    rw [← integral_sub hiP hiM, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp only; ring)
  unfold quadratic
  rw [integral_add hiF hiH, integral_sub hiF hiH]
  nlinarith

section Product
variable {I X : Type*} [Fintype I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [CompactSpace X] [BorelSpace X] in
theorem affine_partition_product (A F : I → X → ℝ) (a f t : ℝ) :
    CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
      (fun V => a+∑ i, A i (V i)) (fun V => f+∑ i, F i (V i)) t =
      Real.exp (-a+t*f)*∏ i, CompactGibbsSource.partition μ (A i) (F i) t := by
  rw [← WilsonBlockIntegration.partition_product μ A F t]
  unfold CompactGibbsSource.partition CompactGibbsSource.weight CompactGibbsSource.action
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun V => by
    dsimp only
    rw [← Real.exp_add]
    congr 1
    ring)

theorem affine_log_partition_product (A F : I → X → ℝ)
    (hA : ∀ i, Continuous (A i)) (hF : ∀ i, Continuous (F i)) (a f t : ℝ) :
    Real.log (CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
      (fun V => a+∑ i, A i (V i)) (fun V => f+∑ i, F i (V i)) t) =
      -a+t*f+∑ i, Real.log (CompactGibbsSource.partition μ (A i) (F i) t) := by
  have hp (i : I) := CompactGibbsSource.partition_positive μ (A i) (F i) (hA i) (hF i) t
  rw [affine_partition_product, Real.log_mul (Real.exp_ne_zero _)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne')), Real.log_exp,
    Real.log_prod (fun i _ => (hp i).ne')]

/-- Variance additivity derived from the actual finite product partition,
including the reference constants in both action and source. -/
theorem product_quadratic_sum (A F : I → X → ℝ)
    (hA : ∀ i, Continuous (A i)) (hF : ∀ i, Continuous (F i)) (a f : ℝ) :
    quadratic (CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ))
      (fun V => a+∑ i, A i (V i))) (fun V => f+∑ i, F i (V i)) =
      ∑ i, quadratic (CompactGibbsContinuity.law μ (A i)) (F i) := by
  have hcA : Continuous (fun V : I → X => a+∑ i, A i (V i)) :=
    continuous_const.add (continuous_finset_sum _ (fun i _ => (hA i).comp (continuous_apply i)))
  have hcF : Continuous (fun V : I → X => f+∑ i, F i (V i)) :=
    continuous_const.add (continuous_finset_sum _ (fun i _ => (hF i).comp (continuous_apply i)))
  have hd (t : ℝ) : HasDerivAt (fun s => Real.log
      (CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
        (fun V => a+∑ i, A i (V i)) (fun V => f+∑ i, F i (V i)) s))
      (f+∑ i, CompactGibbsSource.expectation μ (A i) (F i) (F i) t) t := by
    rw [funext (affine_log_partition_product μ A F hA hF a f)]
    convert ((hasDerivAt_const t (-a)).add ((hasDerivAt_id t).mul_const f)).add
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        CompactGibbsSource.log_partition_hasDerivAt μ (A i) (F i) (hA i) (hF i) t)) using 1
    simp
  have hd2 : HasDerivAt (fun t => deriv (fun s => Real.log
      (CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
        (fun V => a+∑ i, A i (V i)) (fun V => f+∑ i, F i (V i)) s)) t)
      (∑ i, CompactGibbsSource.covariance μ (A i) (F i) (F i) (F i) 0) 0 := by
    rw [funext (fun t => (hd t).deriv)]
    convert (hasDerivAt_const 0 f).add
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        CompactGibbsSource.mean_hasDerivAt μ (A i) (F i) (hA i) (hF i) 0)) using 1
    simp
  have he := (CompactGibbsSource.log_partition_second_hasDerivAt
    (Measure.pi (fun _ : I => μ)) _ _ hcA hcF 0).unique hd2
  have hz : CompactGibbsSource.action (fun V : I → X => a+∑ i, A i (V i))
      (fun V : I → X => f+∑ i, F i (V i)) 0 =
        (fun V : I → X => a+∑ i, A i (V i)) := by
    funext V
    simp [CompactGibbsSource.action]
  have hzi (i : I) : CompactGibbsSource.action (A i) (F i) 0 = A i := by
    funext x
    simp [CompactGibbsSource.action]
  simpa only [CompactGibbsSource.covariance, CompactGibbsSource.expectation,
    hz, hzi, quadratic, pow_two] using he

/-- Disjoint coordinate dependence kills the mixed covariance under the
actual normalized additive Gibbs law, not merely under reference Haar. -/
theorem product_response_mul (A F H : I → X → ℝ)
    (hA : ∀ i, Continuous (A i)) (hF : ∀ i, Continuous (F i))
    (hH : ∀ i, Continuous (H i)) (a f h : ℝ)
    (hsep : ∀ i, (∀ x, F i x = 0) ∨ (∀ x, H i x = 0)) :
    (∫ V, (f+∑ i, F i (V i))*(h+∑ i, H i (V i))
      ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (fun V => a+∑ i, A i (V i))) =
      (∫ V, f+∑ i, F i (V i)
        ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (fun V => a+∑ i, A i (V i)))*
      (∫ V, h+∑ i, H i (V i)
        ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (fun V => a+∑ i, A i (V i))) := by
  let ν := CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ))
    (fun V => a+∑ i, A i (V i))
  have hcA : Continuous (fun V : I → X => a+∑ i, A i (V i)) :=
    continuous_const.add (continuous_finset_sum _ (fun i _ => (hA i).comp (continuous_apply i)))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability _ _ hcA
  let P : (I → X) → ℝ := fun V => f+∑ i, F i (V i)
  let Q : (I → X) → ℝ := fun V => h+∑ i, H i (V i)
  have hP : Continuous P :=
    continuous_const.add (continuous_finset_sum _ (fun i _ => (hF i).comp (continuous_apply i)))
  have hQ : Continuous Q :=
    continuous_const.add (continuous_finset_sum _ (fun i _ => (hH i).comp (continuous_apply i)))
  have hp : (fun V => P V+Q V) = (fun V => (f+h)+∑ i, (F i (V i)+H i (V i))) := by
    funext V
    simp only [P, Q, Finset.sum_add_distrib]
    ring
  have hm : (fun V => P V-Q V) = (fun V => (f-h)+∑ i, (F i (V i)-H i (V i))) := by
    funext V
    simp only [P, Q, Finset.sum_sub_distrib]
    ring
  have heq : quadratic ν (fun V => P V+Q V) = quadratic ν (fun V => P V-Q V) := by
    rw [hp, hm]
    change quadratic (CompactGibbsContinuity.law _ _) _ =
      quadratic (CompactGibbsContinuity.law _ _) _
    rw [product_quadratic_sum μ A (fun i x => F i x+H i x) hA (fun i => (hF i).add (hH i)),
      product_quadratic_sum μ A (fun i x => F i x-H i x) hA (fun i => (hF i).sub (hH i))]
    apply Finset.sum_congr rfl
    intro i _
    rcases hsep i with hi | hi
    · simp_rw [hi, zero_add, zero_sub]
      exact (quadratic_neg _ _).symm
    · simp_rw [hi, add_zero, sub_zero]
  have hz := quadratic_polarization ν P Q hP hQ
  rw [heq, sub_self] at hz
  change (∫ V, P V*Q V ∂ν) = (∫ V, P V ∂ν)*(∫ V, Q V ∂ν)
  linarith
end Product

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance : DecidableEq (Link n) := Classical.decEq _

/-- No selected link touches both plaquette source supports. Merely
disjoint sets of plaquettes would not imply this condition. -/
def SeparatedOnBlock (S : Finset (Edge (Vertex n))) (f g : PlaquetteIndex n → ℝ) : Prop :=
  ∀ e ∈ S,
    (∀ p ∈ affected n (edgeCoord n e).1 (edgeCoord n e).2, f p = 0) ∨
    (∀ p ∈ affected n (edgeCoord n e).1 (edgeCoord n e).2, g p = 0)

def splitSource (χ : G → ℂ) (c : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ)
    (z : WilsonBlockMarginal.Outside (G := G) S × WilsonBlockMarginal.Inside (G := G) S) : ℝ :=
  WilsonBlockIntegration.source n G χ c f (WilsonBlockMarginal.assemble S z)

omit [NeZero n] in
theorem edgeCoord_injective : Function.Injective (edgeCoord n) := by
  intro e e' h
  rw [← selected_edgeCoord n e, ← selected_edgeCoord n e', h]

def assignment (S : Finset (Edge (Vertex n))) (V : WilsonBlockMarginal.Inside (G := G) S)
    (a : Link n) : G :=
  if h : selectedLink n a.1 a.2 ∈ S then V ⟨selectedLink n a.1 a.2,h⟩ else 1

omit [NeZero n] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem assignment_edge (S : Finset (Edge (Vertex n)))
    (V : WilsonBlockMarginal.Inside (G := G) S) (e : {e : Edge (Vertex n) // e ∈ S}) :
    assignment n G S V (edgeCoord n e.1) = V e := by
  simp [assignment, selected_edgeCoord, e.2]

omit [NeZero n] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem assemble_blockUpdate (S : Finset (Edge (Vertex n)))
    (b : WilsonBlockMarginal.Outside (G := G) S) (V : WilsonBlockMarginal.Inside (G := G) S) :
    WilsonBlockMarginal.assemble S (b,V) =
      blockUpdate n G (WilsonBlockMarginal.assemble S (b,fun _ => 1))
        (S.image (edgeCoord n)) (assignment n G S V) := by
  funext e
  have hm : edgeCoord n e ∈ S.image (edgeCoord n) ↔ e ∈ S := by
    constructor
    · intro h
      obtain ⟨e',he',heq⟩ := Finset.mem_image.mp h
      exact (edgeCoord_injective n heq) ▸ he'
    · exact fun h => Finset.mem_image.mpr ⟨e,h,rfl⟩
  by_cases he : e ∈ S
  · rw [WilsonBlockMarginal.assemble_inside S _ e he]
    simp [blockUpdate, hm.mpr he, assignment, selected_edgeCoord, he]
  · rw [WilsonBlockMarginal.assemble_outside S _ e he]
    rw [blockUpdate_outside n G _ _ _ e (fun h => he (hm.mp h)),
      WilsonBlockMarginal.assemble_outside S _ e he]

omit [NeZero n] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
/-- Reindexes the actual geometric decomposition onto selected-edge subtype
variables; their product Haar measure has no unused auxiliary coordinates. -/
theorem inside_sum (S : Finset (Edge (Vertex n)))
    (b : WilsonBlockMarginal.Outside (G := G) S) (H : Configuration (Vertex n) G → ℝ)
    (hH : ∀ V : Link n → G,
      H (blockUpdate n G (WilsonBlockMarginal.assemble S (b,fun _ => 1))
        (S.image (edgeCoord n)) V) = H (WilsonBlockMarginal.assemble S (b,fun _ => 1))+
        ∑ a ∈ S.image (edgeCoord n),
          (H (Function.update (WilsonBlockMarginal.assemble S (b,fun _ => 1))
            (selectedLink n a.1 a.2) (V a))-H (WilsonBlockMarginal.assemble S (b,fun _ => 1))))
    (V : WilsonBlockMarginal.Inside (G := G) S) :
    H (WilsonBlockMarginal.assemble S (b,V)) = H (WilsonBlockMarginal.assemble S (b,fun _ => 1))+
      ∑ e : {e : Edge (Vertex n) // e ∈ S},
        (H (Function.update (WilsonBlockMarginal.assemble S (b,fun _ => 1)) e.1 (V e))-
          H (WilsonBlockMarginal.assemble S (b,fun _ => 1))) := by
  rw [assemble_blockUpdate n G S b V, hH,
    Finset.sum_image (fun e _ e' _ heq => edgeCoord_injective n heq), ← Finset.sum_coe_sort]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [selected_edgeCoord, assignment_edge]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem inside_action_sum (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n)))
    (b : WilsonBlockMarginal.Outside (G := G) S) (V : WilsonBlockMarginal.Inside (G := G) S) :
    WilsonBlockIntegration.action n G χ β c (WilsonBlockMarginal.assemble S (b,V)) =
      WilsonBlockIntegration.action n G χ β c (WilsonBlockMarginal.assemble S (b,fun _ => 1))+
      ∑ e : {e : Edge (Vertex n) // e ∈ S},
        (WilsonBlockIntegration.action n G χ β c
          (Function.update (WilsonBlockMarginal.assemble S (b,fun _ => 1)) e.1 (V e))-
        WilsonBlockIntegration.action n G χ β c
          (WilsonBlockMarginal.assemble S (b,fun _ => 1))) := by
  apply inside_sum n G S b (WilsonBlockIntegration.action n G χ β c) _ V
  intro W
  have h := action_decomposition n G χ β c (WilsonBlockMarginal.assemble S (b,fun _ => 1))
    (S.image (edgeCoord n)) hS W
  simp only [blockUpdate_singleton] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem inside_source_sum (χ : G → ℂ) (c : ℝ) (f : PlaquetteIndex n → ℝ)
    (S : Finset (Edge (Vertex n))) (hS : Independent n (S.image (edgeCoord n)))
    (b : WilsonBlockMarginal.Outside (G := G) S) (V : WilsonBlockMarginal.Inside (G := G) S) :
    splitSource n G χ c S f (b,V) =
      WilsonBlockIntegration.source n G χ c f (WilsonBlockMarginal.assemble S (b,fun _ => 1))+
      ∑ e : {e : Edge (Vertex n) // e ∈ S},
        (WilsonBlockIntegration.source n G χ c f
          (Function.update (WilsonBlockMarginal.assemble S (b,fun _ => 1)) e.1 (V e))-
        WilsonBlockIntegration.source n G χ c f
          (WilsonBlockMarginal.assemble S (b,fun _ => 1))) := by
  apply inside_sum n G S b (WilsonBlockIntegration.source n G χ c f) _ V
  intro W
  have h := WilsonBlockIntegration.source_sum n G χ c f
    (WilsonBlockMarginal.assemble S (b,fun _ => 1)) (S.image (edgeCoord n)) hS W
  simpa only [WilsonBlockIntegration.localSource, Finset.sum_ite_mem_eq] using h

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem source_update_unchanged (χ : G → ℂ) (c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) (e : Edge (Vertex n))
    (hf : ∀ p ∈ affected n (edgeCoord n e).1 (edgeCoord n e).2, f p = 0) (v : G) :
    WilsonBlockIntegration.source n G χ c f (Function.update U e v) =
      WilsonBlockIntegration.source n G χ c f U := by
  unfold WilsonBlockIntegration.source
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ affected n (edgeCoord n e).1 (edgeCoord n e).2
  · rw [hf p hp]
    simp
  · have h := term_update_unchanged n G χ c U {edgeCoord n e} (fun _ => v) p
      (by simpa using hp)
    simp only [blockUpdate_singleton, selected_edgeCoord] at h
    rw [h]

omit [NeZero n] [Group G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem edge_update_continuous (U : Configuration (Vertex n) G) (e : Edge (Vertex n)) :
    Continuous (fun v : G => Function.update U e v) := by
  simpa only [selected_edgeCoord] using
    WilsonBlockIntegration.update_continuous n G U (edgeCoord n e)

/-- Mixed conditional covariance vanishes under the true selected-edge Haar
fiber of the original Wilson action. All factorization and source locality
used here have been derived from the actual lattice geometry. -/
theorem actual_response_product (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (hS : Independent n (S.image (edgeCoord n)))
    (f g : PlaquetteIndex n → ℝ) (hsep : SeparatedOnBlock n S f g)
    (b : WilsonBlockMarginal.Outside (G := G) S) :
    GibbsMarginalTower.response (WilsonBlockMarginal.insideMeasure S (compactHaar G))
      (WilsonBlockMarginal.splitAction n G χ β c S)
      (fun z => splitSource n G χ c S f z*splitSource n G χ c S g z) b =
      GibbsMarginalTower.response (WilsonBlockMarginal.insideMeasure S (compactHaar G))
        (WilsonBlockMarginal.splitAction n G χ β c S) (splitSource n G χ c S f) b *
      GibbsMarginalTower.response (WilsonBlockMarginal.insideMeasure S (compactHaar G))
        (WilsonBlockMarginal.splitAction n G χ β c S) (splitSource n G χ c S g) b := by
  let U : Configuration (Vertex n) G := WilsonBlockMarginal.assemble S (b,fun _ => 1)
  let A : {e : Edge (Vertex n) // e ∈ S} → G → ℝ := fun e v =>
    WilsonBlockIntegration.action n G χ β c (Function.update U e.1 v)-
      WilsonBlockIntegration.action n G χ β c U
  let F : {e : Edge (Vertex n) // e ∈ S} → G → ℝ := fun e v =>
    WilsonBlockIntegration.source n G χ c f (Function.update U e.1 v)-
      WilsonBlockIntegration.source n G χ c f U
  let H : {e : Edge (Vertex n) // e ∈ S} → G → ℝ := fun e v =>
    WilsonBlockIntegration.source n G χ c g (Function.update U e.1 v)-
      WilsonBlockIntegration.source n G χ c g U
  have hA (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (A e) :=
    ((continuous_orientedWilsonAction (Vertex n) G χ hχ (base n) (loops n) β c).comp
      (edge_update_continuous n G U e.1)).sub continuous_const
  have hF (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (F e) :=
    ((WilsonBlockIntegration.source_continuous n G χ hχ c f).comp
      (edge_update_continuous n G U e.1)).sub continuous_const
  have hH (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (H e) :=
    ((WilsonBlockIntegration.source_continuous n G χ hχ c g).comp
      (edge_update_continuous n G U e.1)).sub continuous_const
  have hs (e : {e : Edge (Vertex n) // e ∈ S}) :
      (∀ v, F e v = 0) ∨ (∀ v, H e v = 0) := by
    rcases hsep e.1 e.2 with he | he
    · exact Or.inl (fun v => sub_eq_zero.mpr (source_update_unchanged n G χ c f U e.1 he v))
    · exact Or.inr (fun v => sub_eq_zero.mpr (source_update_unchanged n G χ c g U e.1 he v))
  have hact (V : WilsonBlockMarginal.Inside (G := G) S) :
      WilsonBlockMarginal.splitAction n G χ β c S (b,V) =
        WilsonBlockIntegration.action n G χ β c U+∑ e, A e (V e) :=
    inside_action_sum n G χ β c S hS b V
  have hfs (V : WilsonBlockMarginal.Inside (G := G) S) :
      splitSource n G χ c S f (b,V) =
        WilsonBlockIntegration.source n G χ c f U+∑ e, F e (V e) :=
    inside_source_sum n G χ c f S hS b V
  have hgs (V : WilsonBlockMarginal.Inside (G := G) S) :
      splitSource n G χ c S g (b,V) =
        WilsonBlockIntegration.source n G χ c g U+∑ e, H e (V e) :=
    inside_source_sum n G χ c g S hS b V
  simp only [GibbsMarginalTower.response_eq_expectation _ _ _
    (WilsonBlockMarginal.splitAction_continuous n G χ hχ β c S) b]
  simp_rw [hact, hfs, hgs]
  exact product_response_mul (compactHaar G) A F H hA hF hH
    (WilsonBlockIntegration.action n G χ β c U)
    (WilsonBlockIntegration.source n G χ c f U)
    (WilsonBlockIntegration.source n G χ c g U) hs

end
end UnifiedTheory.Clay.YangMills.WilsonSeparatedSources
