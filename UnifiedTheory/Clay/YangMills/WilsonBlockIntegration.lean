/- Exact source-preserving integration of geometrically independent Wilson
link blocks. The partition and its first two log derivatives are computed
from actual plaquette/action decompositions, not an assumed factorization.
This is one finite-cutoff step, not closure under repeated renormalization. -/
import UnifiedTheory.Clay.YangMills.WilsonIndependentBlocks
import UnifiedTheory.Clay.YangMills.CompactGibbsSource
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBlockIntegration
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonIndependentBlocks

section Product
variable {I X : Type*} [Fintype I] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [CompactSpace X] [BorelSpace X] in
/-- The source partition factorization includes the source at every real value. -/
theorem partition_product (A F : I → X → ℝ) (t : ℝ) :
    CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
      (fun V => ∑ i, A i (V i)) (fun V => ∑ i, F i (V i)) t =
      ∏ i, CompactGibbsSource.partition μ (A i) (F i) t := by
  unfold CompactGibbsSource.partition CompactGibbsSource.weight CompactGibbsSource.action
  have he (V : I → X) : -(∑ i, A i (V i) - t * ∑ i, F i (V i)) =
      ∑ i, -(A i (V i) - t * F i (V i)) := by
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [he, Real.exp_sum]
  exact integral_fintype_prod_eq_prod (μ := fun _ : I => μ)
    (fun i x => Real.exp (-(A i x - t * F i x)))

theorem log_partition_product (A F : I → X → ℝ)
    (hA : ∀ i, Continuous (A i)) (hF : ∀ i, Continuous (F i)) (t : ℝ) :
    Real.log (CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
      (fun V => ∑ i, A i (V i)) (fun V => ∑ i, F i (V i)) t) =
      ∑ i, Real.log (CompactGibbsSource.partition μ (A i) (F i) t) := by
  rw [partition_product]
  exact Real.log_prod (fun i _ => (CompactGibbsSource.partition_positive μ _ _ (hA i) (hF i) t).ne')

theorem log_product_hasDerivAt (A F : I → X → ℝ)
    (hA : ∀ i, Continuous (A i)) (hF : ∀ i, Continuous (F i)) (t : ℝ) :
    HasDerivAt (fun s => Real.log (CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
      (fun V => ∑ i, A i (V i)) (fun V => ∑ i, F i (V i)) s))
      (∑ i, CompactGibbsSource.expectation μ (A i) (F i) (F i) t) t := by
  have he := funext (log_partition_product μ A F hA hF)
  rw [he]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    CompactGibbsSource.log_partition_hasDerivAt μ _ _ (hA i) (hF i) t)

theorem log_product_second_hasDerivAt (A F : I → X → ℝ)
    (hA : ∀ i, Continuous (A i)) (hF : ∀ i, Continuous (F i)) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun u => Real.log
      (CompactGibbsSource.partition (Measure.pi (fun _ : I => μ))
        (fun V => ∑ i, A i (V i)) (fun V => ∑ i, F i (V i)) u)) s)
      (∑ i, CompactGibbsSource.covariance μ (A i) (F i) (F i) (F i) t) t := by
  have he := funext (fun s => (log_product_hasDerivAt μ A F hA hF s).deriv)
  rw [he]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    CompactGibbsSource.mean_hasDerivAt μ _ _ (hA i) (hF i) t)
end Product

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance : DecidableEq (Link n) := Classical.decEq _

def action (χ : G → ℂ) (β c : ℝ) (U : Configuration (Vertex n) G) : ℝ :=
  orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U

def source (χ : G → ℂ) (c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) : ℝ :=
  ∑ p, f p * plaquetteTerm n G χ c U p

def localAction (χ : G → ℂ) (β c : ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (a : Link n) (g : G) : ℝ :=
  if a ∈ S then action n G χ β c (Function.update U (selectedLink n a.1 a.2) g) -
    action n G χ β c U else 0

def localSource (χ : G → ℂ) (c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (a : Link n) (g : G) : ℝ :=
  if a ∈ S then source n G χ c f (Function.update U (selectedLink n a.1 a.2) g) -
    source n G χ c f U else 0

omit [NeZero n] [Group G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem update_continuous (U : Configuration (Vertex n) G) (a : Link n) :
    Continuous (fun g : G => Function.update U (selectedLink n a.1 a.2) g) := by
  apply continuous_pi
  intro e
  by_cases he : e = selectedLink n a.1 a.2
  · subst e
    simpa only [Function.update_self] using (continuous_id : Continuous (fun g : G => g))
  · simpa only [Function.update_of_ne he] using (continuous_const : Continuous (fun _ : G => U e))

omit [NeZero n] [Group G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem blockUpdate_continuous (U : Configuration (Vertex n) G) (S : Finset (Link n)) :
    Continuous (blockUpdate n G U S) := by
  apply continuous_pi
  intro e
  unfold blockUpdate
  by_cases he : edgeCoord n e ∈ S
  · simpa only [he, ↓reduceIte] using continuous_apply (edgeCoord n e)
  · simp only [he, ↓reduceIte]
    exact continuous_const

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem source_continuous (χ : G → ℂ) (hχ : Continuous χ) (c : ℝ)
    (f : PlaquetteIndex n → ℝ) : Continuous (source n G χ c f) := by
  apply continuous_finset_sum
  intro p _
  apply continuous_const.mul
  apply continuous_const.sub
  exact Complex.continuous_re.comp
    ((continuous_wilson (Quiver.Symmetrify (Vertex n)) G χ hχ (loops n p)).comp
      (continuous_orientedExtension (Vertex n) G))

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem localAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (a : Link n) :
    Continuous (localAction n G χ β c U S a) := by
  unfold localAction
  by_cases ha : a ∈ S
  · simp only [ha, ↓reduceIte]
    exact ((continuous_orientedWilsonAction (Vertex n) G χ hχ (base n) (loops n) β c).comp
      (update_continuous n G U a)).sub continuous_const
  · simp only [ha, ↓reduceIte]
    exact continuous_const

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem localSource_continuous (χ : G → ℂ) (hχ : Continuous χ) (c : ℝ)
    (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (a : Link n) : Continuous (localSource n G χ c f U S a) := by
  unfold localSource
  by_cases ha : a ∈ S
  · simp only [ha, ↓reduceIte]
    exact ((source_continuous n G χ hχ c f).comp (update_continuous n G U a)).sub continuous_const
  · simp only [ha, ↓reduceIte]
    exact continuous_const

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem action_sum (χ : G → ℂ) (β c : ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (hS : Independent n S) (V : Link n → G) :
    action n G χ β c (blockUpdate n G U S V) = action n G χ β c U +
      ∑ a, localAction n G χ β c U S a (V a) := by
  have h := action_decomposition n G χ β c U S hS V
  simp only [blockUpdate_singleton] at h
  simp only [localAction, Finset.sum_ite_mem_eq]
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem source_sum (χ : G → ℂ) (c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (hS : Independent n S)
    (V : Link n → G) :
    source n G χ c f (blockUpdate n G U S V) = source n G χ c f U +
      ∑ a, localSource n G χ c f U S a (V a) := by
  have h : source n G χ c f (blockUpdate n G U S V) - source n G χ c f U =
      ∑ a ∈ S, (source n G χ c f (Function.update U (selectedLink n a.1 a.2) (V a)) -
        source n G χ c f U) := by
    unfold source
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, term_decomposition n G χ c U S hS V, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp only [blockUpdate_singleton, mul_sub, Finset.sum_sub_distrib]
  simp only [localSource, Finset.sum_ite_mem_eq]
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Unselected auxiliary coordinates integrate to one; selected coordinates
are integrated with their actual Haar measures, with the exterior fixed. -/
def fiberPartition (χ : G → ℂ) (β c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (t : ℝ) : ℝ :=
  ∫ V, Real.exp (-action n G χ β c (blockUpdate n G U S V) +
    t * source n G χ c f (blockUpdate n G U S V))
    ∂Measure.pi (fun _ : Link n => compactHaar G)

theorem fiberPartition_eq (χ : G → ℂ) (β c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (hS : Independent n S) (t : ℝ) :
    fiberPartition n G χ β c f U S t =
      Real.exp (-action n G χ β c U + t * source n G χ c f U) *
      ∏ a, CompactGibbsSource.partition (compactHaar G)
        (localAction n G χ β c U S a) (localSource n G χ c f U S a) t := by
  rw [← partition_product]
  unfold fiberPartition CompactGibbsSource.partition CompactGibbsSource.weight
    CompactGibbsSource.action
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun V => by
    dsimp only
    rw [action_sum n G χ β c U S hS V, source_sum n G χ c f U S hS V, ← Real.exp_add]
    congr 1
    ring)

theorem fiber_log_eq (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (hS : Independent n S) (t : ℝ) :
    Real.log (fiberPartition n G χ β c f U S t) =
      -action n G χ β c U + t * source n G χ c f U +
      ∑ a, Real.log (CompactGibbsSource.partition (compactHaar G)
        (localAction n G χ β c U S a) (localSource n G χ c f U S a) t) := by
  have hp (a : Link n) : 0 < CompactGibbsSource.partition (compactHaar G)
      (localAction n G χ β c U S a) (localSource n G χ c f U S a) t :=
    CompactGibbsSource.partition_positive _ _ _ (localAction_continuous n G χ hχ β c U S a)
      (localSource_continuous n G χ hχ c f U S a) t
  rw [fiberPartition_eq n G χ β c f U S hS t,
    Real.log_mul (Real.exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr (fun a _ => (hp a).ne')),
    Real.log_exp, Real.log_prod (fun a _ => (hp a).ne')]

theorem fiber_log_hasDerivAt (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (hS : Independent n S) (t : ℝ) :
    HasDerivAt (fun s => Real.log (fiberPartition n G χ β c f U S s))
      (source n G χ c f U + ∑ a, CompactGibbsSource.expectation (compactHaar G)
        (localAction n G χ β c U S a) (localSource n G χ c f U S a)
        (localSource n G χ c f U S a) t) t := by
  rw [funext (fiber_log_eq n G χ hχ β c f U S hS)]
  convert ((hasDerivAt_const t (-action n G χ β c U)).add
    ((hasDerivAt_id t).mul_const (source n G χ c f U))).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
      CompactGibbsSource.log_partition_hasDerivAt (compactHaar G) _ _
      (localAction_continuous n G χ hχ β c U S a)
      (localSource_continuous n G χ hχ c f U S a) t)) using 1
  simp

/-- The conditional source curvature is the sum of actual one-link variances.
Covariances of the retained conditional means are not removed by this identity. -/
theorem fiber_log_second_hasDerivAt (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (hS : Independent n S) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun u => Real.log (fiberPartition n G χ β c f U S u)) s)
      (∑ a, CompactGibbsSource.covariance (compactHaar G)
        (localAction n G χ β c U S a) (localSource n G χ c f U S a)
        (localSource n G χ c f U S a) (localSource n G χ c f U S a) t) t := by
  rw [funext (fun s => (fiber_log_hasDerivAt n G χ hχ β c f U S hS s).deriv)]
  convert (hasDerivAt_const t (source n G χ c f U)).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
      CompactGibbsSource.mean_hasDerivAt (compactHaar G) _ _
      (localAction_continuous n G χ hχ β c U S a)
      (localSource_continuous n G χ hχ c f U S a) t)) using 1
  simp

omit [SecondCountableTopology G] in
theorem fiber_source_partition (χ : G → ℂ) (β c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (t : ℝ) :
    fiberPartition n G χ β c f U S t = CompactGibbsSource.partition
      (Measure.pi (fun _ : Link n => compactHaar G))
      (fun V => action n G χ β c (blockUpdate n G U S V))
      (fun V => source n G χ c f (blockUpdate n G U S V)) t := by
  unfold fiberPartition CompactGibbsSource.partition CompactGibbsSource.weight
    CompactGibbsSource.action
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun V => by dsimp only; congr 1; ring)

/-- Equality for the actual sourced fixed-exterior Gibbs variance, not just
a formal differentiation rule. Compactness proves all differentiation bounds. -/
theorem fiber_covariance_eq_sum (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (hS : Independent n S) (t : ℝ) :
    CompactGibbsSource.covariance (Measure.pi (fun _ : Link n => compactHaar G))
      (fun V => action n G χ β c (blockUpdate n G U S V))
      (fun V => source n G χ c f (blockUpdate n G U S V))
      (fun V => source n G χ c f (blockUpdate n G U S V))
      (fun V => source n G χ c f (blockUpdate n G U S V)) t =
      ∑ a, CompactGibbsSource.covariance (compactHaar G)
        (localAction n G χ β c U S a) (localSource n G χ c f U S a)
        (localSource n G χ c f U S a) (localSource n G χ c f U S a) t := by
  have hA := (continuous_orientedWilsonAction (Vertex n) G χ hχ (base n) (loops n) β c).comp
    (blockUpdate_continuous n G U S)
  have hF := (source_continuous n G χ hχ c f).comp (blockUpdate_continuous n G U S)
  have hd := CompactGibbsSource.log_partition_second_hasDerivAt
    (Measure.pi (fun _ : Link n => compactHaar G)) _ _ hA hF t
  have hb := fiber_log_second_hasDerivAt n G χ hχ β c f U S hS t
  simp_rw [fiber_source_partition n G χ β c f U S] at hb
  exact hd.unique hb

end
end UnifiedTheory.Clay.YangMills.WilsonBlockIntegration
