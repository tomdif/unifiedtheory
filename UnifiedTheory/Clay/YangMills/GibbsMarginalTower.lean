/- Exact elimination of compact Gibbs variables and mean-square transport.
The retained measure is the actual pushforward of the original Gibbs law;
its effective action is minus the logarithm of the integrated partition.
All sources in the analytic statements below are continuous. -/
import UnifiedTheory.Clay.YangMills.WilsonResponseL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsMarginalTower
noncomputable section
open MeasureTheory LocalGibbsComparison
open scoped ENNReal

section OneStep
variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

def fiberMass (A : B × X → ℝ) (b : B) : ℝ := ∫ x, Real.exp (-A (b,x)) ∂μX

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
theorem fiberMass_positive (A : B × X → ℝ) (hA : Continuous A) (b : B) :
    0 < fiberMass μX A b :=
  CompactGibbsContinuity.partition_positive μX _
    (hA.comp (continuous_const.prodMk continuous_id))

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem fiber_integral_continuous (F : B × X → ℝ) (hF : Continuous F) :
    Continuous (fun b => ∫ x, F (b,x) ∂μX) := by
  obtain ⟨M,hM⟩ := (isCompact_range hF).isBounded.exists_norm_le
  apply continuous_of_dominated (bound := fun _ => M)
  · intro b
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro b
    exact Filter.Eventually.of_forall (fun x => hM _ ⟨(b,x),rfl⟩)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall
      (fun x => hF.comp (continuous_id.prodMk continuous_const))

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem fiberMass_continuous (A : B × X → ℝ) (hA : Continuous A) :
    Continuous (fiberMass μX A) :=
  fiber_integral_continuous μX _ (Real.continuous_exp.comp hA.neg)

def effectiveAction (A : B × X → ℝ) (b : B) : ℝ := -Real.log (fiberMass μX A b)

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem effectiveAction_continuous (A : B × X → ℝ) (hA : Continuous A) :
    Continuous (effectiveAction μX A) :=
  ((fiberMass_continuous μX A hA).log (fun b => (fiberMass_positive μX A hA b).ne')).neg

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
theorem exp_effectiveAction (A : B × X → ℝ) (hA : Continuous A) (b : B) :
    Real.exp (-effectiveAction μX A b) = fiberMass μX A b := by
  rw [effectiveAction, neg_neg, Real.exp_log (fiberMass_positive μX A hA b)]

theorem partition_eliminate (A : B × X → ℝ) (hA : Continuous A) :
    (∫ b, fiberMass μX A b ∂μB) = ∫ p, Real.exp (-A p) ∂μB.prod μX := by
  exact (integral_prod _ ((Real.continuous_exp.comp hA.neg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))).symm

def response (A F : B × X → ℝ) (b : B) : ℝ :=
  (∫ x, Real.exp (-A (b,x))*F (b,x) ∂μX) / fiberMass μX A b

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem response_continuous (A F : B × X → ℝ) (hA : Continuous A) (hF : Continuous F) :
    Continuous (response μX A F) :=
  (fiber_integral_continuous μX _ ((Real.continuous_exp.comp hA.neg).mul hF)).div
    (fiberMass_continuous μX A hA) (fun b => (fiberMass_positive μX A hA b).ne')

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
theorem response_eq_expectation (A F : B × X → ℝ) (hA : Continuous A) (b : B) :
    response μX A F b =
      ∫ x, F (b,x) ∂CompactGibbsContinuity.law μX (fun x => A (b,x)) := by
  symm
  exact weighted_integral μX _
    (Real.continuous_exp.comp (hA.comp (continuous_const.prodMk continuous_id)).neg).measurable
    (fun x => (Real.exp_pos _).le) (fiberMass_positive μX A hA b) _

def marginal (A : B × X → ℝ) : Measure B :=
  (CompactGibbsContinuity.law (μB.prod μX) A).map Prod.fst

omit [SecondCountableTopology B] in
theorem marginal_probability (A : B × X → ℝ) (hA : Continuous A) :
    IsProbabilityMeasure (marginal μB μX A) := by
  letI := CompactGibbsContinuity.law_probability (μB.prod μX) A hA
  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- Exact density of the actual pushforward marginal; the weight is the
integrated original Boltzmann weight, not a supplied replacement law. -/
theorem marginal_eq_weightedLaw (A : B × X → ℝ) (hA : Continuous A) :
    marginal μB μX A = weightedLaw μB (fiberMass μX A) := by
  ext s hs
  rw [marginal, Measure.map_apply measurable_fst hs]
  simp only [CompactGibbsContinuity.law, weightedLaw, Measure.smul_apply, smul_eq_mul]
  rw [partition_eliminate μB μX A hA]
  congr 1
  rw [withDensity_apply _ (measurable_fst hs), withDensity_apply _ hs]
  have hset : (Prod.fst : B × X → B) ⁻¹' s = s ×ˢ Set.univ := by ext p; simp
  rw [hset]
  rw [← Measure.restrict_prod_eq_prod_univ]
  rw [lintegral_prod (fun p => ENNReal.ofReal (Real.exp (-A p)))
    (Real.continuous_exp.comp hA.neg).measurable.ennreal_ofReal.aemeasurable]
  have hi (b : B) : Integrable (fun x => Real.exp (-A (b,x))) μX :=
    (Real.continuous_exp.comp (hA.comp (continuous_const.prodMk continuous_id)).neg)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun b =>
    (ofReal_integral_eq_lintegral_ofReal (hi b)
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-A (b,x))).le))).symm)

theorem marginal_eq_effectiveLaw (A : B × X → ℝ) (hA : Continuous A) :
    marginal μB μX A = CompactGibbsContinuity.law μB (effectiveAction μX A) := by
  rw [marginal_eq_weightedLaw μB μX A hA]
  unfold CompactGibbsContinuity.law
  congr 1
  funext b
  exact (exp_effectiveAction μX A hA b).symm

/-- The normalized response integrates to the original full expectation. -/
theorem response_expectation (A F : B × X → ℝ) (hA : Continuous A) (hF : Continuous F) :
    (∫ b, response μX A F b ∂marginal μB μX A) =
      ∫ p, F p ∂CompactGibbsContinuity.law (μB.prod μX) A := by
  rw [marginal_eq_weightedLaw μB μX A hA,
    weighted_integral μB _ (fiberMass_continuous μX A hA).measurable
      (fun b => (fiberMass_positive μX A hA b).le)
      (by rw [partition_eliminate μB μX A hA]
          exact CompactGibbsContinuity.partition_positive _ A hA),
    CompactGibbsContinuity.law,
    weighted_integral (μB.prod μX) (fun p => Real.exp (-A p))
      (Real.continuous_exp.comp hA.neg).measurable
      (fun p => (Real.exp_pos _).le) (CompactGibbsContinuity.partition_positive _ A hA),
    partition_eliminate μB μX A hA]
  congr 1
  have hc (b : B) : fiberMass μX A b * response μX A F b =
      ∫ x, Real.exp (-A (b,x))*F (b,x) ∂μX := by
    unfold response
    field_simp [(fiberMass_positive μX A hA b).ne']
  simp_rw [hc]
  have hi : Integrable (fun p => Real.exp (-A p)*F p) (μB.prod μX) :=
    ((Real.continuous_exp.comp hA.neg).mul hF).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (integral_prod _ hi).symm

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
theorem response_sub (A F H : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hH : Continuous H) (b : B) :
    response μX A (fun p => F p-H p) b = response μX A F b-response μX A H b := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b,x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  simp only [response_eq_expectation μX _ _ hA b]
  exact integral_sub
    ((hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((hH.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
theorem response_boundary (A : B × X → ℝ) (hA : Continuous A) (g : B → ℝ) (b : B) :
    response μX A (fun p => g p.1) b = g b := by
  letI := CompactGibbsContinuity.law_probability μX (fun x => A (b,x))
    (hA.comp (continuous_const.prodMk continuous_id))
  rw [response_eq_expectation μX _ _ hA b]
  simp

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
theorem response_sub_boundary (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (g : B → ℝ) (hg : Continuous g) (b : B) :
    response μX A (fun p => F p-g p.1) b = response μX A F b-g b := by
  rw [response_sub μX A F (fun p => g p.1) hA hF (hg.comp continuous_fst),
    response_boundary μX A hA]

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
theorem response_square_le (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (b : B) :
    (response μX A F b)^2 ≤ response μX A (fun p => (F p)^2) b := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b,x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  have h := WilsonResponseL2.mean_square_le ν (fun x => (F (b,x) : ℂ))
    (Complex.continuous_ofReal.comp (hF.comp (continuous_const.prodMk continuous_id)))
  simp only [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  simpa only [response_eq_expectation μX _ _ hA b] using h

/-- Conditional averaging contracts the squared error under its actual
marginal, with constant one and no partition lower-bound premise. -/
theorem response_l2_bound (A F : B × X → ℝ) (hA : Continuous A) (hF : Continuous F) :
    (∫ b, (response μX A F b)^2 ∂marginal μB μX A) ≤
      ∫ p, (F p)^2 ∂CompactGibbsContinuity.law (μB.prod μX) A := by
  letI := marginal_probability μB μX A hA
  have hiR : Integrable (fun b => (response μX A F b)^2) (marginal μB μX A) :=
    ((response_continuous μX A F hA hF).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiQ : Integrable (response μX A (fun p => (F p)^2)) (marginal μB μX A) :=
    (response_continuous μX A (fun p => (F p)^2) hA (hF.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ b, response μX A (fun p => (F p)^2) b ∂marginal μB μX A :=
      integral_mono hiR hiQ (response_square_le μX A F hA hF)
    _ = _ := response_expectation μB μX A _ hA (hF.pow 2)

/-- A constant vacuum subtraction and a retained source are carried without
enlarging their mean-square residual under the original Gibbs law. -/
theorem response_error_l2_bound (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (g : B → ℝ) (hg : Continuous g) (c : ℝ) :
    (∫ b, (response μX A F b-(c+g b))^2 ∂marginal μB μX A) ≤
      ∫ p, (F p-(c+g p.1))^2 ∂CompactGibbsContinuity.law (μB.prod μX) A := by
  have h := response_l2_bound μB μX A (fun p => F p-(c+g p.1)) hA
    (hF.sub (continuous_const.add (hg.comp continuous_fst)))
  simpa only [response_sub_boundary μX A F hA hF (fun b => c+g b)
    (continuous_const.add hg)] using h

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
/-- The conditional variance is the second moment minus the square of the
conditional mean; its within-fiber term is retained explicitly. -/
theorem response_variance_identity (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (b : B) :
    response μX A (fun p => (F p-response μX A F p.1)^2) b =
      response μX A (fun p => (F p)^2) b-(response μX A F b)^2 := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b,x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  have h := ConnectedGramLimit.complex_variance_identity ν (fun x => (F (b,x) : ℂ))
    (Complex.continuous_ofReal.comp (hF.comp (continuous_const.prodMk continuous_id)))
  simp only [integral_complex_ofReal, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Complex.ofReal_mul, Complex.ofReal_re] at h
  simpa only [response_eq_expectation μX _ _ hA b, pow_two] using h

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
theorem conditional_centered_square (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (c : ℝ) (b : B) :
    response μX A (fun p => (F p-c)^2) b =
      response μX A (fun p => (F p-response μX A F p.1)^2) b+
        (response μX A F b-c)^2 := by
  have h := response_variance_identity μX A (fun p => F p-c) hA
    (hF.sub continuous_const) b
  have he : (fun p : B × X => ((F p-c)-response μX A (fun q => F q-c) p.1)^2) =
      (fun p => (F p-response μX A F p.1)^2) := by
    funext p
    rw [response_sub_boundary μX A F hA hF (fun _ => c) continuous_const]
    congr 1
    ring
  rw [he, response_sub_boundary μX A F hA hF (fun _ => c) continuous_const] at h
  linarith

/-- Exact total centered-square decomposition under the original law and
its actual marginal. Taking c to be the full mean gives total variance. -/
theorem centered_square_identity (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (c : ℝ) :
    (∫ p, (F p-c)^2 ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      (∫ p, (F p-response μX A F p.1)^2
        ∂CompactGibbsContinuity.law (μB.prod μX) A)+
      ∫ b, (response μX A F b-c)^2 ∂marginal μB μX A := by
  letI := marginal_probability μB μX A hA
  have hR := response_continuous μX A F hA hF
  have hQ : Continuous (fun p : B × X => (F p-response μX A F p.1)^2) :=
    (hF.sub (hR.comp continuous_fst)).pow 2
  have hiQ := (response_continuous μX A _ hA hQ).integrable_of_hasCompactSupport
    (μ := marginal μB μX A) (HasCompactSupport.of_compactSpace _)
  have hiR : Integrable (fun b => (response μX A F b-c)^2) (marginal μB μX A) :=
    ((hR.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ b, response μX A (fun p => (F p-c)^2) b ∂marginal μB μX A :=
      (response_expectation μB μX A _ hA ((hF.sub continuous_const).pow 2)).symm
    _ = ∫ b, (response μX A (fun p => (F p-response μX A F p.1)^2) b+
        (response μX A F b-c)^2) ∂marginal μB μX A := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (conditional_centered_square μX A F hA hF c)
    _ = (∫ b, response μX A (fun p => (F p-response μX A F p.1)^2) b
        ∂marginal μB μX A)+∫ b, (response μX A F b-c)^2 ∂marginal μB μX A :=
      integral_add hiQ hiR
    _ = _ := by rw [response_expectation μB μX A _ hA hQ]

end OneStep

def reassociate {X Y Z E : Type*} (F : (Z × Y) × X → E) : Z × (Y × X) → E :=
  fun p => F ((p.1,p.2.1),p.2.2)

theorem reassociate_continuous {X Y Z E : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace E]
    (F : (Z × Y) × X → E) (hF : Continuous F) : Continuous (reassociate F) :=
  hF.comp ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd))

section TwoSteps
variable {X Y Z : Type*}
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [TopologicalSpace Z] [CompactSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Z] [BorelSpace Z]
  (μZ : Measure Z) (μY : Measure Y) (μX : Measure X)
  [IsProbabilityMeasure μZ] [IsProbabilityMeasure μY] [IsProbabilityMeasure μX]

omit [CompactSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
/-- Integrating X and then Y gives exactly the joint fiber partition. -/
theorem fiberMass_tower (A : (Z × Y) × X → ℝ) (hA : Continuous A) (z : Z) :
    fiberMass μY (effectiveAction μX A) z =
      fiberMass (μY.prod μX) (reassociate A) z := by
  change (∫ y, Real.exp (-effectiveAction μX A (z,y)) ∂μY) =
    ∫ q, Real.exp (-A ((z,q.1),q.2)) ∂μY.prod μX
  simp_rw [exp_effectiveAction μX A hA]
  have hc : Continuous (fun q : Y × X => Real.exp (-A ((z,q.1),q.2))) :=
    Real.continuous_exp.comp
      (hA.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).neg
  exact (integral_prod _
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm

omit [CompactSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
/-- The exact normalized tower; its intermediate action is the actual
negative logarithm of the X partition. -/
theorem response_tower (A F : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (z : Z) :
    response μY (effectiveAction μX A) (response μX A F) z =
      response (μY.prod μX) (reassociate A) (reassociate F) z := by
  have hc (y : Y) : Real.exp (-effectiveAction μX A (z,y))*response μX A F (z,y) =
      ∫ x, Real.exp (-A ((z,y),x))*F ((z,y),x) ∂μX := by
    rw [exp_effectiveAction μX A hA]
    unfold response
    field_simp [(fiberMass_positive μX A hA (z,y)).ne']
  change (∫ y, Real.exp (-effectiveAction μX A (z,y))*response μX A F (z,y) ∂μY) /
      fiberMass μY (effectiveAction μX A) z =
    (∫ q, Real.exp (-A ((z,q.1),q.2))*F ((z,q.1),q.2) ∂μY.prod μX) /
      fiberMass (μY.prod μX) (reassociate A) z
  simp_rw [hc]
  rw [fiberMass_tower μY μX A hA z]
  congr 1
  have hmap : Continuous (fun q : Y × X => ((z,q.1),q.2)) :=
    (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  exact (integral_prod _ (((Real.continuous_exp.comp (hA.comp hmap).neg).mul
    (hF.comp hmap)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm

/-- The twice retained measure is the actual coarse-coordinate pushforward
of the original three-variable interacting Gibbs law. -/
theorem marginal_tower (A : (Z × Y) × X → ℝ) (hA : Continuous A) :
    marginal μZ μY (effectiveAction μX A) =
      (CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A).map (fun p => p.1.1) := by
  calc
    _ = (marginal (μZ.prod μY) μX A).map Prod.fst := by
      rw [marginal_eq_effectiveLaw (μZ.prod μY) μX A hA]
      rfl
    _ = _ := by
      rw [marginal, Measure.map_map measurable_fst measurable_fst]
      rfl

/-- Further integration contracts the already obtained residual under its
true first marginal. The same constant subtraction is retained. -/
theorem nested_residual_l2_bound (A F : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (G : Z × Y → ℝ) (hG : Continuous G) (c : ℝ) :
    (∫ z, (response μY (effectiveAction μX A) (response μX A F) z-c-
        response μY (effectiveAction μX A) G z)^2
      ∂marginal μZ μY (effectiveAction μX A)) ≤
      ∫ p, (response μX A F p-c-G p)^2 ∂marginal (μZ.prod μY) μX A := by
  have hS := effectiveAction_continuous μX A hA
  have hR := response_continuous μX A F hA hF
  have h := response_l2_bound μZ μY (effectiveAction μX A)
    (fun p => response μX A F p-c-G p) hS ((hR.sub continuous_const).sub hG)
  have he (z : Z) :
      response μY (effectiveAction μX A) (fun p => response μX A F p-c-G p) z =
        response μY (effectiveAction μX A) (response μX A F) z-c-
          response μY (effectiveAction μX A) G z := by
    rw [response_sub μY (effectiveAction μX A) (fun p => response μX A F p-c) G
      hS (hR.sub continuous_const) hG,
      response_sub_boundary μY (effectiveAction μX A) (response μX A F) hS hR
        (fun _ => c) continuous_const]
  simp_rw [he] at h
  rw [← marginal_eq_effectiveLaw (μZ.prod μY) μX A hA] at h
  exact h

/-- Both eliminations preserve the original mean-square error bound with
constant one. This does not assume or establish a new small RG error. -/
theorem nested_error_l2_bound (A F : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (G : Z × Y → ℝ) (hG : Continuous G) (c : ℝ) :
    (∫ z, (response μY (effectiveAction μX A) (response μX A F) z-c-
        response μY (effectiveAction μX A) G z)^2
      ∂marginal μZ μY (effectiveAction μX A)) ≤
      ∫ p, (F p-c-G p.1)^2 ∂CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A := by
  have h := response_error_l2_bound (μZ.prod μY) μX A F hA hF G hG c
  simp only [sub_add_eq_sub_sub] at h
  exact (nested_residual_l2_bound μZ μY μX A F hA hF G hG c).trans h

end TwoSteps
end
end UnifiedTheory.Clay.YangMills.GibbsMarginalTower
