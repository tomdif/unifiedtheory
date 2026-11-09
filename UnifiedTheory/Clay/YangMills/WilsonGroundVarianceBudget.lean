/- Actual ground-law conditional variances cannot exceed total variance.
A nonconstant physical plaquette makes the resulting lower constraint on
any proposed variance-factorization constant nonvacuous at finite cutoff. -/
import UnifiedTheory.Clay.YangMills.WilsonHaarLinkResponse
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteTransport
import UnifiedTheory.Clay.YangMills.HaarCenteredFluctuation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonGroundLocalComparison WilsonPhysicalVariance CompactDensityEntropy
open WilsonHaarLinkResponse WilsonHaarRefresh
open scoped ENNReal

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem ground_reference_absolutelyContinuous (β : ℝ) (hβ : 0 ≤ β) :
    WilsonSlabOperator.measure n ≪ groundLaw n β hβ := by
  change WilsonSlabOperator.measure n ≪ (WilsonSlabOperator.measure n).withDensity
    (fun u => ENNReal.ofReal ((ground n β hβ u)^2))
  exact withDensity_absolutelyContinuous'
    (((ground n β hβ).continuous.pow 2).measurable.ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall (fun u =>
      (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (ground_pos n β hβ u))).ne'))

theorem ground_openPos (β : ℝ) (hβ : 0 ≤ β) :
    Measure.IsOpenPosMeasure (groundLaw n β hβ) := by
  haveI : Measure.IsOpenPosMeasure (WilsonSlabOperator.measure n) := by
    unfold WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar RegulatedGauge.compactHaar
    infer_instance
  exact (ground_reference_absolutelyContinuous n β hβ).isOpenPosMeasure

theorem variance_positive (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (u v : Slice n) (hne : f u ≠ f v) : 0 < variance n β hβ f := by
  letI := groundLaw_probability n β hβ
  letI := ground_openPos n β hβ
  exact HaarCenteredFluctuation.real_variance_positive (groundLaw n β hβ)
    f f.continuous u v hne

variable [Fact (1 < n)]

omit [NeZero n] in
theorem spatialStep_ne (x : SpatialVertex n) (i : Fin 3) : spatialStep n x i ≠ x := by
  intro he
  have h := congrArg (fun y : SpatialVertex n => y i) he
  change x i + (Pi.single i (1 : ZMod n) : SpatialVertex n) i = x i at h
  have hz : (1 : ZMod n) = 0 := by simpa only [Pi.single_eq_same, add_eq_left] using h
  exact one_ne_zero hz

def singleLink (x : SpatialVertex n) (i : Fin 3) (q : Q) : Slice n :=
  Function.update (1 : Slice n) (x, i) q

omit [NeZero n] in
theorem singleLink_holonomy (x : SpatialVertex n) (i j : Fin 3) (hij : i ≠ j) (q : Q) :
    spatialHolonomy (singleLink n x i q) x i j = q := by
  have h1 : (spatialStep n x i, j) ≠ (x, i) := by
    intro h
    exact hij (congrArg Prod.snd h).symm
  have h2 : (spatialStep n x j, i) ≠ (x, i) := by
    intro h
    exact spatialStep_ne n x j (congrArg Prod.fst h)
  have h3 : (x, j) ≠ (x, i) := by
    intro h
    exact hij (congrArg Prod.snd h).symm
  simp only [spatialHolonomy, singleLink, Function.update_self,
    Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Pi.one_apply, inv_one, mul_one]

/-- Strict finite-cutoff variance of a physical spatial plaquette under the actual ground law. -/
theorem plaquette_variance_positive (β : ℝ) (hβ : 0 ≤ β)
    (x : SpatialVertex n) (i j : Fin 3) (hij : i ≠ j) :
    0 < variance n β hβ (WilsonPlaquetteTransport.plaquette n x i j) := by
  apply variance_positive n β hβ _ (singleLink n x i 1) (singleLink n x i (-1))
  change (WilsonSingleLinkStaples.character (spatialHolonomy (singleLink n x i 1) x i j)).re ≠
    (WilsonSingleLinkStaples.character (spatialHolonomy (singleLink n x i (-1)) x i j)).re
  rw [singleLink_holonomy n x i j hij, singleLink_holonomy n x i j hij]
  norm_num [WilsonSingleLinkStaples.character_re, Unitary.coe_neg]

omit [Fact (1 < n)] in
theorem heatBathEnergy_le_variance (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    heatBathEnergy n β hβ S f ≤ variance n β hβ f := by
  letI := outsideLaw_probability n β hβ S
  let m := ∫ u, f u ∂groundLaw n β hβ
  let F : Slice n → ℝ := fun u => (f u-m)^2
  have hF : Continuous F := (f.continuous.sub continuous_const).pow 2
  have hj : Continuous (fun r : Outside n S =>
      ∫ a, F (WilsonBlockMarginal.assemble S (r, a)) ∂conditionalLaw n β hβ S r) :=
    fiberMean_continuous n β hβ S ⟨F, hF⟩
  have hp (r : Outside n S) :
      ProbabilityTheory.variance (fiber n S f r) (conditionalLaw n β hβ S r) ≤
        ∫ a, F (WilsonBlockMarginal.assemble S (r, a)) ∂conditionalLaw n β hβ S r := by
    letI := conditionalLaw_probability n β hβ S r
    exact CompactCrossVariance.variance_le_square _ _ (fiber n S f r).continuous m
  have h := integral_mono (continuous_integrable (outsideLaw n β hβ S) _
    (fiberVariance_continuous n β hβ S f)) (continuous_integrable _ _ hj) hp
  rw [disintegration n β hβ S F hF] at h
  rw [WilsonGroundHeatBathVariance.heatBathEnergy_eq_conditional_variance n β hβ S f
    f.continuous, variance,
    ProbabilityTheory.variance_eq_integral f.continuous.measurable.aemeasurable]
  exact h

omit [Fact (1 < n)] in
theorem totalConditionalVariance_le (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    totalConditionalVariance n β hβ f ≤
      (Fintype.card (SpatialVertex n × Fin 3) : ℝ) * variance n β hβ f := by
  calc
    _ ≤ ∑ _e : SpatialVertex n × Fin 3, variance n β hβ f :=
      Finset.sum_le_sum (fun e _ => heatBathEnergy_le_variance n β hβ {e} f)
    _ = _ := by simp

omit [Fact (1 < n)] in
theorem factorization_budget_of_positive (β : ℝ) (hβ : 0 ≤ β) (A : ℝ) (hA : 0 ≤ A)
    (f : C(Slice n, ℝ)) (hv : 0 < variance n β hβ f)
    (hfactor : variance n β hβ f ≤ A * totalConditionalVariance n β hβ f) :
    1 ≤ A * (Fintype.card (SpatialVertex n × Fin 3) : ℝ) := by
  have h := hfactor.trans (mul_le_mul_of_nonneg_left (totalConditionalVariance_le n β hβ f) hA)
  nlinarith

/-- No nontriviality premise: a genuine physical plaquette enforces the budget constraint. -/
theorem factorization_budget (β : ℝ) (hβ : 0 ≤ β) (A : ℝ) (hA : 0 ≤ A)
    (hfactor : ∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance n β hβ f ≤ A * totalConditionalVariance n β hβ f) :
    1 ≤ A * (Fintype.card (SpatialVertex n × Fin 3) : ℝ) := by
  let f := WilsonPlaquetteTransport.plaquette n 0 0 1
  exact factorization_budget_of_positive n β hβ A hA f
    (plaquette_variance_positive n β hβ 0 0 1 (by decide))
    (hfactor f (WilsonPlaquetteTransport.plaquette_gauge n 0 0 1))

end
end UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget
