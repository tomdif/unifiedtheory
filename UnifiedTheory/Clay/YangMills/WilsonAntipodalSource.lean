/- A source-weighted bound for the actual near-antipodal endpoint region.
It applies to every continuous observable, with no regularity modulus.
The payment is stationary variance, not one-step variance loss. -/
import UnifiedTheory.Clay.YangMills.WilsonAntipodalSuppression
import UnifiedTheory.Clay.YangMills.WilsonBridgeResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAntipodalSource
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonMiddleBridge WilsonAntipodalSuppression WilsonPhysicalVariance
open WilsonGroundHeatBath CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def tube : Set (Slice n × Slice n) :=
  {z | oppositeCost n z.1 z.2 ≤ (Fintype.card (SpatialVertex n × Fin 3) : ℝ) / 8}

theorem tube_measurable : MeasurableSet (tube n) :=
  (isClosed_le (oppositeCost_continuous n) continuous_const).measurableSet

theorem endpoint_symm (β : ℝ) (hβ : 0 ≤ β) (v w : Slice n) :
    endpointWeight n β hβ v w = endpointWeight n β hβ w v := by
  have hm : mass n β v w = mass n β w v := by
    apply integral_congr_ae
    filter_upwards with u
    exact mul_comm _ _
  unfold endpointWeight
  rw [hm, mul_comm (ground n β hβ v) (ground n β hβ w)]

/-- Both centered source terms are paid using their own true stationary density. -/
theorem source_pointwise (β : ℝ) (hβ : 0 ≤ β) (hlarge : 112 * Real.log 201 ≤ β)
    (heven : 2 ∣ n) (f : Slice n → ℝ) (m : ℝ) (z : Slice n × Slice n)
    (hz : z ∈ tube n) :
    endpointWeight n β hβ z.1 z.2 * (f z.1-f z.2)^2 ≤
      2 * Real.exp (-2 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)) *
        ((ground n β hβ z.1)^2 * (f z.1-m)^2+(ground n β hβ z.2)^2 * (f z.2-m)^2) := by
  have hv := endpoint_tube_upper n β hβ hlarge heven z.1 z.2 hz
  have hw := endpoint_tube_upper n β hβ hlarge heven z.2 z.1
    (by simpa only [oppositeCost_symm n z.2 z.1] using hz)
  rw [← endpoint_symm n β hβ z.1 z.2] at hw
  have hsq : (f z.1-f z.2)^2 ≤ 2 * (f z.1-m)^2+2 * (f z.2-m)^2 := by
    nlinarith [sq_nonneg (f z.1+f z.2-2 * m)]
  have h0 := mul_le_mul_of_nonneg_left hsq (endpointWeight_pos n β hβ z.1 z.2).le
  have h1 := mul_le_mul_of_nonneg_right hv (sq_nonneg (f z.1-m))
  have h2 := mul_le_mul_of_nonneg_right hw (sq_nonneg (f z.2-m))
  nlinarith

/-- This is the restricted part of the exact variance-loss pair integral. -/
def sourceMass (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  (∫ z in tube n, endpointWeight n β hβ z.1 z.2 * (f z.1-f z.2)^2
    ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) / 2

theorem sourceMass_nonneg (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    0 ≤ sourceMass n β hβ f := by
  apply div_nonneg _ (by norm_num)
  exact integral_nonneg (fun z => mul_nonneg (endpointWeight_pos n β hβ z.1 z.2).le
    (sq_nonneg _))

theorem sourceMass_le_loss (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    sourceMass n β hβ f ≤ loss n β hβ f := by
  rw [sourceMass, loss_pair]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply setIntegral_le_integral
    (continuous_integrable _ _ ((WilsonBridgeResponse.endpoint_continuous n β hβ).mul
      (by fun_prop)))
  exact Filter.Eventually.of_forall (fun z =>
    mul_nonneg (endpointWeight_pos n β hβ z.1 z.2).le (sq_nonneg _))

/-- A full neighborhood estimate for arbitrary continuous sources. Gauge
invariance of f is not needed. Even period is used only for the ground ratio. -/
theorem sourceMass_upper (β : ℝ) (hβ : 0 ≤ β) (hlarge : 112 * Real.log 201 ≤ β)
    (heven : 2 ∣ n) (f : C(Slice n, ℝ)) :
    sourceMass n β hβ f ≤
      2 * Real.exp (-2 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)) * variance n β hβ f := by
  let μ := (WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)
  let m := ∫ u, f u ∂groundLaw n β hβ
  let H : Slice n → ℝ := fun u => (ground n β hβ u)^2 * (f u-m)^2
  let c := Real.exp (-2 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ))
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hH : Continuous H := ((ground n β hβ).continuous.pow 2).mul
    ((f.continuous.sub continuous_const).pow 2)
  have hHpos (u : Slice n) : 0 ≤ H u := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHmean : (∫ u, H u ∂WilsonSlabOperator.measure n) = variance n β hβ f := by
    rw [variance, ProbabilityTheory.variance_eq_integral f.continuous.measurable.aemeasurable,
      groundLaw, GroundStateDirichlet.stationary_integral (WilsonSlabOperator.measure n)
        (ground n β hβ) (ground n β hβ).continuous]
    rfl
  have hfirst : (∫ z : Slice n × Slice n, H z.1 ∂μ) = variance n β hβ f := by
    dsimp only [μ]
    rw [integral_prod (fun z : Slice n × Slice n => H z.1)
      (continuous_integrable μ _ (hH.comp continuous_fst))]
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hHmean
  have hsecond : (∫ z : Slice n × Slice n, H z.2 ∂μ) = variance n β hβ f := by
    dsimp only [μ]
    rw [integral_prod (fun z : Slice n × Slice n => H z.2)
      (continuous_integrable μ _ (hH.comp continuous_snd))]
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hHmean
  have hJ : Continuous (fun z : Slice n × Slice n =>
      endpointWeight n β hβ z.1 z.2 * (f z.1-f z.2)^2) :=
    (WilsonBridgeResponse.endpoint_continuous n β hβ).mul (by fun_prop)
  have hi := integral_mono
    ((continuous_integrable μ _ hJ).indicator (tube_measurable n))
    (continuous_integrable μ _
      (continuous_const.mul ((hH.comp continuous_fst).add (hH.comp continuous_snd))))
    (g := fun z => 2 * c * (H z.1+H z.2)) (fun z => by
      by_cases hz : z ∈ tube n
      · rw [Set.indicator_of_mem hz]
        exact source_pointwise n β hβ hlarge heven f m z hz
      · rw [Set.indicator_of_notMem hz]
        exact mul_nonneg (mul_nonneg (by norm_num) hc) (add_nonneg (hHpos _) (hHpos _)))
  rw [integral_indicator (tube_measurable n), integral_const_mul,
    integral_add (f := fun z : Slice n × Slice n => H z.1) (g := fun z => H z.2)
      (continuous_integrable μ _ (hH.comp continuous_fst))
      (continuous_integrable μ _ (hH.comp continuous_snd)), hfirst, hsecond] at hi
  unfold sourceMass
  change _ ≤ 2 * c * variance n β hβ f
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonAntipodalSource
