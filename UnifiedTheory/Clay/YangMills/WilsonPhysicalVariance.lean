/- The actual stationary variance lost by one transfer step is the mean of
its actual row variances. Local response is paid for by that loss. -/
import UnifiedTheory.Clay.YangMills.WilsonVarianceResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalVariance
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalResponse WilsonAveragedResponse
open WilsonSymmetricLinkChange WilsonVarianceResponse CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def step (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  ⟨rowMean n β hβ f, rowMean_continuous n β hβ f⟩

theorem step_full (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (u : Slice n) :
    step n β hβ f u = ∫ v, transition n β hβ u v*f v ∂WilsonSlabOperator.measure n :=
  rowMean_eq_full n β hβ f hinv u

theorem step_gauge (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (h : SliceGauge n Q) (u : Slice n) :
    step n β hβ f (gaugeSlice h u) = step n β hβ f u :=
  rowMean_gauge n β hβ f hinv h u

/-- Detailed balance and row normalization give exact stationarity of the constructed law. -/
theorem stationary_mean (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    (∫ u, step n β hβ f u ∂WilsonGroundHeatBath.groundLaw n β hβ) =
      ∫ u, f u ∂WilsonGroundHeatBath.groundLaw n β hβ := by
  rw [WilsonGroundHeatBath.groundLaw,
    GroundStateDirichlet.stationary_integral (WilsonSlabOperator.measure n) (ground n β hβ)
      (ground n β hβ).continuous,
    GroundStateDirichlet.stationary_integral (WilsonSlabOperator.measure n) (ground n β hβ)
      (ground n β hβ).continuous]
  change (∫ u, (ground n β hβ u)^2 * rowMean n β hβ f u ∂WilsonSlabOperator.measure n) = _
  simp_rw [rowMean_eq_raw, ← integral_const_mul]
  have hc : Continuous (fun z : Slice n × Slice n =>
      (ground n β hβ z.1)^2 * (rawTransition n β hβ z.1 z.2*f z.2)) :=
    (((ground n β hβ).continuous.comp continuous_fst).pow 2).mul
      ((rawTransition_continuous n β hβ).mul (f.continuous.comp continuous_snd))
  rw [integral_integral_swap
    (hc.integrable_of_hasCompactSupport (μ := (WilsonSlabOperator.measure n).prod
      (WilsonSlabOperator.measure n))
      (HasCompactSupport.of_compactSpace _))]
  have he (u v : Slice n) : (ground n β hβ u)^2 * (rawTransition n β hβ u v*f v) =
      (ground n β hβ v)^2 * (rawTransition n β hβ v u*f v) := by
    rw [← mul_assoc, raw_detailed_balance, mul_assoc]
  simp_rw [he, integral_const_mul, integral_mul_const, rawTransition_mass, one_mul]

def variance (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  ProbabilityTheory.variance f (WilsonGroundHeatBath.groundLaw n β hβ)

theorem variance_nonneg (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    0 ≤ variance n β hβ f := by
  rw [variance, ProbabilityTheory.variance_eq_integral f.continuous.measurable.aemeasurable]
  exact integral_nonneg (fun u => sq_nonneg _)

theorem variance_formula (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    variance n β hβ f = (∫ u, (f u)^2 ∂WilsonGroundHeatBath.groundLaw n β hβ) -
      (∫ u, f u ∂WilsonGroundHeatBath.groundLaw n β hβ)^2 := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  exact CompactLikelihoodVariance.variance_formula _ f f.continuous

def rowVariance (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) : ℝ :=
  ProbabilityTheory.variance f (rowLaw n β hβ u)

theorem rowVariance_nonneg (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) :
    0 ≤ rowVariance n β hβ f u := by
  rw [rowVariance, ProbabilityTheory.variance_eq_integral f.continuous.measurable.aemeasurable]
  exact integral_nonneg (fun v => sq_nonneg _)

theorem rowVariance_formula (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) :
    rowVariance n β hβ f u = step n β hβ (f^2) u - (step n β hβ f u)^2 := by
  letI := rowLaw_probability n β hβ u
  exact CompactLikelihoodVariance.variance_formula _ f f.continuous

theorem rowVariance_continuous (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Continuous (rowVariance n β hβ f) := by
  have he : rowVariance n β hβ f = fun u => step n β hβ (f^2) u-(step n β hβ f u)^2 :=
    funext (rowVariance_formula n β hβ f)
  rw [he]
  exact (step n β hβ (f^2)).continuous.sub ((step n β hβ f).continuous.pow 2)

def loss (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  variance n β hβ f - variance n β hβ (step n β hβ f)

/-- This is the actual loss of source variance, not an assumed factorization estimate. -/
theorem mean_rowVariance_eq_loss (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    (∫ u, rowVariance n β hβ f u ∂WilsonGroundHeatBath.groundLaw n β hβ) =
      loss n β hβ f := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  simp_rw [rowVariance_formula]
  have hi := integral_sub
    (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _ (step n β hβ (f^2)).continuous)
    (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _
      ((step n β hβ f).continuous.pow 2))
  rw [hi, stationary_mean]
  unfold loss
  rw [variance_formula, variance_formula, stationary_mean]
  simp only [ContinuousMap.pow_apply]
  ring

theorem loss_nonneg (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    0 ≤ loss n β hβ f := by
  rw [← mean_rowVariance_eq_loss]
  exact integral_nonneg (rowVariance_nonneg n β hβ f)

theorem variance_step_le (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    variance n β hβ (step n β hβ f) ≤ variance n β hβ f :=
  sub_nonneg.mp (loss_nonneg n β hβ f)

def responseEnergy (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q)
    (f : C(Slice n, ℝ)) : ℝ :=
  ∫ u, (f (shift n e q u)-f u)^2 ∂WilsonGroundHeatBath.groundLaw n β hβ

theorem responseEnergy_nonneg (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) :
    0 ≤ responseEnergy n β hβ e q f := integral_nonneg (fun u => sq_nonneg (f (shift n e q u)-f u))

/-- Finite-difference response of Pf is bounded by the variance dissipated by that same step. -/
theorem response_le_loss (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) :
    responseEnergy n β hβ e q (step n β hβ f) ≤ coefficient β q * loss n β hβ f := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  have hf := (step n β hβ f).continuous
  have h := integral_mono
    (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _
      (((hf.comp (shift_continuous n e q)).sub hf).pow 2))
    ((continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _
      (rowVariance_continuous n β hβ f)).const_mul (coefficient β q))
    (fun u => response_sq_conditional_variance n β hβ e q u f)
  rw [integral_const_mul, mean_rowVariance_eq_loss] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalVariance
