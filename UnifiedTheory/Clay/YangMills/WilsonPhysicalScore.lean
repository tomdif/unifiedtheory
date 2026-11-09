/- Canonical physical scores from the original gauge-averaged transfer.
They preserve all continuous physical responses, and their difference from
the raw scores is orthogonal to every continuous physical observable. -/
import UnifiedTheory.Clay.YangMills.WilsonGaugeResidual
import UnifiedTheory.Clay.YangMills.WilsonHeatBathComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalScore
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalResponse
open WilsonVarianceResponse WilsonPhysicalVariance CompactDensityEntropy

variable (n : ℕ) [NeZero n]

theorem transition_continuous (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    Continuous (transition n β hβ u) :=
  (WilsonHeatBathComparison.transitionMap n β hβ).continuous.comp
    (f := fun v : Slice n => (u, v)) (continuous_const.prodMk continuous_id)

theorem transition_gauge_right (β : ℝ) (hβ : 0 ≤ β)
    (u v : Slice n) (h : SliceGauge n Q) :
    transition n β hβ u (gaugeSlice h v) = transition n β hβ u v := by
  unfold transition GroundStateDirichlet.transition
  simp only [kernelMap, ContinuousMap.coe_mk,
    WilsonSlabGauge.kernel_gauge_right WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_classFunction, ground_invariant]

def score (β : ℝ) (hβ : 0 ≤ β) (u w v : Slice n) : ℝ :=
  transition n β hβ w v / transition n β hβ u v - 1

theorem score_continuous (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) :
    Continuous (score n β hβ u w) :=
  ((transition_continuous n β hβ w).div (transition_continuous n β hβ u)
    (fun v => (transition_pos n β hβ u v).ne')).sub continuous_const

theorem score_gauge (β : ℝ) (hβ : 0 ≤ β) (u w v : Slice n) (h : SliceGauge n Q) :
    score n β hβ u w (gaugeSlice h v) = score n β hβ u w v := by
  simp only [score, transition_gauge_right]

/-- Every pure-gauge input displacement has identically zero physical score. -/
theorem pure_gauge_zero (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) (h : SliceGauge n Q) :
    score n β hβ u (gaugeSlice h u) v = 0 := by
  rw [score, full_transition_gauge_left, div_self (transition_pos n β hβ u v).ne', sub_self]

theorem row_integral_physical (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (F : Slice n → ℝ) (hF : Continuous F) (hinv : ∀ h v, F (gaugeSlice h v) = F v) :
    (∫ v, F v ∂rowLaw n β hβ u) =
      ∫ v, transition n β hβ u v * F v ∂WilsonSlabOperator.measure n := by
  rw [rowLaw_integral]
  exact (invariant_transition n β hβ F hF hinv u).symm

theorem score_pairing (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, score n β hβ u w v * f v ∂rowLaw n β hβ u) =
      step n β hβ f w-step n β hβ f u := by
  rw [row_integral_physical n β hβ u (fun v => score n β hβ u w v * f v)
    ((score_continuous n β hβ u w).mul f.continuous)
    (fun h v => by dsimp only; rw [score_gauge, hinv])]
  have he (v : Slice n) : transition n β hβ u v * (score n β hβ u w v * f v) =
      transition n β hβ w v * f v-transition n β hβ u v * f v := by
    unfold score
    field_simp [(transition_pos n β hβ u v).ne']
  simp_rw [he]
  rw [integral_sub (continuous_integrable (WilsonSlabOperator.measure n)
    (fun v => transition n β hβ w v * f v)
    ((transition_continuous n β hβ w).mul f.continuous))
    (continuous_integrable (WilsonSlabOperator.measure n)
      (fun v => transition n β hβ u v * f v)
      ((transition_continuous n β hβ u).mul f.continuous)),
    step_full n β hβ f hinv w, step_full n β hβ f hinv u]

theorem raw_pairing (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) (f : C(Slice n, ℝ)) :
    (∫ v, (likelihood n β hβ u w v-1)*f v ∂rowLaw n β hβ u) =
      step n β hβ f w-step n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  simp_rw [sub_mul, one_mul]
  rw [integral_sub (continuous_integrable (rowLaw n β hβ u)
    (fun v => likelihood n β hβ u w v * f v)
    ((likelihood_continuous n β hβ u w).mul f.continuous))
    (continuous_integrable (rowLaw n β hβ u) _ f.continuous), likelihood_reweight]
  rfl

theorem score_mean_zero (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) :
    (∫ v, score n β hβ u w v ∂rowLaw n β hβ u) = 0 := by
  have hm (z : Slice n) : step n β hβ (ContinuousMap.const _ 1) z = 1 := by
    letI := rowLaw_probability n β hβ z
    change (∫ _v, (1 : ℝ) ∂rowLaw n β hβ z) = 1
    simp
  have h := score_pairing n β hβ u w (ContinuousMap.const _ 1) (fun _ _ => rfl)
  simpa only [ContinuousMap.const_apply, mul_one, hm, sub_self] using h

/-- The residual is orthogonal to every continuous physical test, including every physical score. -/
theorem residual_orthogonal (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, ((likelihood n β hβ u w v-1)-score n β hβ u w v)*f v
      ∂rowLaw n β hβ u) = 0 := by
  letI := rowLaw_probability n β hβ u
  have h1 := continuous_integrable (rowLaw n β hβ u)
    (fun v => (likelihood n β hβ u w v-1)*f v)
    (((likelihood_continuous n β hβ u w).sub continuous_const).mul f.continuous)
  have h2 := continuous_integrable (rowLaw n β hβ u)
    (fun v => score n β hβ u w v*f v)
    ((score_continuous n β hβ u w).mul f.continuous)
  have he (v : Slice n) : ((likelihood n β hβ u w v-1)-score n β hβ u w v)*f v =
      (likelihood n β hβ u w v-1)*f v-score n β hβ u w v*f v := sub_mul _ _ _
  simp_rw [he]
  rw [integral_sub h1 h2, raw_pairing, score_pairing n β hβ u w f hinv, sub_self]

theorem score_response (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, score n β hβ u w v*(f v-∫ z, f z ∂rowLaw n β hβ u)
      ∂rowLaw n β hβ u) = step n β hβ f w-step n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  let F : C(Slice n, ℝ) := f-ContinuousMap.const _ (∫ z, f z ∂rowLaw n β hβ u)
  have hF : ∀ h v, F (gaugeSlice h v) = F v := by
    intro h v
    simp only [F, ContinuousMap.sub_apply, ContinuousMap.const_apply, hinv]
  have hr := CompactLikelihoodVariance.centered_likelihood (rowLaw n β hβ u)
    (likelihood n β hβ u w) f (likelihood_continuous n β hβ u w) f.continuous
    (likelihood_mean n β hβ u w)
  rw [likelihood_reweight] at hr
  change _ = step n β hβ f w-step n β hβ f u at hr
  exact ((score_pairing n β hβ u w F hF).trans (raw_pairing n β hβ u w F).symm).trans hr

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalScore
