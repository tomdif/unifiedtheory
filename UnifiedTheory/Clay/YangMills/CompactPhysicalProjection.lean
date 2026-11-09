/- Exact Gram decomposition when the removed scores are orthogonal to
the retained physical scores. No bound on the retained form is assumed. -/
import UnifiedTheory.Clay.YangMills.CompactScoreResidual

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactPhysicalProjection
noncomputable section
open MeasureTheory CompactDensityEntropy CompactGramResponse CompactScoreResidual

variable {I X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem gram_decomposition (s p : I → X → ℝ)
    (hs : ∀ i, Continuous (s i)) (hp : ∀ i, Continuous (p i))
    (horth : ∀ i j, (∫ x, (s i x - p i x) * p j x ∂μ) = 0) (i j : I) :
    gram μ s i j = gram μ p i j + gram μ (fun k x => s k x-p k x) i j := by
  have h1 := continuous_integrable μ _ ((hp i).mul (hp j))
  have h2 := continuous_integrable μ _ (((hs i).sub (hp i)).mul ((hs j).sub (hp j)))
  have h3 := continuous_integrable μ _ (((hs i).sub (hp i)).mul (hp j))
  have h4 := continuous_integrable μ _ (((hs j).sub (hp j)).mul (hp i))
  have ha := integral_add ((h1.add h2).add h3) h4
  have hb := integral_add (h1.add h2) h3
  have hc := integral_add h1 h2
  simp only [Pi.add_apply, Pi.mul_apply] at ha hb hc
  unfold gram
  calc
    _ = ∫ x, ((p i x*p j x+(s i x-p i x)*(s j x-p j x))+
        (s i x-p i x)*p j x)+(s j x-p j x)*p i x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = _ := by rw [ha, hb, hc, horth i j, horth j i]; ring

variable [Fintype I]

theorem gram_le (s p : I → X → ℝ)
    (hs : ∀ i, Continuous (s i)) (hp : ∀ i, Continuous (p i))
    (horth : ∀ i j, (∫ x, (s i x - p i x) * p j x ∂μ) = 0) (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*gram μ p i j) ≤ ∑ i, ∑ j, a i*a j*gram μ s i j := by
  simp_rw [gram_decomposition μ s p hs hp horth, mul_add, Finset.sum_add_distrib]
  exact le_add_of_nonneg_right (gram_positive μ (fun i x => s i x-p i x)
    (fun i => (hs i).sub (hp i)) a)

theorem gram_le_residual (s p : I → X → ℝ) (t : X → ℝ)
    (hs : ∀ i, Continuous (s i)) (hp : ∀ i, Continuous (p i)) (ht : Continuous t)
    (horth : ∀ i j, (∫ x, (s i x - p i x) * p j x ∂μ) = 0)
    (htp : ∀ j, pair μ t (p j) = 0) (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*gram μ p i j) ≤
      ∑ i, ∑ j, a i*a j*gram μ (fun i => residual μ (s i) t) i j := by
  apply gram_le μ _ p (fun i => residual_continuous μ _ _ (hs i) ht) hp
    (fun i j => ?_) a
  have ho := horth i j
  have hsi : Integrable (fun x => s i x*p j x) μ :=
    continuous_integrable μ _ ((hs i).mul (hp j))
  have hpi : Integrable (fun x => p i x*p j x) μ :=
    continuous_integrable μ _ ((hp i).mul (hp j))
  have hri : Integrable (fun x => residual μ (s i) t x*p j x) μ :=
    continuous_integrable μ _ ((residual_continuous μ _ _ (hs i) ht).mul (hp j))
  simp_rw [sub_mul] at ho ⊢
  rw [integral_sub hsi hpi] at ho
  rw [integral_sub hri hpi]
  change pair μ (residual μ (s i) t) (p j)-pair μ (p i) (p j) = 0
  rw [pair_residual_left μ (s i) t (p j) (hs i) ht (hp j), htp j, mul_zero, sub_zero]
  exact ho

end
end UnifiedTheory.Clay.YangMills.CompactPhysicalProjection
