/- Collective response uses the row sums of the actual likelihood Gram
matrix, rather than adding one variance bound for each direction. -/
import UnifiedTheory.Clay.YangMills.CompactLikelihoodVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactGramResponse
noncomputable section
open MeasureTheory CompactDensityEntropy

variable {I : Type*} [Fintype I]

theorem scalar_pair_bound (a b c : ℝ) : a*b*c ≤ |c| * (a^2+b^2)/2 := by
  have h := le_abs_self (a*b*c)
  rw [abs_mul, abs_mul] at h
  have hs : 2*|a| * |b| ≤ a^2+b^2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg c)]

/-- A symmetric matrix has a quadratic bound controlled by its largest absolute row sum. -/
theorem quadratic_le_rows (G : I → I → ℝ) (hs : ∀ i j, G i j = G j i)
    (κ : ℝ) (hrow : ∀ i, ∑ j, |G i j| ≤ κ) (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*G i j) ≤ κ * ∑ i, (a i)^2 := by
  have ht : (∑ i, ∑ j, |G i j| * (a j)^2) = ∑ i, ∑ j, |G i j| * (a i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  calc
    _ ≤ ∑ i, ∑ j, |G i j| * ((a i)^2+(a j)^2)/2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        scalar_pair_bound (a i) (a j) (G i j)))
    _ = ∑ i, (∑ j, |G i j|)*(a i)^2 := by
      simp_rw [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [ht, ← add_div, add_self_div_two]
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ i, κ*(a i)^2 := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def gram (s : I → X → ℝ) (i j : I) : ℝ := ∫ x, s i x*s j x ∂μ

omit [Fintype I] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [IsProbabilityMeasure μ] in
theorem gram_symm (s : I → X → ℝ) (i j : I) : gram μ s i j = gram μ s j i := by
  simp only [gram, mul_comm]

theorem gram_quadratic (s : I → X → ℝ) (hs : ∀ i, Continuous (s i)) (a : I → ℝ) :
    (∫ x, (∑ i, a i*s i x)^2 ∂μ) = ∑ i, ∑ j, a i*a j*gram μ s i j := by
  have he (x : X) : (∑ i, a i*s i x)^2 =
      ∑ i, ∑ j, (a i*a j)*(s i x*s j x) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : I) : Integrable (fun x => (a i*a j)*(s i x*s j x)) μ :=
    continuous_integrable μ _ (continuous_const.mul ((hs i).mul (hs j)))
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j), integral_const_mul]
  rfl

theorem gram_positive (s : I → X → ℝ) (hs : ∀ i, Continuous (s i)) (a : I → ℝ) :
    0 ≤ ∑ i, ∑ j, a i*a j*gram μ s i j := by
  rw [← gram_quadratic μ s hs a]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- Bessel's inequality with an actual, possibly correlated, family of scores. -/
theorem collective_response (s : I → X → ℝ) (hs : ∀ i, Continuous (s i))
    (f : X → ℝ) (hf : Continuous f) (κ : ℝ) (hκ : 0 ≤ κ)
    (hrow : ∀ i, ∑ j, |gram μ s i j| ≤ κ) :
    (∑ i, (∫ x, s i x*(f x-∫ y, f y ∂μ) ∂μ)^2) ≤
      κ * ProbabilityTheory.variance f μ := by
  let d : I → ℝ := fun i => ∫ x, s i x*(f x-∫ y, f y ∂μ) ∂μ
  let S := ∑ i, (d i)^2
  let A := fun x => ∑ i, d i*s i x
  have hA : Continuous A := continuous_finset_sum _ (fun i _ => continuous_const.mul (hs i))
  have he : (∫ x, A x*(f x-∫ y, f y ∂μ) ∂μ) = S := by
    simp only [A, Finset.sum_mul]
    have hi (i : I) : Integrable (fun x => d i*s i x*(f x-∫ y, f y ∂μ)) μ :=
      continuous_integrable μ _ ((continuous_const.mul (hs i)).mul (hf.sub continuous_const))
    rw [integral_finset_sum _ (fun i _ => hi i)]
    simp_rw [mul_assoc, integral_const_mul]
    simp only [S, d, pow_two]
  have hq : (∫ x, (A x)^2 ∂μ) ≤ κ*S := by
    rw [gram_quadratic μ s hs d]
    exact quadratic_le_rows (gram μ s) (gram_symm μ s) κ hrow d
  have hc := integral_product_sq μ A (fun x => f x-∫ y, f y ∂μ)
    hA (hf.sub continuous_const)
  rw [he, ← ProbabilityTheory.variance_eq_integral hf.measurable.aemeasurable] at hc
  have hv : 0 ≤ ProbabilityTheory.variance f μ := by
    rw [ProbabilityTheory.variance_eq_integral hf.measurable.aemeasurable]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hh := hc.trans (mul_le_mul_of_nonneg_right hq hv)
  change S ≤ κ * ProbabilityTheory.variance f μ
  by_cases hz : S = 0
  · rw [hz]
    exact mul_nonneg hκ hv
  · have hp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    nlinarith

end
end UnifiedTheory.Clay.YangMills.CompactGramResponse
