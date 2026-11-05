/- Genuine ordinary Gram positivity and compactness for bounded continuous
observables under probability measures. This is not time-reflection positivity. -/
import UnifiedTheory.Clay.YangMills.CountableCorrelationCompactness
import UnifiedTheory.Clay.YangMills.WilsonMomentBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ProbabilityGramCompactness
noncomputable section
open MeasureTheory CountableCorrelationCompactness
open scoped BigOperators

section OneMeasure
variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] (F : ι → X → ℂ)

def kernel (i : ι × ι) : ℂ := ∫ x, star (F i.1 x) * F i.2 x ∂μ

def combination (n : ℕ) (index : Fin n → ι) (a : Fin n → ℂ) (x : X) : ℂ :=
  ∑ j, a j * F (index j) x

theorem gram_as_square (hF : ∀ i, Continuous (F i)) (n : ℕ)
    (index : Fin n → ι) (a : Fin n → ℂ) :
    gramValue (fun i j => (i, j)) (kernel μ F) n index a =
      ∫ x, star (combination F n index a x) * combination F n index a x ∂μ := by
  have hpoly (x : X) : star (combination F n index a x) * combination F n index a x =
      ∑ i, ∑ j, (star (a i) * a j) * (star (F (index i) x) * F (index j) x) := by
    simp only [combination, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : Fin n) : Integrable
      (fun x => (star (a i) * a j) * (star (F (index i) x) * F (index j) x)) μ :=
    (continuous_const.mul ((hF (index i)).star.mul (hF (index j)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [hpoly]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j), integral_const_mul]
  rfl

theorem kernel_positive (hF : ∀ i, Continuous (F i)) :
    GramPositive (fun i j => (i, j)) (kernel μ F) := by
  intro n index a
  rw [gram_as_square μ F hF]
  have he (x : X) : star (combination F n index a x) * combination F n index a x =
      ((‖combination F n index a x‖ ^ 2 : ℝ) : ℂ) :=
    by simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' _
  simp_rw [he]
  rw [integral_complex_ofReal]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact integral_nonneg (fun x => sq_nonneg _)

theorem kernel_bound (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hb : ∀ i x, ‖F i x‖ ≤ B i) (i : ι × ι) :
    ‖kernel μ F i‖ ≤ B i.1 * B i.2 := by
  have he : ∀ x, ‖star (F i.1 x) * F i.2 x‖ ≤ B i.1 * B i.2 := by
    intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb i.1 x) (hb i.2 x) (norm_nonneg _) (hB i.1)
  simpa only [kernel, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall he)

theorem kernel_normalized (i : ι) (hi : ∀ x, F i x = 1) : kernel μ F (i, i) = 1 := by
  simp [kernel, hi]
end OneMeasure

section Family
variable {ι : Type*} [Countable ι] {X : ℕ → Type*}
  [∀ k, TopologicalSpace (X k)] [∀ k, CompactSpace (X k)]
  [∀ k, MeasurableSpace (X k)] [∀ k, BorelSpace (X k)]
  (μ : ∀ k, Measure (X k)) [∀ k, IsProbabilityMeasure (μ k)]
  (F : ∀ k, ι → X k → ℂ) (hF : ∀ k i, Continuous (F k i))
  (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hb : ∀ k i x, ‖F k i x‖ ≤ B i)

include hF hB hb in
theorem exists_positive_kernel_limit :
    ∃ (w : ι × ι → ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      CoordinateConvergence (fun k => kernel (μ (phi k)) (F (phi k))) w ∧
      (∀ i, ‖w i‖ ≤ B i.1 * B i.2) ∧ GramPositive (fun i j => (i, j)) w := by
  obtain ⟨w, phi, hphi, hc, hw⟩ := exists_common_subsequence
    (fun k => kernel (μ k) (F k)) (fun i => B i.1 * B i.2)
    (fun k i => kernel_bound (μ k) (F k) B hB (hb k) i)
  exact ⟨w, phi, hphi, hc, hw, gram_positive_survives _ _ hc _
    (fun k => kernel_positive (μ (phi k)) (F (phi k)) (hF (phi k)))⟩

include hF hB hb in
theorem exists_normalized_positive_kernel_limit (unitIndex : ι)
    (hn : ∀ k x, F k unitIndex x = 1) :
    ∃ (w : ι × ι → ℂ) (phi : ℕ → ℕ), StrictMono phi ∧
      CoordinateConvergence (fun k => kernel (μ (phi k)) (F (phi k))) w ∧
      (∀ i, ‖w i‖ ≤ B i.1 * B i.2) ∧ GramPositive (fun i j => (i, j)) w ∧
      w (unitIndex, unitIndex) = 1 := by
  obtain ⟨w, phi, hphi, hc, hw, hp⟩ := exists_positive_kernel_limit μ F hF B hB hb
  exact ⟨w, phi, hphi, hc, hw, hp, normalization_survives _ _ hc _
    (fun k => kernel_normalized (μ (phi k)) (F (phi k)) unitIndex (hn (phi k)))⟩
end Family

end
end UnifiedTheory.Clay.YangMills.ProbabilityGramCompactness
