/- Spatial covariance decay under a weighted mixed budget, including every
finite stage of genuine coordinate elimination. The hypotheses concern the
initial action and geometric weights, not output covariances or colorings. -/
import UnifiedTheory.Clay.YangMills.GibbsWeightedCovariance
import UnifiedTheory.Clay.YangMills.WeightedMixedInfluence
import UnifiedTheory.Clay.YangMills.MixedEliminationTower

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.GibbsWeightedClustering
noncomputable section
open MeasureTheory FiniteProductInfluence GibbsSiteCovariance

variable {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

omit [Fintype I] [Nonempty I] [SecondCountableTopology X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] in
theorem supported_oscillation (F : C(I → X, ℝ)) (S : Finset I)
    (hF : DependsOn F (S : Set I)) :
    OscBound F (fun i => if i ∈ S then 2 * ‖F‖ else 0) := by
  intro i U V hUV
  change |F U - F V| ≤ if i ∈ S then 2 * ‖F‖ else 0
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    exact ParallelOscillation.uniform_oscillation F i U V hUV
  · rw [if_neg hi]
    have he : F U = F V := hF (fun j hj => hUV j (by intro h; subst j; exact hi hj))
    simp [he]

variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- Exponential decay for separated supports, with a prefactor depending on one support only. -/
theorem covariance_decay (A F G : C(I → X, ℝ)) (C : I → I → ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hlocal : ParallelOscillation.LocalInfluence
      (fun i U => CompactGibbsContinuity.law μ (fun q => A (Function.update U i q))) C)
    (d : I → I → ℝ) (hd : ∀ i j, 0 ≤ d i j)
    (r : I → ℝ) (hr : ∀ i j, r i ≤ d i j + r j)
    (m α R : ℝ) (hm : 0 ≤ m) (hα : 0 ≤ α) (hα1 : α < 1)
    (hweighted : ∀ i, ∑ j, Real.exp (m * d i j) * C i j ≤ α)
    (S T : Finset I) (hF : DependsOn F (S : Set I)) (hG : DependsOn G (T : Set I))
    (hS : ∀ i ∈ S, R ≤ r i) (hT : ∀ i ∈ T, r i = 0) :
    |(∫ U, F U * G U ∂law μ A) -
      (∫ U, F U ∂law μ A) * (∫ U, G U ∂law μ A)| ≤
      (S.card : ℝ) * ‖F‖ * ‖G‖ * Real.exp (-m * R) / (1 - α) := by
  have hdenpos : 0 < 1 - α := sub_pos.mpr hα1
  let u := fun i => Real.exp (-m * r i)
  let f := fun i => if i ∈ S then 2 * ‖F‖ else 0
  let g := fun i => if i ∈ T then 2 * ‖G‖ else 0
  have hf : ∀ i, 0 ≤ f i := by intro i; dsimp [f]; split <;> positivity
  have hg (i : I) : g i ≤ (2 * ‖G‖) * u i := by
    by_cases hi : i ∈ T
    · simp [g, u, hi, hT i hi]
    · simp only [g, if_neg hi]
      positivity
  have hrow := WeightedMixedInfluence.unweighted_row C (fun i j => Real.exp (m * d i j)) hC
    (fun i j => Real.one_le_exp_iff.mpr (mul_nonneg hm (hd i j))) α hweighted
  have h := GibbsWeightedCovariance.covariance_bound μ A F G C hC hlocal u f g
    (fun i => (Real.exp_pos _).le) hf (supported_oscillation F S hF)
    (supported_oscillation G T hG) α (2 * ‖G‖) hα hα1 (by positivity) hrow
    (WeightedOscillation.exp_site_row C hC d r hr m α hm hweighted) hg
  have hs : (∑ i, u i * f i) ≤ 2 * ‖F‖ * (S.card : ℝ) * Real.exp (-m * R) := by
    calc
      _ = ∑ i ∈ S, Real.exp (-m * r i) * (2 * ‖F‖) := by
        simp only [u, f, mul_ite, mul_zero, ← Finset.sum_filter,
          Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ ≤ ∑ _i ∈ S, Real.exp (-m * R) * (2 * ‖F‖) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [hS i hi]
      _ = _ := by simp; ring
  calc
    _ ≤ (2 * ‖G‖) * (∑ i, u i * f i) / (4 * (1 - α)) := h
    _ ≤ (2 * ‖G‖) * (2 * ‖F‖ * (S.card : ℝ) * Real.exp (-m * R)) /
        (4 * (1 - α)) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
    _ = _ := by field_simp; ring

/-- The initial weighted mixed budget gives the same spatial estimate at every finite depth. -/
theorem tower_covariance_decay (A : C(I → X, ℝ)) (c d : I → I → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) (hA : GibbsMixedElimination.MixedBound A c)
    (hd : ∀ i j, 0 ≤ d i j) (htriangle : ∀ i e j, d i j ≤ d i e + d e j)
    (m α : ℝ) (hm : 0 ≤ m) (hα : 0 ≤ α) (hα1 : α < 1)
    (hweighted : ∀ i, ∑ j, Real.exp (m * d i j) * c i j ≤ α)
    (E : ℕ → I) (k : ℕ) (F G : C(I → X, ℝ))
    (S T : Finset I) (hF : DependsOn F (S : Set I)) (hG : DependsOn G (T : Set I))
    (r : I → ℝ) (hr : ∀ i j, r i ≤ d i j + r j)
    (R : ℝ) (hS : ∀ i ∈ S, R ≤ r i) (hT : ∀ i ∈ T, r i = 0) :
    |(∫ U, F U * G U ∂law μ (GibbsCoordinateTower.action μ (fun t => {E t}) A k)) -
      (∫ U, F U ∂law μ (GibbsCoordinateTower.action μ (fun t => {E t}) A k)) *
      (∫ U, G U ∂law μ (GibbsCoordinateTower.action μ (fun t => {E t}) A k))| ≤
      (S.card : ℝ) * ‖F‖ * ‖G‖ * Real.exp (-m * R) / (1 - α) := by
  have hrows := WeightedMixedInfluence.unweighted_row c (fun i j => Real.exp (m * d i j)) hc
    (fun i j => Real.one_le_exp_iff.mpr (mul_nonneg hm (hd i j))) α hweighted
  have hw := WeightedMixedInfluence.iterate_rows c (fun i j => Real.exp (m * d i j)) hc
    (fun i j => (Real.exp_pos _).le) hdiag
    (WeightedMixedInfluence.exp_triangle d htriangle m hm) α hα hα1.le hweighted E k
  exact covariance_decay μ _ F G (MixedInfluenceBudget.iterate c E k) hw.1
    (MixedEliminationTower.tower_localInfluence μ A c hc hsym hdiag hA α hα hα1.le hrows E k)
    d hd r hr m α R hm hα hα1 hw.2.2 S T hF hG hS hT

end
end UnifiedTheory.Clay.YangMills.GibbsWeightedClustering
