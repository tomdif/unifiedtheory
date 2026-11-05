/- Quantitative mixing for genuine Gibbs laws with arbitrary local factors.
The rate is independent of volume whenever the row budget and number of
independent colors are. This is an auxiliary update theorem, not a physical gap. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorParallelKernel
import UnifiedTheory.Clay.YangMills.ContinuousUpdateContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteFactorContraction
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorInfluence FiniteFactorParallelKernel
open ParallelOscillation

variable {I P X Color : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [Fintype Color] [DecidableEq Color] [Nonempty Color]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Independence must be checked against the full current factor supports. -/
def AdmissibleColoring (D : P → Finset I) (color : I → Color) : Prop :=
  ∀ c, Independent D (Finset.univ.filter (fun i => color i = c))

def law (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p)) : Measure (I → X) :=
  CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (actionMap Φ hΦc)

instance law_probability (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p)) :
    IsProbabilityMeasure (law μ Φ hΦc) :=
  CompactGibbsContinuity.law_probability _ _ (actionMap Φ hΦc).continuous

/-- Average of actual conditional-expectation operators for the selected colors. -/
def update (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p)) (color : I → Color)
    (F : C(I → X, ℝ)) : C(I → X, ℝ) :=
  (Fintype.card Color : ℝ)⁻¹ • ∑ c : Color,
    CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
      (Finset.univ.filter (fun i => color i = c)) F

omit [Nonempty Color] in
theorem update_apply (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (color : I → Color) (F : C(I → X, ℝ)) (U : I → X) :
    update μ Φ hΦc color F U = (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color,
      CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
        (Finset.univ.filter (fun i => color i = c)) F U := by
  simp only [update, ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]

theorem update_stationary (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (color : I → Color) (F : C(I → X, ℝ)) :
    (∫ U, update μ Φ hΦc color F U ∂law μ Φ hΦc) = ∫ U, F U ∂law μ Φ hΦc := by
  simp only [update_apply, integral_const_mul]
  rw [integral_finset_sum Finset.univ (fun c _ =>
    (CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
      (Finset.univ.filter (fun i => color i = c)) F).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  simp_rw [law, CompactGibbsBlockUpdate.blockAverage_stationary]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

omit [Nonempty Color] in
theorem update_reversible (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (color : I → Color) (F H : C(I → X, ℝ)) :
    (∫ U, F U * update μ Φ hΦc color H U ∂law μ Φ hΦc) =
      ∫ U, update μ Φ hΦc color F U * H U ∂law μ Φ hΦc := by
  have hleft (U : I → X) : F U * update μ Φ hΦc color H U =
      (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color, F U *
        CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
          (Finset.univ.filter (fun i => color i = c)) H U := by
    rw [update_apply, ← mul_assoc, mul_comm (F U) _, mul_assoc, Finset.mul_sum]
  have hright (U : I → X) : update μ Φ hΦc color F U * H U =
      (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color,
        CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
          (Finset.univ.filter (fun i => color i = c)) F U * H U := by
    rw [update_apply, mul_assoc, Finset.sum_mul]
  simp_rw [hleft, hright]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have hiL (c : Color) : Integrable (fun U : I → X => F U *
      CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
        (Finset.univ.filter (fun i => color i = c)) H U) (law μ Φ hΦc) :=
    (F.continuous.mul (CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
      (Finset.univ.filter (fun i => color i = c)) H).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hiR (c : Color) : Integrable (fun U : I → X =>
      CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
        (Finset.univ.filter (fun i => color i = c)) F U * H U) (law μ Φ hΦc) :=
    ((CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc)
      (Finset.univ.filter (fun i => color i = c)) F).continuous.mul H.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum Finset.univ (fun c _ => hiL c),
    integral_finset_sum Finset.univ (fun c _ => hiR c)]
  apply Finset.sum_congr rfl
  intro c _
  exact CompactGibbsBlockUpdate.blockAverage_reversible μ (actionMap Φ hΦc) _ F H

omit [Nonempty Color] in
/-- The independent-color product kernel is derived from the actual full interaction. -/
theorem update_eq_colorAverage (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (color : I → Color) (hcolor : AdmissibleColoring D color) (F : C(I → X, ℝ)) (U : I → X) :
    update μ Φ hΦc color F U = colorAverage (coordinateLaw μ Φ) color F U := by
  rw [update_apply]
  unfold colorAverage
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  exact blockAverage_eq_parallelAverage μ D Φ hΦc hΦ U _ (hcolor c) F

/-- Concrete local oscillation budgets yield uniform expectation mixing. -/
theorem iterate_expectation_error [Nonempty X] (D : P → Finset I)
    (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (w : P → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw : OscillationBound Φ w)
    (color : I → Color) (hcolor : AdmissibleColoring D color)
    (α : ℝ) (hα : 0 ≤ α) (hrow : ∀ i, rowBudget D w i ≤ α)
    (F : C(I → X, ℝ)) (d : I → ℝ) (hF : FiniteProductInfluence.OscBound F d)
    (hd : ∀ i, 0 ≤ d i) (k : ℕ) (U : I → X) :
    |updateIterate (update μ Φ hΦc color) k F U - ∫ V, F V ∂law μ Φ hΦc| ≤
      colorRate (Color := Color) α ^ k * ∑ i, d i := by
  letI (i : I) (V : I → X) : IsProbabilityMeasure (coordinateLaw μ Φ i V) :=
    coordinateLaw_probability μ Φ hΦc i V
  exact stationary_error (coordinateLaw μ Φ) color (coefficient D w)
    (localInfluence μ D Φ hΦc hΦ w hw0 hw) (coefficient_nonneg D w hw0)
    (update μ Φ hΦc color) (update_eq_colorAverage μ D Φ hΦc hΦ color hcolor)
    (law μ Φ hΦc) (update_stationary μ Φ hΦc color) F d hF hd α hα
    (fun i => (coefficient_row_sum D w i).trans_le (hrow i)) k U

/-- Centered moments decay for every continuous observable, not just a selected two-point test. -/
theorem centered_moment_bound [Nonempty X] (D : P → Finset I)
    (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (w : P → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw : OscillationBound Φ w)
    (color : I → Color) (hcolor : AdmissibleColoring D color)
    (α : ℝ) (hα : 0 ≤ α) (hrow : ∀ i, rowBudget D w i ≤ α)
    (F : C(I → X, ℝ)) (hmean : (∫ U, F U ∂law μ Φ hΦc) = 0) (k : ℕ) :
    |∫ U, F U * updateIterate (update μ Φ hΦc color) k F U ∂law μ Φ hΦc| ≤
      (2 * Fintype.card I * ‖F‖^2) * colorRate (Color := Color) α ^ k := by
  letI (i : I) (V : I → X) : IsProbabilityMeasure (coordinateLaw μ Φ i V) :=
    coordinateLaw_probability μ Φ hΦc i V
  exact stationary_correlation_uniform (coordinateLaw μ Φ) color (coefficient D w)
    (localInfluence μ D Φ hΦc hΦ w hw0 hw) (coefficient_nonneg D w hw0)
    (update μ Φ hΦc color) (update_eq_colorAverage μ D Φ hΦc hΦ color hcolor)
    (law μ Φ hΦc) (update_stationary μ Φ hΦc color) F hmean α hα
    (fun i => (coefficient_row_sum D w i).trans_le (hrow i)) k

omit [Nonempty Color] in
theorem iterate_eq (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (color : I → Color) (F : C(I → X, ℝ)) (k : ℕ) :
    ContinuousUpdateGap.iterate (update μ Φ hΦc color) k F =
      updateIterate (update μ Φ hΦc color) k F := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ContinuousUpdateGap.iterate, updateIterate, ih]

/-- L2 contraction has no volume prefactor. A fixed color count and α<1 give a uniform rate. -/
theorem centered_norm_contraction [Nonempty X] (D : P → Finset I)
    (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (w : P → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw : OscillationBound Φ w)
    (color : I → Color) (hcolor : AdmissibleColoring D color)
    (α : ℝ) (hα : 0 ≤ α) (hrow : ∀ i, rowBudget D w i ≤ α)
    (F : C(I → X, ℝ)) (hmean : (∫ U, F U ∂law μ Φ hΦc) = 0) :
    ‖ContinuousMap.toLp 2 (law μ Φ hΦc) ℝ (update μ Φ hΦc color F)‖ ≤
      colorRate (Color := Color) α * ‖ContinuousMap.toLp 2 (law μ Φ hΦc) ℝ F‖ := by
  apply ContinuousUpdateContraction.norm_le_of_moments (law μ Φ hΦc) (update μ Φ hΦc color)
    (update_reversible μ Φ hΦc color) F (colorRate (Color := Color) α)
    (2 * Fintype.card I * ‖F‖^2) (colorRate_nonneg _ hα)
  intro k
  simpa only [ContinuousUpdateGap.pairing, iterate_eq] using
    centered_moment_bound μ D Φ hΦc hΦ w hw0 hw color hcolor α hα hrow F hmean k

/-- The sharper mixed-interaction criterion requires no small whole-factor amplitude.
The full action rectangle bounds may come from actual logarithmic integration. -/
theorem centered_norm_contraction_of_mixed [Nonempty X] (D : P → Finset I)
    (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (r : I → I → ℝ)
    (hr0 : ∀ i j, 0 ≤ r i j) (hr : MixedOscillationBound Φ r)
    (color : I → Color) (hcolor : AdmissibleColoring D color)
    (α : ℝ) (hα : 0 ≤ α) (hrow : ∀ i, ∑ j, r i j ≤ 4 * α)
    (F : C(I → X, ℝ)) (hmean : (∫ U, F U ∂law μ Φ hΦc) = 0) :
    ‖ContinuousMap.toLp 2 (law μ Φ hΦc) ℝ (update μ Φ hΦc color F)‖ ≤
      colorRate (Color := Color) α * ‖ContinuousMap.toLp 2 (law μ Φ hΦc) ℝ F‖ := by
  letI (i : I) (V : I → X) : IsProbabilityMeasure (coordinateLaw μ Φ i V) :=
    coordinateLaw_probability μ Φ hΦc i V
  have hnonneg (i j : I) : 0 ≤ r i j / 4 := div_nonneg (hr0 i j) (by norm_num)
  have hrows (i : I) : ∑ j, r i j / 4 ≤ α := by
    rw [← Finset.sum_div]
    linarith [hrow i]
  apply ContinuousUpdateContraction.norm_le_of_moments (law μ Φ hΦc) (update μ Φ hΦc color)
    (update_reversible μ Φ hΦc color) F (colorRate (Color := Color) α)
    (2 * Fintype.card I * ‖F‖^2) (colorRate_nonneg _ hα)
  intro k
  have h := stationary_correlation_uniform (coordinateLaw μ Φ) color (fun i j => r i j / 4)
    (localInfluence_of_mixed μ Φ hΦc r hr) hnonneg
    (update μ Φ hΦc color) (update_eq_colorAverage μ D Φ hΦc hΦ color hcolor)
    (law μ Φ hΦc) (update_stationary μ Φ hΦc color) F hmean α hα hrows k
  simpa only [ContinuousUpdateGap.pairing, iterate_eq] using h

end
end UnifiedTheory.Clay.YangMills.FiniteFactorContraction
