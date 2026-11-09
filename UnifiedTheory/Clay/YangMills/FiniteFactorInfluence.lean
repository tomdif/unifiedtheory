/- Quantitative conditional influence for arbitrary finite local factors.
The coefficient charges only factors containing both coordinates. Constants
and factors outside the updated coordinate cancel from the actual Gibbs law. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorElimination
import UnifiedTheory.Clay.YangMills.CompactGibbsOscillation
import UnifiedTheory.Clay.YangMills.GibbsConstantShift
import UnifiedTheory.Clay.YangMills.ParallelOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteFactorInfluence
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorElimination

section Algebra
variable {I P X : Type*} [Fintype P] [DecidableEq I]

/-- A global oscillation bound for each actual factor; no norm of its constant part. -/
def OscillationBound (Φ : P → (I → X) → ℝ) (w : P → ℝ) : Prop :=
  ∀ p U V, |Φ p U - Φ p V| ≤ w p

/-- Oscillation of an exterior change as the resampled coordinate varies.
Only the mixed rectangle is charged, rather than the whole action amplitude. -/
def MixedOscillationBound (Φ : P → (I → X) → ℝ) (r : I → I → ℝ) : Prop :=
  ∀ i j U V, (∀ l, l ≠ j → U l = V l) → ∀ q z,
    |(action Φ (Function.update U i q) - action Φ (Function.update V i q)) -
      (action Φ (Function.update U i z) - action Φ (Function.update V i z))| ≤ r i j

/-- Factorwise mixed-rectangle estimates add to a bound for the actual full action. -/
theorem mixedBound_of_factor_bounds (Φ : P → (I → X) → ℝ) (r : P → I → I → ℝ)
    (hr : ∀ p i j U V, (∀ l, l ≠ j → U l = V l) → ∀ q z,
      |(Φ p (Function.update U i q) - Φ p (Function.update V i q)) -
        (Φ p (Function.update U i z) - Φ p (Function.update V i z))| ≤ r p i j) :
    MixedOscillationBound Φ (fun i j => ∑ p, r p i j) := by
  intro i j U V hUV q z
  simp only [action, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun p _ => hr p i j U V hUV q z))

/-- Sum of exactly the factors incident to the resampled coordinate. -/
def localAction (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (i : I) (U : I → X) (q : X) : ℝ :=
  ∑ p ∈ touching D i, Φ p (Function.update U i q)

/-- Shared-factor oscillation budget, with zero diagonal. -/
def coefficient (D : P → Finset I) (w : P → ℝ) (i j : I) : ℝ :=
  if i = j then 0 else (∑ p ∈ touching D i, if j ∈ D p then w p else 0) / 2

theorem coefficient_nonneg (D : P → Finset I) (w : P → ℝ)
    (hw : ∀ p, 0 ≤ w p) (i j : I) : 0 ≤ coefficient D w i j := by
  unfold coefficient
  split
  · exact le_rfl
  · exact div_nonneg (Finset.sum_nonneg (fun p _ => by
      split
      · exact hw p
      · exact le_rfl)) (by norm_num)

/-- The exterior is an additive constant in the one-coordinate action. -/
theorem action_eq_constant_add (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (i : I) (U : I → X) (q : X) :
    action Φ (Function.update U i q) =
      (action Φ U - ∑ p ∈ touching D i, Φ p U) + localAction D Φ i U q := by
  have h := action_increment_eq_sum D Φ hΦ U i q
  rw [Finset.sum_sub_distrib] at h
  unfold localAction
  linarith

/-- Changing one exterior coordinate costs only factors shared with that coordinate. -/
theorem localAction_difference_bound (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (w : P → ℝ)
    (hw : OscillationBound Φ w) (i j : I) (U V : I → X)
    (hUV : ∀ l, l ≠ j → U l = V l) (q : X) :
    |localAction D Φ i U q - localAction D Φ i V q| ≤
      ∑ p ∈ touching D i, if j ∈ D p then w p else 0 := by
  unfold localAction
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p _
  by_cases hj : j ∈ D p
  · rw [if_pos hj]
    exact hw p _ _
  · rw [if_neg hj]
    have he : Φ p (Function.update U i q) = Φ p (Function.update V i q) := by
      apply hΦ p
      intro l hl
      by_cases hli : l = i
      · subst l
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hli]
        exact hUV l (by intro h; subst l; exact hj hl)
    rw [he, sub_self, abs_zero]

variable [Fintype I]

/-- Local weighted support-size budget; the updated coordinate itself is removed. -/
def rowBudget (D : P → Finset I) (w : P → ℝ) (i : I) : ℝ :=
  (∑ p ∈ touching D i, ((D p).erase i).card * w p) / 2

/-- The full row sum is exactly the support-size budget, without a volume factor. -/
theorem coefficient_row_sum (D : P → Finset I) (w : P → ℝ) (i : I) :
    ∑ j, coefficient D w i j = rowBudget D w i := by
  have he (j : I) : coefficient D w i j =
      (∑ p ∈ touching D i, if j ∈ (D p).erase i then w p else 0) / 2 := by
    by_cases hij : i = j
    · subst j
      simp [coefficient]
    · simp [coefficient, hij, Finset.mem_erase, ne_comm]
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_comm]
  unfold rowBudget
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_ite_mem_eq]
  simp

end Algebra

section Analytic
variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- The actual conditional law of the full sum of factors. -/
def coordinateLaw (Φ : P → (I → X) → ℝ) (i : I) (U : I → X) : Measure X :=
  CompactGibbsContinuity.law μ (fun q => action Φ (Function.update U i q))

omit [Fintype I] [SecondCountableTopology X] in
theorem coordinateLaw_probability (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (i : I) (U : I → X) :
    IsProbabilityMeasure (coordinateLaw μ Φ i U) :=
  CompactGibbsContinuity.law_probability μ _
    ((action_continuous Φ hΦc).comp (update_continuous U i))

omit [Fintype I] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem localAction_continuous (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (i : I) (U : I → X) :
    Continuous (localAction D Φ i U) :=
  continuous_finset_sum _ (fun p _ => (hΦc p).comp (update_continuous U i))

omit [Fintype I] [CompactSpace X] [SecondCountableTopology X] [IsProbabilityMeasure μ] in
/-- Normalization cancels the entire exterior action exactly. -/
theorem coordinateLaw_eq_local (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (i : I) (U : I → X) :
    coordinateLaw μ Φ i U = CompactGibbsContinuity.law μ (localAction D Φ i U) := by
  unfold coordinateLaw
  rw [funext (action_eq_constant_add D Φ hΦ i U)]
  exact GibbsConstantShift.law_const_add μ _ (localAction_continuous D Φ hΦc i U) _

omit [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [IsProbabilityMeasure μ] in
/-- A one-site conditional ignores the previous value at that site. -/
theorem coordinateLaw_self (Φ : P → (I → X) → ℝ) (i : I) (U V : I → X)
    (hUV : ∀ l, l ≠ i → U l = V l) : coordinateLaw μ Φ i U = coordinateLaw μ Φ i V := by
  unfold coordinateLaw
  congr 1
  funext q
  congr 1
  funext l
  by_cases hli : l = i
  · subst l
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hli, hUV l hli]

omit [Fintype I] [SecondCountableTopology X] in
/-- General generated interactions satisfy the derived local influence inequality. -/
theorem localInfluence [Nonempty X] (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (w : P → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw : OscillationBound Φ w) :
    ParallelOscillation.LocalInfluence (coordinateLaw μ Φ) (coefficient D w) := by
  intro i j U V hUV G d hG
  by_cases hij : i = j
  · subst j
    rw [coordinateLaw_self μ Φ i U V hUV]
    simp [coefficient]
  · rw [coordinateLaw_eq_local μ D Φ hΦc hΦ i U,
      coordinateLaw_eq_local μ D Φ hΦc hΦ i V]
    obtain ⟨c, hcd, hGb⟩ := ParallelOscillation.interval_of_oscillation G d hG
    let b := ∑ p ∈ touching D i, if j ∈ D p then w p else 0
    have hb : 0 ≤ b := Finset.sum_nonneg (fun p _ => by
      split
      · exact hw0 p
      · exact le_rfl)
    have h := CompactGibbsOscillation.action_expectation_difference μ
      (localAction D Φ i V) (localAction D Φ i U) G
      (localAction_continuous D Φ hΦc i V) (localAction_continuous D Φ hΦc i U)
      G.continuous (-b) b c (c + d) (by linarith) hcd
      (fun q => abs_le.mp (localAction_difference_bound D Φ hΦ w hw i j V U
        (fun l hl => (hUV l hl).symm) q)) hGb
    calc
      _ ≤ ((c + d) - c) * (b - -b) / 4 := h
      _ = coefficient D w i j * d := by rw [coefficient, if_neg hij]; dsimp [b]; ring

omit [Fintype I] [SecondCountableTopology X] in
/-- Mixed action differences give the sharper quarter-oscillation influence bound.
This can be used with the actual generated free-energy rectangle estimates. -/
theorem localInfluence_of_mixed [Nonempty X] (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (r : I → I → ℝ)
    (hr : MixedOscillationBound Φ r) :
    ParallelOscillation.LocalInfluence (coordinateLaw μ Φ) (fun i j => r i j / 4) := by
  intro i j U V hUV G d hG
  have hc (W : I → X) : Continuous (fun q => action Φ (Function.update W i q)) :=
    (action_continuous Φ hΦc).comp (update_continuous W i)
  let Δ : C(X, ℝ) := ⟨fun q => action Φ (Function.update V i q) -
    action Φ (Function.update U i q), (hc V).sub (hc U)⟩
  obtain ⟨a, hab, hAB⟩ := ParallelOscillation.interval_of_oscillation Δ (r i j)
    (fun q z => hr i j V U (fun l hl => (hUV l hl).symm) q z)
  obtain ⟨c, hcd, hGb⟩ := ParallelOscillation.interval_of_oscillation G d hG
  have h := CompactGibbsOscillation.action_expectation_difference μ
    (fun q => action Φ (Function.update V i q))
    (fun q => action Φ (Function.update U i q)) G (hc V) (hc U) G.continuous
    a (a + r i j) c (c + d) hab hcd hAB hGb
  calc
    _ ≤ ((c + d) - c) * ((a + r i j) - a) / 4 := h
    _ = r i j / 4 * d := by ring

end Analytic
end
end UnifiedTheory.Clay.YangMills.FiniteFactorInfluence
