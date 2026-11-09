/- Genuine conditional product laws from finite interaction supports.
Each factor may depend nonlinearly on all coordinates in its stated support.
A selected block meeting each support at most once yields the proved affine
single-coordinate decomposition and hence its actual normalized product law. -/
import UnifiedTheory.Clay.YangMills.WilsonParallelConditional
import Mathlib.Logic.Function.DependsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteFactorConditional
noncomputable section
open MeasureTheory

section Algebra
variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]

/-- No original or generated factor contains two selected coordinates. -/
def Independent (D : P → Finset I) (T : Finset I) : Prop :=
  ∀ p, ∀ i ∈ T, ∀ j ∈ T, i ∈ D p → j ∈ D p → i = j

/-- Replace precisely the selected coordinates, with no redundant auxiliary variables. -/
def replace (T : Finset I) (U : I → X) (V : T → X) : I → X :=
  fun i => if hi : i ∈ T then V ⟨i, hi⟩ else U i

/-- The literal action associated with the finite factor family. -/
def action (Φ : P → (I → X) → ℝ) (U : I → X) : ℝ := ∑ p, Φ p U

omit [Fintype I] [Fintype P] in
theorem update_unchanged (D : Finset I) (F : (I → X) → ℝ)
    (hF : DependsOn F (D : Set I)) (U : I → X) (i : I) (hi : i ∉ D) (q : X) :
    F (Function.update U i q) = F U := by
  apply hF
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  exact Function.update_of_ne hji _ _

omit [Fintype I] [Fintype P] in
/-- One factor can vary with at most one coordinate of an independent block. -/
theorem factor_decomposition (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : Finset I) (hT : Independent D T)
    (U : I → X) (V : T → X) (p : P) :
    Φ p (replace T U V) = Φ p U +
      ∑ i : T, (Φ p (Function.update U i.val (V i)) - Φ p U) := by
  classical
  by_cases hx : ∃ i ∈ T, i ∈ D p
  · obtain ⟨i, hiT, hiD⟩ := hx
    let e : T := ⟨i, hiT⟩
    have he : Φ p (replace T U V) = Φ p (Function.update U i (V e)) := by
      apply hΦ p
      intro j hj
      by_cases hjT : j ∈ T
      · have hji := hT p j hjT i hiT hj hiD
        subst j
        simp only [replace, dif_pos hiT, Function.update_self, e]
      · have hji : j ≠ i := by intro h; subst j; exact hjT hiT
        simp only [replace, dif_neg hjT, Function.update_of_ne hji]
    have hs : (∑ j : T, (Φ p (Function.update U j.val (V j)) - Φ p U)) =
        Φ p (Function.update U i (V e)) - Φ p U := by
      apply Finset.sum_eq_single e
      · intro j _ hje
        have hjD : j.val ∉ D p := by
          intro hjD
          have hji := hT p j.val j.property i hiT hjD hiD
          exact hje (Subtype.ext hji)
        rw [update_unchanged (D p) (Φ p) (hΦ p) U j.val hjD (V j), sub_self]
      · intro h
        exact False.elim (h (Finset.mem_univ e))
    rw [he, hs]
    ring
  · have hnone : ∀ i ∈ T, i ∉ D p := by
      intro i hi hid
      exact hx ⟨i, hi, hid⟩
    have he : Φ p (replace T U V) = Φ p U := by
      apply hΦ p
      intro j hj
      have hjT : j ∉ T := by intro h; exact hnone j h hj
      simp only [replace, dif_neg hjT]
    have hs : (∑ j : T, (Φ p (Function.update U j.val (V j)) - Φ p U)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [update_unchanged (D p) (Φ p) (hΦ p) U j.val (hnone j.val j.property) (V j),
        sub_self]
    rw [he, hs, add_zero]

omit [Fintype I] in
/-- The actual full action is an affine sum of selected-coordinate increments. -/
theorem action_decomposition (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : Finset I) (hT : Independent D T)
    (U : I → X) (V : T → X) :
    action Φ (replace T U V) = action Φ U +
      ∑ i : T, (action Φ (Function.update U i.val (V i)) - action Φ U) := by
  unfold action
  simp_rw [factor_decomposition D Φ hΦ T hT U V]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib]

end Algebra

section Analytic
variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype I] [DecidableEq I] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem action_continuous (Φ : P → (I → X) → ℝ) (hΦ : ∀ p, Continuous (Φ p)) :
    Continuous (action Φ) := continuous_finset_sum _ (fun p _ => hΦ p)

omit [Fintype I] [Fintype P] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem update_continuous (U : I → X) (i : I) :
    Continuous (fun q => Function.update U i q) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using (continuous_id : Continuous (fun q : X => q))
  · simpa only [Function.update_of_ne hji] using
      (continuous_const : Continuous (fun _ : X => U j))

omit [Fintype I] in
/-- The normalized conditional law is proved equal to the product of its genuine
single-coordinate laws; the factorization is not supplied as a premise. -/
theorem conditional_product_law (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : Finset I) (hT : Independent D T) (U : I → X) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : T => μ))
      (fun V => action Φ (replace T U V)) =
      Measure.pi (fun i : T => CompactGibbsContinuity.law μ
        (fun q => action Φ (Function.update U i.val q) - action Φ U)) := by
  have he : (fun V : T → X => action Φ (replace T U V)) =
      fun V : T → X => action Φ U +
        ∑ i : T, (action Φ (Function.update U i.val (V i)) - action Φ U) :=
    funext (fun V => action_decomposition D Φ hΦ T hT U V)
  rw [he]
  have hc : Continuous (action Φ) := action_continuous Φ hΦc
  have hloc (i : T) :
      Continuous (fun q : X => action Φ (Function.update U i.val q) - action Φ U) := by
    exact (hc.comp (update_continuous U i.val)).sub continuous_const
  exact WilsonParallelConditional.affine_product_law (I := T) (X := X) μ
    (fun i q => action Φ (Function.update U i.val q) - action Φ U) hloc (action Φ U)


end Analytic
end
end UnifiedTheory.Clay.YangMills.FiniteFactorConditional
