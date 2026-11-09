/- Repeatable exact elimination for arbitrary finite local compact Gibbs factors.
Every output potential is computed by actual integration. Its support is derived
from the original supports, rather than supplied as an evolved-law hypothesis.
The coordinate set stays fixed; integrated coordinates become irrelevant in all
new factors. The genuine retained marginal is identified separately. -/
import UnifiedTheory.Clay.YangMills.LocalPotentialElimination
import UnifiedTheory.Clay.YangMills.CompactGibbsBlockUpdate

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteFactorElimination
noncomputable section
open MeasureTheory FiniteFactorConditional WilsonBlockMarginal

section Algebra
variable {I P X : Type*} [Fintype P] [DecidableEq I]

/-- Fill the eliminated coordinates with a fixed reference value. -/
def reference (T : Finset I) (x₀ : X) (U : I → X) : I → X :=
  fun i => if i ∈ T then x₀ else U i

/-- Original factors touching a selected coordinate. -/
def touching (D : P → Finset I) (i : I) : Finset P :=
  Finset.univ.filter (fun p => i ∈ D p)

/-- The exact support available to a one-coordinate full-action increment. -/
def factorStar (D : P → Finset I) (i : I) : Finset I :=
  (touching D i).biUnion D

/-- Computed supports of the old retained factors and newly generated potentials. -/
def nextSupport (D : P → Finset I) (T : Finset I) : P ⊕ T → Finset I :=
  Sum.elim (fun p => D p \ T) (fun i => factorStar D i.val \ T)

/-- Retained original factors after reference filling. -/
def retainedFactor (Φ : P → (I → X) → ℝ) (T : Finset I) (x₀ : X)
    (p : P) (U : I → X) : ℝ := Φ p (reference T x₀ U)

/-- Literal action increment of one eliminated coordinate. -/
def increment (Φ : P → (I → X) → ℝ) (T : Finset I) (x₀ : X)
    (i : T) (z : (I → X) × X) : ℝ :=
  action Φ (Function.update (reference T x₀ z.1) i.val z.2) -
    action Φ (reference T x₀ z.1)

omit [Fintype P] in
theorem replace_reference (T : Finset I) (x₀ : X) (U : I → X) (V : T → X) :
    replace T (reference T x₀ U) V = replace T U V := by
  funext i
  by_cases hi : i ∈ T <;> simp only [replace, reference, hi, dite_true, dite_false, ite_false]

omit [Fintype P] in
theorem reference_idempotent (T : Finset I) (x₀ : X) (U : I → X) :
    reference T x₀ (reference T x₀ U) = reference T x₀ U := by
  funext i
  by_cases hi : i ∈ T <;> simp only [reference, hi, ite_true, ite_false]

omit [Fintype P] in
theorem reference_dependsOn (T D : Finset I) (x₀ : X) (F : (I → X) → ℝ)
    (hF : DependsOn F (D : Set I)) :
    DependsOn (fun U => F (reference T x₀ U)) ((D \ T : Finset I) : Set I) := by
  intro U V hUV
  apply hF
  intro i hi
  by_cases hit : i ∈ T
  · simp only [reference, if_pos hit]
  · simp only [reference, if_neg hit]
    exact hUV i (Finset.mem_sdiff.mpr ⟨hi, hit⟩)

theorem mem_factorStar (D : P → Finset I) (i j : I) :
    j ∈ factorStar D i ↔ ∃ p, i ∈ D p ∧ j ∈ D p := by
  simp only [factorStar, touching, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- All unaffected factors cancel before locality is assigned to the increment. -/
theorem action_increment_eq_sum (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (U : I → X) (i : I) (q : X) :
    action Φ (Function.update U i q) - action Φ U =
      ∑ p ∈ touching D i, (Φ p (Function.update U i q) - Φ p U) := by
  unfold action
  rw [← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  have hip : i ∉ D p := by
    intro h
    exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  rw [update_unchanged (D p) (Φ p) (hΦ p) U i hip q, sub_self]

theorem action_increment_dependsOn (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (i : I) (q : X) :
    DependsOn (fun U => action Φ (Function.update U i q) - action Φ U)
      (factorStar D i : Set I) := by
  intro U V hUV
  dsimp only
  rw [action_increment_eq_sum D Φ hΦ, action_increment_eq_sum D Φ hΦ]
  apply Finset.sum_congr rfl
  intro p hp
  have hip : i ∈ D p := (Finset.mem_filter.mp hp).2
  have he : Φ p U = Φ p V :=
    hΦ p (fun j hj => hUV j ((mem_factorStar D i j).mpr ⟨p, hip, hj⟩))
  have hu : Φ p (Function.update U i q) = Φ p (Function.update V i q) := by
    apply hΦ p
    intro j hj
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji]
      exact hUV j ((mem_factorStar D i j).mpr ⟨p, hip, hj⟩)
  rw [he, hu]

omit [Fintype P] in
theorem retainedFactor_dependsOn (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : Finset I) (x₀ : X) (p : P) :
    DependsOn (retainedFactor Φ T x₀ p) ((D p \ T : Finset I) : Set I) :=
  reference_dependsOn T (D p) x₀ (Φ p) (hΦ p)

theorem increment_dependsOn (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : Finset I) (x₀ : X) (i : T) (q : X) :
    DependsOn (fun U => increment Φ T x₀ i (U, q))
      ((factorStar D i.val \ T : Finset I) : Set I) :=
  reference_dependsOn T (factorStar D i.val) x₀ _
    (action_increment_dependsOn D Φ hΦ i.val q)

/-- This exact representation is available for every supported finite factor family. -/
theorem action_replace_eq_firstAction (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : Finset I) (hT : Independent D T)
    (x₀ : X) (U : I → X) (V : T → X) :
    action Φ (replace T U V) = LocalPotentialElimination.firstAction
      (retainedFactor Φ T x₀) (increment Φ T x₀) (U, V) := by
  rw [← replace_reference T x₀ U V, action_decomposition D Φ hΦ T hT]
  rfl

theorem nextSupport_disjoint (D : P → Finset I) (T : Finset I) (j : P ⊕ T) :
    Disjoint (nextSupport D T j) T := by
  cases j <;> exact Finset.sdiff_disjoint

/-- Elimination never reintroduces a coordinate already absent from every factor. -/
theorem nextSupport_subset (D : P → Finset I) (T B : Finset I)
    (hD : ∀ p, D p ⊆ B) (j : P ⊕ T) : nextSupport D T j ⊆ B \ T := by
  intro i hi
  rcases j with p | e
  · obtain ⟨hid, hit⟩ := Finset.mem_sdiff.mp hi
    exact Finset.mem_sdiff.mpr ⟨hD p hid, hit⟩
  · obtain ⟨his, hit⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨p, _, hip⟩ := (mem_factorStar D e.val i).mp his
    exact Finset.mem_sdiff.mpr ⟨hD p hip, hit⟩

end Algebra

section Analytic
variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- The actual full-coordinate integrated action; selected input coordinates are ignored. -/
def integrated (Φ : P → (I → X) → ℝ) (T : Finset I) (U : I → X) : ℝ :=
  -Real.log (∫ V : T → X, Real.exp (-action Φ (replace T U V))
    ∂Measure.pi (fun _ : T => μ))

/-- Output factors are literal one-site logarithmic partition potentials. -/
def nextFactor (Φ : P → (I → X) → ℝ) (T : Finset I) (x₀ : X) :
    P ⊕ T → (I → X) → ℝ :=
  LocalPotentialElimination.evolvedFactor μ (retainedFactor Φ T x₀) (increment Φ T x₀)

omit [Fintype I] [Fintype P] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem reference_continuous (T : Finset I) (x₀ : X) : Continuous (reference T x₀) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ T
  · simpa only [reference, if_pos hi] using
      (continuous_const : Continuous (fun _ : I → X => x₀))
  · simpa only [reference, if_neg hi] using
      (continuous_apply i : Continuous (fun U : I → X => U i))

omit [Fintype I] [Fintype P] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem retainedFactor_continuous (Φ : P → (I → X) → ℝ) (hΦ : ∀ p, Continuous (Φ p))
    (T : Finset I) (x₀ : X) (p : P) : Continuous (retainedFactor Φ T x₀ p) :=
  (hΦ p).comp (reference_continuous T x₀)

omit [Fintype I] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem increment_continuous (Φ : P → (I → X) → ℝ) (hΦ : ∀ p, Continuous (Φ p))
    (T : Finset I) (x₀ : X) (i : T) : Continuous (increment Φ T x₀ i) := by
  have hA : Continuous (action Φ) := action_continuous Φ hΦ
  exact (hA.comp (((reference_continuous T x₀).comp continuous_fst).update i.val
    continuous_snd)).sub (hA.comp ((reference_continuous T x₀).comp continuous_fst))

omit [Fintype I] in
theorem nextFactor_continuous [Finite I] (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, Continuous (Φ p)) (T : Finset I) (x₀ : X) (j : P ⊕ T) :
    Continuous (nextFactor μ Φ T x₀ j) :=
  LocalPotentialElimination.evolvedFactor_continuous μ _ _
    (retainedFactor_continuous Φ hΦ T x₀) (increment_continuous Φ hΦ T x₀) j

omit [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [IsProbabilityMeasure μ] in
theorem nextFactor_dependsOn (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : Finset I) (x₀ : X) (j : P ⊕ T) :
    DependsOn (nextFactor μ Φ T x₀ j) (nextSupport D T j : Set I) :=
  LocalPotentialElimination.evolvedFactor_dependsOn μ _ _ _ _
    (retainedFactor_dependsOn D Φ hΦ T x₀) (increment_dependsOn D Φ hΦ T x₀) j

omit [Fintype I] in
/-- Exact closure under elimination into a newly computed finite local factor family. -/
theorem integrated_eq_action (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : Finset I) (hT : Independent D T) (x₀ : X) :
    integrated μ Φ T = action (nextFactor μ Φ T x₀) := by
  have he : (fun z : (I → X) × (T → X) => action Φ (replace T z.1 z.2)) =
      LocalPotentialElimination.firstAction (retainedFactor Φ T x₀) (increment Φ T x₀) :=
    funext (fun z => action_replace_eq_firstAction D Φ hΦ T hT x₀ z.1 z.2)
  change GibbsMarginalTower.effectiveAction (Measure.pi (fun _ : T => μ))
    (fun z => action Φ (replace T z.1 z.2)) = _
  rw [he]
  exact LocalPotentialElimination.effective_eq_factorAction μ _ _
    (increment_continuous Φ hΦc T x₀)

omit [Fintype I] in
/-- The sum is independent of the auxiliary reference, although individual factors need not be. -/
theorem next_action_reference_independent (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : Finset I) (hT : Independent D T) (x₀ x₁ : X) :
    action (nextFactor μ Φ T x₀) = action (nextFactor μ Φ T x₁) := by
  rw [← integrated_eq_action μ D Φ hΦc hΦ T hT x₀,
    ← integrated_eq_action μ D Φ hΦc hΦ T hT x₁]

omit [Fintype I] [Fintype P] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] in
/-- Selected-coordinate replacement is the literal outside/inside reconstruction. -/
theorem replace_eq_assemble (T : Finset I) (U : I → X) (V : T → X) :
    replace T U V = assemble T (((assemble T).symm U).1, V) := by
  funext i
  by_cases hi : i ∈ T
  · simp only [replace, dif_pos hi, assemble_inside T _ i hi]
  · simp only [replace, dif_neg hi, assemble_outside T _ i hi]
    have h := congrArg (fun W : I → X => W i) ((assemble T).apply_symm_apply U)
    simpa only [assemble_outside T _ i hi] using h.symm

omit [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [IsProbabilityMeasure μ] in
/-- Equality with genuine coordinate elimination, matching the actual marginal
construction and fixed-coordinate response tower without a law hypothesis. -/
theorem integrated_eq_splitEffective (Φ : P → (I → X) → ℝ) (T : Finset I) (U : I → X) :
    integrated μ Φ T U = GibbsMarginalTower.effectiveAction (insideMeasure T μ)
      (fun z => action Φ (assemble T z)) (((assemble T).symm U).1) := by
  unfold integrated GibbsMarginalTower.effectiveAction GibbsMarginalTower.fiberMass
  simp_rw [replace_eq_assemble]

end Analytic
end
end UnifiedTheory.Clay.YangMills.FiniteFactorElimination
