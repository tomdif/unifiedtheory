/- A mixed-interaction recurrence for genuine one-coordinate Gibbs integration.
The new two-step term is proved from the actual logarithmic partition, with
no bound assumed on an output action. The input coefficient is normalized so
that its mixed-action rectangle has size at most four times that coefficient. -/
import UnifiedTheory.Clay.YangMills.MixedInfluenceBudget
import UnifiedTheory.Clay.YangMills.FiniteFactorInfluence
import UnifiedTheory.Clay.YangMills.GibbsMixedInteraction
import UnifiedTheory.Clay.YangMills.GibbsCoordinateTower
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.GibbsMixedElimination
noncomputable section
open MeasureTheory FiniteFactorConditional

section Algebra
variable {I P X : Type*} [DecidableEq I]

/-- Four times the influence budget bounds every mixed action rectangle. -/
def MixedBound (A : (I → X) → ℝ) (c : I → I → ℝ) : Prop :=
  ∀ i j U V, (∀ l, l ≠ j → U l = V l) → ∀ q z,
    |(A (Function.update U i q) - A (Function.update V i q)) -
      (A (Function.update U i z) - A (Function.update V i z))| ≤ 4 * c i j

/-- Exact dictionary with the generated-factor mixing criterion. -/
theorem factor_mixedBound_iff [Fintype P] (Φ : P → (I → X) → ℝ) (c : I → I → ℝ) :
    MixedBound (action Φ) c ↔
      FiniteFactorInfluence.MixedOscillationBound Φ (fun i j => 4 * c i j) := Iff.rfl

/-- A common coordinate replacement preserves agreement outside one specified site. -/
theorem update_agrees (U V : I → X) (j : I) (hUV : ∀ l, l ≠ j → U l = V l)
    (e : I) (q : X) : ∀ l, l ≠ j → Function.update U e q l = Function.update V e q l := by
  intro l hl
  by_cases he : l = e
  · subst l
    simp only [Function.update_self]
  · simp only [Function.update_of_ne he, hUV l hl]

/-- Replacing the only possibly different coordinate removes that difference. -/
theorem update_eq_of_agrees (U V : I → X) (e : I)
    (hUV : ∀ l, l ≠ e → U l = V l) (q : X) :
    Function.update U e q = Function.update V e q := by
  funext l
  by_cases he : l = e
  · subst l
    simp only [Function.update_self]
  · simp only [Function.update_of_ne he, hUV l he]

end Algebra

section FreeEnergy
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Only oscillations in the integrated variable are charged to the new coupling. -/
theorem rectangle_oscillation_bound (A₀₀ A₁₀ A₀₁ A₁₁ : X → ℝ)
    (h₀₀ : Continuous A₀₀) (h₁₀ : Continuous A₁₀) (h₀₁ : Continuous A₀₁)
    (h₁₁ : Continuous A₁₁) (s t d : ℝ)
    (hF : ∀ q z, |(A₀₀ q - A₁₀ q) - (A₀₀ z - A₁₀ z)| ≤ s)
    (hG : ∀ q z, |(A₀₀ q - A₀₁ q) - (A₀₀ z - A₀₁ z)| ≤ t)
    (hD : ∀ q, |A₁₁ q - A₁₀ q - A₀₁ q + A₀₀ q| ≤ d) :
    |GibbsMixedInteraction.freeEnergy μ A₁₁ - GibbsMixedInteraction.freeEnergy μ A₁₀ -
      GibbsMixedInteraction.freeEnergy μ A₀₁ + GibbsMixedInteraction.freeEnergy μ A₀₀| ≤
        d + s * t / 4 := by
  obtain ⟨f, hf, hFb⟩ := ParallelOscillation.interval_of_oscillation
    (⟨fun q => A₀₀ q - A₁₀ q, h₀₀.sub h₁₀⟩ : C(X, ℝ)) s hF
  obtain ⟨g, hg, hGb⟩ := ParallelOscillation.interval_of_oscillation
    (⟨fun q => A₀₀ q - A₀₁ q, h₀₀.sub h₀₁⟩ : C(X, ℝ)) t hG
  have h := GibbsMixedInteraction.rectangle_bound μ A₀₀ A₁₀ A₀₁ A₁₁
    h₀₀ h₁₀ h₀₁ h₁₁ f (f + s) g (g + t) d hf hg hFb hGb hD
  simpa only [add_sub_cancel_left] using h

end FreeEnergy

variable {I X : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- This is the existing genuine coordinate-elimination operator, for a singleton block. -/
def singleAction (A : C(I → X, ℝ)) (e : I) : C(I → X, ℝ) :=
  GibbsCoordinateElimination.blockAction μ {e} A

/-- The singleton fiber integral is exactly integration against the original one-site measure. -/
theorem singleAction_apply (A : C(I → X, ℝ)) (e : I) (U : I → X) :
    singleAction μ A e U = GibbsMixedInteraction.freeEnergy μ
      (fun q => A (Function.update U e q)) := by
  let Φ : Unit → (I → X) → ℝ := fun _ => A
  have hΦ : action Φ = (A : (I → X) → ℝ) := by
    funext W
    simp [action, Φ]
  have h := FiniteFactorElimination.integrated_eq_splitEffective μ Φ {e} U
  unfold FiniteFactorElimination.integrated at h
  simp_rw [hΦ] at h
  change -Real.log (∫ V : ({e} : Finset I) → X,
    Real.exp (-A (replace {e} U V)) ∂Measure.pi (fun _ => μ)) = singleAction μ A e U at h
  let e₀ : ({e} : Finset I) := ⟨e, Finset.mem_singleton_self e⟩
  have he (V : ({e} : Finset I) → X) : replace {e} U V = Function.update U e (V e₀) := by
    funext i
    by_cases hi : i = e
    · subst i
      simp [replace, e₀]
    · simp [replace, hi]
  simp_rw [he] at h
  have hc : AEStronglyMeasurable (fun q : X => Real.exp (-A (Function.update U e q))) μ :=
    (Real.continuous_exp.comp
      (A.continuous.comp (update_continuous U e)).neg).aestronglyMeasurable
  rw [integral_comp_eval (μ := fun _ : ({e} : Finset I) => μ) (i := e₀) hc] at h
  exact h.symm

/-- The old value at an integrated coordinate is irrelevant. -/
theorem singleAction_update (A : C(I → X, ℝ)) (e : I) (U : I → X) (q : X) :
    singleAction μ A e (Function.update U e q) = singleAction μ A e U := by
  simp only [singleAction_apply, Function.update_idem]

theorem singleAction_eq_of_agrees (A : C(I → X, ℝ)) (e : I) (U V : I → X)
    (hUV : ∀ l, l ≠ e → U l = V l) : singleAction μ A e U = singleAction μ A e V := by
  simp only [singleAction_apply, update_eq_of_agrees U V e hUV]

/-- The actual induced action satisfies the computed two-step interaction recurrence. -/
theorem singleAction_mixed [Nonempty X] (A : C(I → X, ℝ)) (c : I → I → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hc : MixedBound A c) (e : I) :
    MixedBound (singleAction μ A e) (MixedInfluenceBudget.step c e) := by
  intro i j U V hUV q z
  by_cases hi : i = e
  · subst i
    simp only [singleAction_update, sub_self, abs_zero]
    simp [MixedInfluenceBudget.step]
  by_cases hj : j = e
  · subst j
    have hq := singleAction_eq_of_agrees μ A e (Function.update U i q)
      (Function.update V i q) (update_agrees U V e hUV i q)
    have hz := singleAction_eq_of_agrees μ A e (Function.update U i z)
      (Function.update V i z) (update_agrees U V e hUV i z)
    rw [hq, hz]
    simp [MixedInfluenceBudget.step]
  by_cases hij : i = j
  · subst j
    rw [update_eq_of_agrees U V i hUV q, update_eq_of_agrees U V i hUV z]
    simp [MixedInfluenceBudget.step]
  let A₀₀ := fun t => A (Function.update (Function.update V i z) e t)
  let A₁₀ := fun t => A (Function.update (Function.update V i q) e t)
  let A₀₁ := fun t => A (Function.update (Function.update U i z) e t)
  let A₁₁ := fun t => A (Function.update (Function.update U i q) e t)
  have hcont (W : I → X) : Continuous (fun t => A (Function.update W e t)) :=
    A.continuous.comp (update_continuous W e)
  have hF (t s : X) : |(A₀₀ t - A₁₀ t) - (A₀₀ s - A₁₀ s)| ≤ 4 * c e i := by
    apply hc e i (Function.update V i z) (Function.update V i q)
    intro l hl
    simp only [Function.update_of_ne hl]
  have hG (t s : X) : |(A₀₀ t - A₀₁ t) - (A₀₀ s - A₀₁ s)| ≤ 4 * c e j :=
    hc e j (Function.update V i z) (Function.update U i z)
      (update_agrees V U j (fun l hl => (hUV l hl).symm) i z) t s
  have hcomm (W : I → X) (t s : X) :
      Function.update (Function.update W e t) i s =
        Function.update (Function.update W i s) e t :=
    Function.update_comm (Ne.symm hi) t s W
  have hD (t : X) : |A₁₁ t - A₁₀ t - A₀₁ t + A₀₀ t| ≤ 4 * c i j := by
    have h := hc i j (Function.update U e t) (Function.update V e t)
      (update_agrees U V j hUV e t) q z
    simp only [hcomm] at h
    convert h using 1
    dsimp [A₁₁, A₁₀, A₀₁, A₀₀]
    congr 1
    ring
  have h := rectangle_oscillation_bound μ A₀₀ A₁₀ A₀₁ A₁₁
    (hcont _) (hcont _) (hcont _) (hcont _) (4 * c e i) (4 * c e j) (4 * c i j) hF hG hD
  simp only [singleAction_apply]
  calc
    _ = |GibbsMixedInteraction.freeEnergy μ A₁₁ - GibbsMixedInteraction.freeEnergy μ A₁₀ -
        GibbsMixedInteraction.freeEnergy μ A₀₁ + GibbsMixedInteraction.freeEnergy μ A₀₀| := by
      dsimp [A₀₀, A₁₀, A₀₁, A₁₁]
      congr 1
      ring
    _ ≤ 4 * c i j + (4 * c e i) * (4 * c e j) / 4 := h
    _ = 4 * MixedInfluenceBudget.step c e i j := by
      rw [MixedInfluenceBudget.step, if_neg (by tauto), hsym e i]
      ring

end
end UnifiedTheory.Clay.YangMills.GibbsMixedElimination
