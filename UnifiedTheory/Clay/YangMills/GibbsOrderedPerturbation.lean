/- A bounded nonnegative action perturbation survives every exact compact
Gibbs integration with the same bound. Partition functions, normalized
densities and bounded observables are controlled without any exceptional
large-field event. A new perturbation at each stage would have its own cost. -/
import UnifiedTheory.Clay.YangMills.GibbsMixedInteraction
import UnifiedTheory.Clay.YangMills.GibbsCoordinateTower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsOrderedPerturbation
noncomputable section
open MeasureTheory GibbsMixedInteraction

section Compact
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem partition_bounds (A B : X → ℝ) (hA : Continuous A) (hB : Continuous B)
    (d : ℝ) (hAB : ∀ x, B x - A x ∈ Set.Icc 0 d) :
    Real.exp (-d) * (∫ x, Real.exp (-A x) ∂μ) ≤ ∫ x, Real.exp (-B x) ∂μ ∧
      (∫ x, Real.exp (-B x) ∂μ) ≤ ∫ x, Real.exp (-A x) ∂μ := by
  have hi (F : X → ℝ) (hF : Continuous F) : Integrable (fun x => Real.exp (-F x)) μ :=
    (Real.continuous_exp.comp hF.neg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  constructor
  · rw [← integral_const_mul]
    apply integral_mono ((hi A hA).const_mul _) (hi B hB)
    intro x
    change Real.exp (-d) * Real.exp (-A x) ≤ Real.exp (-B x)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(hAB x).2])
  · apply integral_mono (hi B hB) (hi A hA)
    intro x
    exact Real.exp_le_exp.mpr (by linarith [(hAB x).1])

/-- Exact integration preserves the ordered interval, including the sign. -/
theorem freeEnergy_bounds (A B : X → ℝ) (hA : Continuous A) (hB : Continuous B)
    (d : ℝ) (hAB : ∀ x, B x - A x ∈ Set.Icc 0 d) :
    freeEnergy μ B - freeEnergy μ A ∈ Set.Icc 0 d := by
  have h := partition_bounds μ A B hA hB d hAB
  have ha := CompactGibbsContinuity.partition_positive μ A hA
  have hb := CompactGibbsContinuity.partition_positive μ B hB
  have hupper := Real.log_le_log hb h.2
  have hlower := Real.log_le_log (mul_pos (Real.exp_pos _) ha) h.1
  rw [Real.log_mul (Real.exp_ne_zero _) ha.ne', Real.log_exp] at hlower
  unfold freeEnergy
  exact ⟨by linarith, by linarith⟩

/-- The literal density relative to the reference probability. -/
def normalizedWeight (A : X → ℝ) (x : X) : ℝ := Real.exp (freeEnergy μ A - A x)

theorem normalizedWeight_eq (A : X → ℝ) (hA : Continuous A) (x : X) :
    normalizedWeight μ A x =
      Real.exp (-A x) / (∫ y, Real.exp (-A y) ∂μ) := by
  unfold normalizedWeight freeEnergy
  rw [show -Real.log (∫ y, Real.exp (-A y) ∂μ) - A x =
    -A x - Real.log (∫ y, Real.exp (-A y) ∂μ) by ring, Real.exp_sub,
    Real.exp_log (CompactGibbsContinuity.partition_positive μ A hA)]

theorem normalizedWeight_ratio_bounds (A B : X → ℝ) (hA : Continuous A)
    (hB : Continuous B) (d : ℝ) (hAB : ∀ x, B x - A x ∈ Set.Icc 0 d) (x : X) :
    Real.exp (-d) ≤ normalizedWeight μ B x / normalizedWeight μ A x ∧
      normalizedWeight μ B x / normalizedWeight μ A x ≤ Real.exp d := by
  have h := freeEnergy_bounds μ A B hA hB d hAB
  simp only [normalizedWeight, ← Real.exp_sub]
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith [(hAB x).1, (hAB x).2, h.1, h.2]

/-- A bounded observable comparison charges only the interval width. -/
theorem expectation_difference (A B F : X → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hF : Continuous F) (d M : ℝ) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hAB : ∀ x, B x - A x ∈ Set.Icc 0 d) (hFb : ∀ x, |F x| ≤ M) :
    |(∫ x, F x ∂CompactGibbsContinuity.law μ B) -
      (∫ x, F x ∂CompactGibbsContinuity.law μ A)| ≤ M * d / 2 := by
  have h := CompactGibbsOscillation.action_expectation_difference μ A B F hA hB hF
    (-d) 0 (-M) M (by linarith) (by linarith)
    (fun x => ⟨by linarith [(hAB x).2], by linarith [(hAB x).1]⟩)
    (fun x => abs_le.mp (hFb x))
  convert h using 1
  ring

end Compact

section Tower
variable {I X : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
open GibbsCoordinateElimination GibbsCoordinateTower CompactGibbsBlockUpdate WilsonBlockMarginal

theorem blockAction_bounds (T : Finset I) (A B : C(I → X, ℝ)) (d : ℝ)
    (hAB : ∀ U, B U - A U ∈ Set.Icc 0 d) (U : I → X) :
    blockAction μ T B U - blockAction μ T A U ∈ Set.Icc 0 d := by
  let b := (split T U).1
  have hc (F : C(I → X, ℝ)) : Continuous (fun q => F (join T (b, q))) :=
    (F.continuous.comp (join T).continuous).comp (continuous_const.prodMk continuous_id)
  exact freeEnergy_bounds (insideMeasure T μ) _ _ (hc A) (hc B) d
    (fun q => hAB (join T (b, q)))

/-- Arbitrarily many exact integrations retain the original error budget. -/
theorem action_bounds (T : ℕ → Finset I) (A B : C(I → X, ℝ)) (d : ℝ)
    (hAB : ∀ U, B U - A U ∈ Set.Icc 0 d) (k : ℕ) (U : I → X) :
    action μ T B k U - action μ T A k U ∈ Set.Icc 0 d := by
  induction k generalizing U with
  | zero => exact hAB U
  | succ k ih => exact blockAction_bounds μ (T k) (action μ T A k) (action μ T B k) d ih U

theorem stage_density_ratio_bounds (T : ℕ → Finset I) (A B : C(I → X, ℝ)) (d : ℝ)
    (hAB : ∀ U, B U - A U ∈ Set.Icc 0 d) (k : ℕ) (U : I → X) :
    Real.exp (-d) ≤ normalizedWeight (Measure.pi (fun _ : I => μ)) (action μ T B k) U /
      normalizedWeight (Measure.pi (fun _ : I => μ)) (action μ T A k) U ∧
    normalizedWeight (Measure.pi (fun _ : I => μ)) (action μ T B k) U /
      normalizedWeight (Measure.pi (fun _ : I => μ)) (action μ T A k) U ≤ Real.exp d :=
  normalizedWeight_ratio_bounds _ _ _ (action μ T A k).continuous (action μ T B k).continuous
    d (action_bounds μ T A B d hAB k) U

theorem stage_expectation_difference (T : ℕ → Finset I) (A B F : C(I → X, ℝ))
    (d M : ℝ) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hAB : ∀ U, B U - A U ∈ Set.Icc 0 d) (hF : ∀ U, |F U| ≤ M) (k : ℕ) :
    |(∫ U, F U ∂law μ T B k) - (∫ U, F U ∂law μ T A k)| ≤ M * d / 2 :=
  expectation_difference _ _ _ _ (action μ T A k).continuous (action μ T B k).continuous
    F.continuous d M hd hM (action_bounds μ T A B d hAB k) hF

end Tower
end
end UnifiedTheory.Clay.YangMills.GibbsOrderedPerturbation
