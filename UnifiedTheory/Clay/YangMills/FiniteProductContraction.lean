/- Quantitative pushforward domination tensorizes over the actual finite
product measure. No independence is imposed on a subsequently tilted law. -/
import UnifiedTheory.Clay.YangMills.QuaternionCapContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteProductContraction
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

variable {I : Type*} [Fintype I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]

theorem pi_mono (μ ν : ∀ i, Measure (X i)) (h : ∀ i, μ i ≤ ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans
      (Finset.prod_le_prod' (fun i _ => h i (s i)))
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi, Measure.pi, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact ho s

theorem pi_scale (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)] (C : ℝ≥0) :
    Measure.pi (fun i => (C : ℝ≥0∞) • μ i) =
      (C : ℝ≥0∞) ^ Fintype.card I • Measure.pi μ := by
  letI (i : I) : IsFiniteMeasure ((C : ℝ≥0∞) • μ i) :=
    (μ i).smul_finite ENNReal.coe_ne_top
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

theorem pi_map_bound (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    (T : ∀ i, X i → X i) (hT : ∀ i, Measurable (T i)) (C : ℝ≥0)
    (hmap : ∀ i, (μ i).map (T i) ≤ (C : ℝ≥0∞) • μ i) :
    (Measure.pi μ).map (fun x i => T i (x i)) ≤
      (C : ℝ≥0∞) ^ Fintype.card I • Measure.pi μ := by
  rw [Measure.pi_map_pi (fun i => (hT i).aemeasurable)]
  exact (pi_mono _ _ hmap).trans_eq (pi_scale μ C)

end
end UnifiedTheory.Clay.YangMills.FiniteProductContraction
