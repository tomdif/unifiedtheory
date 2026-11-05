/- Product expectation comparison by changing one genuine marginal at a time. -/
import UnifiedTheory.Clay.YangMills.SingleCoordinateProduct
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteProductInfluence
noncomputable section
open MeasureTheory SingleCoordinateProduct

variable {I X : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- A bound on the oscillation when just one input coordinate changes. -/
def OscBound (F : (I → X) → ℝ) (d : I → ℝ) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ d i

omit [CompactSpace X] [BorelSpace X] in
/-- Splitting a finite product at a coordinate preserves its actual, possibly unequal, marginals. -/
theorem assemble_preserving_family (e : I) (μ : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (assemble e)
      ((Measure.pi (fun i : {j : I // j ≠ e} => μ i)).prod (μ e)) (Measure.pi μ) := by
  let ν : Option {i : I // i ≠ e} → Measure X := fun i => μ (Equiv.optionSubtypeNe e i)
  have hopt : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i : I // i ≠ e} => X)).symm
      ((Measure.pi (fun i : {j : I // j ≠ e} => μ i)).prod (μ e)) (Measure.pi ν) :=
    ⟨(MeasurableEquiv.piOptionEquivProd _).symm.measurable,
      Measure.pi_map_piOptionEquivProd ν⟩
  exact (measurePreserving_piCongrLeft μ (Equiv.optionSubtypeNe e)).comp hopt

/-- Exact one-coordinate Fubini formula for a continuous observable. -/
theorem integral_split (e : I) (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : C(I → X, ℝ)) :
    (∫ x, F x ∂Measure.pi μ) =
      ∫ r, ∫ a, F (assemble e (r, a)) ∂μ e
        ∂Measure.pi (fun i : {j : I // j ≠ e} => μ i) := by
  rw [← (assemble_preserving_family e μ).integral_comp' F]
  exact integral_prod _ ((F.continuous.comp (assemble_continuous e)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

omit [DecidableEq I] in
/-- Changing just one marginal is controlled by its actual test discrepancy. -/
theorem one_marginal_comparison (e : I) (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hsame : ∀ i, i ≠ e → μ i = ν i) (F : C(I → X, ℝ)) (d b : ℝ)
    (hF : ∀ x y, (∀ j, j ≠ e → x j = y j) → |F x - F y| ≤ d)
    (hlocal : ∀ G : C(X, ℝ), (∀ a b, |G a - G b| ≤ d) →
      |(∫ a, G a ∂μ e) - (∫ a, G a ∂ν e)| ≤ b) :
    |(∫ x, F x ∂Measure.pi μ) - (∫ x, F x ∂Measure.pi ν)| ≤ b := by
  classical
  have hout : (fun i : {j : I // j ≠ e} => μ i) = (fun i : {j : I // j ≠ e} => ν i) := by
    funext i
    exact hsame i i.property
  rw [integral_split e μ F, integral_split e ν F, ← hout]
  let G : Outside (G := X) e → C(X, ℝ) := fun r =>
    ⟨fun a => F (assemble e (r, a)),
      F.continuous.comp ((assemble_continuous e).comp (continuous_const.prodMk continuous_id))⟩
  have hG (r : Outside (G := X) e) : |(∫ a, G r a ∂μ e) - (∫ a, G r a ∂ν e)| ≤ b := by
    apply hlocal
    intro a a'
    apply hF
    intro j hj
    simp only [assemble_other e j hj]
  have hc (ρ : Measure X) [IsProbabilityMeasure ρ] :
      Continuous (fun r : Outside (G := X) e => ∫ a, F (assemble e (r, a)) ∂ρ) := by
    exact GibbsMarginalTower.fiber_integral_continuous ρ _
      (F.continuous.comp (assemble_continuous e))
  have hiμ := (hc (μ e)).integrable_of_hasCompactSupport
    (μ := Measure.pi (fun i : {j : I // j ≠ e} => μ i)) (HasCompactSupport.of_compactSpace _)
  have hiν := (hc (ν e)).integrable_of_hasCompactSupport
    (μ := Measure.pi (fun i : {j : I // j ≠ e} => μ i)) (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hiμ hiν]
  calc
    _ ≤ ∫ r, |(∫ a, F (assemble e (r, a)) ∂μ e) -
        (∫ a, F (assemble e (r, a)) ∂ν e)|
        ∂Measure.pi (fun i : {j : I // j ≠ e} => μ i) := abs_integral_le_integral_abs
    _ ≤ ∫ _r : Outside (G := X) e, b
        ∂Measure.pi (fun i : {j : I // j ≠ e} => μ i) :=
      integral_mono (hiμ.sub hiν).abs (integrable_const b) hG
    _ = b := by simp

/-- Product marginals after replacing a finite set of coordinates. -/
def switched (μ ν : I → Measure X) (S : Finset I) (i : I) : Measure X :=
  if i ∈ S then ν i else μ i

instance switched_probability (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (S : Finset I) (i : I) : IsProbabilityMeasure (switched μ ν S i) := by
  unfold switched
  split <;> infer_instance

/-- Replacing several independent marginals incurs the sum of their actual discrepancies. -/
theorem product_comparison_partial (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (F : C(I → X, ℝ)) (d b : I → ℝ) (hF : OscBound F d)
    (hlocal : ∀ i, ∀ G : C(X, ℝ), (∀ a a', |G a - G a'| ≤ d i) →
      |(∫ a, G a ∂μ i) - (∫ a, G a ∂ν i)| ≤ b i) (S : Finset I) :
    |(∫ x, F x ∂Measure.pi (switched μ ν S)) - (∫ x, F x ∂Measure.pi μ)| ≤
      ∑ i ∈ S, b i := by
  induction S using Finset.induction_on with
  | empty =>
    have he : switched μ ν ∅ = μ := by funext i; simp [switched]
    simp only [he, sub_self, abs_zero, Finset.sum_empty, le_refl]
  | @insert e S he ih =>
    have hstep :
        |(∫ x, F x ∂Measure.pi (switched μ ν (insert e S))) -
          (∫ x, F x ∂Measure.pi (switched μ ν S))| ≤ b e := by
      refine one_marginal_comparison e _ _ ?_ F (d e) (b e) (hF e) ?_
      · intro i hi
        simp only [switched, Finset.mem_insert, hi, false_or]
      · intro G hG
        simpa only [switched, Finset.mem_insert_self, ↓reduceIte, he, abs_sub_comm]
          using hlocal e G hG
    calc
      _ ≤ |(∫ x, F x ∂Measure.pi (switched μ ν (insert e S))) -
          (∫ x, F x ∂Measure.pi (switched μ ν S))| +
          |(∫ x, F x ∂Measure.pi (switched μ ν S)) -
          (∫ x, F x ∂Measure.pi μ)| := abs_sub_le _ _ _
      _ ≤ b e + ∑ i ∈ S, b i := add_le_add hstep ih
      _ = _ := by rw [Finset.sum_insert he]

omit [DecidableEq I] in
/-- Comparison of genuine finite product laws, derived without measurable maximal couplings. -/
theorem product_comparison (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (F : C(I → X, ℝ)) (d b : I → ℝ) (hF : OscBound F d)
    (hlocal : ∀ i, ∀ G : C(X, ℝ), (∀ a a', |G a - G a'| ≤ d i) →
      |(∫ a, G a ∂μ i) - (∫ a, G a ∂ν i)| ≤ b i) :
    |(∫ x, F x ∂Measure.pi ν) - (∫ x, F x ∂Measure.pi μ)| ≤ ∑ i, b i := by
  classical
  have he : switched μ ν Finset.univ = ν := by funext i; simp [switched]
  simpa only [he] using product_comparison_partial μ ν F d b hF hlocal Finset.univ

end
end UnifiedTheory.Clay.YangMills.FiniteProductInfluence
