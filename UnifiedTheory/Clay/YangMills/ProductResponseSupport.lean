/- Locality of arbitrary nonlinear responses under a genuine independent
compact Gibbs elimination. Inactive coordinate probability factors cancel. -/
import UnifiedTheory.Clay.YangMills.LocalPotentialElimination
import UnifiedTheory.Clay.YangMills.CoordinateSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ProductResponseSupport
noncomputable section
open MeasureTheory

section Products
variable {E X : Type*} [Fintype E] [DecidableEq E]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X]

omit [DecidableEq E] [BorelSpace X] [Nonempty X] in
theorem restriction_preserving (ν : E → Measure X) [∀ e, IsProbabilityMeasure (ν e)]
    (L : Finset E) :
    MeasurePreserving (fun V : E → X => fun e : L => V e)
      (Measure.pi ν) (Measure.pi (fun e : L => ν e)) := by
  classical
  convert measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd ν
    (fun e => e ∈ L)) using 1
  congr 1
  exact Subsingleton.elim _ _

omit [Nonempty X] in
/-- The normalized laws on unused coordinates disappear from the actual integral. -/
theorem integral_restrict (ν : E → Measure X) [∀ e, IsProbabilityMeasure (ν e)]
    (L : Finset E) (F : (E → X) → ℝ) (hF : Continuous F)
    (hL : DependsOn F (L : Set E)) (x₀ : X) :
    (∫ V, F V ∂Measure.pi ν) =
      ∫ W, F (CoordinateSupport.fill L x₀ W) ∂Measure.pi (fun e : L => ν e) := by
  have hc : Continuous (fun W => F (CoordinateSupport.fill L x₀ W)) :=
    hF.comp (CoordinateSupport.fill_continuous L x₀)
  have hm := (restriction_preserving ν L).map_eq
  have hi := integral_map (μ := Measure.pi ν)
    (f := fun W => F (CoordinateSupport.fill L x₀ W))
    (restriction_preserving ν L).measurable.aemeasurable hc.aestronglyMeasurable
  rw [hm] at hi
  simpa only [CoordinateSupport.fill_restrict hL x₀] using hi.symm

omit [DecidableEq E] in
/-- Equality of only the active coordinate laws suffices for every supported source. -/
theorem integral_eq_of_active_laws (ν η : E → Measure X)
    [∀ e, IsProbabilityMeasure (ν e)] [∀ e, IsProbabilityMeasure (η e)]
    (L : Finset E) (F : (E → X) → ℝ) (hF : Continuous F)
    (hL : DependsOn F (L : Set E)) (hνη : ∀ e ∈ L, ν e = η e) :
    (∫ V, F V ∂Measure.pi ν) = ∫ V, F V ∂Measure.pi η := by
  classical
  let x₀ : X := Classical.choice inferInstance
  rw [integral_restrict ν L F hF hL x₀, integral_restrict η L F hF hL x₀]
  have heq : (fun e : L => ν e.val) = (fun e : L => η e.val) :=
    funext (fun e => hνη e e.property)
  rw [heq]
end Products

section Response
variable {J P E X : Type*} [Fintype J] [Fintype P] [Fintype E]
  [DecidableEq J] [DecidableEq E]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Exterior coordinates required by the source and its active conditional laws. -/
def responseSupport (D₀ : Finset J) (D : E → Finset J) (L : Finset E) : Finset J :=
  D₀ ∪ L.biUnion D

omit [Fintype J] [DecidableEq J] [DecidableEq E] in
/-- Genuine product expectation of an arbitrary, possibly nonlinear, multi-coordinate source. -/
theorem response_eq_product (Φ : P → (J → X) → ℝ)
    (A : E → (J → X) × X → ℝ) (F : (J → X) × (E → X) → ℝ)
    (hΦ : ∀ p, Continuous (Φ p)) (hA : ∀ e, Continuous (A e)) (U : J → X) :
    GibbsMarginalTower.response (Measure.pi (fun _ : E => μ))
      (LocalPotentialElimination.firstAction Φ A) F U =
      ∫ V, F (U, V) ∂Measure.pi (fun e =>
        CompactGibbsContinuity.law μ (fun q => A e (U, q))) := by
  rw [GibbsMarginalTower.response_eq_expectation _ _ _
    (LocalPotentialElimination.firstAction_continuous Φ A hΦ hA) U]
  change (∫ V, F (U, V) ∂CompactGibbsContinuity.law
    (Measure.pi (fun _ : E => μ))
    (fun V => (∑ p, Φ p U) + ∑ e, A e (U, V e))) = _
  rw [WilsonParallelConditional.affine_product_law μ (fun e q => A e (U, q))
    (fun e => (hA e).comp (continuous_const.prodMk continuous_id))]

omit [Fintype J] [DecidableEq E] in
/-- Source locality survives actual integration even when the source couples
several removed coordinates nonlinearly. No additive-source hypothesis is used. -/
theorem response_dependsOn (Φ : P → (J → X) → ℝ)
    (A : E → (J → X) × X → ℝ) (F : (J → X) × (E → X) → ℝ)
    (hΦ : ∀ p, Continuous (Φ p)) (hA : ∀ e, Continuous (A e)) (hF : Continuous F)
    (D₀ : Finset J) (D : E → Finset J) (L : Finset E)
    (hDA : ∀ e q, DependsOn (fun U => A e (U, q)) (D e : Set J))
    (hDF : ∀ V, DependsOn (fun U => F (U, V)) (D₀ : Set J))
    (hLF : ∀ U, DependsOn (fun V => F (U, V)) (L : Set E)) :
    DependsOn (GibbsMarginalTower.response (Measure.pi (fun _ : E => μ))
      (LocalPotentialElimination.firstAction Φ A) F)
      (responseSupport D₀ D L : Set J) := by
  classical
  letI : Nonempty X := nonempty_of_isProbabilityMeasure μ
  intro U U' hUU'
  rw [response_eq_product μ Φ A F hΦ hA U, response_eq_product μ Φ A F hΦ hA U']
  have hFF : (fun V => F (U, V)) = (fun V => F (U', V)) := by
    funext V
    apply hDF V
    intro j hj
    exact hUU' j (Finset.mem_union_left _ hj)
  rw [hFF]
  let ν : E → Measure X := fun e => CompactGibbsContinuity.law μ (fun q => A e (U, q))
  let η : E → Measure X := fun e => CompactGibbsContinuity.law μ (fun q => A e (U', q))
  letI (e : E) : IsProbabilityMeasure (ν e) :=
    CompactGibbsContinuity.law_probability μ _
      ((hA e).comp (continuous_const.prodMk continuous_id))
  letI (e : E) : IsProbabilityMeasure (η e) :=
    CompactGibbsContinuity.law_probability μ _
      ((hA e).comp (continuous_const.prodMk continuous_id))
  apply integral_eq_of_active_laws ν η L (fun V => F (U', V))
    (hF.comp (continuous_const.prodMk continuous_id)) (hLF U')
  intro e he
  have heq : (fun q => A e (U, q)) = (fun q => A e (U', q)) := by
    funext q
    apply hDA e q
    intro j hj
    exact hUU' j (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hj⟩))
  change CompactGibbsContinuity.law μ _ = CompactGibbsContinuity.law μ _
  rw [heq]
end Response
end
end UnifiedTheory.Clay.YangMills.ProductResponseSupport
