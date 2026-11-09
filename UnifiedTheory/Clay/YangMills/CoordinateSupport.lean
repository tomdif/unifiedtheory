/-
Continuous observables supported on disjoint coordinate sets are independent
under an actual finite product probability. Uses mathlib's existing DependsOn
predicate and reconstructs the observables from their restricted coordinates.
-/
import Mathlib.Probability.Independence.Integration
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Logic.Function.DependsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CoordinateSupport
noncomputable section
open MeasureTheory ProbabilityTheory

variable {I X Y : Type*}

variable [DecidableEq I]

/-- Extend restricted coordinates by one fixed value on the complement. -/
def fill (S : Finset I) (x₀ : X) (u : S → X) : I → X :=
  fun i => if hi : i ∈ S then u ⟨i, hi⟩ else x₀

theorem fill_restrict {S : Finset I} {F : (I → X) → Y}
    (hF : DependsOn F (S : Set I)) (x₀ : X) (U : I → X) :
    F (fill S x₀ (fun i => U i)) = F U := by
  apply hF
  intro i hi
  change i ∈ S at hi
  simp [fill, hi]

variable [TopologicalSpace X]

theorem fill_continuous (S : Finset I) (x₀ : X) : Continuous (fill S x₀) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ S
  · simpa only [fill, dif_pos hi] using
      (continuous_apply (⟨i, hi⟩ : S) : Continuous (fun u : S → X => u ⟨i, hi⟩))
  · simpa only [fill, dif_neg hi] using (continuous_const : Continuous (fun _ : S → X => x₀))

variable [Fintype I] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [Nonempty X]

omit [DecidableEq I] in
/-- Disjoint coordinate supports give actual independence under every product probability. -/
theorem indepFun_of_disjoint (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Finset I) (hST : Disjoint S T) (F G : (I → X) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hFS : DependsOn F (S : Set I)) (hGT : DependsOn G (T : Set I)) :
    IndepFun F G (Measure.pi μ) := by
  classical
  let x₀ : X := Classical.choice inferInstance
  have hi : iIndepFun (fun i (U : I → X) => U i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hST' := hi.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  have hc := hST'.comp ((hF.comp (fill_continuous S x₀)).measurable)
    ((hG.comp (fill_continuous T x₀)).measurable)
  have hf : (F ∘ fill S x₀) ∘ (fun (U : I → X) (i : S) => U i) = F := by
    funext U
    exact fill_restrict hFS x₀ U
  have hg : (G ∘ fill T x₀) ∘ (fun (U : I → X) (i : T) => U i) = G := by
    funext U
    exact fill_restrict hGT x₀ U
  rw [hf, hg] at hc
  exact hc

omit [DecidableEq I] in
/-- The product-moment identity is derived from the product law and disjoint supports. -/
theorem integral_mul_of_disjoint
    (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Finset I) (hST : Disjoint S T) (F G : (I → X) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hFS : DependsOn F (S : Set I)) (hGT : DependsOn G (T : Set I)) :
    (∫ U, F U * G U ∂Measure.pi μ) =
      (∫ U, F U ∂Measure.pi μ) * (∫ U, G U ∂Measure.pi μ) :=
  (indepFun_of_disjoint μ S T hST F G hF hG hFS hGT).integral_fun_mul_eq_mul_integral
    hF.aestronglyMeasurable hG.aestronglyMeasurable

end
end UnifiedTheory.Clay.YangMills.CoordinateSupport
