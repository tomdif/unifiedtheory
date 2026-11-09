/- Locality and actual conditional factorization after independent elimination.
The generated potentials are the literal negative logarithms of the integrated
single-coordinate weights. Their sum equals the true induced action. A second
block meeting each generated support at most once therefore has a proved
product conditional law. No Wilson-form closure or contraction is assumed. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorConditional
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower
import UnifiedTheory.Clay.YangMills.SU2WilsonBlockEffectiveAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.LocalPotentialElimination
noncomputable section
open MeasureTheory

section Locality
variable {J X Y : Type*} [MeasurableSpace X] (μ : Measure X)

theorem effectiveAction_dependsOn (A : (J → Y) × X → ℝ) (D : Set J)
    (hA : ∀ q, DependsOn (fun U => A (U, q)) D) :
    DependsOn (GibbsMarginalTower.effectiveAction μ A) D := by
  intro U V hUV
  unfold GibbsMarginalTower.effectiveAction GibbsMarginalTower.fiberMass
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q =>
    congrArg (fun t : ℝ => Real.exp (-t)) (hA q hUV))

/-- The numerator and normalizing denominator have the same local exterior
information; locality is proved for the normalized response itself. -/
theorem response_dependsOn (A F : (J → Y) × X → ℝ) (DA DF : Set J)
    (hA : ∀ q, DependsOn (fun U => A (U, q)) DA)
    (hF : ∀ q, DependsOn (fun U => F (U, q)) DF) :
    DependsOn (GibbsMarginalTower.response μ A F) (DA ∪ DF) := by
  intro U V hUV
  have hUa : ∀ q, A (U, q) = A (V, q) :=
    fun q => hA q (fun j hj => hUV j (Set.mem_union_left _ hj))
  have hUf : ∀ q, F (U, q) = F (V, q) :=
    fun q => hF q (fun j hj => hUV j (Set.mem_union_right _ hj))
  unfold GibbsMarginalTower.response GibbsMarginalTower.fiberMass
  simp_rw [hUa, hUf]
end Locality

section Elimination
variable {J P E X : Type*} [Fintype J] [Fintype P] [Fintype E] [DecidableEq J]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- A literal independent-coordinate action, with arbitrary nonlinear local
star potentials and retained factors. -/
def firstAction (Φ : P → (J → X) → ℝ) (A : E → (J → X) × X → ℝ)
    (z : (J → X) × (E → X)) : ℝ :=
  (∑ p, Φ p z.1) + ∑ e, A e (z.1, z.2 e)

/-- The generated factor is defined by actual integration. -/
def generated (A : (J → X) × X → ℝ) : (J → X) → ℝ :=
  GibbsMarginalTower.effectiveAction μ A

/-- The full effective action is defined by actual simultaneous integration. -/
def effective (Φ : P → (J → X) → ℝ) (A : E → (J → X) × X → ℝ) : (J → X) → ℝ :=
  GibbsMarginalTower.effectiveAction (Measure.pi (fun _ : E => μ)) (firstAction Φ A)

/-- Original retained factors and newly generated factors stay distinct. -/
def evolvedFactor (Φ : P → (J → X) → ℝ) (A : E → (J → X) × X → ℝ) :
    P ⊕ E → (J → X) → ℝ := Sum.elim Φ (fun e => generated μ (A e))

def evolvedSupport (D : P → Finset J) (R : E → Finset J) : P ⊕ E → Finset J :=
  Sum.elim D R

omit [Fintype J] [DecidableEq J] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X] in
theorem firstAction_continuous (Φ : P → (J → X) → ℝ) (A : E → (J → X) × X → ℝ)
    (hΦ : ∀ p, Continuous (Φ p)) (hA : ∀ e, Continuous (A e)) :
    Continuous (firstAction Φ A) :=
  (continuous_finset_sum _ (fun p _ => (hΦ p).comp continuous_fst)).add
    (continuous_finset_sum _ (fun e _ =>
      (hA e).comp (continuous_fst.prodMk ((continuous_apply e).comp continuous_snd))))

omit [Fintype J] [Fintype P] [Fintype E] [DecidableEq J] in
theorem generated_continuous [Finite J] (A : (J → X) × X → ℝ) (hA : Continuous A) :
    Continuous (generated μ A) := by
  letI : Fintype J := Fintype.ofFinite J
  exact GibbsMarginalTower.effectiveAction_continuous μ A hA

omit [Fintype J] [Fintype P] [Fintype E] [DecidableEq J] in
theorem evolvedFactor_continuous [Finite J] (Φ : P → (J → X) → ℝ) (A : E → (J → X) × X → ℝ)
    (hΦ : ∀ p, Continuous (Φ p)) (hA : ∀ e, Continuous (A e)) :
    ∀ z, Continuous (evolvedFactor μ Φ A z)
  | .inl p => hΦ p
  | .inr e => generated_continuous μ (A e) (hA e)

omit [Fintype J] [DecidableEq J] in
/-- Exact action of the actual retained marginal, including its constant term. -/
theorem effective_eq_sum (Φ : P → (J → X) → ℝ) (A : E → (J → X) × X → ℝ)
    (hA : ∀ e, Continuous (A e)) (U : J → X) :
    effective μ Φ A U = (∑ p, Φ p U) + ∑ e, generated μ (A e) U := by
  unfold effective firstAction generated GibbsMarginalTower.effectiveAction
    GibbsMarginalTower.fiberMass
  exact SU2WilsonBlockEffectiveAction.log_integral_affine_sum μ
    (fun e q => A e (U, q))
    (fun e => (hA e).comp (continuous_const.prodMk continuous_id)) (∑ p, Φ p U)

omit [Fintype J] [DecidableEq J] in
theorem effective_eq_factorAction (Φ : P → (J → X) → ℝ)
    (A : E → (J → X) × X → ℝ) (hA : ∀ e, Continuous (A e)) :
    effective μ Φ A = FiniteFactorConditional.action (evolvedFactor μ Φ A) := by
  funext U
  rw [effective_eq_sum μ Φ A hA]
  simp only [FiniteFactorConditional.action, Fintype.sum_sum_type, evolvedFactor, Sum.elim_inl,
    Sum.elim_inr]

omit [Fintype P] [Fintype E] [DecidableEq J] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] [Fintype J] [IsProbabilityMeasure μ] in
theorem generated_dependsOn (A : (J → X) × X → ℝ) (D : Finset J)
    (hA : ∀ q, DependsOn (fun U => A (U, q)) (D : Set J)) :
    DependsOn (generated μ A) (D : Set J) := effectiveAction_dependsOn μ A D hA

omit [Fintype J] [Fintype P] [Fintype E] [DecidableEq J] [TopologicalSpace X]
  [CompactSpace X] [SecondCountableTopology X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem evolvedFactor_dependsOn (Φ : P → (J → X) → ℝ)
    (A : E → (J → X) × X → ℝ) (D : P → Finset J) (R : E → Finset J)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set J))
    (hA : ∀ e q, DependsOn (fun U => A e (U, q)) (R e : Set J)) :
    ∀ z, DependsOn (evolvedFactor μ Φ A z) (evolvedSupport D R z : Set J)
  | .inl p => hΦ p
  | .inr e => generated_dependsOn μ (A e) (R e) (hA e)

omit [Fintype J] in
/-- A separated second block has its genuine product conditional probability
law under the nonlinear induced action, not under the original Wilson action. -/
theorem second_conditional_product_law [Finite J] (Φ : P → (J → X) → ℝ)
    (A : E → (J → X) × X → ℝ) (D : P → Finset J) (R : E → Finset J)
    (hΦc : ∀ p, Continuous (Φ p)) (hAc : ∀ e, Continuous (A e))
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set J))
    (hA : ∀ e q, DependsOn (fun U => A e (U, q)) (R e : Set J))
    (T : Finset J) (hT : FiniteFactorConditional.Independent (evolvedSupport D R) T)
    (U : J → X) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : T => μ))
      (fun V => effective μ Φ A (FiniteFactorConditional.replace T U V)) =
      Measure.pi (fun i : T => CompactGibbsContinuity.law μ
        (fun q => effective μ Φ A (Function.update U i.val q) - effective μ Φ A U)) := by
  rw [effective_eq_factorAction μ Φ A hAc]
  exact FiniteFactorConditional.conditional_product_law μ (evolvedSupport D R)
    (evolvedFactor μ Φ A) (evolvedFactor_continuous μ Φ A hΦc hAc)
    (evolvedFactor_dependsOn μ Φ A D R hΦ hA) T hT U

omit [Fintype J] [DecidableEq J] in
/-- Exact cancellation of all other star partitions in a one-coordinate
source response under the full independently integrated action. -/
theorem first_response_coordinate (Φ : P → (J → X) → ℝ)
    (A : E → (J → X) × X → ℝ) (F : (J → X) × X → ℝ)
    (hΦ : ∀ p, Continuous (Φ p)) (hA : ∀ e, Continuous (A e))
    (hF : Continuous F) (e : E) (U : J → X) :
    GibbsMarginalTower.response (Measure.pi (fun _ : E => μ)) (firstAction Φ A)
      (fun z => F (z.1, z.2 e)) U = GibbsMarginalTower.response μ (A e) F U := by
  rw [GibbsMarginalTower.response_eq_expectation _ _ _
    (firstAction_continuous Φ A hΦ hA) U]
  change (∫ V, F (U, V e) ∂CompactGibbsContinuity.law
    (Measure.pi (fun _ : E => μ)) (fun V => (∑ p, Φ p U) + ∑ d, A d (U, V d))) = _
  rw [WilsonParallelConditional.affine_product_law μ (fun d q => A d (U, q))
    (fun d => (hA d).comp (continuous_const.prodMk continuous_id))]
  rw [GibbsMarginalTower.response_eq_expectation μ (A e) F (hA e) U]
  let ν : E → Measure X := fun d => CompactGibbsContinuity.law μ (fun q => A d (U, q))
  letI (d : E) : IsProbabilityMeasure (ν d) :=
    CompactGibbsContinuity.law_probability μ _
      ((hA d).comp (continuous_const.prodMk continuous_id))
  have hm := (measurePreserving_eval ν e).map_eq
  have hcF : Continuous (fun q : X => F (U, q)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hi := integral_map (μ := Measure.pi ν) (f := fun q => F (U, q))
    (measurable_pi_apply e).aemeasurable hcF.aestronglyMeasurable
  rw [hm] at hi
  exact hi.symm

omit [Fintype J] [DecidableEq J] in
/-- The actual full first response of a single-coordinate insertion depends
only on the union of that insertion's exterior support and its star support. -/
theorem first_response_coordinate_dependsOn (Φ : P → (J → X) → ℝ)
    (A : E → (J → X) × X → ℝ) (F : (J → X) × X → ℝ)
    (hΦ : ∀ p, Continuous (Φ p)) (hA : ∀ e, Continuous (A e))
    (hF : Continuous F) (e : E) (DA DF : Set J)
    (hDA : ∀ q, DependsOn (fun U => A e (U, q)) DA)
    (hDF : ∀ q, DependsOn (fun U => F (U, q)) DF) :
    DependsOn (GibbsMarginalTower.response (Measure.pi (fun _ : E => μ))
      (firstAction Φ A) (fun z => F (z.1, z.2 e))) (DA ∪ DF) := by
  rw [funext (first_response_coordinate μ Φ A F hΦ hA hF e)]
  exact response_dependsOn μ (A e) F DA DF hDA hDF

omit [DecidableEq J] in
/-- This effective law is the actual first marginal of the original compact
Gibbs law; no replacement law is supplied. -/
theorem actual_marginal (Φ : P → (J → X) → ℝ) (A : E → (J → X) × X → ℝ)
    (hΦ : ∀ p, Continuous (Φ p)) (hA : ∀ e, Continuous (A e)) :
    GibbsMarginalTower.marginal (Measure.pi (fun _ : J => μ))
      (Measure.pi (fun _ : E => μ)) (firstAction Φ A) =
      CompactGibbsContinuity.law (Measure.pi (fun _ : J => μ)) (effective μ Φ A) :=
  GibbsMarginalTower.marginal_eq_effectiveLaw _ _ _ (firstAction_continuous Φ A hΦ hA)

end Elimination
end
end UnifiedTheory.Clay.YangMills.LocalPotentialElimination
