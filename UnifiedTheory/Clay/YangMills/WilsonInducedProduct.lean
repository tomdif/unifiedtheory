/- Genuine local factors and second-block conditional product laws for the
actual retained Wilson action. The generated interactions are computed by
integrating the first independent block; they are not postulated Wilson terms.
Second-block separation is explicit and no uniform contraction is asserted. -/
import UnifiedTheory.Clay.YangMills.LocalPotentialElimination
import UnifiedTheory.Clay.YangMills.WilsonInducedSupport
import UnifiedTheory.Clay.YangMills.WilsonRetainedLawComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonInducedProduct
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks
open WilsonBlockMarginal WilsonMomentBounds WilsonInducedSupport

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- Literal identity completion of the genuine first-stage exterior. -/
def base (S : Finset (Edge (Vertex n))) (b : Outside (G := G) S) :
    Configuration (Vertex n) G := assemble S (b, fun _ => 1)

/-- Project an actual native edge support to the retained coordinate subtype. -/
def support (S D : Finset (Edge (Vertex n))) :
    Finset {e : Edge (Vertex n) // e ∉ S} := Finset.univ.filter (fun e => e.val ∈ D)

/-- Retained original plaquette factors, evaluated at the fixed first block. -/
def originalFactor (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (p : PlaquetteIndex n) (b : Outside (G := G) S) : ℝ :=
  β * plaquetteTerm n G χ c (base n G S b) p

/-- Exact original-action increment associated with an integrated edge. -/
def starAction (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (e : S) (z : Outside (G := G) S × G) : ℝ :=
  WilsonBlockIntegration.action n G χ β c (Function.update (base n G S z.1) e.val z.2) -
    WilsonBlockIntegration.action n G χ β c (base n G S z.1)

/-- Actual retained and generated potentials, indexed by their true origins. -/
def factor (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n))) :
    PlaquetteIndex n ⊕ S → Outside (G := G) S → ℝ :=
  LocalPotentialElimination.evolvedFactor (compactHaar G)
    (originalFactor n G χ β c S) (starAction n G χ β c S)

def factorSupport (S : Finset (Edge (Vertex n))) (j : PlaquetteIndex n ⊕ S) :
    Finset {e : Edge (Vertex n) // e ∉ S} := support n S (inducedSupport n S j)

omit [NeZero n] [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] in
theorem base_continuous (S : Finset (Edge (Vertex n))) : Continuous (base n G S) :=
  (assemble_continuous S).comp (continuous_id.prodMk continuous_const)

omit [NeZero n] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem base_reference (S : Finset (Edge (Vertex n))) (b : Outside (G := G) S) :
    reference n G S (base n G S b) = base n G S b := by
  funext e
  by_cases he : e ∈ S
  · simp [reference, base, he]
  · simp only [reference, if_neg he]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem base_dependsOn (S D : Finset (Edge (Vertex n)))
    (F : Configuration (Vertex n) G → ℝ) (hF : DependsOn F (D : Set _)) :
    DependsOn (fun b => F (base n G S b)) (support n S D : Set _) := by
  intro b b' hbb
  apply hF
  intro e he
  by_cases hS : e ∈ S
  · simp [base, hS]
  · simpa only [base, assemble_outside S _ e hS] using
      hbb ⟨e, hS⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)

omit [NeZero n] [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem originalFactor_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (p : PlaquetteIndex n) :
    Continuous (originalFactor n G χ β c S p) :=
  continuous_const.mul ((continuous_const.sub
    (Complex.continuous_re.comp
      (loopObservable_continuous (Vertex n) G χ hχ (loops n p)))).comp
      (base_continuous n G S))

omit [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem starAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : S) :
    Continuous (starAction n G χ β c S e) := by
  have ha : Continuous (WilsonBlockIntegration.action n G χ β c) :=
    continuous_orientedWilsonAction _ G χ hχ (PeriodicLattice4.base n) (loops n) β c
  exact (ha.comp (((base_continuous n G S).comp continuous_fst).update e.val
    continuous_snd)).sub (ha.comp ((base_continuous n G S).comp continuous_fst))

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
/-- Literal Wilson split-action identity supplies the generic independent
factor representation, including the retained reference action. -/
theorem splitAction_eq (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (WilsonIndependentBlocks.edgeCoord n))) :
    splitAction n G χ β c S = LocalPotentialElimination.firstAction
      (originalFactor n G χ β c S) (starAction n G χ β c S) := by
  funext z
  change WilsonBlockIntegration.action n G χ β c (assemble S (z.1, z.2)) = _
  rw [WilsonSeparatedSources.inside_action_sum n G χ β c S hS z.1 z.2]
  change WilsonBlockIntegration.action n G χ β c (base n G S z.1) + _ = _
  simp only [LocalPotentialElimination.firstAction, originalFactor, starAction]
  change β * (∑ p, plaquetteTerm n G χ c (base n G S z.1) p) + _ = _
  rw [Finset.mul_sum]
  rfl

/-- The actual evolved Wilson action equals the sum of the computed local factors. -/
theorem evolvedAction_eq (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (WilsonIndependentBlocks.edgeCoord n))) :
    WilsonRetainedLawComparison.evolvedAction n G χ β c S =
      FiniteFactorConditional.action (factor n G χ β c S) := by
  unfold WilsonRetainedLawComparison.evolvedAction
  rw [splitAction_eq n G χ β c S hS]
  exact LocalPotentialElimination.effective_eq_factorAction (compactHaar G)
    (originalFactor n G χ β c S) (starAction n G χ β c S)
    (starAction_continuous n G χ hχ β c S)

/-- The generated-factor law is the actual original Wilson marginal. -/
theorem retainedLaw_eq_factorLaw (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (WilsonIndependentBlocks.edgeCoord n))) :
    WilsonCrossCovariance.retainedLaw n G χ β c S =
      CompactGibbsContinuity.law (outsideMeasure S (compactHaar G))
        (FiniteFactorConditional.action (factor n G χ β c S)) := by
  rw [WilsonRetainedLawComparison.retainedLaw_eq_effective n G χ hχ β c S,
    evolvedAction_eq n G χ hχ β c S hS]

theorem factor_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (j : PlaquetteIndex n ⊕ S) :
    Continuous (factor n G χ β c S j) :=
  LocalPotentialElimination.evolvedFactor_continuous (compactHaar G)
    (originalFactor n G χ β c S) (starAction n G χ β c S)
    (originalFactor_continuous n G χ hχ β c S)
    (starAction_continuous n G χ hχ β c S) j

omit [SecondCountableTopology G] in
theorem factor_dependsOn (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (j : PlaquetteIndex n ⊕ S) :
    DependsOn (factor n G χ β c S j) (factorSupport n S j : Set _) := by
  rcases j with p | e
  · intro b b' hbb
    have hp := base_dependsOn n G S (plaquetteEdges n p \ S)
      (fun U => plaquetteTerm n G χ c (reference n G S U) p)
      (plaquette_reference_dependsOn n G χ c S p) hbb
    simpa only [base_reference] using congrArg (fun t : ℝ => β * t) hp
  · apply LocalPotentialElimination.generated_dependsOn
    intro q
    have hi := base_dependsOn n G S (retainedStar n S e.val)
      (fun U => WilsonBlockIntegration.action n G χ β c
        (Function.update (reference n G S U) e.val q) -
        WilsonBlockIntegration.action n G χ β c (reference n G S U))
      (increment_reference_dependsOn n G χ β c S e.val q)
    simpa only [base_reference] using hi

/-- Exact retained-coordinate form of the geometric separation hypothesis. -/
def NextSeparated (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) : Prop :=
  SeparatedStars n (T.image Subtype.val)

theorem factor_independent (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (hT : NextSeparated n S T) :
    FiniteFactorConditional.Independent (factorSupport n S) T := by
  intro j e he d hd hej hdj
  apply Subtype.ext
  exact next_selected_unique n S (T.image Subtype.val) hT j e.val d.val
    (Finset.mem_image.mpr ⟨e, he, rfl⟩) (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
    (Finset.mem_filter.mp hej).2 (Finset.mem_filter.mp hdj).2

/-- The actual induced Wilson law has a genuine product conditional law on
any star-separated second block of surviving edges. -/
theorem conditional_product_law (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (hT : NextSeparated n S T)
    (U : Outside (G := G) S) :
    CompactGibbsContinuity.law (insideMeasure T (compactHaar G))
      (fun V => WilsonRetainedLawComparison.evolvedAction n G χ β c S
        (FiniteFactorConditional.replace T U V)) =
      Measure.pi (fun i : T => CompactGibbsContinuity.law (compactHaar G)
        (fun q => WilsonRetainedLawComparison.evolvedAction n G χ β c S
          (Function.update U i.val q) -
          WilsonRetainedLawComparison.evolvedAction n G χ β c S U)) := by
  rw [evolvedAction_eq n G χ hχ β c S hS]
  exact FiniteFactorConditional.conditional_product_law (compactHaar G) (factorSupport n S)
    (factor n G χ β c S) (factor_continuous n G χ hχ β c S)
    (factor_dependsOn n G χ β c S) T (factor_independent n S T hT) U

omit [SecondCountableTopology G] in
/-- Literal equality with the nested retained action already used by the
successive covariance and noise definitions. -/
theorem retainedAction_eq_evolved (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (z : Outside (G := G) T × Inside (G := G) T) :
    retainedAction n G χ β c S T z =
      WilsonRetainedLawComparison.evolvedAction n G χ β c S (assemble T z) := rfl

omit [NeZero n] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem replace_base (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (r : Outside (G := G) T) (V : Inside (G := G) T) :
    FiniteFactorConditional.replace T (assemble T (r, fun _ => 1)) V =
      assemble T (r, V) := by
  funext e
  by_cases he : e ∈ T
  · simp only [FiniteFactorConditional.replace, dif_pos he, assemble_inside T _ e he]
  · simp only [FiniteFactorConditional.replace, dif_neg he, assemble_outside T _ e he]

/-- Exact second-fiber probability factorization in the literal nested
coordinates used by the actual second removed covariance. -/
theorem second_fiber_product_law (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (hT : NextSeparated n S T)
    (r : Outside (G := G) T) :
    CompactGibbsContinuity.law (insideMeasure T (compactHaar G))
      (fun V => retainedAction n G χ β c S T (r, V)) =
      Measure.pi (fun i : T => CompactGibbsContinuity.law (compactHaar G)
        (fun q => WilsonRetainedLawComparison.evolvedAction n G χ β c S
          (Function.update (assemble T (r, fun _ => 1)) i.val q) -
          WilsonRetainedLawComparison.evolvedAction n G χ β c S
            (assemble T (r, fun _ => 1)))) := by
  have h := conditional_product_law n G χ hχ β c S hS T hT
    (assemble T (r, fun _ => 1))
  simp_rw [replace_base] at h
  simpa only [retainedAction_eq_evolved] using h

end
end UnifiedTheory.Clay.YangMills.WilsonInducedProduct
