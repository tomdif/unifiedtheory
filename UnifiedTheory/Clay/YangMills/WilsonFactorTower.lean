/- Actual Wilson seed for the repeatable finite-factor elimination construction.
All later potentials and supports are computed from the original plaquette factors.
Admissibility means independence for the recomputed support family at each stage.
No small evolved interaction or continuum correlation bound is assumed or claimed. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorIteration
import UnifiedTheory.Clay.YangMills.WilsonInducedSupport
import UnifiedTheory.Clay.YangMills.WilsonSingleLinkStaples

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonFactorTower
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks
open WilsonSingleLinkStaples WilsonMomentBounds

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The literal original Wilson plaquette potential. -/
def initialFactor (β : ℝ) (p : PlaquetteIndex n) (U : Configuration (Vertex n) Q) : ℝ :=
  β * plaquetteTerm n Q character 2 U p

/-- The actual original Wilson action, without any changed reference probability. -/
def initialAction (β : ℝ) : C(Configuration (Vertex n) Q, ℝ) :=
  ⟨WilsonBlockIntegration.action n Q character β 2,
    continuous_orientedWilsonAction _ Q character character_continuous (base n) (loops n) β 2⟩

omit [NeZero n] in
theorem initialFactor_continuous (β : ℝ) (p : PlaquetteIndex n) :
    Continuous (initialFactor n β p) :=
  continuous_const.mul (continuous_const.sub
    (Complex.continuous_re.comp (loopObservable_continuous (Vertex n) Q character
      character_continuous (loops n p))))

theorem initialFactor_dependsOn (β : ℝ) (p : PlaquetteIndex n) :
    DependsOn (initialFactor n β p) (WilsonInducedSupport.plaquetteEdges n p : Set _) := by
  intro U V hUV
  exact congrArg (fun t : ℝ => β * t)
    (WilsonInducedSupport.plaquetteTerm_dependsOn n Q character 2 p hUV)

/-- The finite factor sum is exactly the full original Wilson action. -/
theorem initial_sum (β : ℝ) :
    FiniteFactorConditional.action (initialFactor n β) = initialAction n β := by
  funext U
  change (∑ p, β * plaquetteTerm n Q character 2 U p) =
    β * ∑ p, plaquetteTerm n Q character 2 U p
  exact (Finset.mul_sum _ _ _).symm

/-- Evolving support family, calculated from the actual original plaquette incidences. -/
def supports (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ) :
    FiniteFactorIteration.Index (PlaquetteIndex n) T k → Finset (Edge (Vertex n)) :=
  FiniteFactorIteration.supports (WilsonInducedSupport.plaquetteEdges n) T k

/-- Independence is tested on the current induced supports. -/
def Admissible (T : ℕ → Finset (Edge (Vertex n))) : Prop :=
  ∀ k, FiniteFactorConditional.Independent (supports n T k) (T k)

/-- The actual computed Wilson stage potentials with identity reference value. -/
def factors (β : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ) :
    FiniteFactorIteration.Index (PlaquetteIndex n) T k → Configuration (Vertex n) Q → ℝ :=
  FiniteFactorIteration.factors (compactHaar Q) (initialFactor n β) T 1 k

/-- The continuous action obtained by summing the computed stage potentials. -/
def stageAction (β : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ) :
    C(Configuration (Vertex n) Q, ℝ) :=
  FiniteFactorIteration.stageAction (compactHaar Q) (initialFactor n β)
    (initialFactor_continuous n β) T 1 k

theorem factors_continuous (β : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ)
    (j : FiniteFactorIteration.Index (PlaquetteIndex n) T k) :
    Continuous (factors n β T k j) :=
  FiniteFactorIteration.factors_continuous (compactHaar Q) (initialFactor n β)
    (initialFactor_continuous n β) T 1 k j

theorem factors_dependsOn (β : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ)
    (j : FiniteFactorIteration.Index (PlaquetteIndex n) T k) :
    DependsOn (factors n β T k j) (supports n T k j : Set _) :=
  FiniteFactorIteration.factors_dependsOn (compactHaar Q)
    (WilsonInducedSupport.plaquetteEdges n) (initialFactor n β)
    (initialFactor_dependsOn n β) T 1 k j

/-- The generated factors represent the actual interacting Wilson elimination tower. -/
theorem stageAction_eq_tower (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (hT : Admissible n T) (k : ℕ) :
    stageAction n β T k = GibbsCoordinateTower.action (compactHaar Q) T (initialAction n β) k := by
  have h := FiniteFactorIteration.stageAction_eq_tower (compactHaar Q)
    (WilsonInducedSupport.plaquetteEdges n) (initialFactor n β)
    (initialFactor_continuous n β) (initialFactor_dependsOn n β) T 1 hT k
  have he : (⟨FiniteFactorConditional.action (initialFactor n β),
      FiniteFactorConditional.action_continuous _ (initialFactor_continuous n β)⟩ :
        C(Configuration (Vertex n) Q, ℝ)) = initialAction n β := by
    ext U
    exact congrFun (initial_sum n β) U
  rw [he] at h
  exact h

/-- The tower starts from the literal original normalized Wilson measure. -/
theorem initial_law (β : ℝ) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
      (initialAction n β) = wilsonLaw n Q character β 2 := by
  symm
  exact GibbsCoordinateTransport.gibbs_eq_weightedLaw (Vertex n) Q
    (WilsonBlockIntegration.action n Q character β 2) (initialAction n β).continuous

/-- Every represented stage law is the actual recursively induced law from that Wilson seed. -/
theorem stage_law (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (hT : Admissible n T) (k : ℕ) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
      (stageAction n β T k) =
      GibbsCoordinateTower.law (compactHaar Q) T (initialAction n β) k := by
  rw [stageAction_eq_tower n β T hT k]
  rfl

end
end UnifiedTheory.Clay.YangMills.WilsonFactorTower
