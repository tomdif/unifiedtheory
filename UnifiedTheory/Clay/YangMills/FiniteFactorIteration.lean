/- Explicit finite-depth local factor closure for genuine coordinate elimination.
The factor index and support family are constructed recursively. At each stage,
independence is checked against the newly computed supports, never against the
initial interaction alone. No uniform interaction estimate is asserted. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorElimination
import UnifiedTheory.Clay.YangMills.GibbsCoordinateTower

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteFactorIteration
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorElimination

universe u v
variable {I P : Type u} {X : Type v} [DecidableEq I]

/-- The actual factor inventory includes every newly integrated coordinate. -/
def Index (P : Type u) (T : ℕ → Finset I) : ℕ → Type u
  | 0 => P
  | k + 1 => Index P T k ⊕ T k

instance indexFintype [Fintype P] (T : ℕ → Finset I) : (k : ℕ) → Fintype (Index P T k)
  | 0 => inferInstanceAs (Fintype P)
  | k + 1 => by
      letI : Fintype (Index P T k) := indexFintype T k
      exact inferInstanceAs (Fintype (Index P T k ⊕ T k))

variable [Fintype P]

/-- Supports are recomputed from the actual previous support hypergraph. -/
def supports (D : P → Finset I) (T : ℕ → Finset I) : (k : ℕ) → Index P T k → Finset I
  | 0 => D
  | k + 1 => nextSupport (supports D T k) (T k)

/-- Remaining active coordinates; this contains every stage support. -/
def active (B : Finset I) (T : ℕ → Finset I) : ℕ → Finset I
  | 0 => B
  | k + 1 => active B T k \ T k

theorem supports_subset_active (D : P → Finset I) (T : ℕ → Finset I)
    (B : Finset I) (hD : ∀ p, D p ⊆ B) :
    ∀ k, ∀ j, supports D T k j ⊆ active B T k := by
  intro k
  induction k with
  | zero => exact hD
  | succ k ih =>
      exact nextSupport_subset (supports D T k) (T k) (active B T k) ih

variable [MeasurableSpace X] (μ : Measure X)

/-- Every potential is obtained from the preceding factors by actual integration. -/
def factors (Φ : P → (I → X) → ℝ) (T : ℕ → Finset I) (x₀ : X) :
    (k : ℕ) → Index P T k → (I → X) → ℝ
  | 0 => Φ
  | k + 1 => nextFactor μ (factors Φ T x₀ k) (T k) x₀

/-- Locality at every finite depth is derived from the computed predecessors. -/
theorem factors_dependsOn (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : ℕ → Finset I) (x₀ : X) :
    ∀ k, ∀ j, DependsOn (factors μ Φ T x₀ k j) (supports D T k j : Set I) := by
  intro k
  induction k with
  | zero => exact hΦ
  | succ k ih =>
      exact nextFactor_dependsOn μ (supports D T k) (factors μ Φ T x₀ k) ih (T k) x₀

section AnalyticCore
variable [Finite I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [IsProbabilityMeasure μ]

theorem factors_continuous (Φ : P → (I → X) → ℝ) (hΦ : ∀ p, Continuous (Φ p))
    (T : ℕ → Finset I) (x₀ : X) : ∀ k, ∀ j, Continuous (factors μ Φ T x₀ k j) := by
  intro k
  induction k with
  | zero => exact hΦ
  | succ k ih => exact nextFactor_continuous μ (factors μ Φ T x₀ k) ih (T k) x₀

/-- The continuous action assembled from the explicitly computed stage factors. -/
def stageAction (Φ : P → (I → X) → ℝ) (hΦ : ∀ p, Continuous (Φ p))
    (T : ℕ → Finset I) (x₀ : X) (k : ℕ) : C(I → X, ℝ) :=
  ⟨action (factors μ Φ T x₀ k), action_continuous _ (factors_continuous μ Φ hΦ T x₀ k)⟩

/-- The successor factor sum equals genuine integration of the preceding action. -/
theorem stageAction_succ_integrated (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : ℕ → Finset I) (x₀ : X) (k : ℕ)
    (hT : Independent (supports D T k) (T k)) (U : I → X) :
    stageAction μ Φ hΦc T x₀ (k + 1) U = integrated μ (factors μ Φ T x₀ k) (T k) U := by
  exact congrFun (integrated_eq_action μ (supports D T k) (factors μ Φ T x₀ k)
    (factors_continuous μ Φ hΦc T x₀ k) (factors_dependsOn μ D Φ hΦ T x₀ k)
    (T k) hT x₀).symm U

end AnalyticCore

variable [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [IsProbabilityMeasure μ]

/-- The computed successor is the genuine marginal action used by the fixed-space Gibbs tower. -/
theorem stageAction_succ (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : ℕ → Finset I) (x₀ : X) (k : ℕ)
    (hT : Independent (supports D T k) (T k)) :
    stageAction μ Φ hΦc T x₀ (k + 1) =
      GibbsCoordinateElimination.blockAction μ (T k) (stageAction μ Φ hΦc T x₀ k) := by
  ext U
  rw [stageAction_succ_integrated μ D Φ hΦc hΦ T x₀ k hT]
  exact integrated_eq_splitEffective μ (factors μ Φ T x₀ k) (T k) U

/-- Every finite stage is exactly the actual recursive induced Gibbs action;
no hypothesis says that an induced action has a local representation. -/
theorem stageAction_eq_tower (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : ℕ → Finset I) (x₀ : X)
    (hT : ∀ k, Independent (supports D T k) (T k)) :
    ∀ k, stageAction μ Φ hΦc T x₀ k =
      GibbsCoordinateTower.action μ T ⟨action Φ, action_continuous Φ hΦc⟩ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [stageAction_succ μ D Φ hΦc hΦ T x₀ k (hT k),
        GibbsCoordinateTower.action_succ, ih]

/-- Auxiliary reference choices leave the actual action unchanged at every stage. -/
theorem stageAction_reference_independent (D : P → Finset I)
    (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : ℕ → Finset I)
    (hT : ∀ k, Independent (supports D T k) (T k)) (x₀ x₁ : X) (k : ℕ) :
    stageAction μ Φ hΦc T x₀ k = stageAction μ Φ hΦc T x₁ k := by
  rw [stageAction_eq_tower μ D Φ hΦc hΦ T x₀ hT,
    stageAction_eq_tower μ D Φ hΦc hΦ T x₁ hT]

end
end UnifiedTheory.Clay.YangMills.FiniteFactorIteration
