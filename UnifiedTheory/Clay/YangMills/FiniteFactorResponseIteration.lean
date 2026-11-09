/- Actual arbitrary-depth response locality and quantitative support growth.
The observable is the genuine normalized-response tower, and its factor laws
are the exact recursively integrated actions. No evolved locality is assumed. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorIteration
import UnifiedTheory.Clay.YangMills.FiniteFactorSupportGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteFactorResponseIteration
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorElimination
open FiniteFactorIteration FiniteFactorSupportGrowth

universe u v
variable {I P : Type u} {X : Type v} [DecidableEq I] [Fintype P]

/-- The actual source support expands using each newly computed factor hypergraph. -/
def sourceSupports (D : P → Finset I) (T : ℕ → Finset I) (Q : Finset I) : ℕ → Finset I
  | 0 => Q
  | k + 1 => sourceSupport (supports D T k) (T k) (sourceSupports D T Q k)

theorem sourceSupports_succ (D : P → Finset I) (T : ℕ → Finset I) (Q : Finset I) (k : ℕ) :
    sourceSupports D T Q (k + 1) =
      sourceSupport (supports D T k) (T k) (sourceSupports D T Q k) := rfl

/-- Actual evolving factor supports have a dyadic diameter envelope at every depth. -/
theorem supports_dyadic (Close : ℕ → I → I → Prop)
    (hsymm : ∀ r i j, Close r i j → Close r j i)
    (hmono : ∀ r s i j, r ≤ s → Close r i j → Close s i j)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (D : P → Finset I) (T : ℕ → Finset I) (hD : RelationDiameter Close D 1) :
    ∀ k, RelationDiameter Close (supports D T k) (2 ^ k) := by
  intro k
  induction k with
  | zero => simpa only [supports, pow_zero] using hD
  | succ k ih => exact nextSupport_dyadic Close hsymm hmono hadd _ (T k) k ih

/-- A radius-separated block is independent for the computed stage factors. -/
theorem stage_independent_of_separation (Close : ℕ → I → I → Prop)
    (hsymm : ∀ r i j, Close r i j → Close r j i)
    (hmono : ∀ r s i j, r ≤ s → Close r i j → Close s i j)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (D : P → Finset I) (T : ℕ → Finset I) (hD : RelationDiameter Close D 1)
    (k : ℕ) (hsep : ∀ i ∈ T k, ∀ j ∈ T k, i ≠ j → ¬Close (2 ^ k) i j) :
    Independent (supports D T k) (T k) := by
  intro p i hi j hj hip hjp
  by_contra hij
  exact hsep i hi j hj hij (supports_dyadic Close hsymm hmono hadd D T hD k p i hip j hjp)

/-- Radius growth is proved for the recursively generated source supports. -/
theorem sourceSupports_dyadic (Close : ℕ → I → I → Prop)
    (hsymm : ∀ r i j, Close r i j → Close r j i)
    (hmono : ∀ r s i j, r ≤ s → Close r i j → Close s i j)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (D : P → Finset I) (T : ℕ → Finset I) (hD : RelationDiameter Close D 1)
    (Q : Finset I) (o : I) (hQ : ∀ i ∈ Q, Close 1 o i) :
    ∀ k, ∀ i ∈ sourceSupports D T Q k, Close (2 ^ k) o i := by
  intro k
  induction k with
  | zero => simpa only [sourceSupports, pow_zero] using hQ
  | succ k ih =>
    exact sourceSupport_dyadic Close hmono hadd (supports D T k) (T k) _ k
      (supports_dyadic Close hsymm hmono hadd D T hD k) o ih

/-- Independence at each actual stage limits the evolving incidence to geometric growth. -/
theorem supports_incidence (D : P → Finset I) (T : ℕ → Finset I)
    (hT : ∀ k, Independent (supports D T k) (T k)) (t₀ : ℕ)
    (hD : ∀ i, (touching D i).card ≤ t₀) :
    ∀ k i, (touching (supports D T k) i).card ≤ 2 ^ k * t₀ := by
  intro k
  induction k with
  | zero => simpa only [supports, pow_zero, one_mul] using hD
  | succ k ih =>
    intro i
    calc
      _ ≤ 2 * (touching (supports D T k) i).card := next_touching_card _ _ (hT k) i
      _ ≤ 2 * (2 ^ k * t₀) := Nat.mul_le_mul_left 2 (ih i)
      _ = 2 ^ (k + 1) * t₀ := by rw [pow_succ']; ring

/-- A finite explicit upper envelope for the size of every generated factor. -/
def sizeEnvelope (d₀ t₀ : ℕ) : ℕ → ℕ
  | 0 => d₀
  | k + 1 => max 1 (2 ^ k * t₀) * sizeEnvelope d₀ t₀ k

theorem supports_card (D : P → Finset I) (T : ℕ → Finset I)
    (hT : ∀ k, Independent (supports D T k) (T k)) (d₀ t₀ : ℕ)
    (hD : ∀ p, (D p).card ≤ d₀) (ht : ∀ i, (touching D i).card ≤ t₀) :
    ∀ k p, (supports D T k p).card ≤ sizeEnvelope d₀ t₀ k := by
  intro k
  induction k with
  | zero => exact hD
  | succ k ih =>
    intro p
    have hh := nextSupport_card_bound (supports D T k) (T k)
      (sizeEnvelope d₀ t₀ k) (2 ^ k * t₀) ih (supports_incidence D T hT t₀ ht k) p
    exact hh.trans (by
      change max (sizeEnvelope d₀ t₀ k) ((2 ^ k * t₀) * sizeEnvelope d₀ t₀ k) ≤
        max 1 (2 ^ k * t₀) * sizeEnvelope d₀ t₀ k
      apply max_le
      · calc
          sizeEnvelope d₀ t₀ k = 1 * sizeEnvelope d₀ t₀ k := by omega
          _ ≤ max 1 (2 ^ k * t₀) * sizeEnvelope d₀ t₀ k :=
            Nat.mul_le_mul_right _ (le_max_left _ _)
      · exact Nat.mul_le_mul_right _ (le_max_right _ _))

section Response
variable [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The fixed-space update is literally the normalized selected-coordinate integral. -/
theorem blockResponse_eq_raw (T : Finset I) (A F : C(I → X, ℝ)) (U : I → X) :
    GibbsCoordinateElimination.blockResponse μ T A F U =
      GibbsMarginalTower.response (Measure.pi (fun _ : T => μ))
        (fun z => A (replace T z.1 z.2)) (fun z => F (replace T z.1 z.2)) U := by
  have he := GibbsCoordinateElimination.blockResponse_assemble μ T A F
    ((WilsonBlockMarginal.assemble T).symm U)
  rw [MeasurableEquiv.apply_symm_apply] at he
  rw [he]
  unfold GibbsMarginalTower.response GibbsMarginalTower.fiberMass
  simp_rw [replace_eq_assemble]
  rfl

/-- The actual fixed-space conditional response has the computed factor-star support. -/
theorem blockResponse_dependsOn (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : Finset I) (hT : Independent D T) (F : C(I → X, ℝ))
    (Q : Finset I) (hF : DependsOn F (Q : Set I)) :
    DependsOn (GibbsCoordinateElimination.blockResponse μ T
      ⟨action Φ, action_continuous Φ hΦc⟩ F) (sourceSupport D T Q : Set I) := by
  have he : (GibbsCoordinateElimination.blockResponse μ T
      ⟨action Φ, action_continuous Φ hΦc⟩ F : (I → X) → ℝ) =
      GibbsMarginalTower.response (Measure.pi (fun _ : T => μ))
        (fun z => action Φ (replace T z.1 z.2)) (fun z => F (replace T z.1 z.2)) :=
    funext (blockResponse_eq_raw μ T _ F)
  rw [he]
  exact block_response_dependsOn μ D Φ hΦc hΦ T hT F F.continuous Q hF

/-- Every finite stage of the actual response tower has the computed support.
The hypotheses concern only the initial factors/source and independence of the
computed block supports, never locality of an induced observable or law. -/
theorem observable_dependsOn (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : ℕ → Finset I) (hT : ∀ k, Independent (supports D T k) (T k))
    (F : C(I → X, ℝ)) (Q : Finset I) (hF : DependsOn F (Q : Set I)) :
    ∀ k, DependsOn (GibbsCoordinateTower.observable μ T
      ⟨action Φ, action_continuous Φ hΦc⟩ F k) (sourceSupports D T Q k : Set I) := by
  let x₀ : X := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  intro k
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [GibbsCoordinateTower.observable_succ,
      ← stageAction_eq_tower μ D Φ hΦc hΦ T x₀ hT k]
    exact blockResponse_dependsOn μ (supports D T k) (factors μ Φ T x₀ k)
      (factors_continuous μ Φ hΦc T x₀ k) (factors_dependsOn μ D Φ hΦ T x₀ k)
      (T k) (hT k) _ (sourceSupports D T Q k) ih
/-- Geometric separation suffices for locality of the entire genuine response tower;
no separate assumption of independence for the induced factors is needed. -/
theorem observable_dependsOn_of_separated (Close : ℕ → I → I → Prop)
    (hsymm : ∀ r i j, Close r i j → Close r j i)
    (hmono : ∀ r s i j, r ≤ s → Close r i j → Close s i j)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (hD : RelationDiameter Close D 1) (T : ℕ → Finset I)
    (hsep : ∀ k, ∀ i ∈ T k, ∀ j ∈ T k, i ≠ j → ¬Close (2 ^ k) i j)
    (F : C(I → X, ℝ)) (Q : Finset I) (hF : DependsOn F (Q : Set I)) :
    ∀ k, DependsOn (GibbsCoordinateTower.observable μ T
      ⟨action Φ, action_continuous Φ hΦc⟩ F k) (sourceSupports D T Q k : Set I) :=
  observable_dependsOn μ D Φ hΦc hΦ T
    (fun k => stage_independent_of_separation Close hsymm hmono hadd D T hD k (hsep k))
    F Q hF

end Response
end
end UnifiedTheory.Clay.YangMills.FiniteFactorResponseIteration
