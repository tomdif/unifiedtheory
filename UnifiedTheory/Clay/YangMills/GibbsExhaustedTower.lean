/- Complete covariance exhaustion when a genuine coordinate-elimination schedule
empties the active coordinate inventory. Every stage observable support is
contained in the remaining active set; when the active set is empty, the
retained response is constant and its covariance vanishes identically. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorResponseIteration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsExhaustedTower
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorElimination
open FiniteFactorSupportGrowth FiniteFactorIteration FiniteFactorResponseIteration

universe u v
variable {I P : Type u} {X : Type v}

/-- A function depending on the empty coordinate set is constant on the product space. -/
theorem empty_dependsOn_const {F : (I → X) → ℝ} (hF : DependsOn F (∅ : Set I))
    (U V : I → X) : F U = F V :=
  hF (fun _ hi => False.elim hi)

/-- Expectation of an empty-support observable under any probability law equals its point value. -/
theorem integral_eq_eval_of_empty_dependsOn [MeasurableSpace (I → X)]
    (ν : Measure (I → X)) [IsProbabilityMeasure ν] {F : (I → X) → ℝ}
    (hF : DependsOn F (∅ : Set I)) (U : I → X) :
    (∫ V, F V ∂ν) = F U := by
  have hc : (fun V => F V) = (fun _ => F U) := funext (fun V => empty_dependsOn_const hF V U)
  rw [hc, integral_const, probReal_univ, one_smul]

/-- Any observable depending on the empty set has zero covariance with every observable. -/
theorem covariance_eq_zero_of_empty_dependsOn_left [MeasurableSpace (I → X)]
    (ν : Measure (I → X)) [IsProbabilityMeasure ν] [Nonempty (I → X)]
    {F G : (I → X) → ℝ} (hF : DependsOn F (∅ : Set I)) :
    GibbsCrossCovariance.covariance ν F G = 0 := by
  let U₀ : I → X := Classical.arbitrary (I → X)
  have hFG : (fun V => F V * G V) = (fun V => F U₀ * G V) :=
    funext (fun V => by rw [empty_dependsOn_const hF V U₀])
  unfold GibbsCrossCovariance.covariance
  rw [hFG, integral_const_mul, integral_eq_eval_of_empty_dependsOn ν hF U₀, sub_self]

/-- Symmetric empty-support covariance vanishing in the second argument. -/
theorem covariance_eq_zero_of_empty_dependsOn_right [MeasurableSpace (I → X)]
    (ν : Measure (I → X)) [IsProbabilityMeasure ν] [Nonempty (I → X)]
    {F G : (I → X) → ℝ} (hG : DependsOn G (∅ : Set I)) :
    GibbsCrossCovariance.covariance ν F G = 0 := by
  let U₀ : I → X := Classical.arbitrary (I → X)
  have hFG : (fun V => F V * G V) = (fun V => G U₀ * F V) :=
    funext (fun V => by rw [empty_dependsOn_const hG V U₀, mul_comm])
  unfold GibbsCrossCovariance.covariance
  rw [hFG, integral_const_mul, integral_eq_eval_of_empty_dependsOn ν hG U₀, mul_comm, sub_self]

variable [DecidableEq I] [Fintype P]

/-- One-step source support expansion remains inside the remaining active coordinates. -/
theorem sourceSupport_subset (D : P → Finset I) (T Q B : Finset I)
    (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) :
    sourceSupport D T Q ⊆ B \ T := by
  intro i hi
  obtain ⟨hiT, hsrc⟩ := (mem_sourceSupport D T Q i).mp hi
  refine Finset.mem_sdiff.mpr ⟨?_, hiT⟩
  rcases hsrc with hiQ | ⟨_, _, _, p, _, hip⟩
  · exact hQ hiQ
  · exact hD p hip

/-- At every elimination depth, the evolved source support lies inside the active set. -/
theorem sourceSupports_subset_active (D : P → Finset I) (T : ℕ → Finset I)
    (Q B : Finset I) (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) :
    ∀ k, sourceSupports D T Q k ⊆ active B T k := by
  intro k
  induction k with
  | zero => exact hQ
  | succ k ih =>
    exact sourceSupport_subset (supports D T k) (T k) (sourceSupports D T Q k)
      (active B T k) (supports_subset_active D T B hD k) ih

/-- Exhausting the active coordinate inventory forces the evolved source support to be empty. -/
theorem sourceSupports_eq_empty_of_active_empty (D : P → Finset I) (T : ℕ → Finset I)
    (Q B : Finset I) (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) (N : ℕ)
    (hN : active B T N = ∅) :
    sourceSupports D T Q N = ∅ :=
  Finset.subset_empty.mp (hN ▸ sourceSupports_subset_active D T Q B hD hQ N)

section ExhaustedTower
variable [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- At an exhaustion depth, the genuine conditional response depends on no coordinates. -/
theorem observable_dependsOn_empty_of_exhausted (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : ℕ → Finset I) (hT : ∀ k, Independent (supports D T k) (T k))
    (F : C(I → X, ℝ)) (Q B : Finset I) (hF : DependsOn F (Q : Set I))
    (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) (N : ℕ) (hN : active B T N = ∅) :
    DependsOn (GibbsCoordinateTower.observable μ T
      ⟨action Φ, action_continuous Φ hΦc⟩ F N) (∅ : Set I) := by
  have hd := observable_dependsOn μ D Φ hΦc hΦ T hT F Q hF N
  rw [sourceSupports_eq_empty_of_active_empty D T Q B hD hQ N hN, Finset.coe_empty] at hd
  exact hd

/-- At an exhaustion depth, the genuine conditional response is a constant function. -/
theorem observable_const_of_exhausted (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : ℕ → Finset I) (hT : ∀ k, Independent (supports D T k) (T k))
    (F : C(I → X, ℝ)) (Q B : Finset I) (hF : DependsOn F (Q : Set I))
    (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) (N : ℕ) (hN : active B T N = ∅)
    (U V : I → X) :
    GibbsCoordinateTower.observable μ T ⟨action Φ, action_continuous Φ hΦc⟩ F N U =
      GibbsCoordinateTower.observable μ T ⟨action Φ, action_continuous Φ hΦc⟩ F N V :=
  empty_dependsOn_const
    (observable_dependsOn_empty_of_exhausted μ D Φ hΦc hΦ T hT F Q B hF hD hQ N hN) U V

/-- The retained covariance at an exhaustion depth vanishes identically. -/
theorem covarianceAt_eq_zero_of_exhausted (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : ℕ → Finset I) (hT : ∀ k, Independent (supports D T k) (T k))
    (F G : C(I → X, ℝ)) (Q B : Finset I) (hF : DependsOn F (Q : Set I))
    (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) (N : ℕ) (hN : active B T N = ∅) :
    GibbsCoordinateTower.covarianceAt μ T ⟨action Φ, action_continuous Φ hΦc⟩ F G N = 0 := by
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure μ
  exact covariance_eq_zero_of_empty_dependsOn_left
    (GibbsCoordinateTower.law μ T ⟨action Φ, action_continuous Φ hΦc⟩ N)
    (observable_dependsOn_empty_of_exhausted μ D Φ hΦc hΦ T hT F Q B hF hD hQ N hN)

/-- Complete finite-depth covariance decomposition with zero unintegrated remainder. -/
theorem exhausted_covariance_eq_sum (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : ℕ → Finset I) (hT : ∀ k, Independent (supports D T k) (T k))
    (F G : C(I → X, ℝ)) (Q B : Finset I) (hF : DependsOn F (Q : Set I))
    (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) (N : ℕ) (hN : active B T N = ∅) :
    GibbsCoordinateTower.covarianceAt μ T ⟨action Φ, action_continuous Φ hΦc⟩ F G 0 =
      ∑ k ∈ Finset.range N,
        GibbsCoordinateTower.coefficient μ T ⟨action Φ, action_continuous Φ hΦc⟩ F G k := by
  rw [GibbsCoordinateTower.covariance_telescope μ T ⟨action Φ, action_continuous Φ hΦc⟩ F G N,
    covarianceAt_eq_zero_of_exhausted μ D Φ hΦc hΦ T hT F G Q B hF hD hQ N hN, add_zero]

end ExhaustedTower
end
end UnifiedTheory.Clay.YangMills.GibbsExhaustedTower
