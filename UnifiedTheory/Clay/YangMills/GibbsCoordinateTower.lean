/- Arbitrarily long genuine coordinate-elimination towers.
Every action is computed by the preceding fiber integration and every source
by its normalized conditional response. Covariance identities use those actual
successive laws; no uniform continuum bound is inferred from telescoping. -/
import UnifiedTheory.Clay.YangMills.GibbsCoordinateElimination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsCoordinateTower
noncomputable section
open MeasureTheory GibbsCrossCovariance GibbsCoordinateElimination

variable {I X : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def action (T : ℕ → Finset I) (A : C(I → X, ℝ)) : ℕ → C(I → X, ℝ) :=
  Nat.rec A (fun k B => blockAction μ (T k) B)

def observable (T : ℕ → Finset I) (A F : C(I → X, ℝ)) : ℕ → C(I → X, ℝ) :=
  Nat.rec F (fun k H => blockResponse μ (T k) (action μ T A k) H)

def law (T : ℕ → Finset I) (A : C(I → X, ℝ)) (k : ℕ) : Measure (I → X) :=
  CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (action μ T A k)

instance lawProbability (T : ℕ → Finset I) (A : C(I → X, ℝ)) (k : ℕ) :
    IsProbabilityMeasure (law μ T A k) :=
  CompactGibbsContinuity.law_probability _ _ (action μ T A k).continuous

def coefficient (T : ℕ → Finset I) (A F G : C(I → X, ℝ)) (k : ℕ) : ℝ :=
  removedGram μ (T k) (action μ T A k) (observable μ T A F k) (observable μ T A G k)

def covarianceAt (T : ℕ → Finset I) (A F G : C(I → X, ℝ)) (k : ℕ) : ℝ :=
  covariance (law μ T A k) (observable μ T A F k) (observable μ T A G k)

@[simp] theorem action_zero (T : ℕ → Finset I) (A : C(I → X, ℝ)) : action μ T A 0 = A := rfl

@[simp] theorem action_succ (T : ℕ → Finset I) (A : C(I → X, ℝ)) (k : ℕ) :
    action μ T A (k + 1) = blockAction μ (T k) (action μ T A k) := rfl

@[simp] theorem observable_zero (T : ℕ → Finset I) (A F : C(I → X, ℝ)) :
    observable μ T A F 0 = F := rfl

@[simp] theorem observable_succ (T : ℕ → Finset I) (A F : C(I → X, ℝ)) (k : ℕ) :
    observable μ T A F (k + 1) =
      blockResponse μ (T k) (action μ T A k) (observable μ T A F k) := rfl

/-- Every stage source retains its original pointwise interval under the genuine successive laws. -/
theorem observable_bounds (T : ℕ → Finset I) (A F : C(I → X, ℝ)) (lo hi : ℝ)
    (hF : ∀ U, F U ∈ Set.Icc lo hi) (k : ℕ) (U : I → X) :
    observable μ T A F k U ∈ Set.Icc lo hi := by
  induction k generalizing U with
  | zero => exact hF U
  | succ k ih =>
    exact response_bounds μ (T k) (action μ T A k) (observable μ T A F k) lo hi
      ih U

/-- Actual stage covariance telescopes into its removed fluctuation and its actual next law. -/
theorem covariance_step (T : ℕ → Finset I) (A F G : C(I → X, ℝ)) (k : ℕ) :
    covarianceAt μ T A F G k = coefficient μ T A F G k + covarianceAt μ T A F G (k + 1) :=
  GibbsCoordinateElimination.covariance_decomposition μ (T k) (action μ T A k)
    (observable μ T A F k) (observable μ T A G k)

/-- Exact finite-depth covariance removal for any sequence of genuine block eliminations. -/
theorem covariance_telescope (T : ℕ → Finset I) (A F G : C(I → X, ℝ)) (N : ℕ) :
    covarianceAt μ T A F G 0 =
      (∑ k ∈ Finset.range N, coefficient μ T A F G k) + covarianceAt μ T A F G N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := covariance_step μ T A F G N
    linarith

theorem covariance_sub_sum (T : ℕ → Finset I) (A F G : C(I → X, ℝ)) (N : ℕ) :
    covarianceAt μ T A F G 0 - (∑ k ∈ Finset.range N, coefficient μ T A F G k) =
      covarianceAt μ T A F G N := by
  have h := covariance_telescope μ T A F G N
  linarith

/-- The actual removed coefficient bound is independent of elimination depth. -/
theorem coefficient_abs_le (T : ℕ → Finset I) (A F G : C(I → X, ℝ))
    (lo hi lo' hi' : ℝ) (hlo : lo ≤ hi) (hlo' : lo' ≤ hi')
    (hF : ∀ U, F U ∈ Set.Icc lo hi) (hG : ∀ U, G U ∈ Set.Icc lo' hi') (k : ℕ) :
    |coefficient μ T A F G k| ≤ (hi - lo) * (hi' - lo') / 4 :=
  removedGram_abs_le μ (T k) (action μ T A k) (observable μ T A F k)
    (observable μ T A G k) lo hi lo' hi' hlo hlo'
    (observable_bounds μ T A F lo hi hF k) (observable_bounds μ T A G lo' hi' hG k)

theorem coefficient_self_nonneg (T : ℕ → Finset I) (A F : C(I → X, ℝ)) (k : ℕ) :
    0 ≤ coefficient μ T A F F k :=
  removedGram_self_nonneg μ (T k) (action μ T A k) (observable μ T A F k)

theorem covarianceAt_self_nonneg (T : ℕ → Finset I) (A F : C(I → X, ℝ)) (k : ℕ) :
    0 ≤ covarianceAt μ T A F F k :=
  GibbsSuccessiveCovariance.covariance_self_nonneg (law μ T A k)
    (observable μ T A F k) (observable μ T A F k).continuous

/-- The finite accumulated diagonal removal is at most the original variance. -/
theorem cumulative_variance_budget (T : ℕ → Finset I) (A F : C(I → X, ℝ)) (N : ℕ) :
    0 ≤ (∑ k ∈ Finset.range N, coefficient μ T A F F k) ∧
      (∑ k ∈ Finset.range N, coefficient μ T A F F k) ≤ covarianceAt μ T A F F 0 := by
  refine ⟨Finset.sum_nonneg (fun k _ => coefficient_self_nonneg μ T A F k), ?_⟩
  have h := covariance_telescope μ T A F F N
  have hn := covarianceAt_self_nonneg μ T A F N
  linarith

/-- Every retained variance decreases along this true tower, with no asserted strict contraction. -/
theorem covarianceAt_antitone (T : ℕ → Finset I) (A F : C(I → X, ℝ)) :
    Antitone (covarianceAt μ T A F F) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := covariance_step μ T A F F k
  have hn := coefficient_self_nonneg μ T A F k
  linarith

end
end UnifiedTheory.Clay.YangMills.GibbsCoordinateTower
