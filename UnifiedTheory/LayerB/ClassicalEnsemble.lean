/-
  LayerB/ClassicalEnsemble.lean
  ──────────────────────────────

  **Finite classical ensembles** and their mutual information /
  Jensen–Shannon-style divergence to the ensemble average.

  This is the classical (commuting / diagonal) precursor to the
  Holevo bound.  Every theorem in this file lives in the
  probability-vector layer; no operator log is invoked.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `ClassicalEnsemble α X`
         — a finite labelled mixture of probability vectors.
    2. `ensembleAverage E`             — the mixture as a `ProbabilityVector X`.
    3. `ensembleAverage_apply`         — definitional accessor.
    4. `state_ac_average_of_weight_pos`
         — when `weight a > 0`, the component state `E.state a` is
           absolutely continuous w.r.t. the average.
    5. `mutualInformation E`           — `∑_a w_a · KL(ρ_a ‖ ρ̄)`.
    6. `mutualInformation_nonneg`      — Gibbs corollary.
    7. `mapStates`                     — pushforward of the
                                          state-family through a
                                          stochastic channel.
    8. `ensembleAverage_mapStates_apply`
         — the average commutes with the channel (pointwise).
    9. `mutualInformation_contracts_under_stochastic`
         — **classical Holevo precursor**: applying a stochastic
           channel to every state contracts the mutual information.

  Full Holevo (quantum) and accessible-information statements are
  intentionally deferred.
-/

import UnifiedTheory.LayerB.GibbsInequality

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Ensemble

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.LogSumInequality
open UnifiedTheory.LayerB.GibbsInequality

variable {α X Y : Type*} [Fintype α] [Fintype X] [Fintype Y]

/-! ## 1. The ensemble structure -/

/-- A finite labelled classical ensemble: a probability-weighted
    family of probability vectors. -/
structure ClassicalEnsemble (α X : Type*) [Fintype α] [Fintype X] where
  /-- Label weights `p(a)`. -/
  weight : ProbabilityVector α
  /-- Component states `ρ_a`. -/
  state : α → ProbabilityVector X

/-! ## 2. The ensemble average -/

/-- The ensemble average (mixture) `ρ̄(x) = ∑_a w_a · ρ_a(x)`. -/
noncomputable def ensembleAverage
    (E : ClassicalEnsemble α X) : ProbabilityVector X where
  p x := ∑ a, E.weight.p a * (E.state a).p x
  nonneg x := Finset.sum_nonneg fun a _ =>
    mul_nonneg (E.weight.nonneg a) ((E.state a).nonneg x)
  sum_one := by
    rw [Finset.sum_comm]
    have h_each : ∀ a, ∑ x, E.weight.p a * (E.state a).p x = E.weight.p a := by
      intro a
      rw [← Finset.mul_sum, (E.state a).sum_one, mul_one]
    simp_rw [h_each]
    exact E.weight.sum_one

@[simp]
theorem ensembleAverage_apply
    (E : ClassicalEnsemble α X) (x : X) :
    (ensembleAverage E).p x = ∑ a, E.weight.p a * (E.state a).p x := rfl

/-! ## 3. Component states are AC w.r.t. the average -/

/-- **Component-average absolute continuity.**  If `weight.p a > 0`,
    then the component state `E.state a` is absolutely continuous
    w.r.t. the ensemble average: any `x` in the support of
    `E.state a` is also in the support of `ensembleAverage E`,
    because `weight.p a · (state a).p x` is one of the summands. -/
theorem state_ac_average_of_weight_pos
    (E : ClassicalEnsemble α X) {a : α} (ha : 0 < E.weight.p a) :
    IsAbsolutelyContinuous (E.state a) (ensembleAverage E) := by
  intro x hx
  change ∑ a', E.weight.p a' * (E.state a').p x ≠ 0
  -- The single summand at `a` is strictly positive
  have h_state_pos : 0 < (E.state a).p x :=
    lt_of_le_of_ne ((E.state a).nonneg x) (Ne.symm hx)
  have h_summand_pos : 0 < E.weight.p a * (E.state a).p x :=
    mul_pos ha h_state_pos
  have h_summands_nn : ∀ a' ∈ Finset.univ,
      0 ≤ E.weight.p a' * (E.state a').p x := fun a' _ =>
    mul_nonneg (E.weight.nonneg a') ((E.state a').nonneg x)
  have h_sum_pos : 0 < ∑ a', E.weight.p a' * (E.state a').p x :=
    Finset.sum_pos' h_summands_nn ⟨a, Finset.mem_univ _, h_summand_pos⟩
  exact ne_of_gt h_sum_pos

/-! ## 4. Classical mutual information (KL to the average) -/

/-- The classical mutual information of an ensemble: the weighted
    KL divergence of each component state from the ensemble
    average. -/
noncomputable def mutualInformation (E : ClassicalEnsemble α X) : ℝ :=
  ∑ a, E.weight.p a * klDivergence (E.state a) (ensembleAverage E)

/-- **Gibbs corollary: mutual information is non-negative.**
    Zero-weight terms vanish; positive-weight terms invoke
    `state_ac_average_of_weight_pos` to apply Gibbs. -/
theorem mutualInformation_nonneg (E : ClassicalEnsemble α X) :
    0 ≤ mutualInformation E := by
  unfold mutualInformation
  apply Finset.sum_nonneg
  intro a _
  by_cases hwa : E.weight.p a = 0
  · rw [hwa, zero_mul]
  · have h_pos : 0 < E.weight.p a :=
      lt_of_le_of_ne (E.weight.nonneg a) (Ne.symm hwa)
    have h_ac := state_ac_average_of_weight_pos E h_pos
    exact mul_nonneg (E.weight.nonneg a)
                     (klDivergence_nonneg_of_ac _ _ h_ac)

/-! ## 5. Pushforward of an ensemble through a stochastic channel -/

/-- Apply a stochastic channel to every component state, keeping
    the label weights. -/
noncomputable def mapStates
    (E : ClassicalEnsemble α X) (T : StochasticMatrix X Y) :
    ClassicalEnsemble α Y where
  weight := E.weight
  state a := T.push (E.state a)

/-- **The ensemble average commutes with stochastic pushforward**
    (pointwise on the `p` field). -/
theorem ensembleAverage_mapStates_apply
    (E : ClassicalEnsemble α X) (T : StochasticMatrix X Y) (y : Y) :
    (ensembleAverage (mapStates E T)).p y
      = (T.push (ensembleAverage E)).p y := by
  -- LHS: ∑ a, weight a · (T·state a)_y = ∑ a, weight a · ∑ x, T(y,x)·state(a,x)
  -- RHS: ∑ x, T(y,x) · (∑ a, weight a · state(a,x))
  -- Distribute, swap, refactor.
  change ∑ a, E.weight.p a * (∑ x, T.M y x * (E.state a).p x)
       = ∑ x, T.M y x * (∑ a, E.weight.p a * (E.state a).p x)
  simp_rw [Finset.mul_sum]
  -- Now both sides are double sums with the same scalar shape.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-! ## 6. Classical Holevo precursor: mutual information contracts -/

/-- **Classical / commuting Holevo precursor (DPI for mutual
    information).**  Applying a stochastic channel to every state
    of an ensemble cannot increase the ensemble's mutual
    information:

      I(E ; T)  ≤  I(E).

    Proof: per-label, the weight factors out and the inner KL
    divergence contracts under `T` by the classical DPI.
    Absolute continuity is supplied by
    `state_ac_average_of_weight_pos`. -/
theorem mutualInformation_contracts_under_stochastic
    (E : ClassicalEnsemble α X) (T : StochasticMatrix X Y) :
    mutualInformation (mapStates E T) ≤ mutualInformation E := by
  unfold mutualInformation
  apply Finset.sum_le_sum
  intro a _
  -- Weights are equal by definition of `mapStates`.
  -- Goal:
  --   E.weight.p a * KL((mapStates E T).state a, ensembleAverage (mapStates E T))
  --     ≤ E.weight.p a * KL(E.state a, ensembleAverage E)
  by_cases hwa : E.weight.p a = 0
  · rw [show (mapStates E T).weight.p a = E.weight.p a from rfl, hwa, zero_mul, zero_mul]
  · have h_pos : 0 < E.weight.p a :=
      lt_of_le_of_ne (E.weight.nonneg a) (Ne.symm hwa)
    have h_ac := state_ac_average_of_weight_pos E h_pos
    -- Rewrite the average inside the LHS KL via congr.
    have h_avg_eq :
        klDivergence ((mapStates E T).state a) (ensembleAverage (mapStates E T))
          = klDivergence (T.push (E.state a)) (T.push (ensembleAverage E)) := by
      apply klDivergence_congr
      · intro y; rfl
      · intro y; exact ensembleAverage_mapStates_apply E T y
    rw [show (mapStates E T).weight.p a = E.weight.p a from rfl, h_avg_eq]
    apply mul_le_mul_of_nonneg_left _ (E.weight.nonneg a)
    -- Classical DPI on the rewritten KL.
    exact klDivergence_contracts_under_stochastic_of_logsum
      T (E.state a) (ensembleAverage E) h_ac logSumInequality_holds

end UnifiedTheory.LayerB.Ensemble
