/-
  Audit/KFCausalSetGeometricOrientationAsymptotics.lean

  LARGE-RANK GEOMETRIC ORIENTATION

  The finite-rank strict-interior theorem left an apparent loophole: perhaps
  extreme events approach the pure values `±1/2` as rank grows.  They do not.
  The normalization in the geometric channel is by the total number of causal
  incidences, not by a local past-plus-future count.

  This file proves:

  * an `n`-chain has
        y_i = (2 i + 1 - n) / (n (n+1)),
    so its largest magnitude tends to zero;
  * an antichain has `y_i = 0` exactly;
  * every event of every finite causet satisfies the stronger universal bound
        |y_i| < 1/4;
  * one-top and one-bottom causets approach `±1/4`, so the universal constant is
    optimal even though it is never attained at finite rank.

  Consequently no sampling probability law on finite causal-set growth can
  concentrate this geometric channel near a pure orientation endpoint.  This
  includes any separately normalized distribution extracted from critical
  harmonic cylinders; the cylinder quantum measure itself is nonadditive and
  does not canonically define such a distribution.  The gap from `±1/2` is
  uniformly at least `1/4`.
-/

import UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics

noncomputable section

open scoped BigOperators
open Filter Topology
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFOrientationHistoryRigidity

/-! ## 1. Exact chain and antichain profiles -/

/-- The total order on `Fin n`. -/
def cardinalCausalChain (n : ℕ) : CardinalCausalOrder n where
  rel := fun i j => decide (i ≤ j)
  refl := by simp
  antisymm := by
    intro i j hij hji
    exact le_antisymm (of_decide_eq_true hij) (of_decide_eq_true hji)
  trans := by
    intro i j k hij hjk
    exact decide_eq_true
      (le_trans (of_decide_eq_true hij) (of_decide_eq_true hjk))

theorem causalPastVolumeQ_chain {n : ℕ} (i : Fin n) :
    causalPastVolumeQ (cardinalCausalChain n) i = (i.val + 1 : ℕ) := by
  simp [causalPastVolumeQ, cardinalCausalChain, Finset.sum_boole,
    Finset.filter_ge_eq_Iic, Fin.card_Iic]

theorem causalFutureVolumeQ_chain {n : ℕ} (i : Fin n) :
    causalFutureVolumeQ (cardinalCausalChain n) i = (n - i.val : ℕ) := by
  simp [causalFutureVolumeQ, cardinalCausalChain, Finset.sum_boole,
    Finset.filter_le_eq_Ici, Fin.card_Ici]

theorem totalCausalPastVolumeQ_chain (n : ℕ) :
    totalCausalPastVolumeQ (cardinalCausalChain n) =
      (n : ℚ) * (n + 1) / 2 := by
  unfold totalCausalPastVolumeQ
  simp_rw [causalPastVolumeQ_chain]
  rw [Finset.sum_fin_eq_sum_range]
  have hsum :
      (∑ i ∈ Finset.range n,
        if h : i < n then (((i + 1 : ℕ) : ℚ)) else 0) =
        ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℚ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.1 hi]
  rw [hsum]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  by_cases hn : n = 0
  · subst n
    norm_num
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  have h := congrArg (fun x : ℕ => (x : ℚ))
    (Finset.sum_range_id_mul_two n)
  push_cast [Nat.cast_sub hnpos] at h
  nlinarith

/-- Exact all-event chain profile.  The cast of `i.val` is written explicitly
to keep the asymptotic scale visible. -/
theorem causalOrientationDensityQ_chain {n : ℕ} (i : Fin n) :
    causalOrientationDensityQ (cardinalCausalChain n) i =
      ((2 : ℚ) * i.val + 1 - n) / ((n : ℚ) * (n + 1)) := by
  unfold causalOrientationDensityQ
  unfold normalizedCausalPastVolumeDensityQ
  unfold normalizedCausalFutureVolumeDensityQ
  rw [causalPastVolumeQ_chain, causalFutureVolumeQ_chain,
    totalCausalPastVolumeQ_chain]
  have hi : i.val ≤ n := Nat.le_of_lt i.isLt
  push_cast [Nat.cast_sub hi]
  field_simp
  ring

theorem causalOrientationDensityQ_chain_first (n : ℕ) :
    causalOrientationDensityQ
        (cardinalCausalChain (n + 1)) (0 : Fin (n + 1)) =
      -(n : ℚ) / ((n + 1) * (n + 2)) := by
  rw [causalOrientationDensityQ_chain]
  norm_num
  field_simp
  ring

theorem causalOrientationDensityQ_chain_last (n : ℕ) :
    causalOrientationDensityQ
        (cardinalCausalChain (n + 1)) (Fin.last n) =
      (n : ℚ) / ((n + 1) * (n + 2)) := by
  rw [causalOrientationDensityQ_chain]
  simp
  field_simp
  ring

/-- Even the extremal chain event dilutes to the mixed center rather than
approaching a pure orientation endpoint. -/
theorem causalOrientationDensity_chain_last_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        ((causalOrientationDensityQ
          (cardinalCausalChain (n + 1)) (Fin.last n) : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have hTailOne := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hTailTwo :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    apply (hTailOne.comp hShift).congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring
  have hOneMinus :
      Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hTailOne)
  have hProduct := hOneMinus.mul hTailTwo
  have hProduct' : Tendsto
      (fun n : ℕ =>
        (1 - 1 / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 2)))
      atTop (𝓝 0) := by
    simpa using hProduct
  apply hProduct'.congr'
  filter_upwards [] with n
  rw [causalOrientationDensityQ_chain_last]
  push_cast
  field_simp
  ring

theorem causalPastVolumeQ_antichain {n : ℕ} (i : Fin n) :
    causalPastVolumeQ (cardinalCausalAntichain n) i = 1 := by
  simp [causalPastVolumeQ, cardinalCausalAntichain]

theorem causalFutureVolumeQ_antichain {n : ℕ} (i : Fin n) :
    causalFutureVolumeQ (cardinalCausalAntichain n) i = 1 := by
  simp [causalFutureVolumeQ, cardinalCausalAntichain]

theorem causalOrientationDensityQ_antichain {n : ℕ} (i : Fin n) :
    causalOrientationDensityQ (cardinalCausalAntichain n) i = 0 := by
  unfold causalOrientationDensityQ
  unfold normalizedCausalPastVolumeDensityQ
  unfold normalizedCausalFutureVolumeDensityQ
  rw [causalPastVolumeQ_antichain, causalFutureVolumeQ_antichain]
  ring

/-! ## 2. A universal quarter-gap theorem -/

theorem causalPastVolumeQ_one_le {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    1 ≤ causalPastVolumeQ parent i := by
  unfold causalPastVolumeQ
  have hNonnegative : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (if parent.rel j i = true then (1 : ℚ) else 0) := by
    intro j _hj
    split <;> norm_num
  have hTermLe := Finset.single_le_sum hNonnegative (Finset.mem_univ i)
  simpa only [parent.refl i, if_true] using hTermLe

theorem causalFutureVolumeQ_one_le {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    1 ≤ causalFutureVolumeQ parent i := by
  rw [causalFutureVolumeQ_eq_dualPast]
  exact causalPastVolumeQ_one_le (cardinalCausalOrderDual parent) i

theorem causalPastVolumeQ_le_rank {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalPastVolumeQ parent i ≤ n := by
  unfold causalPastVolumeQ
  calc
    (∑ j : Fin n, if parent.rel j i = true then (1 : ℚ) else 0) ≤
        ∑ _j : Fin n, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro j _hj
      split <;> norm_num
    _ = n := by simp

theorem causalFutureVolumeQ_le_rank {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalFutureVolumeQ parent i ≤ n := by
  rw [causalFutureVolumeQ_eq_dualPast]
  exact causalPastVolumeQ_le_rank (cardinalCausalOrderDual parent) i

/-- The total incidence count contains the selected past count plus at least
one reflexive incidence from every other event. -/
theorem rank_add_past_sub_one_le_total {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    (n : ℚ) + causalPastVolumeQ parent i - 1 ≤
      totalCausalPastVolumeQ parent := by
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn : 1 ≤ n := hn0
  have hOthers : (((n - 1 : ℕ) : ℚ)) ≤
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        causalPastVolumeQ parent j := by
    calc
      (((n - 1 : ℕ) : ℚ)) =
          ∑ _j ∈ (Finset.univ : Finset (Fin n)).erase i, (1 : ℚ) := by
        simp [Finset.card_erase_of_mem, hn]
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          causalPastVolumeQ parent j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact causalPastVolumeQ_one_le parent j
  unfold totalCausalPastVolumeQ
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  push_cast [Nat.cast_sub hn] at hOthers
  linarith

/-- The dual future version of the same incidence lower bound. -/
theorem rank_add_future_sub_one_le_total {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    (n : ℚ) + causalFutureVolumeQ parent i - 1 ≤
      totalCausalPastVolumeQ parent := by
  have hDual := rank_add_past_sub_one_le_total
    (cardinalCausalOrderDual parent) i
  rw [causalPastVolumeQ_dual, totalCausalPastVolumeQ_dual] at hDual
  exact hDual

/-- Uniform large-rank separation from the pure endpoints.  The earlier
`1/2` bound can be improved by a factor of two for every finite causet. -/
theorem causalOrientationDensityQ_abs_lt_quarter {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    |causalOrientationDensityQ parent i| < (1 : ℚ) / 4 := by
  let past := causalPastVolumeQ parent i
  let future := causalFutureVolumeQ parent i
  let total := totalCausalPastVolumeQ parent
  have hPastOne : 1 ≤ past := causalPastVolumeQ_one_le parent i
  have hFutureOne : 1 ≤ future := causalFutureVolumeQ_one_le parent i
  have hPastRank : past ≤ n := causalPastVolumeQ_le_rank parent i
  have hFutureRank : future ≤ n := causalFutureVolumeQ_le_rank parent i
  have hTotalPast : (n : ℚ) + past - 1 ≤ total :=
    rank_add_past_sub_one_le_total parent i
  have hTotalFuture : (n : ℚ) + future - 1 ≤ total :=
    rank_add_future_sub_one_le_total parent i
  have hTotalPos : 0 < total := totalCausalPastVolumeQ_pos parent i
  have hUpperNumerator : past - future < total / 2 := by
    have hnPast : past ≤ (n : ℚ) := hPastRank
    linarith
  have hLowerNumerator : -(total / 2) < past - future := by
    have hnFuture : future ≤ (n : ℚ) := hFutureRank
    linarith
  have hUpperRatio : (past - future) / total < (1 : ℚ) / 2 := by
    exact (div_lt_iff₀ hTotalPos).2 (by linarith)
  have hLowerRatio : -(1 : ℚ) / 2 < (past - future) / total := by
    exact (lt_div_iff₀ hTotalPos).2 (by linarith)
  rw [abs_lt]
  unfold causalOrientationDensityQ
  unfold normalizedCausalPastVolumeDensityQ
  unfold normalizedCausalFutureVolumeDensityQ
  dsimp [past, future, total] at hUpperRatio hLowerRatio
  rw [← sub_div]
  constructor <;> linarith

theorem causalOrientationDensityR_abs_lt_quarter {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    |((causalOrientationDensityQ parent i : ℚ) : ℝ)| < 1 / 4 := by
  have hQ := causalOrientationDensityQ_abs_lt_quarter parent i
  have hCast : (((|causalOrientationDensityQ parent i| : ℚ) : ℝ)) <
      (((1 : ℚ) / 4 : ℚ) : ℝ) := by
    exact_mod_cast hQ
  simpa using hCast

/-! ## 3. The quarter bound is asymptotically optimal -/

/-- A causet with `n` mutually unrelated lower events and one top event. -/
def cardinalCausalOneTop (n : ℕ) : CardinalCausalOrder (n + 1) where
  rel := fun i j => decide (i = j ∨ j = Fin.last n)
  refl := by simp
  antisymm := by
    intro i j hij hji
    simp only [decide_eq_true_eq] at hij hji
    rcases hij with hij | hjTop
    · exact hij
    rcases hji with hji | hiTop
    · exact hji.symm
    · exact hiTop.trans hjTop.symm
  trans := by
    intro i j k hij hjk
    simp only [decide_eq_true_eq] at hij hjk ⊢
    rcases hjk with hjk | hkTop
    · rcases hij with hij | hjTop
      · exact Or.inl (hij.trans hjk)
      · exact Or.inr (hjk ▸ hjTop)
    · exact Or.inr hkTop

theorem oneTop_causalPastVolumeQ_top (n : ℕ) :
    causalPastVolumeQ (cardinalCausalOneTop n) (Fin.last n) = n + 1 := by
  simp [causalPastVolumeQ, cardinalCausalOneTop]

theorem oneTop_causalFutureVolumeQ_top (n : ℕ) :
    causalFutureVolumeQ (cardinalCausalOneTop n) (Fin.last n) = 1 := by
  unfold causalFutureVolumeQ
  simp only [cardinalCausalOneTop, decide_eq_true_eq]
  have hCondition : ∀ j : Fin (n + 1),
      (Fin.last n = j ∨ j = Fin.last n) ↔ j = Fin.last n := by
    intro j
    constructor
    · rintro (h | h)
      · exact h.symm
      · exact h
    · exact Or.inr
  simp_rw [hCondition]
  simp

theorem oneTop_causalPastVolumeQ (n : ℕ) (i : Fin (n + 1)) :
    causalPastVolumeQ (cardinalCausalOneTop n) i =
      if i = Fin.last n then n + 1 else 1 := by
  by_cases hi : i = Fin.last n
  · subst i
    simp [oneTop_causalPastVolumeQ_top]
  · simp [causalPastVolumeQ, cardinalCausalOneTop, hi]

theorem oneTop_totalCausalPastVolumeQ (n : ℕ) :
    totalCausalPastVolumeQ (cardinalCausalOneTop n) = 2 * n + 1 := by
  unfold totalCausalPastVolumeQ
  simp_rw [oneTop_causalPastVolumeQ]
  push_cast
  rw [show (fun i : Fin (n + 1) =>
      if i = Fin.last n then (n : ℚ) + 1 else 1) =
      (fun i : Fin (n + 1) =>
        1 + if i = Fin.last n then (n : ℚ) else 0) by
    funext i
    split <;> ring]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']
  ring

/-- The top event approaches the optimal universal magnitude `1/4`. -/
theorem oneTop_causalOrientationDensityQ_top (n : ℕ) :
    causalOrientationDensityQ (cardinalCausalOneTop n) (Fin.last n) =
      (n : ℚ) / (2 * (2 * n + 1)) := by
  unfold causalOrientationDensityQ
  unfold normalizedCausalPastVolumeDensityQ
  unfold normalizedCausalFutureVolumeDensityQ
  rw [oneTop_causalPastVolumeQ_top,
    oneTop_causalFutureVolumeQ_top,
    oneTop_totalCausalPastVolumeQ]
  field_simp
  ring

/-- The optimal witnesses converge to `1/4`, proving that no smaller universal
constant can replace the quarter bound. -/
theorem oneTop_causalOrientationDensity_tendsto_quarter :
    Tendsto
      (fun n : ℕ =>
        ((causalOrientationDensityQ
          (cardinalCausalOneTop n) (Fin.last n) : ℚ) : ℝ))
      atTop (𝓝 (1 / 4)) := by
  have hCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hTwice : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hCast
  have hDenominator :
      Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hTwice
  have hInverse :
      Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    hDenominator.inv_tendsto_atTop
  have hCorrection :
      Tendsto (fun n : ℕ => (1 / 4 : ℝ) *
        (2 * (n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hInverse)
  have hLimit := (tendsto_const_nhds (x := (1 / 4 : ℝ))).sub hCorrection
  have hLimit' : Tendsto
      (fun n : ℕ => (1 / 4 : ℝ) -
        (1 / 4 : ℝ) * (2 * (n : ℝ) + 1)⁻¹)
      atTop (𝓝 (1 / 4)) := by
    simpa using hLimit
  apply hLimit'.congr'
  filter_upwards [] with n
  rw [oneTop_causalOrientationDensityQ_top]
  push_cast
  field_simp
  ring

/-- The universal quarter bound is equivalently a uniform positive gap from
both pure orientation endpoints. -/
theorem geometricOrientation_uniform_gap_from_pure_endpoints {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    (1 : ℚ) / 4 < |(1 : ℚ) / 2 - causalOrientationDensityQ parent i|
      ∧ (1 : ℚ) / 4 <
        |-(1 : ℚ) / 2 - causalOrientationDensityQ parent i| := by
  have hQuarter := causalOrientationDensityQ_abs_lt_quarter parent i
  rw [abs_lt] at hQuarter
  constructor
  · rw [abs_of_pos]
    · linarith
    · linarith
  · rw [abs_of_neg]
    · linarith
    · linarith

/-- Any finite-rank probability weighting inherits the same pointwise quarter
gap.  This predicate-level form applies without choosing a particular growth
measure or resolving cylinder events. -/
theorem every_weighted_orientation_sample_has_quarter_gap
    {Sample : Type*} {n : ℕ}
    (parent : Sample → CardinalCausalOrder n)
    (event : Sample → Fin n) :
    ∀ sample,
      |((causalOrientationDensityQ (parent sample) (event sample) : ℚ) : ℝ)| <
        1 / 4 := by
  intro sample
  exact causalOrientationDensityR_abs_lt_quarter
    (parent sample) (event sample)

/-- Any separately normalized nonnegative finite sampling distribution has
mean absolute geometric orientation at most `1/4`.  The critical cylinder
functional is a nonadditive quantum measure, so obtaining such a probability
distribution from it requires an additional sampling/conditioning rule; no
choice of that rule can evade the pointwise bound. -/
theorem weighted_mean_abs_orientation_le_quarter
    {Sample : Type*} [Fintype Sample]
    (weight : Sample → ℝ)
    (hWeightNonnegative : ∀ sample, 0 ≤ weight sample)
    (hWeightNormalized : ∑ sample, weight sample = 1)
    {n : ℕ} (parent : Sample → CardinalCausalOrder n)
    (event : Sample → Fin n) :
    ∑ sample, weight sample *
        |((causalOrientationDensityQ
          (parent sample) (event sample) : ℚ) : ℝ)| ≤ 1 / 4 := by
  calc
    ∑ sample, weight sample *
        |((causalOrientationDensityQ
          (parent sample) (event sample) : ℚ) : ℝ)| ≤
        ∑ sample, weight sample * (1 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro sample _hsample
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (causalOrientationDensityR_abs_lt_quarter
          (parent sample) (event sample)))
        (hWeightNonnegative sample)
    _ = (∑ sample, weight sample) * (1 / 4 : ℝ) := by
      rw [Finset.sum_mul]
    _ = 1 / 4 := by rw [hWeightNormalized, one_mul]

/-- Capstone: chains dilute to the center, antichains are exactly centered,
and every finite growth law remains uniformly separated from pure chirality. -/
theorem geometric_orientation_large_rank_frontier :
    (∀ {n : ℕ} (i : Fin n),
      causalOrientationDensityQ (cardinalCausalChain n) i =
        ((2 : ℚ) * i.val + 1 - n) / ((n : ℚ) * (n + 1)))
      ∧ (∀ {n : ℕ} (i : Fin n),
        causalOrientationDensityQ (cardinalCausalAntichain n) i = 0)
      ∧ (∀ {n : ℕ} (parent : CardinalCausalOrder n) (i : Fin n),
        |causalOrientationDensityQ parent i| < (1 : ℚ) / 4)
      ∧ (∀ n : ℕ,
        causalOrientationDensityQ
            (cardinalCausalOneTop n) (Fin.last n) =
          (n : ℚ) / (2 * (2 * n + 1))) := by
  exact ⟨causalOrientationDensityQ_chain,
    causalOrientationDensityQ_antichain,
    causalOrientationDensityQ_abs_lt_quarter,
    oneTop_causalOrientationDensityQ_top⟩

#print axioms causalOrientationDensityQ_chain
#print axioms causalOrientationDensity_chain_last_tendsto_zero
#print axioms causalOrientationDensityQ_antichain
#print axioms causalOrientationDensityQ_abs_lt_quarter
#print axioms oneTop_causalOrientationDensityQ_top
#print axioms oneTop_causalOrientationDensity_tendsto_quarter
#print axioms geometricOrientation_uniform_gap_from_pure_endpoints
#print axioms every_weighted_orientation_sample_has_quarter_gap
#print axioms weighted_mean_abs_orientation_le_quarter
#print axioms geometric_orientation_large_rank_frontier

end

end UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
