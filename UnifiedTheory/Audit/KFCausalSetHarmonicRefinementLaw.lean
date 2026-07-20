/-
  Audit/KFCausalSetHarmonicRefinementLaw.lean

  THE HARMONIC CRITICAL TRAJECTORY AS A LOCAL REFINEMENT LAW

  The multiplicity-corrected schedule was previously given in closed form.
  This module replaces that presentation by a rank-local microscopic recursion.
  Its rescaled critical charge

      Q_n = 2(n-1)(lambda_n - 1)

  receives one uniform-spectator increment at each birth:

      Q_(n+1) = Q_n + 1/(n+1).

  Without a boundary condition the recursion leaves exactly one parameter:

      Q_n = H_n + Q_2 - H_2.

  Starting from Q_2 = H_2 = 3/2, it uniquely forces Q_n = H_n and hence

      lambda_n = 1 + H_n/(2(n-1)).

  A second theorem identifies the universality class.  If a positive pair
  coupling has first-order offset

      2n(lambda_(n+1)-1) - log(n+1) -> delta

  and its logarithmic nonlinear remainder vanishes at the required scale,
  then the coherent unlabeled one-missing/timid Born ratio tends to
  exp(-2 delta).  For every nonnegative seed the remainder condition follows,
  and the ratio tends to exp(-2(gamma + Q_2 - H_2)).  Thus matching the
  harmonic infrared constant selects Q_2 = H_2 exactly.  Euler's constant is
  the accumulated finite part of the uniform-spectator source, not an inserted
  coupling.  What remains open is deriving the additive source law and its
  rank-two boundary datum from a causal action.
-/

import UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetHarmonicRefinementLaw

noncomputable section

open Filter Topology
open UnifiedTheory.Audit.KFCausalSetCriticalMultiplicity
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning

/-! ## 1. A rank-local uniform-spectator source -/

/-- The source contributed by one uniformly selected slot after a birth to
rank `n`. -/
def uniformSpectatorSourceQ (n : ℕ) : ℚ := 1 / (n : ℚ)

/-- Covariance makes all spectator slots equivalent; normalization fixes their
total weight. -/
def IsExchangeableNormalizedSpectatorSource {n : ℕ}
    (source : Fin n → ℚ) : Prop :=
  (∀ i j, source i = source j) ∧ ∑ i, source i = 1

/-- Uniform spectator weight is not an extra continuous parameter: on every
nonempty rank it is forced by exchangeability and unit normalization. -/
theorem exchangeable_normalized_spectator_source_unique
    {n : ℕ} (hn : 0 < n) (source : Fin n → ℚ)
    (hSource : IsExchangeableNormalizedSpectatorSource source) (i : Fin n) :
    source i = uniformSpectatorSourceQ n := by
  have hSum : (n : ℚ) * source i = 1 := by
    calc
      (n : ℚ) * source i = ∑ _j : Fin n, source i := by simp
      _ = ∑ j : Fin n, source j := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact (hSource.1 j i).symm
      _ = 1 := hSource.2
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [uniformSpectatorSourceQ, eq_div_iff hnQ]
  simpa [mul_comm] using hSum

/-- Total source accumulated from the first `n` unlabeled births. -/
def accumulatedUniformSpectatorSourceQ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, uniformSpectatorSourceQ (k + 1)

theorem accumulatedUniformSpectatorSourceQ_eq_harmonic (n : ℕ) :
    accumulatedUniformSpectatorSourceQ n = harmonic n := by
  unfold accumulatedUniformSpectatorSourceQ harmonic uniformSpectatorSourceQ
  apply Finset.sum_congr rfl
  intro k _hk
  simp [div_eq_mul_inv]

/-- Rescaled excess pair coupling.  This is the variable on which refinement
acts additively. -/
def harmonicCriticalChargeQ (n : ℕ) : ℚ :=
  2 * (n - 1 : ℕ) * (harmonicCriticalPairCouplingQ n - 1)

/-- Above the two-event base rank, the rescaled charge is exactly the rational
harmonic number. -/
theorem harmonicCriticalChargeQ_eq_harmonic {n : ℕ} (hn : 2 ≤ n) :
    harmonicCriticalChargeQ n = harmonic n := by
  have hbranch : ¬ n ≤ 1 := by omega
  simp only [harmonicCriticalChargeQ, harmonicCriticalPairCouplingQ,
    hbranch, if_false, add_sub_cancel_left]
  have hne : (n : ℚ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 1 by omega))
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  field_simp
  ring

/-- Exact discrete beta law: one refinement step adds the uniform spectator
source `1/(n+1)` to the critical charge. -/
theorem harmonicCriticalChargeQ_succ {n : ℕ} (hn : 2 ≤ n) :
    harmonicCriticalChargeQ (n + 1) =
      harmonicCriticalChargeQ n + uniformSpectatorSourceQ (n + 1) := by
  rw [harmonicCriticalChargeQ_eq_harmonic (by omega),
    harmonicCriticalChargeQ_eq_harmonic hn, harmonic_succ]
  simp [uniformSpectatorSourceQ, div_eq_mul_inv]

/-- The same local law written directly as an affine discrete beta function
for the physical pair coupling. -/
theorem harmonicCriticalPairCouplingQ_affine_beta {n : ℕ} (hn : 2 ≤ n) :
    harmonicCriticalPairCouplingQ (n + 1) - 1 =
      ((n - 1 : ℕ) : ℚ) / (n : ℚ) *
          (harmonicCriticalPairCouplingQ n - 1) +
        1 / (2 * (n : ℚ) * (n + 1 : ℕ)) := by
  have hbranchN : ¬ n ≤ 1 := by omega
  have hbranchSucc : ¬ n + 1 ≤ 1 := by omega
  simp only [harmonicCriticalPairCouplingQ, hbranchN, hbranchSucc,
    if_false, add_sub_cancel_left]
  rw [harmonic_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnOneQ : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hnSubQ : (n : ℚ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 1 by omega))
  field_simp [hnQ, hnOneQ, hnSubQ]
  ring

/-- A charge trajectory obeys the microscopic uniform-spectator refinement
law when it has the two-event seed and the local source recursion. -/
def IsUniformSpectatorRefinementLaw (charge : ℕ → ℚ) : Prop :=
  charge 2 = accumulatedUniformSpectatorSourceQ 2 ∧
    ∀ n : ℕ, 2 ≤ n →
      charge (n + 1) = charge n + uniformSpectatorSourceQ (n + 1)

theorem harmonicCriticalChargeQ_isUniformSpectatorRefinementLaw :
    IsUniformSpectatorRefinementLaw harmonicCriticalChargeQ := by
  constructor
  · rw [accumulatedUniformSpectatorSourceQ_eq_harmonic]
    exact harmonicCriticalChargeQ_eq_harmonic (by norm_num)
  · intro n hn
    exact harmonicCriticalChargeQ_succ hn

/-- The local source and the rank-two seed uniquely determine the entire
large-rank charge trajectory. -/
theorem uniformSpectatorRefinementLaw_unique
    {charge : ℕ → ℚ} (hLaw : IsUniformSpectatorRefinementLaw charge)
    {n : ℕ} (hn : 2 ≤ n) :
    charge n = harmonic n := by
  induction n, hn using Nat.le_induction with
  | base => simpa [accumulatedUniformSpectatorSourceQ_eq_harmonic] using hLaw.1
  | succ n hn ih =>
      rw [hLaw.2 n hn, ih, harmonic_succ]
      simp [uniformSpectatorSourceQ, div_eq_mul_inv]

/-- The local update without a boundary condition leaves exactly one rational
parameter: the rank-two charge. -/
def seededUniformSpectatorChargeQ (seed : ℚ) (n : ℕ) : ℚ :=
  seed + harmonic n - harmonic 2

theorem seededUniformSpectatorChargeQ_two (seed : ℚ) :
    seededUniformSpectatorChargeQ seed 2 = seed := by
  simp [seededUniformSpectatorChargeQ]

theorem seededUniformSpectatorChargeQ_succ (seed : ℚ) (n : ℕ) :
    seededUniformSpectatorChargeQ seed (n + 1) =
      seededUniformSpectatorChargeQ seed n +
        uniformSpectatorSourceQ (n + 1) := by
  rw [seededUniformSpectatorChargeQ, seededUniformSpectatorChargeQ,
    harmonic_succ]
  simp [uniformSpectatorSourceQ, div_eq_mul_inv]
  ring

theorem seededUniformSpectatorChargeQ_nonneg {seed : ℚ} (hSeed : 0 ≤ seed)
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ seededUniformSpectatorChargeQ seed n := by
  induction n, hn using Nat.le_induction with
  | base => simpa [seededUniformSpectatorChargeQ_two] using hSeed
  | succ n hn ih =>
      rw [seededUniformSpectatorChargeQ_succ]
      apply add_nonneg ih
      unfold uniformSpectatorSourceQ
      positivity

/-- Classification theorem: exchangeable normalized additive refinement fixes
all ranks relative to `Q_2`, but does not by itself select `Q_2`. -/
theorem uniformSpectatorRefinementStep_seed_classification
    {charge : ℕ → ℚ}
    (hStep : ∀ n : ℕ, 2 ≤ n →
      charge (n + 1) = charge n + uniformSpectatorSourceQ (n + 1))
    {n : ℕ} (hn : 2 ≤ n) :
    charge n = seededUniformSpectatorChargeQ (charge 2) n := by
  induction n, hn using Nat.le_induction with
  | base => rw [seededUniformSpectatorChargeQ_two]
  | succ n hn ih =>
      rw [hStep n hn, ih, seededUniformSpectatorChargeQ_succ]

/-- The harmonic member is selected exactly by the canonical rank-two seed.
This isolates the boundary datum from the local refinement mechanism. -/
theorem seededUniformSpectatorChargeQ_eq_harmonic_iff (seed : ℚ) :
    seededUniformSpectatorChargeQ seed = harmonic ↔ seed = harmonic 2 := by
  constructor
  · intro h
    have hTwo := congrFun h 2
    simpa [seededUniformSpectatorChargeQ] using hTwo
  · intro hSeed
    funext n
    rw [hSeed]
    simp [seededUniformSpectatorChargeQ]

/-- Reconstruct a pair coupling from an additive critical charge, retaining
the same harmless base-rank convention as the complete growth law. -/
def pairCouplingFromChargeQ (charge : ℕ → ℚ) (n : ℕ) : ℚ :=
  if n ≤ 1 then 2 else 1 + charge n / (2 * (n - 1))

/-- The uniform-spectator recursion does not merely admit the harmonic
trajectory: it selects it uniquely. -/
theorem uniformSpectatorRefinementLaw_selects_harmonic
    {charge : ℕ → ℚ} (hLaw : IsUniformSpectatorRefinementLaw charge) :
    pairCouplingFromChargeQ charge = harmonicCriticalPairCouplingQ := by
  funext n
  by_cases hn : n ≤ 1
  · simp [pairCouplingFromChargeQ, harmonicCriticalPairCouplingQ, hn]
  · have hn2 : 2 ≤ n := by omega
    rw [pairCouplingFromChargeQ, harmonicCriticalPairCouplingQ,
      if_neg hn, if_neg hn]
    rw [uniformSpectatorRefinementLaw_unique hLaw hn2]

/-! ## 2. The discrete-continuum spectator anomaly -/

/-- Pair coupling reconstructed from an arbitrary rank-two boundary charge. -/
def seededUniformSpectatorPairCouplingQ (seed : ℚ) (n : ℕ) : ℚ :=
  pairCouplingFromChargeQ (seededUniformSpectatorChargeQ seed) n

def seededUniformSpectatorPairCoupling (seed : ℚ) (n : ℕ) : ℝ :=
  (seededUniformSpectatorPairCouplingQ seed n : ℝ)

theorem seededUniformSpectatorPairCoupling_one_le {seed : ℚ}
    (hSeed : 0 ≤ seed) (n : ℕ) :
    1 ≤ seededUniformSpectatorPairCoupling seed n := by
  rw [seededUniformSpectatorPairCoupling,
    seededUniformSpectatorPairCouplingQ, pairCouplingFromChargeQ]
  by_cases hn : n ≤ 1
  · simp [hn]
  · rw [if_neg hn]
    have hn2 : 2 ≤ n := by omega
    have hCharge := seededUniformSpectatorChargeQ_nonneg hSeed hn2
    simp only [Rat.cast_add, Rat.cast_one, Rat.cast_div]
    push_cast
    have hChargeR :
        0 ≤ (seededUniformSpectatorChargeQ seed n : ℝ) := by
      exact_mod_cast hCharge
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hDenR : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hnR)
    exact le_add_of_nonneg_right (div_nonneg hChargeR hDenR)

/-- Difference between accumulated discrete spectator weight and its continuum
logarithmic entropy. -/
def uniformSpectatorEntropyAnomaly (n : ℕ) : ℝ :=
  (accumulatedUniformSpectatorSourceQ n : ℝ) - Real.log n

/-- The anomaly for the same local law with an arbitrary rank-two boundary
charge. -/
def seededUniformSpectatorEntropyAnomaly (seed : ℚ) (n : ℕ) : ℝ :=
  (seededUniformSpectatorChargeQ seed n : ℝ) - Real.log n

/-- Euler's constant is exactly the infrared finite part of the normalized
spectator source after subtracting continuum logarithmic entropy. -/
theorem uniformSpectatorEntropyAnomaly_tendsto : Tendsto
    uniformSpectatorEntropyAnomaly atTop
    (nhds Real.eulerMascheroniConstant) := by
  apply Real.tendsto_harmonic_sub_log.congr'
  filter_upwards [] with n
  rw [uniformSpectatorEntropyAnomaly,
    accumulatedUniformSpectatorSourceQ_eq_harmonic]

/-- The unselected rank-two datum survives in the infrared as an additive
shift of Euler's constant. -/
theorem seededUniformSpectatorEntropyAnomaly_tendsto (seed : ℚ) : Tendsto
    (seededUniformSpectatorEntropyAnomaly seed) atTop
    (nhds (Real.eulerMascheroniConstant +
      ((seed - harmonic 2 : ℚ) : ℝ))) := by
  have h := uniformSpectatorEntropyAnomaly_tendsto.add_const
    ((seed - harmonic 2 : ℚ) : ℝ)
  apply h.congr'
  filter_upwards [] with n
  rw [seededUniformSpectatorEntropyAnomaly,
    uniformSpectatorEntropyAnomaly,
    accumulatedUniformSpectatorSourceQ_eq_harmonic,
    seededUniformSpectatorChargeQ]
  push_cast
  ring

theorem shifted_harmonic_div_tendsto_zero : Tendsto
    (fun n : ℕ => (harmonic (n + 1) : ℝ) / (n : ℝ))
    atTop (nhds 0) := by
  have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_add_right n 1) tendsto_id
  have hHarmonic := harmonic_div_tendsto_zero.comp hShift
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hFactor : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    have hBase := (tendsto_const_nhds (x := (1 : ℝ))).add hInv
    have hEq :
        (fun n : ℕ => 1 + (1 : ℝ) / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      push_cast
      field_simp
    simpa using hBase.congr' hEq
  have hEq :
      (fun n : ℕ =>
        ((harmonic (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
          (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => (harmonic (n + 1) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    push_cast
    field_simp
  simpa [Function.comp_def] using (hHarmonic.mul hFactor).congr' hEq

/-- Adding a finite rank-two boundary charge does not spoil the logarithmic
critical window: its squared excess remains sublinear. -/
theorem seededUniformSpectatorCharge_sq_div_tendsto_zero (seed : ℚ) : Tendsto
    (fun n : ℕ =>
      (seededUniformSpectatorChargeQ seed (n + 1) : ℝ) ^ 2 / (n : ℝ))
    atTop (nhds 0) := by
  let c : ℝ := ((seed - harmonic 2 : ℚ) : ℝ)
  have hSq := shifted_harmonic_sq_div_tendsto_zero
  have hCross := shifted_harmonic_div_tendsto_zero.const_mul (2 * c)
  have hConst : Tendsto (fun n : ℕ => c ^ 2 / (n : ℝ))
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat (c ^ 2)
  have hSum := (hSq.add hCross).add hConst
  have hSum' : Tendsto
      (fun n : ℕ =>
        (harmonic (n + 1) : ℝ) ^ 2 / (n : ℝ) +
          2 * c * ((harmonic (n + 1) : ℝ) / (n : ℝ)) +
          c ^ 2 / (n : ℝ)) atTop (nhds 0) := by
    simpa using hSum
  apply hSum'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  dsimp [c]
  rw [seededUniformSpectatorChargeQ]
  push_cast
  field_simp
  ring

/-- At every positive rank, the finite first-order pair-coupling offset is
exactly the seeded spectator anomaly. -/
theorem seededUniformSpectatorPairCoupling_firstOrder_eq_anomaly
    (seed : ℚ) {n : ℕ} (hn : 0 < n) :
    2 * (n : ℝ) *
          (seededUniformSpectatorPairCoupling seed (n + 1) - 1) -
        Real.log (n + 1) =
      seededUniformSpectatorEntropyAnomaly seed (n + 1) := by
  have hbranch : ¬ n + 1 ≤ 1 := by omega
  rw [seededUniformSpectatorEntropyAnomaly,
    seededUniformSpectatorPairCoupling,
    seededUniformSpectatorPairCouplingQ,
    pairCouplingFromChargeQ, if_neg hbranch]
  simp only [Rat.cast_add, Rat.cast_one, Rat.cast_div]
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnR]
  ring

/-- Every nonnegative boundary seed automatically satisfies the nonlinear
small-error condition needed for coherent infrared universality. -/
theorem seededUniformSpectator_scaledLogError_tendsto_zero
    {seed : ℚ} (hSeed : 0 ≤ seed) : Tendsto
    (fun n : ℕ => 4 * (n : ℝ) *
      (Real.log (seededUniformSpectatorPairCoupling seed (n + 1)) -
        (seededUniformSpectatorPairCoupling seed (n + 1) - 1)))
    atTop (nhds 0) := by
  have hBound : Tendsto
      (fun n : ℕ =>
        (seededUniformSpectatorChargeQ seed (n + 1) : ℝ) ^ 2 /
          (2 * (n : ℝ))) atTop (nhds 0) := by
    have h := (seededUniformSpectatorCharge_sq_div_tendsto_zero seed).div_const 2
    have hEq :
        (fun n : ℕ =>
          (seededUniformSpectatorChargeQ seed (n + 1) : ℝ) ^ 2 /
            (n : ℝ) / 2) =ᶠ[atTop]
        (fun n : ℕ =>
          (seededUniformSpectatorChargeQ seed (n + 1) : ℝ) ^ 2 /
            (2 * (n : ℝ))) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp
    simpa using h.congr' hEq
  apply squeeze_zero_norm' _ hBound
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hbranch : ¬ n + 1 ≤ 1 := by omega
  let q : ℝ := (seededUniformSpectatorChargeQ seed (n + 1) : ℝ)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact_mod_cast seededUniformSpectatorChargeQ_nonneg hSeed (by omega)
  have hx : 0 ≤ q / (2 * (n : ℝ)) := div_nonneg hq (by positivity)
  have hTaylor := abs_log_one_add_sub_self_le (q / (2 * (n : ℝ))) hx
  have hLambda : seededUniformSpectatorPairCoupling seed (n + 1) =
      1 + q / (2 * (n : ℝ)) := by
    simp only [seededUniformSpectatorPairCoupling,
      seededUniformSpectatorPairCouplingQ, pairCouplingFromChargeQ,
      hbranch, if_false, Rat.cast_add, Rat.cast_one, Rat.cast_div]
    push_cast
    dsimp [q]
    congr 2
    ring
  rw [hLambda]
  norm_num only [add_sub_cancel_left]
  rw [Real.norm_eq_abs, abs_mul]
  have hcoef : |4 * (n : ℝ)| = 4 * (n : ℝ) :=
    abs_of_nonneg (by positivity)
  rw [hcoef]
  calc
    4 * (n : ℝ) *
        |Real.log (1 + q / (2 * (n : ℝ))) - q / (2 * (n : ℝ))| ≤
        4 * (n : ℝ) * ((q / (2 * (n : ℝ))) ^ 2 / 2) := by
      gcongr
    _ = q ^ 2 / (2 * (n : ℝ)) := by
      field_simp
      ring

/-- The first-order offset controlling the coherent Born limit is exactly the
spectator entropy anomaly at every positive rank, not merely asymptotically. -/
theorem harmonicCritical_firstOrder_eq_spectatorEntropyAnomaly
    {n : ℕ} (hn : 0 < n) :
    2 * (n : ℝ) * (harmonicCriticalPairCoupling (n + 1) - 1) -
        Real.log (n + 1) =
      uniformSpectatorEntropyAnomaly (n + 1) := by
  have hbranch : ¬ n + 1 ≤ 1 := by omega
  rw [uniformSpectatorEntropyAnomaly]
  rw [accumulatedUniformSpectatorSourceQ_eq_harmonic]
  simp only [harmonicCriticalPairCoupling, harmonicCriticalPairCouplingQ,
    hbranch, if_false, Rat.cast_add, Rat.cast_one, Rat.cast_div]
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnR]
  ring

/-! ## 3. Universality of the coherent infrared ratio -/

/-- Coherent unlabeled antichain ratio written directly in terms of the pair
coupling rather than its square `g`. -/
def coherentPairBornRatio (pairCoupling : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)) ^ 2 /
    (pairCoupling (n + 1)) ^ (4 * n)

/-- The pair-coupling expression is exactly the coherent ratio already
defined using the effective coupling `g=lambda^2`. -/
theorem coherentPairBornRatio_eq_criticalCoherentRatio
    (pairCoupling : ℕ → ℝ) (n : ℕ) :
    coherentPairBornRatio pairCoupling n =
      criticalCoherentOneMissingBornToTimidRatio
        (fun k => pairCoupling k ^ 2) n := by
  simp only [coherentPairBornRatio,
    criticalCoherentOneMissingBornToTimidRatio]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

theorem coherentPairBornRatio_eq_exp
    (pairCoupling : ℕ → ℝ) (hPositive : ∀ n, 0 < pairCoupling n)
    (n : ℕ) :
    coherentPairBornRatio pairCoupling n =
      Real.exp (2 * Real.log (n + 1) -
        4 * (n : ℝ) * Real.log (pairCoupling (n + 1))) := by
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hPair := hPositive (n + 1)
  rw [Real.exp_sub]
  have hNumerator : Real.exp (2 * Real.log ((n : ℝ) + 1)) =
      (((n + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.exp_nat_mul,
      Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    push_cast
    rfl
  rw [hNumerator]
  have hExponent :
      4 * (n : ℝ) * Real.log (pairCoupling (n + 1)) =
        (((4 * n : ℕ) : ℝ)) * Real.log (pairCoupling (n + 1)) := by
    push_cast
    ring
  rw [hExponent, Real.exp_nat_mul, Real.exp_log hPair]
  rfl

/-- Universal coherent critical limit.  Only the finite first-order offset
`delta` survives; all smaller nonlinear details wash out. -/
theorem coherentCriticalUniversality
    (pairCoupling : ℕ → ℝ) (delta : ℝ)
    (hPositive : ∀ n, 0 < pairCoupling n)
    (hFirstOrder : Tendsto
      (fun n : ℕ =>
        2 * (n : ℝ) * (pairCoupling (n + 1) - 1) - Real.log (n + 1))
      atTop (nhds delta))
    (hNonlinear : Tendsto
      (fun n : ℕ =>
        4 * (n : ℝ) *
          (Real.log (pairCoupling (n + 1)) -
            (pairCoupling (n + 1) - 1)))
      atTop (nhds 0)) :
    Tendsto (coherentPairBornRatio pairCoupling) atTop
      (nhds (Real.exp (-2 * delta))) := by
  have hFirstTwice := hFirstOrder.const_mul 2
  have hLog := (hFirstTwice.add hNonlinear).neg
  have hEq :
      (fun n : ℕ =>
        -(2 *
            (2 * (n : ℝ) * (pairCoupling (n + 1) - 1) -
              Real.log (n + 1)) +
          4 * (n : ℝ) *
            (Real.log (pairCoupling (n + 1)) -
              (pairCoupling (n + 1) - 1)))) =ᶠ[atTop]
      (fun n : ℕ => 2 * Real.log (n + 1) -
        4 * (n : ℝ) * Real.log (pairCoupling (n + 1))) := by
    filter_upwards [] with n
    ring
  have hLog' : Tendsto
      (fun n : ℕ => 2 * Real.log (n + 1) -
        4 * (n : ℝ) * Real.log (pairCoupling (n + 1)))
      atTop (nhds (-2 * delta)) := by
    simpa only [add_zero, neg_mul] using hLog.congr' hEq
  have hExp := Real.continuous_exp.continuousAt.tendsto.comp hLog'
  apply hExp.congr'
  filter_upwards [] with n
  exact (coherentPairBornRatio_eq_exp pairCoupling hPositive n).symm

/-- Complete seeded-family prediction. Every nonnegative rank-two charge gives
a positive trajectory in the same critical window, but its surviving infrared
constant is shifted by the boundary datum. -/
theorem seededUniformSpectatorBornRatio_tendsto
    {seed : ℚ} (hSeed : 0 ≤ seed) :
    Tendsto
      (coherentPairBornRatio (seededUniformSpectatorPairCoupling seed)) atTop
      (nhds (Real.exp (-2 *
        (Real.eulerMascheroniConstant +
          ((seed - harmonic 2 : ℚ) : ℝ))))) := by
  apply coherentCriticalUniversality
      (seededUniformSpectatorPairCoupling seed)
      (Real.eulerMascheroniConstant +
        ((seed - harmonic 2 : ℚ) : ℝ))
  · intro n
    exact lt_of_lt_of_le zero_lt_one
      (seededUniformSpectatorPairCoupling_one_le hSeed n)
  · have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      exact tendsto_atTop_mono' atTop
        (Eventually.of_forall fun n => Nat.le_add_right n 1) tendsto_id
    apply ((seededUniformSpectatorEntropyAnomaly_tendsto seed).comp hShift).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact
      (seededUniformSpectatorPairCoupling_firstOrder_eq_anomaly seed hn).symm
  · exact seededUniformSpectator_scaledLogError_tendsto_zero hSeed

/-- Infrared matching to the harmonic constant selects the canonical
rank-two boundary charge, and no other member of the seeded family. -/
theorem seededInfraredConstant_eq_harmonic_iff (seed : ℚ) :
    Real.exp (-2 *
        (Real.eulerMascheroniConstant +
          ((seed - harmonic 2 : ℚ) : ℝ))) =
      Real.exp (-2 * Real.eulerMascheroniConstant) ↔
    seed = harmonic 2 := by
  rw [Real.exp_injective.eq_iff]
  constructor
  · intro h
    have hCast : (((seed - harmonic 2 : ℚ) : ℝ)) = 0 := by
      linarith
    have hQ : seed - harmonic 2 = 0 := by exact_mod_cast hCast
    exact sub_eq_zero.mp hQ
  · intro hSeed
    rw [hSeed]
    norm_num

/-! ## 4. The explicit law as the selected trajectory -/

theorem harmonicCriticalPairCoupling_from_local_refinement :
    pairCouplingFromChargeQ harmonicCriticalChargeQ =
      harmonicCriticalPairCouplingQ :=
  uniformSpectatorRefinementLaw_selects_harmonic
    harmonicCriticalChargeQ_isUniformSpectatorRefinementLaw

theorem canonicalSeededPairCoupling_eq_harmonic :
    seededUniformSpectatorPairCouplingQ (harmonic 2) =
      harmonicCriticalPairCouplingQ := by
  funext n
  rw [seededUniformSpectatorPairCouplingQ,
    (seededUniformSpectatorChargeQ_eq_harmonic_iff (harmonic 2)).2 rfl]
  by_cases hn : n ≤ 1
  · simp [pairCouplingFromChargeQ, harmonicCriticalPairCouplingQ, hn]
  · simp [pairCouplingFromChargeQ, harmonicCriticalPairCouplingQ, hn]

/-- Capstone: a local additive refinement law uniquely generates the existing
zero-free projective quantum dynamics, and the accumulated source fixes its
coherent infrared constant. -/
theorem harmonicRefinementLaw_capstone :
    IsUniformSpectatorRefinementLaw harmonicCriticalChargeQ
      ∧ pairCouplingFromChargeQ harmonicCriticalChargeQ =
          harmonicCriticalPairCouplingQ
      ∧ Tendsto uniformSpectatorEntropyAnomaly atTop
          (nhds Real.eulerMascheroniConstant)
      ∧ Tendsto harmonicCriticalBornRatio atTop
          (nhds (Real.exp (-2 * Real.eulerMascheroniConstant))) := by
  exact ⟨harmonicCriticalChargeQ_isUniformSpectatorRefinementLaw,
    harmonicCriticalPairCoupling_from_local_refinement,
    uniformSpectatorEntropyAnomaly_tendsto,
    harmonicCriticalBornRatio_tendsto⟩

/-- Stronger classification capstone: the local law supports a one-parameter
critical family, and the harmonic infrared observable removes exactly that
remaining boundary freedom. -/
theorem seededRefinementFamily_capstone (seed : ℚ) (hSeed : 0 ≤ seed) :
    seededUniformSpectatorChargeQ seed 2 = seed
      ∧ (∀ n : ℕ, seededUniformSpectatorChargeQ seed (n + 1) =
          seededUniformSpectatorChargeQ seed n +
            uniformSpectatorSourceQ (n + 1))
      ∧ Tendsto
          (coherentPairBornRatio (seededUniformSpectatorPairCoupling seed))
          atTop
          (nhds (Real.exp (-2 *
            (Real.eulerMascheroniConstant +
              ((seed - harmonic 2 : ℚ) : ℝ)))))
      ∧ (Real.exp (-2 *
            (Real.eulerMascheroniConstant +
              ((seed - harmonic 2 : ℚ) : ℝ))) =
          Real.exp (-2 * Real.eulerMascheroniConstant) ↔
        seed = harmonic 2) := by
  exact ⟨seededUniformSpectatorChargeQ_two seed,
    seededUniformSpectatorChargeQ_succ seed,
    seededUniformSpectatorBornRatio_tendsto hSeed,
    seededInfraredConstant_eq_harmonic_iff seed⟩

#print axioms harmonicCriticalChargeQ_succ
#print axioms harmonicCriticalPairCouplingQ_affine_beta
#print axioms exchangeable_normalized_spectator_source_unique
#print axioms uniformSpectatorRefinementLaw_unique
#print axioms uniformSpectatorRefinementStep_seed_classification
#print axioms seededUniformSpectatorChargeQ_eq_harmonic_iff
#print axioms uniformSpectatorRefinementLaw_selects_harmonic
#print axioms uniformSpectatorEntropyAnomaly_tendsto
#print axioms seededUniformSpectatorEntropyAnomaly_tendsto
#print axioms harmonicCritical_firstOrder_eq_spectatorEntropyAnomaly
#print axioms seededUniformSpectator_scaledLogError_tendsto_zero
#print axioms coherentCriticalUniversality
#print axioms seededUniformSpectatorBornRatio_tendsto
#print axioms seededInfraredConstant_eq_harmonic_iff
#print axioms canonicalSeededPairCoupling_eq_harmonic
#print axioms harmonicRefinementLaw_capstone
#print axioms seededRefinementFamily_capstone

end

end UnifiedTheory.Audit.KFCausalSetHarmonicRefinementLaw
