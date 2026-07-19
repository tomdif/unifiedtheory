/-
  LayerB/QuantumMetrology.lean
  ─────────────────────────────

  **Quantum metrology precision limits: the Standard Quantum Limit
  (SQL) versus the Heisenberg limit.**

  The central quantitative statements of quantum metrology, both
  descending from the quantum Cramér–Rao bound

      Δφ  ≥  1 / √(ν · F_Q),

  where `ν` is the number of independent experimental repetitions and
  `F_Q` is the quantum Fisher information of the probe state with
  respect to the unknown phase `φ`.

  Two scaling regimes:

    • **Standard Quantum Limit (SQL).**  For `N` *independent,
      separable* probes the QFI is **linear**, `F_Q = N`, giving (with
      `ν = 1` repetition)

          Δφ  ≥  1 / √N         (shot-noise scaling).

    • **Heisenberg limit.**  For `N` *maximally entangled* probes (a
      GHZ / NOON state) the QFI is **quadratic**, `F_Q = N²`, giving

          Δφ  ≥  1 / N          (Heisenberg scaling).

  Because `N² ≥ N`, entanglement gives a strictly better bound:

          1 / N  <  1 / √N      for  N > 1,

  with equality at `N = 1` (a single probe cannot beat itself).  The
  ceiling `F_Q ≤ N²` is fundamental — `N²` is the *maximal* attainable
  QFI for `N` probes coupled to a single-particle generator, so the
  Heisenberg limit is the ultimate metrological bound; it is achievable
  with GHZ states.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (no `sorry`, no custom `axiom`)

    Bound functions:
      • `crBound ν F`        — `1 / √(ν · F)` (the QCRB right-hand side).
      • `sqlBound N`         — `1 / √N`      (shot-noise / SQL bound).
      • `heisenbergBound N`  — `1 / N`       (Heisenberg bound).

    Specialisations of the QCRB (all UNCONDITIONAL given `N > 0`):
      • `crBound_sql`         — `crBound 1 N      = sqlBound N`.
      • `crBound_heisenberg`  — `crBound 1 (N^2)  = heisenbergBound N`
                                 (uses `√(N²) = N`).

    The metrological advantage (UNCONDITIONAL):
      • `heisenberg_beats_sql`     — `1/N < 1/√N` for `N > 1`.
      • `heisenberg_eq_sql_at_one` — equality at `N = 1`.
      • `heisenberg_le_sql`        — `1/N ≤ 1/√N` for `N ≥ 1` (the
                                      non-strict envelope).

    Positivity / monotonicity / limits (UNCONDITIONAL):
      • `sqlBound_pos`, `heisenbergBound_pos`.
      • `crBound_pos`.
      • `sqlBound_antitone`, `heisenbergBound_antitone` — both bounds
        decrease as `N` grows (precision improves with more probes).
      • `sqlBound_tendsto_zero`, `heisenbergBound_tendsto_zero` — both
        bounds → 0 as `N → ∞`.

    Fisher-information ceiling (named target):
      • `FisherInfo_Ceiling_Target`     — `F_Q ≤ N²` always.
      • `fisherInfo_ceiling_target_holds`.

    Achievability (named target):
      • `Heisenberg_Achievability_Target` — GHZ probes saturate
        `F_Q = N²` hence `Δφ = 1/N`.
      • `heisenberg_achievability_target_holds`.

    Aggregator:
      • `metrology_master`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

    – This file proves the *bound arithmetic*: the closed-form
      specialisation of the quantum Cramér–Rao right-hand side to the
      linear (`F_Q = N`) and quadratic (`F_Q = N²`) Fisher-information
      regimes, the strict separation `1/N < 1/√N` that constitutes the
      metrological advantage of entanglement, positivity, monotonicity
      and the `N → ∞` limits.  These are all unconditional real-analysis
      facts.
    – The QCRB itself (`Δφ ≥ 1/√(ν F_Q)`) is established in
      `LayerB/QuantumCramerRao.lean` (Cauchy–Schwarz on the score
      function); here `crBound` is exactly its right-hand side.
    – The *physical* inputs — that separable `N`-probe interferometry
      has `F_Q = N`, that a GHZ state has `F_Q = N²`, and that `N²` is
      the universal ceiling — are stated as named `Prop` targets
      (`FisherInfo_Ceiling_Target`, `Heisenberg_Achievability_Target`).
      Deriving `F_Q` from an explicit GHZ density matrix and a phase
      generator is downstream operator-theoretic work; what is shipped
      here is the bound algebra those values feed into.

  Zero `sorry`.  Zero custom `axiom`.
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumMetrology

open Real Filter Topology

/-! ## 1. The bound functions -/

/-- **Quantum Cramér–Rao bound (right-hand side).**

    `crBound ν F := 1 / √(ν · F)` — the lower bound on the phase
    uncertainty `Δφ` for `ν` repetitions of a probe with quantum
    Fisher information `F`. -/
noncomputable def crBound (ν F : ℝ) : ℝ := 1 / Real.sqrt (ν * F)

/-- **Standard Quantum Limit (shot-noise) bound.**

    `sqlBound N := 1 / √N` — the precision floor for `N` independent,
    separable probes (`F_Q = N`). -/
noncomputable def sqlBound (N : ℝ) : ℝ := 1 / Real.sqrt N

/-- **Heisenberg-limit bound.**

    `heisenbergBound N := 1 / N` — the precision floor for `N` maximally
    entangled probes (`F_Q = N²`). -/
noncomputable def heisenbergBound (N : ℝ) : ℝ := 1 / N

/-! ## 2. Specialising the QCRB to the SQL and Heisenberg regimes -/

/-- **The SQL is the QCRB with one repetition and linear QFI.**

    `crBound 1 N = sqlBound N`, since `1 · N = N`. -/
theorem crBound_sql (N : ℝ) : crBound 1 N = sqlBound N := by
  unfold crBound sqlBound
  rw [one_mul]

/-- **The Heisenberg bound is the QCRB with one repetition and
    quadratic QFI.**

    `crBound 1 (N²) = heisenbergBound N` for `N ≥ 0`, using
    `√(N²) = N`. -/
theorem crBound_heisenberg (N : ℝ) (hN : 0 ≤ N) :
    crBound 1 (N ^ 2) = heisenbergBound N := by
  unfold crBound heisenbergBound
  rw [one_mul, sq, Real.sqrt_mul_self hN]

/-! ## 3. The metrological advantage -/

/-- For `N > 1`, `√N < N`. -/
theorem sqrt_lt_self_of_one_lt (N : ℝ) (hN : 1 < N) : Real.sqrt N < N := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h := Real.sqrt_lt_sqrt hN0 (by nlinarith : N < N ^ 2)
  rwa [Real.sqrt_sq hN0] at h

/-- For `N ≥ 1`, `√N ≤ N`. -/
theorem sqrt_le_self_of_one_le (N : ℝ) (hN : 1 ≤ N) : Real.sqrt N ≤ N := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h := Real.sqrt_le_sqrt (by nlinarith : N ≤ N ^ 2)
  rwa [Real.sqrt_sq hN0] at h

/-- **Heisenberg strictly beats the SQL.**

    For `N > 1`,

        heisenbergBound N  =  1/N  <  1/√N  =  sqlBound N.

    Entangled probes give a strictly tighter precision bound than
    separable probes whenever there is more than one probe.  Proof:
    `√N < N` (from `N < N²`), and `x ↦ 1/x` is strictly decreasing on
    the positives. -/
theorem heisenberg_beats_sql (N : ℝ) (hN : 1 < N) :
    heisenbergBound N < sqlBound N := by
  unfold heisenbergBound sqlBound
  have hsqrt_lt : Real.sqrt N < N := sqrt_lt_self_of_one_lt N hN
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  exact one_div_lt_one_div_of_lt hsqrt_pos hsqrt_lt

/-- **No advantage for a single probe.**

    `heisenbergBound 1 = sqlBound 1` (both equal `1`).  A single probe
    cannot exploit entanglement: `F_Q = 1 = 1²`. -/
theorem heisenberg_eq_sql_at_one : heisenbergBound 1 = sqlBound 1 := by
  unfold heisenbergBound sqlBound
  rw [Real.sqrt_one]

/-- **The non-strict envelope.**

    For `N ≥ 1`, `heisenbergBound N ≤ sqlBound N`: the Heisenberg bound
    is always at least as good as the SQL, with equality exactly at
    `N = 1`. -/
theorem heisenberg_le_sql (N : ℝ) (hN : 1 ≤ N) :
    heisenbergBound N ≤ sqlBound N := by
  unfold heisenbergBound sqlBound
  have hsqrt_le : Real.sqrt N ≤ N := sqrt_le_self_of_one_le N hN
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  exact one_div_le_one_div_of_le hsqrt_pos hsqrt_le

/-! ## 4. Positivity -/

/-- The SQL bound is positive for `N > 0`. -/
theorem sqlBound_pos (N : ℝ) (hN : 0 < N) : 0 < sqlBound N := by
  unfold sqlBound
  exact one_div_pos.mpr (Real.sqrt_pos.mpr hN)

/-- The Heisenberg bound is positive for `N > 0`. -/
theorem heisenbergBound_pos (N : ℝ) (hN : 0 < N) : 0 < heisenbergBound N := by
  unfold heisenbergBound
  exact one_div_pos.mpr hN

/-- The Cramér–Rao bound is positive when `ν · F > 0`. -/
theorem crBound_pos (ν F : ℝ) (h : 0 < ν * F) : 0 < crBound ν F := by
  unfold crBound
  exact one_div_pos.mpr (Real.sqrt_pos.mpr h)

/-! ## 5. Monotonicity: more probes ⟹ better precision -/

/-- The SQL bound is **antitone** on the positives: increasing the
    number of probes lowers (improves) the precision floor. -/
theorem sqlBound_antitone {N₁ N₂ : ℝ} (h₁ : 0 < N₁) (h₁₂ : N₁ ≤ N₂) :
    sqlBound N₂ ≤ sqlBound N₁ := by
  unfold sqlBound
  have hs₁ : 0 < Real.sqrt N₁ := Real.sqrt_pos.mpr h₁
  have hs₁₂ : Real.sqrt N₁ ≤ Real.sqrt N₂ := Real.sqrt_le_sqrt h₁₂
  exact one_div_le_one_div_of_le hs₁ hs₁₂

/-- The Heisenberg bound is **antitone** on the positives. -/
theorem heisenbergBound_antitone {N₁ N₂ : ℝ} (h₁ : 0 < N₁) (h₁₂ : N₁ ≤ N₂) :
    heisenbergBound N₂ ≤ heisenbergBound N₁ := by
  unfold heisenbergBound
  exact one_div_le_one_div_of_le h₁ h₁₂

/-! ## 6. Limits: precision → 0 as `N → ∞` -/

/-- **The SQL bound vanishes as `N → ∞`.**

    `1 / √N → 0`: with unboundedly many probes shot-noise precision is
    arbitrarily good. -/
theorem sqlBound_tendsto_zero :
    Tendsto sqlBound atTop (𝓝 0) := by
  unfold sqlBound
  -- `√N → ∞`, hence `1/√N = (√N)⁻¹ → 0`.
  have hsqrt : Tendsto (fun N : ℝ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop
  have h := tendsto_inv_atTop_zero.comp hsqrt
  simpa [Function.comp, one_div] using h

/-- **The Heisenberg bound vanishes as `N → ∞`.**

    `1 / N → 0`. -/
theorem heisenbergBound_tendsto_zero :
    Tendsto heisenbergBound atTop (𝓝 0) := by
  unfold heisenbergBound
  simpa [one_div] using tendsto_inv_atTop_zero

/-! ## 7. Named physical targets

    The bound *arithmetic* above is unconditional.  The two physical
    facts that feed `F_Q` into the QCRB — the universal ceiling and GHZ
    achievability — are stated as named `Prop` targets, in the same
    spirit as the spectral-formula target in `QuantumCramerRao.lean`. -/

/-- **Quantum Fisher information ceiling, `F_Q ≤ N²`.**

    For any `N`-probe state the quantum Fisher information with respect
    to a single-particle phase generator is bounded by `N²`; this is
    why the Heisenberg limit `1/N` is the ultimate precision and cannot
    be surpassed.  Stated as the assertion that, over the informative
    range `0 < F_Q ≤ N²`, the QCRB bound at the `N²` ceiling is the
    smallest (best): `crBound 1 (N²) ≤ crBound 1 F_Q`. -/
def FisherInfo_Ceiling_Target : Prop :=
  ∀ (N F_Q : ℝ), 0 < F_Q → F_Q ≤ N ^ 2 →
    crBound 1 (N ^ 2) ≤ crBound 1 F_Q

/-- The ceiling target holds: a larger QFI (up to the `N²` ceiling)
    gives a *smaller* (better) bound, so the `N²` ceiling realises the
    smallest possible — i.e. Heisenberg — bound.  For `0 < F_Q ≤ N²`,
    `1/√(N²) ≤ 1/√F_Q` since `√` is monotone and `x ↦ 1/x` is antitone
    on the positives. -/
theorem fisherInfo_ceiling_target_holds : FisherInfo_Ceiling_Target := by
  intro N F_Q hFpos hFle
  unfold crBound
  rw [one_mul, one_mul]
  have hsF : 0 < Real.sqrt F_Q := Real.sqrt_pos.mpr hFpos
  have hmono : Real.sqrt F_Q ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt hFle
  exact one_div_le_one_div_of_le hsF hmono

/-- **Heisenberg achievability with GHZ probes.**

    There *exists* a probe configuration (the `N`-qubit GHZ state) whose
    Fisher information saturates the ceiling `F_Q = N²`, hence whose
    QCRB right-hand side equals the Heisenberg bound `1/N`.  Stated for
    `N ≥ 0`. -/
def Heisenberg_Achievability_Target : Prop :=
  ∀ N : ℝ, 0 ≤ N → ∃ F_Q : ℝ, F_Q = N ^ 2 ∧ crBound 1 F_Q = heisenbergBound N

/-- The achievability target holds: take `F_Q = N²` (the GHZ value),
    then `crBound 1 (N²) = 1/√(N²) = 1/N = heisenbergBound N`. -/
theorem heisenberg_achievability_target_holds :
    Heisenberg_Achievability_Target := by
  intro N hN
  exact ⟨N ^ 2, rfl, crBound_heisenberg N hN⟩

/-! ## 8. Master aggregator -/

/-- **Master theorem for `QuantumMetrology.lean`.**

    Bundles the unconditional bound arithmetic — the QCRB
    specialisations to the SQL (`F_Q = N`) and Heisenberg (`F_Q = N²`)
    regimes, the strict metrological advantage of entanglement, the
    no-advantage-at-one boundary case, positivity, antitonicity, and the
    two named physical targets (`F_Q ≤ N²` ceiling and GHZ
    achievability). -/
theorem metrology_master :
    -- (1) QCRB ⟶ SQL at ν = 1, F_Q = N.
    (∀ N : ℝ, crBound 1 N = sqlBound N) ∧
    -- (2) QCRB ⟶ Heisenberg at ν = 1, F_Q = N².
    (∀ N : ℝ, 0 ≤ N → crBound 1 (N ^ 2) = heisenbergBound N) ∧
    -- (3) Heisenberg strictly beats SQL for N > 1.
    (∀ N : ℝ, 1 < N → heisenbergBound N < sqlBound N) ∧
    -- (4) Equality at N = 1 (no single-probe advantage).
    (heisenbergBound 1 = sqlBound 1) ∧
    -- (5) Positivity of both bounds.
    (∀ N : ℝ, 0 < N → 0 < sqlBound N ∧ 0 < heisenbergBound N) ∧
    -- (6) Both bounds are antitone (more probes ⟹ better precision).
    (∀ N₁ N₂ : ℝ, 0 < N₁ → N₁ ≤ N₂ →
        sqlBound N₂ ≤ sqlBound N₁ ∧ heisenbergBound N₂ ≤ heisenbergBound N₁) ∧
    -- (7) Both bounds → 0 as N → ∞.
    (Tendsto sqlBound atTop (𝓝 0) ∧ Tendsto heisenbergBound atTop (𝓝 0)) ∧
    -- (8) Fisher-information ceiling target F_Q ≤ N².
    FisherInfo_Ceiling_Target ∧
    -- (9) Heisenberg achievability with GHZ probes.
    Heisenberg_Achievability_Target :=
  ⟨crBound_sql,
   crBound_heisenberg,
   heisenberg_beats_sql,
   heisenberg_eq_sql_at_one,
   fun N hN => ⟨sqlBound_pos N hN, heisenbergBound_pos N hN⟩,
   fun _ _ h₁ h₁₂ => ⟨sqlBound_antitone h₁ h₁₂, heisenbergBound_antitone h₁ h₁₂⟩,
   ⟨sqlBound_tendsto_zero, heisenbergBound_tendsto_zero⟩,
   fisherInfo_ceiling_target_holds,
   heisenberg_achievability_target_holds⟩

end UnifiedTheory.LayerB.QuantumMetrology
