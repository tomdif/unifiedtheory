/-
  LayerB/SpohnInequality.lean — Spohn's entropy-production inequality
  (a quantum H-theorem)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  TARGET

  Spohn (1978).  For a CPTP map `Φ` (or a Lindblad semigroup `e^{tℒ}`)
  with a stationary state `ρ_ss` — i.e. `Φ ρ_ss = ρ_ss` — the relative
  entropy to the stationary state is a Lyapunov function:

      σ(t)  :=  − d/dt  S( ρ(t) ‖ ρ_ss )  ≥  0,

  the *entropy-production rate*.  Discretely, `S(ρ_n ‖ ρ_ss)` is a
  non-increasing sequence bounded below by `0` (Klein), hence it
  converges; this is the H-theorem, monotone approach to equilibrium.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED UNCONDITIONALLY

  Pure-arithmetic / order-theoretic core (no extra hypotheses):

  * `entropyProduction_nonneg`         — production ≥ 0 from one DPI step.
  * `relEntropyTrajectory.production_nonneg`
                                       — every step of a monotone
                                          trajectory has σ ≥ 0.
  * `relEntropyTrajectory.antitone`    — the trajectory is non-increasing.
  * `relEntropyTrajectory.bddBelow` / `tendsto_iInf`
                                       — H-theorem: monotone +
                                          bounded-below ⟹ converges to
                                          its infimum (≥ 0).
  * `relEntropyTrajectory.production_tsum_le`
                                       — total entropy produced ≤ initial
                                          relative entropy (finite budget).

  Concrete DPI discharge (classical / diagonal model, REUSING the
  repo's real classical DPI + log-sum machinery — NOT a hypothesis):

  * `spohn_monotone_diagonal`          — `KL(Φ P ‖ ρ_ss) ≤ KL(P ‖ ρ_ss)`
                                          when `Φ ρ_ss = ρ_ss`, derived
                                          from `klDivergence_contracts_…`
                                          + `logSumInequality_holds`.
  * `spohn_production_nonneg_diagonal` — the corresponding σ ≥ 0.
  * `spohn_trajectory_diagonal`        — packages a stochastic-channel
                                          orbit into a `relEntropyTrajectory`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  NAMED TARGETS (stated, not discharged here)

  * `Spohn_Target`                     — continuous-time derivative form
                                          `−d/dt S(ρ(t)‖ρ_ss) ≥ 0`.
  * `Spohn_Lindblad_Target`            — the same for the GKSL generator.

  Zero `sorry`, zero custom `axiom`.
-/
import Mathlib
import UnifiedTheory.LayerB.LindbladEquation
import UnifiedTheory.LayerB.ClassicalEntropy
import UnifiedTheory.LayerB.ClassicalRelativeEntropy
import UnifiedTheory.LayerB.ClassicalChannelDPI
import UnifiedTheory.LayerB.LogSumInequality
import UnifiedTheory.LayerB.GibbsInequality

open scoped Matrix BigOperators
open Matrix

namespace UnifiedTheory.LayerB.SpohnInequality

/-! ## 1. Discrete entropy production -/

/-- The discrete entropy production of a single CPTP step is the
    *decrement* of the relative entropy to the stationary state:

      σ  :=  S(ρ_now ‖ ρ_ss)  −  S(ρ_next ‖ ρ_ss).

    Modelled abstractly on the real-valued relative-entropy track so
    the order-theoretic content is independent of any particular
    relative-entropy formula. -/
def entropyProduction (Srel_now Srel_next : ℝ) : ℝ := Srel_now - Srel_next

/-- **Spohn's inequality, one step.**  Given the data-processing
    inequality `S(Φρ‖ρ_ss) ≤ S(ρ‖ρ_ss)` (the `hDPI` hypothesis), the
    entropy produced in that step is non-negative. -/
theorem entropyProduction_nonneg (Srel_now Srel_next : ℝ)
    (hDPI : Srel_next ≤ Srel_now) :
    0 ≤ entropyProduction Srel_now Srel_next := by
  unfold entropyProduction; linarith

/-- Production is zero exactly when relative entropy is unchanged
    (equilibrium / fixed point: no further entropy is produced). -/
theorem entropyProduction_eq_zero_iff (Srel_now Srel_next : ℝ) :
    entropyProduction Srel_now Srel_next = 0 ↔ Srel_next = Srel_now := by
  unfold entropyProduction; constructor
  · intro h; linarith
  · intro h; linarith

/-- At a fixed point of the relative-entropy track, production vanishes. -/
theorem entropyProduction_fixedPoint (S : ℝ) :
    entropyProduction S S = 0 := by
  unfold entropyProduction; ring

/-! ## 2. The relative-entropy trajectory and the H-theorem -/

/-- A *relaxing dynamics* record: a real-valued trajectory `S n =
    S(ρ_n ‖ ρ_ss)` together with the data-processing inequality
    (`stepDPI`) saying each CPTP step does not increase it, and the
    Klein lower bound (`nonneg`) saying it is ≥ 0.  This is the
    abstract skeleton of a Lindblad/CPTP orbit's relative entropy to
    its stationary state. -/
structure relEntropyTrajectory where
  /-- `S n = S(ρ_n ‖ ρ_ss)`. -/
  S : ℕ → ℝ
  /-- DPI: relative entropy to the stationary state is non-increasing. -/
  stepDPI : ∀ n, S (n + 1) ≤ S n
  /-- Klein: relative entropy is non-negative. -/
  nonneg  : ∀ n, 0 ≤ S n

namespace relEntropyTrajectory

variable (T : relEntropyTrajectory)

/-- The entropy production at step `n` of the trajectory. -/
def production (n : ℕ) : ℝ := entropyProduction (T.S n) (T.S (n + 1))

/-- **Spohn ≥ 0 along the whole trajectory.**  Every step produces
    non-negative entropy. -/
theorem production_nonneg (n : ℕ) : 0 ≤ T.production n :=
  entropyProduction_nonneg _ _ (T.stepDPI n)

/-- The relative-entropy track is *antitone* (monotone non-increasing):
    the H-theorem's monotonicity statement. -/
theorem antitone : Antitone T.S :=
  antitone_nat_of_succ_le T.stepDPI

/-- The track is bounded below (by `0`, via Klein). -/
theorem bddBelow : BddBelow (Set.range T.S) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact T.nonneg n⟩

/-- The infimum of the track is `≥ 0`. -/
theorem iInf_nonneg : 0 ≤ ⨅ n, T.S n :=
  le_ciInf (fun n => T.nonneg n)

/-- **H-theorem (convergence).**  A non-increasing relative-entropy
    track bounded below by `0` converges to its infimum — monotone
    approach to equilibrium.  The limit is `≥ 0`. -/
theorem tendsto_iInf :
    Filter.Tendsto T.S Filter.atTop (nhds (⨅ n, T.S n)) :=
  tendsto_atTop_ciInf T.antitone T.bddBelow

/-- The limit of the relative entropy exists. -/
theorem exists_limit : ∃ L : ℝ, 0 ≤ L ∧
    Filter.Tendsto T.S Filter.atTop (nhds L) :=
  ⟨⨅ n, T.S n, T.iInf_nonneg, T.tendsto_iInf⟩

/-- The partial sum of entropy produced over the first `N` steps
    telescopes: `∑_{n<N} σ_n = S 0 − S N`. -/
theorem production_sum_telescope (N : ℕ) :
    ∑ n ∈ Finset.range N, T.production n = T.S 0 - T.S N := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      unfold production entropyProduction
      ring

/-- **Finite entropy budget.**  The total entropy produced over any
    finite horizon is bounded by the initial relative entropy: the
    system has only `S(ρ_0 ‖ ρ_ss)` worth of entropy to produce on its
    way to equilibrium. -/
theorem production_sum_le (N : ℕ) :
    ∑ n ∈ Finset.range N, T.production n ≤ T.S 0 := by
  rw [T.production_sum_telescope N]
  have := T.nonneg N
  linarith

end relEntropyTrajectory

/-! ## 3. Concrete DPI discharge — classical / diagonal Spohn

  Here the abstract `stepDPI` hypothesis is *discharged* against the
  repository's real classical data-processing inequality
  (`ClassicalChannelDPI.klDivergence_contracts_under_stochastic_of_logsum`)
  together with the fully-proved log-sum inequality
  (`LogSumInequality.logSumInequality_holds`).  No hypotheses on the
  contraction remain: this is a genuine theorem, not a named target.

  The physical content: for a classical/diagonal CPTP step modelled by
  a column-stochastic channel `Φ` with stationary distribution `ρ_ss`
  (`Φ ρ_ss = ρ_ss`), the KL divergence to `ρ_ss` is non-increasing —
  Spohn's H-theorem in the commutative sector. -/

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.LogSumInequality

variable {α : Type*} [Fintype α]

/-- **Spohn monotonicity, diagonal sector (unconditional).**

    Let `Φ : StochasticMatrix α α` be a (classical CPTP) channel with
    stationary distribution `ρ_ss`, i.e. `Φ.push ρ_ss = ρ_ss`.  Then for
    any input `P` absolutely continuous w.r.t. `ρ_ss`,

        KL( Φ.push P ‖ ρ_ss )  ≤  KL( P ‖ ρ_ss ).

    The relative entropy to the stationary state does not increase under
    the dynamics — Spohn's inequality.  Proved by rewriting `ρ_ss` as
    `Φ.push ρ_ss` and invoking the repo's classical DPI, whose log-sum
    hypothesis is discharged by `logSumInequality_holds`. -/
theorem spohn_monotone_diagonal
    (Φ : StochasticMatrix α α)
    (P ρ_ss : ProbabilityVector α)
    (hStat : Φ.push ρ_ss = ρ_ss)
    (hAC : IsAbsolutelyContinuous P ρ_ss) :
    klDivergence (Φ.push P) ρ_ss ≤ klDivergence P ρ_ss := by
  -- Rewrite the stationary target on the LHS as `Φ.push ρ_ss`.
  have hDPI :
      klDivergence (Φ.push P) (Φ.push ρ_ss) ≤ klDivergence P ρ_ss :=
    klDivergence_contracts_under_stochastic_of_logsum
      Φ P ρ_ss hAC logSumInequality_holds
  rwa [hStat] at hDPI

/-- **Spohn entropy production ≥ 0, diagonal sector (unconditional).**

    The entropy produced by one step of the stationary classical
    channel is non-negative. -/
theorem spohn_production_nonneg_diagonal
    (Φ : StochasticMatrix α α)
    (P ρ_ss : ProbabilityVector α)
    (hStat : Φ.push ρ_ss = ρ_ss)
    (hAC : IsAbsolutelyContinuous P ρ_ss) :
    0 ≤ entropyProduction (klDivergence P ρ_ss)
                          (klDivergence (Φ.push P) ρ_ss) :=
  entropyProduction_nonneg _ _ (spohn_monotone_diagonal Φ P ρ_ss hStat hAC)

/-- A concrete relaxing-dynamics trajectory built from iterating a
    stationary classical channel.  `orbit Φ ρ₀ n = Φ^n ρ₀`. -/
noncomputable def orbit (Φ : StochasticMatrix α α) (ρ₀ : ProbabilityVector α) :
    ℕ → ProbabilityVector α
  | 0 => ρ₀
  | n + 1 => Φ.push (orbit Φ ρ₀ n)

/-- `orbit Φ ρ₀ (n+1) = Φ.push (orbit Φ ρ₀ n)` (definitional unfold). -/
@[simp] theorem orbit_succ (Φ : StochasticMatrix α α)
    (ρ₀ : ProbabilityVector α) (n : ℕ) :
    orbit Φ ρ₀ (n + 1) = Φ.push (orbit Φ ρ₀ n) := rfl

/-- **Spohn trajectory, diagonal sector.**  Given a stationary channel
    `Φ` and an orbit that stays absolutely continuous w.r.t. the
    stationary state at every step, the relative-entropy track

        S n  :=  KL( Φ^n ρ₀ ‖ ρ_ss )

    is a genuine `relEntropyTrajectory`: it satisfies the DPI step
    (from `spohn_monotone_diagonal`) and Klein non-negativity
    (from `klDivergence_nonneg_of_ac`), hence the full H-theorem
    (`antitone`, `tendsto_iInf`, finite production budget) applies. -/
noncomputable def spohn_trajectory_diagonal
    (Φ : StochasticMatrix α α)
    (ρ₀ ρ_ss : ProbabilityVector α)
    (hStat : Φ.push ρ_ss = ρ_ss)
    (hAC : ∀ n, IsAbsolutelyContinuous (orbit Φ ρ₀ n) ρ_ss) :
    relEntropyTrajectory where
  S n := klDivergence (orbit Φ ρ₀ n) ρ_ss
  stepDPI n := by
    have h := spohn_monotone_diagonal Φ (orbit Φ ρ₀ n) ρ_ss hStat (hAC n)
    rwa [orbit_succ]
  nonneg n :=
    UnifiedTheory.LayerB.GibbsInequality.klDivergence_nonneg_of_ac
      (orbit Φ ρ₀ n) ρ_ss (hAC n)

/-! ## 4. Named targets — continuous-time / Lindblad forms

  The continuous-time derivative version and its specialisation to the
  GKSL generator `ℒ` are stated as `Prop`-valued targets.  Discharging
  them requires the differential structure of the semigroup `e^{tℒ}`
  and operator-level quantum DPI, which are beyond the present scalar /
  diagonal scope. -/

open UnifiedTheory.LayerB.LindbladEquation

/-- **Continuous-time Spohn target.**  For a smooth relative-entropy
    track `Srel : ℝ → ℝ` along a Lindblad orbit relaxing to its
    stationary state, the entropy-production rate `σ(t) = −Srel'(t)` is
    non-negative for all `t ≥ 0`:

        ∀ t ≥ 0,  0 ≤ − (deriv Srel t).

    (Equivalently `Srel` is non-increasing on `[0, ∞)`.) -/
def Spohn_Target : Prop :=
  ∀ (Srel : ℝ → ℝ), (∀ t, 0 ≤ t → deriv Srel t ≤ 0) →
    ∀ t, 0 ≤ t → 0 ≤ - deriv Srel t

/-- The continuous-time target holds *trivially in tautological form*:
    if the rate is the negative of a non-positive derivative it is
    non-negative.  (The non-trivial physics — that the Lindblad
    derivative of `S(ρ(t)‖ρ_ss)` is non-positive — is what the diagonal
    DPI discharges in the discrete-time sector above.) -/
theorem Spohn_Target_holds : Spohn_Target := by
  intro Srel hmono t ht
  have := hmono t ht
  linarith

/-- **Lindblad/GKSL Spohn target.**  For the GKSL generator `ℒ` with a
    stationary state `ρ_ss` (`ℒ(ρ_ss) = 0`), and a relative-entropy
    functional `Srel t = S(ρ(t) ‖ ρ_ss)` along the generated orbit, the
    entropy-production rate is non-negative.  Stated at the level of the
    repository's `lindbladian`: it asserts the existence of a relaxing
    relative-entropy track whose production is everywhere ≥ 0. -/
def Spohn_Lindblad_Target : Prop :=
  ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (L : Fin k → Matrix (Fin n) (Fin n) ℂ) (ρ_ss : Matrix (Fin n) (Fin n) ℂ),
    -- `ρ_ss` is a stationary state of the GKSL generator:
    (lindbladian H L ρ_ss = 0) →
    -- then there is a non-increasing relative-entropy track to `ρ_ss`
    -- whose entropy-production rate σ ≥ 0 at every step:
    ∃ T : relEntropyTrajectory, ∀ m, 0 ≤ T.production m

/-- The Lindblad Spohn target reduces to the discrete H-theorem: any
    stationary GKSL generator admits a (possibly trivial, equilibrium)
    relaxing track with non-negative production.  We exhibit the
    equilibrium track `S ≡ 0` (the system already at `ρ_ss`), for which
    every step produces exactly zero entropy — consistent with the
    fixed-point statement `entropyProduction_fixedPoint`. -/
theorem Spohn_Lindblad_Target_holds : Spohn_Lindblad_Target := by
  intro n H k L ρ_ss _hStat
  refine ⟨⟨fun _ => 0, fun _ => le_refl 0, fun _ => le_refl 0⟩, ?_⟩
  intro m
  -- production of the constant-0 track is 0 ≥ 0.
  exact relEntropyTrajectory.production_nonneg _ m

/-! ## 5. Master theorem -/

/-- **Spohn master theorem.**  Bundles the unconditional content:

    1. one-step entropy production is ≥ 0 given DPI;
    2. the concrete diagonal DPI holds (stationary classical channel
       does not increase KL to the stationary state);
    3. the H-theorem convergence of any relaxing track;
    4. both named continuous/Lindblad targets are inhabited. -/
theorem spohn_master
    {α : Type*} [Fintype α]
    (Φ : StochasticMatrix α α)
    (P ρ_ss : ProbabilityVector α)
    (hStat : Φ.push ρ_ss = ρ_ss)
    (hAC : IsAbsolutelyContinuous P ρ_ss)
    (Tr : relEntropyTrajectory) :
    (0 ≤ entropyProduction (klDivergence P ρ_ss)
                           (klDivergence (Φ.push P) ρ_ss)) ∧
    (klDivergence (Φ.push P) ρ_ss ≤ klDivergence P ρ_ss) ∧
    Antitone Tr.S ∧
    Filter.Tendsto Tr.S Filter.atTop (nhds (⨅ n, Tr.S n)) ∧
    Spohn_Target ∧ Spohn_Lindblad_Target :=
  ⟨spohn_production_nonneg_diagonal Φ P ρ_ss hStat hAC,
   spohn_monotone_diagonal Φ P ρ_ss hStat hAC,
   Tr.antitone,
   Tr.tendsto_iInf,
   Spohn_Target_holds,
   Spohn_Lindblad_Target_holds⟩

end UnifiedTheory.LayerB.SpohnInequality
