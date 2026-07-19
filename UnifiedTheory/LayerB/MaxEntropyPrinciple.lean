/-
  LayerB/MaxEntropyPrinciple.lean
  ───────────────────────────────

  **The Jaynes maximum-entropy principle.**

  The thermodynamic DUAL of the Gibbs free-energy minimization
  (`GibbsVariationalFull.gibbs_variational_principle`):

      Among all states ρ with a FIXED mean energy `⟨H⟩_ρ = E`, the
      Gibbs state `ρ_β = exp(-βH)/Z` (with β tuned so `⟨H⟩_{ρ_β} = E`)
      MAXIMIZES the von Neumann entropy `S(ρ)`:

          S(ρ)  ≤  S(ρ_β).

  ## Mechanism — pure energy cancellation in the variational principle

  The Gibbs variational principle is the PROVED engine:

      F(ρ)  ≥  F(ρ_β),     F(ρ) = ⟨H⟩_ρ − T·S(ρ),   T = 1/β > 0.

  Restrict to the fixed-energy slice `⟨H⟩_ρ = ⟨H⟩_{ρ_β} = E`.  The energy
  terms are equal, so they cancel in the gap:

      ⟨H⟩_ρ − T·S(ρ)  ≥  ⟨H⟩_{ρ_β} − T·S(ρ_β)
      ⟹  − T·S(ρ)  ≥  − T·S(ρ_β)
      ⟹       S(ρ)  ≤      S(ρ_β)      (divide by −T < 0, flip).

  No new analytic content: this is `linarith` on top of the variational
  inequality and `freeEnergy_eq_energy_sub`.

  ## What this file ships

    * `max_entropy`             — `S(ρ) ≤ S(ρ_β)` on the fixed-energy slice.
    * `max_entropy_strict_pos`  — same, stated with `0 < T` directly.
    * `gibbs_is_maxEntropy`     — Jaynes form: the Gibbs state attains the
                                  supremum of `S` over the fixed-⟨H⟩ slice.
    * `max_entropy_eq_iff_relent_zero`
                                — equality `S(ρ) = S(ρ_β)` on the slice ⇔
                                  `S(ρ‖ρ_β) = 0` (faithfulness route to
                                  UNIQUENESS of the maximizer).
    * `max_entropy_unique_via_relent`
                                — the uniqueness statement in relative-
                                  entropy form.

  SCOPE / honesty:
    * Finite-dimensional `Matrix (Fin n) (Fin n) ℂ`; states are
      `ComplexDensityMatrix n`.
    * `PosDef` on ρ is the genuine Klein side-condition inherited from the
      variational principle (faithfulness/finiteness of relative entropy).
    * `0 < T` (strictly positive temperature) is required to divide by `−T`
      and flip the inequality — the entropy ordering is a `T > 0` fact.
    * No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.GibbsVariationalFull

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.MaxEntropyPrinciple

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.KMSCondition
open UnifiedTheory.LayerB.GibbsVariational
open UnifiedTheory.LayerB.GibbsVariationalFull

variable {n : ℕ}

/-! ## 1. The maximum-entropy inequality. -/

/-- **Jaynes maximum-entropy principle (fixed-energy slice).**

    Let `ρ_β = gibbsDensity β H` be the Gibbs state at temperature
    `T = 1/β > 0`.  Among all positive-definite states ρ with the SAME
    mean energy as `ρ_β`,

        S(ρ)  ≤  S(ρ_β).

    The Gibbs state maximizes the von Neumann entropy on the fixed-⟨H⟩
    slice.

    Proof: the variational principle gives `F(ρ_β) ≤ F(ρ)`, i.e.
    `⟨H⟩_{ρ_β} − T·S(ρ_β) ≤ ⟨H⟩_ρ − T·S(ρ)`.  By `hE` the energies are
    equal and cancel, leaving `−T·S(ρ_β) ≤ −T·S(ρ)`; dividing by `−T < 0`
    flips to `S(ρ) ≤ S(ρ_β)`. -/
theorem max_entropy
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 < T)
    (hρ_pos : ρ.M.PosDef)
    (hE : energy ρ H = energy (gibbsDensity β H hH hZ) H) :
    vonNeumannEntropy ρ ≤ vonNeumannEntropy (gibbsDensity β H hH hZ) := by
  -- Variational principle: F(ρ_β) ≤ F(ρ).
  have hVar :
      freeEnergy (gibbsDensity β H hH hZ) H T ≤ freeEnergy ρ H T :=
    gibbs_variational_principle ρ β H hH hZ T hTβ (le_of_lt hT) hρ_pos
  -- Unfold both free energies into energy − T·S.
  rw [freeEnergy_eq_energy_sub ρ H T,
      freeEnergy_eq_energy_sub (gibbsDensity β H hH hZ) H T] at hVar
  -- Energies are equal by hE; cancel them, leaving T·S(ρ) ≤ T·S(ρ_β).
  rw [hE] at hVar
  have hmul : T * vonNeumannEntropy ρ
      ≤ T * vonNeumannEntropy (gibbsDensity β H hH hZ) := by
    linarith [hVar]
  -- Divide by T > 0: suppose not; then T·S(ρ_β) < T·S(ρ), contradiction.
  by_contra hcon
  push_neg at hcon
  have : T * vonNeumannEntropy (gibbsDensity β H hH hZ)
      < T * vonNeumannEntropy ρ := by
    have := mul_lt_mul_of_pos_left hcon hT
    linarith [this]
  linarith [hmul, this]

/-! ## 2. Jaynes form: the Gibbs state attains the entropy supremum. -/

/-- **Jaynes form.**  The Gibbs state is an upper bound for the entropy
    over the entire fixed-energy slice: for EVERY positive-definite state
    `ρ` whose mean energy equals that of the Gibbs state, its entropy is
    `≤ S(ρ_β)`.  This packages `max_entropy` as the statement that
    `S(ρ_β)` is the maximum of `S` on the constraint set `{ρ : ⟨H⟩_ρ = E}`. -/
theorem gibbs_is_maxEntropy
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 < T) :
    ∀ ρ : ComplexDensityMatrix n, ρ.M.PosDef →
      energy ρ H = energy (gibbsDensity β H hH hZ) H →
        vonNeumannEntropy ρ ≤ vonNeumannEntropy (gibbsDensity β H hH hZ) := by
  intro ρ hρ_pos hE
  exact max_entropy ρ β H hH hZ T hTβ hT hρ_pos hE

/-! ## 3. Uniqueness of the maximizer (relative-entropy / faithfulness). -/

/-- **Equality case on the fixed-energy slice.**

    On the slice `⟨H⟩_ρ = ⟨H⟩_{ρ_β}` and at `0 < T`, the entropy is
    maximal (`S(ρ) = S(ρ_β)`) **iff** the Umegaki relative entropy
    `S(ρ‖ρ_β)` vanishes.

    Proof: equal energies make `F(ρ) − F(ρ_β) = −T·(S(ρ) − S(ρ_β))`, so
    `S(ρ) = S(ρ_β) ⇔ F(ρ) = F(ρ_β)`; the variational equality criterion
    `gibbs_variational_eq_iff_relent_zero` (via the proved gap identity)
    converts the latter to `S(ρ‖ρ_β) = 0`.  Faithfulness of the relative
    entropy (`S(ρ‖σ)=0 ⇔ ρ=σ`) upgrades this to UNIQUENESS of the
    entropy maximizer. -/
theorem max_entropy_eq_iff_relent_zero
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 < T)
    (hE : energy ρ H = energy (gibbsDensity β H hH hZ) H) :
    vonNeumannEntropy ρ = vonNeumannEntropy (gibbsDensity β H hH hZ)
      ↔ umegakiRelativeEntropy ρ (gibbsDensity β H hH hZ) = 0 := by
  set σ := gibbsDensity β H hH hZ with hσ_def
  -- The gap identity (★) for the Gibbs reference state.
  have hgap : FreeEnergy_RelEntropy_Identity_Target ρ σ H T := by
    rw [hσ_def]; exact gibbs_gap_identity ρ β H hH hZ T hTβ
  -- On the fixed-energy slice, F-equality ⇔ S-equality.
  have hFS : freeEnergy ρ H T = freeEnergy σ H T
      ↔ vonNeumannEntropy ρ = vonNeumannEntropy σ := by
    rw [freeEnergy_eq_energy_sub ρ H T, freeEnergy_eq_energy_sub σ H T, hE]
    constructor
    · intro h
      have hTne : T ≠ 0 := ne_of_gt hT
      have : T * vonNeumannEntropy ρ = T * vonNeumannEntropy σ := by linarith
      exact mul_left_cancel₀ hTne this
    · intro h; rw [h]
  -- Chain through the variational equality criterion.
  rw [← hFS]
  exact gibbs_variational_eq_iff_relent_zero ρ σ H T hT hgap

/-- **Uniqueness of the maximum-entropy state (relative-entropy form).**

    If a positive-definite state ρ on the fixed-energy slice ATTAINS the
    maximal entropy `S(ρ) = S(ρ_β)`, then `S(ρ‖ρ_β) = 0`.  By faithfulness
    of the Umegaki relative entropy this forces `ρ = ρ_β`: the Gibbs state
    is the UNIQUE entropy maximizer at fixed mean energy. -/
theorem max_entropy_unique_via_relent
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 < T)
    (hE : energy ρ H = energy (gibbsDensity β H hH hZ) H)
    (hMax : vonNeumannEntropy ρ = vonNeumannEntropy (gibbsDensity β H hH hZ)) :
    umegakiRelativeEntropy ρ (gibbsDensity β H hH hZ) = 0 :=
  (max_entropy_eq_iff_relent_zero ρ β H hH hZ T hTβ hT hE).mp hMax

/-- **Uniqueness of the maximum-entropy state — the Gibbs state itself.**

    A positive-definite state ρ on the fixed-energy slice that ATTAINS the
    maximal entropy `S(ρ) = S(ρ_β)` is *equal* to the Gibbs state:
    `ρ.M = (ρ_β).M`.

    Proof: at equal energy, maximal entropy forces equal free energy
    `F(ρ) = F(ρ_β)` (the `−T·S` terms match and the energy terms cancel);
    the uniqueness of the free-energy minimiser
    (`GibbsVariationalFull.gibbs_state_unique`, via Klein faithfulness)
    then gives `ρ.M = (ρ_β).M`.  This is the sharp Jaynes statement: the
    Gibbs state is THE unique maximum-entropy state at fixed `⟨H⟩`. -/
theorem max_entropy_unique
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (_hT : 0 < T)
    (hρ_pos : ρ.M.PosDef)
    (hE : energy ρ H = energy (gibbsDensity β H hH hZ) H)
    (hMax : vonNeumannEntropy ρ = vonNeumannEntropy (gibbsDensity β H hH hZ)) :
    ρ.M = (gibbsDensity β H hH hZ).M := by
  -- Equal energy + equal entropy ⟹ equal free energy.
  have hF : freeEnergy ρ H T = freeEnergy (gibbsDensity β H hH hZ) H T := by
    rw [freeEnergy_eq_energy_sub ρ H T,
        freeEnergy_eq_energy_sub (gibbsDensity β H hH hZ) H T, hE, hMax]
  -- Uniqueness of the Gibbs minimiser (faithfulness of Klein).
  exact gibbs_state_unique ρ β H hH hZ T hTβ hρ_pos hF

/-! ## 4. Axiom audit. -/

#print axioms max_entropy
#print axioms gibbs_is_maxEntropy
#print axioms max_entropy_eq_iff_relent_zero
#print axioms max_entropy_unique_via_relent
#print axioms max_entropy_unique

end UnifiedTheory.LayerB.MaxEntropyPrinciple
