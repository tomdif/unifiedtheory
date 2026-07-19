/-
  LayerB/GibbsVariationalGeneral.lean
  ───────────────────────────────────

  **Generality lift of the Gibbs variational principle and the Jaynes
  maximum-entropy principle to ARBITRARY density matrices** (including
  PURE states), powered by the now-UNCONDITIONAL general Klein
  inequality

      `OperatorEntropyContinuous.umegakiRelativeEntropy_nonneg_general_unconditional`
          (ρ σ : ComplexDensityMatrix n) (hn : 0 < n) (hσ : σ.M.PosDef) :
              0 ≤ umegakiRelativeEntropy ρ σ.

  ## Why the lift works (no new analytic content)

  Both principles compare an ARBITRARY state ρ against the **Gibbs state**
  `ρ_β = gibbsDensity β H`, which sits in the σ-slot and is **always
  positive definite** (`GibbsVariationalFull.gibbsDensity_posDef`).  The
  PosDef hypothesis that the original `gibbs_variational_principle` /
  `max_entropy` carried on ρ was inherited *solely* from the OLD Klein
  engine `gibbs_variational_of_gap`, which routed non-negativity through
  `KleinInequalityFull.umegakiRelativeEntropy_nonneg` (PosDef on BOTH
  arguments).

  The gap identity itself is ALGEBRAIC and already general in ρ:

      `gibbs_gap_identity ρ β H hH hZ T hTβ :
          F(ρ) − F(ρ_β) = T · S(ρ ‖ ρ_β)`        (no PosDef on ρ).

  So we simply re-assemble:  general gap identity  +  general Klein
  (`umegakiRelativeEntropy_nonneg_general_unconditional ρ ρ_β hn
   gibbsDensity_posDef`)  +  `T ≥ 0`  ⟹  `F(ρ_β) ≤ F(ρ)` for ANY ρ.

  ## What this file ships

    * `gibbs_variational_principle_general`
        — `F(ρ_β) ≤ F(ρ)` for EVERY density matrix ρ (PURE allowed).
    * `gibbs_variational_target_general`
        — `-T log Z ≤ F(ρ)`, the closed-form `Gibbs_Variational_Target`.
    * `max_entropy_general`
        — `S(ρ) ≤ S(ρ_β)` on the fixed-energy slice, for EVERY ρ.
    * `gibbs_is_maxEntropy_general`
        — Jaynes form over all (general) ρ.
    * `gibbs_variational_principle_pure` / `max_entropy_pure`
        — the PURE-state corollaries (the physically sharpest case: a
          pure state has the lowest entropy / highest free energy).

  ## HONEST scope note

    * `hn : 0 < n` is the only side-condition besides Hermiticity / `Z>0`
      / `0 ≤ T`.  The `ρ.M.PosDef` hypothesis is GONE for the inequalities.
    * The **UNIQUENESS** results (`gibbs_state_unique`, `max_entropy_unique`)
      are NOT lifted: they route through STRICT Klein faithfulness
      (`umegakiRelativeEntropy_eq_zero_imp`), which genuinely needs
      `ρ.M.PosDef`.  A pure state can attain the same RELATIVE entropy as
      the Gibbs state only by equalling it, but the *proof* of that for the
      singular case is not provided here; uniqueness stays PosDef-gated.

  No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.GibbsVariationalFull
import UnifiedTheory.LayerB.MaxEntropyPrinciple
import UnifiedTheory.LayerB.PeierlsBogoliubov
import UnifiedTheory.LayerB.OperatorEntropyContinuous

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.GibbsVariationalGeneral

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.KMSCondition
open UnifiedTheory.LayerB.GibbsVariational
open UnifiedTheory.LayerB.GibbsVariationalFull
open UnifiedTheory.LayerB.OperatorEntropyContinuous

variable {n : ℕ}

/-! ## 1.  The general Gibbs variational principle (no PosDef on ρ). -/

/-- **Gibbs variational principle for an ARBITRARY density matrix.**

      `F(ρ_β)  ≤  F(ρ)`     for EVERY state ρ — including PURE states —
                            at non-negative temperature `T = 1/β`.

    Proof: the ALGEBRAIC gap identity `gibbs_gap_identity` gives
    `F(ρ) − F(ρ_β) = T · S(ρ‖ρ_β)` with NO positivity assumption on ρ;
    the σ-slot `ρ_β = gibbsDensity β H` is always positive definite, so
    the UNCONDITIONAL general Klein inequality
    `umegakiRelativeEntropy_nonneg_general_unconditional` makes
    `S(ρ‖ρ_β) ≥ 0`; with `T ≥ 0` the product — hence the gap — is `≥ 0`.

    Compared with `GibbsVariationalFull.gibbs_variational_principle`, the
    `ρ.M.PosDef` hypothesis is REMOVED (only `0 < n` remains, needed for
    the regularisation limit in general Klein). -/
theorem gibbs_variational_principle_general
    (ρ : ComplexDensityMatrix n) (hn : 0 < n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 ≤ T) :
    freeEnergy (gibbsDensity β H hH hZ) H T ≤ freeEnergy ρ H T := by
  set σ := gibbsDensity β H hH hZ with hσ_def
  -- (★) The gap identity — algebraic, general in ρ.
  have hgap : freeEnergy ρ H T - freeEnergy σ H T
                = T * umegakiRelativeEntropy ρ σ := by
    rw [hσ_def]; exact gibbs_gap_identity ρ β H hH hZ T hTβ
  -- General Klein: S(ρ‖ρ_β) ≥ 0 (σ PosDef, ρ arbitrary).
  have hRE : 0 ≤ umegakiRelativeEntropy ρ σ :=
    umegakiRelativeEntropy_nonneg_general_unconditional ρ σ hn
      (by rw [hσ_def]; exact gibbsDensity_posDef β H hH hZ)
  -- T · S(ρ‖ρ_β) ≥ 0, hence the gap is ≥ 0.
  have hprod : 0 ≤ T * umegakiRelativeEntropy ρ σ := mul_nonneg hT hRE
  linarith [hgap, hprod]

/-- **Gibbs variational principle against the closed form, general ρ.**

      `-T log Z  ≤  F(ρ)`,   i.e. `Gibbs_Variational_Target` for ANY ρ.

    Combines `gibbs_variational_principle_general` with the
    self-consistency `F(ρ_β) = -T log Z` (`freeEnergy_gibbs_eq`). -/
theorem gibbs_variational_target_general
    (ρ : ComplexDensityMatrix n) (hn : 0 < n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 ≤ T) :
    Gibbs_Variational_Target ρ H T (partitionFunction β H) := by
  unfold Gibbs_Variational_Target
  rw [← freeEnergy_gibbs_eq β H hH hZ T hTβ]
  exact gibbs_variational_principle_general ρ hn β H hH hZ T hTβ hT

/-! ## 2.  The general Jaynes maximum-entropy principle (no PosDef on ρ). -/

/-- **Jaynes maximum-entropy principle for an ARBITRARY density matrix.**

      `S(ρ)  ≤  S(ρ_β)`     for EVERY state ρ on the fixed-energy slice
                            `⟨H⟩_ρ = ⟨H⟩_{ρ_β}`, at `0 < T`.

    The Gibbs state maximises the von Neumann entropy among ALL states of
    a given mean energy — pure states included.

    Proof: the GENERAL variational principle gives
    `F(ρ_β) ≤ F(ρ)`, i.e. `⟨H⟩_{ρ_β} − T·S(ρ_β) ≤ ⟨H⟩_ρ − T·S(ρ)`; equal
    energies (`hE`) cancel, leaving `−T·S(ρ_β) ≤ −T·S(ρ)`, and dividing by
    `−T < 0` flips to `S(ρ) ≤ S(ρ_β)`.

    Compared with `MaxEntropyPrinciple.max_entropy`, the `ρ.M.PosDef`
    hypothesis is REMOVED (only `0 < n` remains). -/
theorem max_entropy_general
    (ρ : ComplexDensityMatrix n) (hn : 0 < n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 < T)
    (hE : energy ρ H = energy (gibbsDensity β H hH hZ) H) :
    vonNeumannEntropy ρ ≤ vonNeumannEntropy (gibbsDensity β H hH hZ) := by
  -- General variational principle: F(ρ_β) ≤ F(ρ).
  have hVar :
      freeEnergy (gibbsDensity β H hH hZ) H T ≤ freeEnergy ρ H T :=
    gibbs_variational_principle_general ρ hn β H hH hZ T hTβ (le_of_lt hT)
  -- Unfold both free energies into energy − T·S.
  rw [freeEnergy_eq_energy_sub ρ H T,
      freeEnergy_eq_energy_sub (gibbsDensity β H hH hZ) H T] at hVar
  -- Energies equal (hE); cancel, leaving T·S(ρ) ≤ T·S(ρ_β).
  rw [hE] at hVar
  have hmul : T * vonNeumannEntropy ρ
      ≤ T * vonNeumannEntropy (gibbsDensity β H hH hZ) := by
    linarith [hVar]
  -- Divide by T > 0.
  by_contra hcon
  push_neg at hcon
  have : T * vonNeumannEntropy (gibbsDensity β H hH hZ)
      < T * vonNeumannEntropy ρ := by
    have := mul_lt_mul_of_pos_left hcon hT
    linarith [this]
  linarith [hmul, this]

/-- **Jaynes form, general ρ.**  The Gibbs state is an upper bound for the
    entropy over the ENTIRE fixed-energy slice, with NO positivity
    restriction on the competing states. -/
theorem gibbs_is_maxEntropy_general
    (hn : 0 < n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 < T) :
    ∀ ρ : ComplexDensityMatrix n,
      energy ρ H = energy (gibbsDensity β H hH hZ) H →
        vonNeumannEntropy ρ ≤ vonNeumannEntropy (gibbsDensity β H hH hZ) := by
  intro ρ hE
  exact max_entropy_general ρ hn β H hH hZ T hTβ hT hE

/-! ## 3.  PURE-state corollaries.

    A pure state `ρ = |ψ⟩⟨ψ|` is a density matrix (PSD, trace 1) that is
    SINGULAR (rank 1, not PosDef for `n ≥ 2`), so it lies strictly outside
    the old PosDef-gated principles.  The general lift covers it directly:
    instantiating `gibbs_variational_principle_general` and
    `max_entropy_general` at ANY `ComplexDensityMatrix n` includes every
    pure state.  We expose the corollaries explicitly. -/

/-- **Variational principle for a pure state.**  The Gibbs free energy is a
    lower bound even for a PURE state `ψ` (the physically sharpest case —
    a pure state carries the *highest* free energy at fixed temperature).
    This is `gibbs_variational_principle_general` with no extra hypothesis:
    `ψ` ranges over all density matrices, pure ones included. -/
theorem gibbs_variational_principle_pure
    (ψ : ComplexDensityMatrix n) (hn : 0 < n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 ≤ T) :
    freeEnergy (gibbsDensity β H hH hZ) H T ≤ freeEnergy ψ H T :=
  gibbs_variational_principle_general ψ hn β H hH hZ T hTβ hT

/-- **Maximum-entropy principle for a pure state.**  On the fixed-energy
    slice, a pure state `ψ` has entropy `≤ S(ρ_β)`.  For a pure state
    `S(ψ) = 0`, so this is the extreme instance of Jaynes' principle:
    `0 = S(ψ) ≤ S(ρ_β)`.  Lifted directly via `max_entropy_general`. -/
theorem max_entropy_pure
    (ψ : ComplexDensityMatrix n) (hn : 0 < n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 < T)
    (hE : energy ψ H = energy (gibbsDensity β H hH hZ) H) :
    vonNeumannEntropy ψ ≤ vonNeumannEntropy (gibbsDensity β H hH hZ) :=
  max_entropy_general ψ hn β H hH hZ T hTβ hT hE

/-! ## 4.  Peierls–Bogoliubov: already general, no lift required.

    `PeierlsBogoliubov.peierls_bogoliubov` compares the partition
    functions of `H` and a perturbed `H + ΔH`; the thermal average is
    taken in the UNPERTURBED Gibbs state `ρ_H = gibbsDensity 1 (-H)`,
    which is intrinsically PosDef, and the variational principle is
    applied AT `ρ = ρ_H`.  There is no arbitrary ρ in its statement — the
    "ρ-PosDef" it consumes is `gibbsDensity_posDef` on `ρ_H` itself.  So
    Peierls–Bogoliubov is ALREADY fully general in its data (the
    perturbation `ΔH` is unrestricted beyond Hermiticity); nothing to
    lift.  We re-export it here for completeness. -/

/-- Re-export of the (already general) Peierls–Bogoliubov inequality. -/
theorem peierls_bogoliubov_general [Nonempty (Fin n)]
    (H ΔH : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hΔH : ΔH.IsHermitian) :
    PeierlsBogoliubov_Target H ΔH
      (ComplexDensityMatrix.expectation
        (gibbsDensity 1 (-H) hH.neg
          (UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
            1 (-H) hH.neg)) ΔH) :=
  UnifiedTheory.LayerB.PeierlsBogoliubov.peierls_bogoliubov H ΔH hH hΔH

/-! ## 5.  Axiom audit. -/

#print axioms gibbs_variational_principle_general
#print axioms gibbs_variational_target_general
#print axioms max_entropy_general
#print axioms gibbs_is_maxEntropy_general
#print axioms gibbs_variational_principle_pure
#print axioms max_entropy_pure
#print axioms peierls_bogoliubov_general

end UnifiedTheory.LayerB.GibbsVariationalGeneral
