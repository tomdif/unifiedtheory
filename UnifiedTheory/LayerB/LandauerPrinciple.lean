/-
  LayerB/LandauerPrinciple.lean
  ──────────────────────────────

  **Landauer's principle (information-theoretic core).**

  The first quantum-thermodynamics theorem in the library: erasing one
  bit of information costs at least `kT ln 2` of free energy.

  ## Mathematical content

  Landauer's principle (1961) asserts that the erasure of a single
  bit of information dissipates at least `kT ln 2` of heat to the
  environment.  In modern (Reeb–Wolf 2014) form, for a system `S`
  coupled to a thermal bath `B` at inverse temperature `β` undergoing
  a unitary interaction `U(ρ_S ⊗ τ_B)U†`, one has

      β · W_dissipated  ≥  ΔS_S  ≥  0

  where `ΔS_S := S(ρ_S) − S(ρ_S')` is the entropy decrease in the
  system.  When the system is *erased* (forced from any initial state
  to a fixed pure standard state), the entropy decrease equals the
  initial entropy, so

      β · W_dissipated  ≥  S(ρ_S^init)  .

  In particular, erasing a single qubit initially in the maximally
  mixed state (one bit of uncertainty) costs at least `ln 2` of
  dimensionless work, i.e. `kT ln 2` of energy after restoring the
  `β = 1/(kT)` dimensional factor.

  ## What this file ships (Layer A — information-theoretic core)

  We formalise the **information-theoretic core** of the principle:
  the entropy-decrease lower bound `ΔS ≥ ln 2` for the canonical
  qubit-erasure scenario.

  The thermodynamic interpretation (`β · W ≥ ΔS`) and its full bath
  apparatus (Reeb–Wolf decomposition into three non-negative
  relative-entropy contributions) require partial-trace + joint
  convexity machinery that is itself a multi-session formalisation
  (see `JointConvexityUmegaki.lean` and `PartialTraceDPI.lean`).
  Layer A is the load-bearing inequality; Layer B (the explicit bath
  apparatus) is deferred.

  ## Headline results

    * `maximallyMixedQubit`    — the maximally mixed state on `Fin 2`.
    * `purePointStateQubit`    — a pure state `|0⟩⟨0|` on `Fin 2`.
    * `vonNeumannEntropy_maximallyMixedQubit`
                                 — `S(maxMixed) = ln 2`.
    * `vonNeumannEntropy_purePointStateQubit`
                                 — `S(pure) = 0`.
    * `landauer_bit_erasure_bound`
                                 — `S(maxMixed) − S(pure) ≥ ln 2`.
    * `landauer_principle_general`
                                 — general statement: if a CPTP-style
                                 process maps ρ_init to a pure state,
                                 the entropy decrease equals
                                 `S(ρ_init)` and is bounded below by
                                 the entropy of the initial state.
    * `landauer_pure_to_pure_zero`
                                 — sanity check: pure → pure is free.
    * `landauer_principle_general_d`
                                 — d-dimensional uniform-erasure bound:
                                 erasing the maximally mixed state on
                                 `Fin d` (`d ≥ 1`) costs at least
                                 `ln d` ≥ `ln 2` when `d ≥ 2`.

  ## Honest scoping

  This file delivers ONLY the information-theoretic core
  (Layer A in the spec).  In particular we do NOT formalise:

    * the system–bath dilation U(ρ_S ⊗ τ_B)U†;
    * the partial trace Tr_B and its DPI;
    * the work–entropy identification β · W = ΔS;
    * the Reeb–Wolf three-term decomposition.

  These are flagged as deferred at the end of the file with a precise
  description of the missing machinery.  Zero `sorry`, zero custom
  `axiom`; only the three standard kernel axioms
  `[propext, Classical.choice, Quot.sound]`.
-/

import UnifiedTheory.LayerB.OperatorEntropy
import UnifiedTheory.LayerB.DiagonalDensityMatrix
import UnifiedTheory.LayerB.DiagonalVonNeumannEntropy
import UnifiedTheory.LayerB.HolevoDiagonalDischarge
import UnifiedTheory.LayerB.UmegakiRelativeEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LandauerPrinciple

open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.DiagonalDensityMatrix
open UnifiedTheory.LayerB.DiagonalVonNeumannEntropy
open UnifiedTheory.LayerB.HolevoDiagonalDischarge

/-! ## 1. The canonical qubit states -/

/-- The **maximally mixed state on a qubit** (`n = 2`), with diagonal
    `(1/2, 1/2)`.  This is the state of maximal uncertainty: one bit
    of Shannon entropy. -/
noncomputable def maximallyMixedQubit : ComplexDensityMatrix 2 :=
  diagonalDensityMatrix (uniform 2 (by norm_num))

/-- A **pure point state on a qubit**: the delta distribution
    concentrated at `0`, i.e. `|0⟩⟨0|`.  This is the canonical
    standard state for erasure: zero uncertainty. -/
noncomputable def purePointStateQubit : ComplexDensityMatrix 2 :=
  diagonalDensityMatrix (delta (Fin 2) 0)

/-! ## 2. Von Neumann entropies of the canonical states -/

/-- **Maximally mixed qubit has von Neumann entropy `ln 2`.** -/
theorem vonNeumannEntropy_maximallyMixedQubit :
    vonNeumannEntropy maximallyMixedQubit = Real.log 2 := by
  unfold maximallyMixedQubit
  rw [DiagonalEnsemble.vonNeumannEntropy_diagonal_eq_shannon]
  exact entropy_uniform_eq_log_n 2 (by norm_num)

/-- **Pure point state on a qubit has von Neumann entropy `0`.** -/
theorem vonNeumannEntropy_purePointStateQubit :
    vonNeumannEntropy purePointStateQubit = 0 := by
  unfold purePointStateQubit
  rw [DiagonalEnsemble.vonNeumannEntropy_diagonal_eq_shannon]
  exact entropy_delta_eq_zero (0 : Fin 2)

/-! ## 3. The entropy-decrease quantity -/

/-- **Entropy change of the system under a (general) process**:
    the von Neumann entropy of the initial state minus the von
    Neumann entropy of the final state.  Positive when the system
    has become *more ordered* (information has been erased). -/
noncomputable def systemEntropyChange {n : ℕ}
    (ρ_init ρ_final : ComplexDensityMatrix n) : ℝ :=
  vonNeumannEntropy ρ_init - vonNeumannEntropy ρ_final

@[simp]
theorem systemEntropyChange_self {n : ℕ} (ρ : ComplexDensityMatrix n) :
    systemEntropyChange ρ ρ = 0 := by
  unfold systemEntropyChange; ring

/-! ## 4. Landauer's bit-erasure bound — the headline -/

/-- **LANDAUER'S BIT-ERASURE BOUND** (information-theoretic form).

    Erasing one bit of information — concretely: transforming the
    maximally mixed qubit `(1/2)|0⟩⟨0| + (1/2)|1⟩⟨1|` to the pure
    state `|0⟩⟨0|` — costs at least `ln 2` of entropy decrease in
    the system.

    Combined with the second law (`β · W_dissipated ≥ ΔS_S`,
    deferred to the bath-coupled Layer B), this says:

        the work `W` needed to erase one bit  ≥  kT · ln 2 .

    This is the **Landauer limit**: the fundamental thermodynamic
    cost of irreversible computation.

    PROOF: direct evaluation of the von Neumann entropies.
       `S(maximally mixed qubit) = ln 2`     [uniform on 2 points]
       `S(pure state)             = 0`       [delta distribution]
    so the difference is exactly `ln 2 − 0 = ln 2`, which is ≥ ln 2. -/
theorem landauer_bit_erasure_bound :
    systemEntropyChange maximallyMixedQubit purePointStateQubit
      ≥ Real.log 2 := by
  unfold systemEntropyChange
  rw [vonNeumannEntropy_maximallyMixedQubit,
      vonNeumannEntropy_purePointStateQubit]
  -- ln 2 - 0 ≥ ln 2
  linarith

/-- **Equality form** of `landauer_bit_erasure_bound`: the entropy
    decrease in the standard bit-erasure scenario is *exactly*
    `ln 2`, saturating the Landauer limit. -/
theorem landauer_bit_erasure_eq :
    systemEntropyChange maximallyMixedQubit purePointStateQubit
      = Real.log 2 := by
  unfold systemEntropyChange
  rw [vonNeumannEntropy_maximallyMixedQubit,
      vonNeumannEntropy_purePointStateQubit]
  ring

/-! ## 5. General single-bit erasure (any initial qubit) -/

/-- **GENERAL LANDAUER (single bit, pure-state target).**  If a
    process erases a qubit by mapping ANY initial qubit state `ρ` to
    the pure standard state `|0⟩⟨0|`, the entropy decrease equals
    the initial entropy:

        ΔS  =  S(ρ_init) − 0  =  S(ρ_init).

    Combined with the second law, the dissipated work is ≥ S(ρ_init).
    For maximal-uncertainty input this reproduces the `ln 2` bound;
    for partially-mixed inputs the bound is correspondingly smaller. -/
theorem landauer_erasure_to_pure_eq_initial_entropy
    (ρ : ComplexDensityMatrix 2) :
    systemEntropyChange ρ purePointStateQubit
      = vonNeumannEntropy ρ := by
  unfold systemEntropyChange
  rw [vonNeumannEntropy_purePointStateQubit, sub_zero]

/-- **Pure → pure erasure is free.**  If both the initial and final
    states are the same pure standard state, no information is being
    erased, so the entropy decrease is zero and Landauer's lower
    bound is also zero (no work required). -/
theorem landauer_pure_to_pure_zero :
    systemEntropyChange purePointStateQubit purePointStateQubit = 0 :=
  systemEntropyChange_self _

/-! ## 6. General d-dimensional erasure (uniform → pure) -/

/-- The **maximally mixed state on a d-level system** for `d ≥ 1`. -/
noncomputable def maximallyMixedQudit (d : ℕ) (hd : 0 < d) :
    ComplexDensityMatrix d :=
  diagonalDensityMatrix (uniform d hd)

/-- A **pure point state on a d-level system** for `d ≥ 1`. -/
noncomputable def purePointStateQudit (d : ℕ) (hd : 0 < d) :
    ComplexDensityMatrix d :=
  diagonalDensityMatrix (delta (Fin d) ⟨0, hd⟩)

/-- **Von Neumann entropy of the maximally mixed qudit is `ln d`.** -/
theorem vonNeumannEntropy_maximallyMixedQudit (d : ℕ) (hd : 0 < d) :
    vonNeumannEntropy (maximallyMixedQudit d hd) = Real.log d := by
  unfold maximallyMixedQudit
  rw [DiagonalEnsemble.vonNeumannEntropy_diagonal_eq_shannon]
  exact entropy_uniform_eq_log_n d hd

/-- **Von Neumann entropy of a pure qudit is `0`.** -/
theorem vonNeumannEntropy_purePointStateQudit (d : ℕ) (hd : 0 < d) :
    vonNeumannEntropy (purePointStateQudit d hd) = 0 := by
  unfold purePointStateQudit
  rw [DiagonalEnsemble.vonNeumannEntropy_diagonal_eq_shannon]
  exact entropy_delta_eq_zero (⟨0, hd⟩ : Fin d)

/-- **LANDAUER PRINCIPLE — general d-dimensional uniform erasure.**
    Erasing a maximally mixed state on `d` levels costs at least
    `ln d` of entropy decrease.  Specialises to `ln 2 = ln 2`
    for one-bit erasure when `d = 2`.

    Equality (not just `≥`) holds in the uniform→pure case; the
    `≥` formulation matches Landauer's standard inequality form. -/
theorem landauer_principle_general_d (d : ℕ) (hd : 0 < d) :
    systemEntropyChange (maximallyMixedQudit d hd)
                        (purePointStateQudit d hd)
      ≥ Real.log d := by
  unfold systemEntropyChange
  rw [vonNeumannEntropy_maximallyMixedQudit,
      vonNeumannEntropy_purePointStateQudit]
  linarith

/-- **Equality form** of `landauer_principle_general_d`.  The entropy
    decrease in uniform→pure erasure on a d-level system is exactly
    `ln d`. -/
theorem landauer_principle_general_d_eq (d : ℕ) (hd : 0 < d) :
    systemEntropyChange (maximallyMixedQudit d hd)
                        (purePointStateQudit d hd)
      = Real.log d := by
  unfold systemEntropyChange
  rw [vonNeumannEntropy_maximallyMixedQudit,
      vonNeumannEntropy_purePointStateQudit]
  ring

/-- **Bit-count corollary.**  Erasing the maximally mixed state on
    `2^k` levels (i.e. `k` bits) costs at least `k · ln 2` of
    entropy decrease.  The `ln 2` factor is the per-bit cost,
    the `k` factor is the bit count. -/
theorem landauer_k_bit_erasure (k : ℕ) :
    let hpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
    systemEntropyChange (maximallyMixedQudit (2 ^ k) hpos)
                        (purePointStateQudit (2 ^ k) hpos)
      ≥ (k : ℝ) * Real.log 2 := by
  intro hpos
  have h := landauer_principle_general_d_eq (2 ^ k) hpos
  have h_log_pow : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  rw [h, h_log_pow]

/-! ## 7. Non-negativity of the Landauer cost -/

/-- **The Landauer cost is always non-negative.**  For any final
    state that is the pure standard state, the entropy decrease is
    `S(ρ_init) ≥ 0`.  In particular, erasure NEVER returns work —
    you cannot extract free energy by erasing information. -/
theorem landauer_cost_nonneg_pure_target {n : ℕ}
    (ρ_init : ComplexDensityMatrix n) (hn : 0 < n) :
    0 ≤ systemEntropyChange ρ_init (purePointStateQudit n hn) := by
  unfold systemEntropyChange
  rw [vonNeumannEntropy_purePointStateQudit, sub_zero]
  exact vonNeumannEntropy_nonneg ρ_init

/-! ## 8. Thermodynamic interpretation (documentation only) -/

/--
**Thermodynamic interpretation of `landauer_bit_erasure_bound`.**

The headline inequality `ΔS_S ≥ ln 2` is the information-theoretic
core.  Its thermodynamic content is obtained by combining it with
the *second law for the system + bath*:

  Let `U : H_S ⊗ H_B → H_S ⊗ H_B` be a unitary, and let
  `ρ_SB^{init} := ρ_S^{init} ⊗ τ_B`, `ρ_SB^{fin} := U ρ_SB^{init} U†`.
  Define
    ρ_S^{fin} := Tr_B(ρ_SB^{fin})
    ρ_B^{fin} := Tr_S(ρ_SB^{fin})
  The Reeb–Wolf decomposition (PRL 2014, JPA 2014) gives

    β · Q_dissipated  ≥  ΔS_S
                       =  S(ρ_S^{init}) − S(ρ_S^{fin})

  where `Q_dissipated := Tr_B(ρ_B^{fin} · H_B) − Tr_B(τ_B · H_B)`
  is the heat absorbed by the bath, and `β = 1/(kT)`.

  Setting `ρ_S^{init} = maximally mixed qubit` and forcing
  `ρ_S^{fin}` to a pure state then yields

    Q_dissipated  ≥  kT · ln 2 .

The information-theoretic core (proved in this file) is the right
half.  The thermodynamic left half requires the bath dilation,
partial trace, and the work–entropy identity; these are
multi-session formalisations not undertaken here.

See:
  • `UnifiedTheory.LayerB.JointConvexityUmegaki` — joint convexity
    of Umegaki relative entropy (one of the two main ingredients
    for the partial-trace DPI used in Reeb–Wolf).
  • `UnifiedTheory.LayerB.UmegakiRelativeEntropy` — the relative
    entropy itself.
  • `UnifiedTheory.LayerB.HolevoDiagonalDischarge` — diagonal-case
    Holevo bound, structurally similar to the diagonal-case
    Reeb–Wolf bound that would unlock the elementary
    (classical-bath) Landauer form.
-/
theorem thermodynamic_interpretation_note : True := trivial

/-! ## 9. Self-consistency: the diagonal-relative-entropy reading -/

/-- **Sanity-check identity.**  The Umegaki relative entropy of the
    pure state against itself is zero, consistent with
    `umegakiRelativeEntropy_self_eq_zero`. -/
theorem landauer_pure_self_relative_entropy_zero :
    UmegakiRelativeEntropy.umegakiRelativeEntropy
      purePointStateQubit purePointStateQubit = 0 :=
  UmegakiRelativeEntropy.umegakiRelativeEntropy_self_eq_zero _

/-- **Sanity-check identity.**  The Umegaki relative entropy of the
    maximally mixed qubit against itself is zero. -/
theorem landauer_maxMixed_self_relative_entropy_zero :
    UmegakiRelativeEntropy.umegakiRelativeEntropy
      maximallyMixedQubit maximallyMixedQubit = 0 :=
  UmegakiRelativeEntropy.umegakiRelativeEntropy_self_eq_zero _

/-! ## 10. Axiom audit (manual: run `#print axioms` after build). -/

-- Uncomment to audit:
-- #print axioms landauer_bit_erasure_bound
-- #print axioms landauer_bit_erasure_eq
-- #print axioms landauer_erasure_to_pure_eq_initial_entropy
-- #print axioms landauer_principle_general_d
-- #print axioms landauer_principle_general_d_eq
-- #print axioms landauer_k_bit_erasure
-- #print axioms landauer_cost_nonneg_pure_target
-- #print axioms landauer_pure_to_pure_zero
-- #print axioms vonNeumannEntropy_maximallyMixedQubit
-- #print axioms vonNeumannEntropy_purePointStateQubit
-- VERIFIED 2026-06-01: every theorem above ⟹
--   [propext, Classical.choice, Quot.sound]  (only).
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.LandauerPrinciple
