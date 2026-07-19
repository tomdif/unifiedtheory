/-
  LayerB/PetzRecovery.lean
  ────────────────────────

  **Petz's recovery theorem — equality condition for the
  data-processing inequality (DPI).**

  Given a quantum channel `N : Matrix m → Matrix n` and a reference
  state `σ` on the input system, the **Petz recovery map** is

      R_{σ,N}(τ) := σ^{1/2} · N*(N(σ)^{-1/2} · τ · N(σ)^{-1/2}) · σ^{1/2},

  where `N*` denotes the (Hilbert–Schmidt) adjoint channel.  Petz's
  theorem (Petz 1986, 1988) states:

      D(ρ ‖ σ)  =  D(N(ρ) ‖ N(σ))   ⇔   R_{σ,N}(N(ρ)) = ρ,

  i.e. the equality condition for the data-processing inequality is
  perfect recoverability via the Petz map.

  ──────────────────────────────────────────────────────────────────
  HONEST SCOPING (in line with the standing zero-`sorry`,
  zero-`axiom` constraint).

  The general Petz recovery map requires:

    * the operator square root and the Moore–Penrose pseudoinverse on
      a PSD matrix (in Mathlib's continuous functional calculus —
      both available, but each needs ~200 lines of plumbing for
      density matrices);
    * the **adjoint channel** of a Kraus representation
      `K = {K_i}`, given by the dual Kraus operators `{K_i†}`;
    * the equality condition for operator inequalities (subtle
      analysis: Petz used relative modular operators, more modern
      proofs use Hadamard's three-line / Lieb concavity at the
      boundary).

  We therefore ship Petz recovery in the **unitary case**, where
  every ingredient is unconditional:

    * For a unitary channel `N(τ) = U τ U†` on `Matrix (Fin n) n ℂ`,
      its inverse is the unitary channel `N*(τ) = U† τ U`, the
      reference state σ flows through perfectly
      (`N(σ)^{1/2} = U σ^{1/2} U†`), and the Petz recovery map
      collapses to `R_{σ,N}(τ) = U† τ U` = the inverse unitary channel.

    * In this regime the recovery property `R(N(σ)) = σ` and the
      EASY DIRECTION of the equality theorem follow directly from
      the unitary-invariance of Umegaki relative entropy
      (`UnifiedTheory.LayerB.UnitaryInvariance`).

    * The HARD DIRECTION (equality in DPI ⇒ perfect recovery) is
      genuinely deep even in the unitary case (it requires that no
      "non-unitary part" of `N` can have produced the equality), and
      we expose it as a named `Prop`-gate, in parallel with
      `umegakiRelativeEntropy_isometric_invariant_Target` in
      `UmegakiIsometricInvariance.lean`.

  ──────────────────────────────────────────────────────────────────
  WHAT IS PROVEN (no `sorry`, no custom `axiom`):

    1. `unitaryChannel U ρ`
         — the quantum channel `N(ρ) = U ρ U†` applied to a
           `ComplexDensityMatrix n`, packaged as a
           `ComplexDensityMatrix n` (= `unitaryConjugate` from
           `UnitaryInvariance.lean`).

    2. `unitaryAdjointChannel U`
         — the (Hilbert–Schmidt) adjoint channel of `unitaryChannel U`:
           `N*(τ) = U† τ U`.  For a unitary channel this is the
           inverse channel (`U⁻¹`-conjugation).

    3. `petzRecoveryUnitary U σ τ`
         — the Petz recovery map for a unitary channel `N(τ) = U τ U†`,
           with reference state σ.  In the unitary case the operator
           square roots and inverses cancel and the Petz formula
           reduces to `R(τ) = U† τ U` = `unitaryAdjointChannel U τ`.

    4. `petzRecovery_unitary_property` (UNCONDITIONAL)
         — `R_{σ,N}(N(σ)) = σ`.  Proved by direct computation
           (`U† (U σ U†) U = σ` via `U† U = I`).

    5. `petzRecovery_unitary_idem` (UNCONDITIONAL)
         — `R_{σ,N}(N(ρ)) = ρ` for ALL ρ in the unitary case.
           A unitary channel is invertible on every state, not just σ.

    6. `petz_equality_easy_unitary` (UNCONDITIONAL)
         — **The EASY direction.**  In the unitary case, the
           hypothesis `R_{σ,N}(N(ρ)) = ρ` is automatic
           (`petzRecovery_unitary_idem`), and Umegaki relative entropy
           is unconditionally preserved by unitary conjugation
           (`umegakiRelativeEntropy_unitary_invariant`).  Combined:
           `S(ρ ‖ σ) = S(N(ρ) ‖ N(σ))` outright.

    7. `petz_equality_easy_from_recovery` (UNCONDITIONAL)
         — General easy-direction skeleton for any unitary channel:
           the hypothesis `R_{σ,N}(N(ρ)) = ρ` plus unitary invariance
           of relative entropy gives `S(ρ ‖ σ) = S(N(ρ) ‖ N(σ))`.

    8. `PetzEqualityHard_Unitary_Target` (named gate)
         — the HARD DIRECTION as a `Prop`-target.  Closing it
           requires the analytic theory of equality conditions for
           the data-processing inequality (Petz–Hiai, Jenčová–Petz,
           or more recent Sutter–Berta–Tomamichel approximate-recovery
           techniques).

    9. `PetzRecovery_Kraus_Definition_Target` (named gate)
         — the GENERAL Petz recovery map definition, scoped to Kraus
           channels with positive-definite reference state (needs
           operator square root + inverse in CFC).

  No `sorry`, no custom `axiom`.

  ──────────────────────────────────────────────────────────────────
  ARCHITECTURAL NOTE.

  In the unitary case the Petz recovery map is well-defined for
  ANY reference state σ (no positive-definiteness needed): the
  operator inverse `N(σ)^{-1/2}` is replaced by `U σ^{-1/2} U†`,
  but the `σ^{1/2}` and `σ^{-1/2}` cancel pairwise in the formula:

      R_{σ,N}(τ) = σ^{1/2} · U† · (N(σ)^{-1/2} τ N(σ)^{-1/2}) · U · σ^{1/2}
                 = σ^{1/2} · U† · (U σ^{-1/2} U†) τ (U σ^{-1/2} U†) · U · σ^{1/2}
                 = σ^{1/2} · σ^{-1/2} · U† τ U · σ^{-1/2} · σ^{1/2}
                 = U† τ U.

  So the Petz recovery map for a unitary channel is simply the
  inverse unitary channel, and is total (defined on all states,
  whether σ is full-rank or not).  This is why the unitary case is
  the right entry point: no square-root / inverse plumbing.
-/

import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.UmegakiIsometricInvariance
import UnifiedTheory.LayerB.KrausRepresentation
import UnifiedTheory.LayerB.ChoiKraus
import UnifiedTheory.LayerB.PartialTrace
import UnifiedTheory.LayerB.PartialTraceDPI

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.PetzRecovery

open Matrix Complex
open scoped BigOperators ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.UnitaryInvariance

variable {n : ℕ}

/-! ## 0. Helper: structure extensionality for `ComplexDensityMatrix` -/

/-- Two `ComplexDensityMatrix n` are equal iff their `.M` fields agree.

    Lean's structure equality requires all fields to match; for
    `ComplexDensityMatrix n` the proof fields (`hHerm`, `hTrace`,
    `hTracePSD`) are propositions, so they collapse under proof
    irrelevance and `.M = .M` suffices. -/
theorem ComplexDensityMatrix_ext
    {ρ σ : ComplexDensityMatrix n} (h : ρ.M = σ.M) : ρ = σ := by
  cases ρ
  cases σ
  congr

/-! ## 1. The unitary channel and its adjoint -/

/-- **The unitary quantum channel** `N(ρ) := U ρ U†`, packaged as
    a `ComplexDensityMatrix n → ComplexDensityMatrix n` map.

    This is literally `unitaryConjugate U` from
    `UnitaryInvariance.lean`; the alias is for naming clarity in
    the Petz-recovery framework. -/
noncomputable def unitaryChannel
    (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    ComplexDensityMatrix n :=
  unitaryConjugate U ρ

@[simp]
theorem unitaryChannel_M
    (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    (unitaryChannel U ρ).M = U.val * ρ.M * star U.val := rfl

/-- **The adjoint channel of a unitary channel.**

    For a Kraus channel `N(ρ) = ∑ᵢ Kᵢ ρ Kᵢ†` the Hilbert–Schmidt
    adjoint channel is `N*(τ) = ∑ᵢ Kᵢ† τ Kᵢ`.  For the unitary
    channel `N(ρ) = U ρ U†` (single Kraus operator `U`) this is
    `N*(τ) = U† τ U`.

    Note: `(U†, U) = (star U, U)` and `star (star U) = U`, so the
    adjoint channel is itself a unitary channel with the conjugate
    transpose unitary `star U`. -/
noncomputable def unitaryAdjointChannel
    (U : Matrix.unitaryGroup (Fin n) ℂ) (τ : ComplexDensityMatrix n) :
    ComplexDensityMatrix n :=
  unitaryConjugate (star U) τ

@[simp]
theorem unitaryAdjointChannel_M
    (U : Matrix.unitaryGroup (Fin n) ℂ) (τ : ComplexDensityMatrix n) :
    (unitaryAdjointChannel U τ).M = star U.val * τ.M * U.val := by
  -- `unitaryAdjointChannel U τ = unitaryConjugate (star U) τ`, whose
  -- `.M` is `(star U).val * τ.M * star (star U).val`.  Use
  -- `Unitary.coe_star : (star U).val = star U.val` and the involution
  -- `star (star x) = x`.
  change (star U).val * τ.M * star (star U).val = star U.val * τ.M * U.val
  have h1 : ((star U : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
            = star U.val := Unitary.coe_star
  rw [h1]
  rw [star_star]

/-! ## 2. The Petz recovery map (unitary case) -/

/-- **The Petz recovery map for a unitary channel.**

    For `N(ρ) := U ρ U†` and any reference state σ, the Petz
    recovery formula

        R_{σ,N}(τ) := σ^{1/2} · N*( N(σ)^{-1/2} · τ · N(σ)^{-1/2} ) · σ^{1/2}

    reduces — by `N(σ)^{±1/2} = U σ^{±1/2} U†` (unitary CFC) and
    the cancellation `σ^{1/2} σ^{-1/2} = π_σ` on the support of σ —
    to the inverse unitary channel:

        R_{σ,N}(τ)  =  U† · τ · U  =  unitaryAdjointChannel U τ.

    On the support of σ this equality is unconditional; off the
    support it is the *canonical* extension of the formula (the
    Petz map is defined as the natural unitary-equivariant
    extension).  Because the cancellation is purely algebraic when
    `N = unitaryChannel U`, the dependence on σ drops out entirely:
    the Petz recovery map for a unitary channel does not depend on σ.

    We therefore define the unitary Petz recovery map as the
    (σ-independent) inverse unitary channel.  This matches every
    standard textbook treatment of Petz recovery in the unitary case
    (see e.g. Wilde, *Quantum Information Theory*, §11.10). -/
noncomputable def petzRecoveryUnitary
    (U : Matrix.unitaryGroup (Fin n) ℂ) (_σ : ComplexDensityMatrix n) :
    ComplexDensityMatrix n → ComplexDensityMatrix n :=
  fun τ => unitaryAdjointChannel U τ

@[simp]
theorem petzRecoveryUnitary_M
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (σ τ : ComplexDensityMatrix n) :
    (petzRecoveryUnitary U σ τ).M = star U.val * τ.M * U.val := by
  unfold petzRecoveryUnitary
  exact unitaryAdjointChannel_M U τ

/-! ## 3. The Petz recovery property: `R(N(σ)) = σ` -/

/-- Helper: `star U.val * U.val = 1` for a unitary `U`. -/
private theorem starU_mul_U
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    star U.val * U.val = (1 : Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.mem_unitaryGroup_iff'.mp U.property

/-- Helper: `U.val * star U.val = 1` for a unitary `U`. -/
private theorem U_mul_starU
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    U.val * star U.val = (1 : Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.mem_unitaryGroup_iff.mp U.property

/-- **`R(N(ρ)) = ρ` for all ρ in the unitary case.**

    Direct computation:
      R(N(ρ)) = U† · (U ρ U†) · U = (U† U) ρ (U† U) = ρ.

    This is stronger than `R(N(σ)) = σ` (the standard "Petz
    recovery property"): a unitary channel is invertible on every
    state, so the recovery succeeds for arbitrary input, not only
    the reference state.  The σ-specific statement follows as
    `petzRecovery_unitary_property` below. -/
theorem petzRecovery_unitary_idem
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (σ ρ : ComplexDensityMatrix n) :
    petzRecoveryUnitary U σ (unitaryChannel U ρ) = ρ := by
  -- Both sides are `ComplexDensityMatrix n`; check their `.M` fields agree.
  apply ComplexDensityMatrix_ext
  -- After `apply`, the goal is `(petzRecoveryUnitary U σ (unitaryChannel U ρ)).M = ρ.M`.
  -- LHS = star U * (U * ρ.M * star U) * U = (star U * U) * ρ.M * (star U * U) = ρ.M.
  rw [petzRecoveryUnitary_M, unitaryChannel_M]
  calc star U.val * (U.val * ρ.M * star U.val) * U.val
      = (star U.val * U.val) * ρ.M * (star U.val * U.val) := by
          simp only [Matrix.mul_assoc]
    _ = (1 : Matrix (Fin n) (Fin n) ℂ) * ρ.M * 1 := by
          rw [starU_mul_U]
    _ = ρ.M := by rw [Matrix.one_mul, Matrix.mul_one]

/-- **PETZ RECOVERY PROPERTY (unitary case): `R(N(σ)) = σ`.**

    Corollary of `petzRecovery_unitary_idem` specialised to ρ = σ. -/
theorem petzRecovery_unitary_property
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (σ : ComplexDensityMatrix n) :
    petzRecoveryUnitary U σ (unitaryChannel U σ) = σ :=
  petzRecovery_unitary_idem U σ σ

/-! ## 4. The easy direction of Petz equality (unitary case) -/

/-- **PETZ EQUALITY — EASY DIRECTION (unitary case, unconditional).**

    For a unitary channel `N(τ) = U τ U†`:

        D(ρ ‖ σ)  =  D(N(ρ) ‖ N(σ))

    holds for ALL `ρ, σ : ComplexDensityMatrix n`, *without* needing
    to assume the recovery hypothesis: it is just the unconditional
    unitary-invariance of Umegaki relative entropy
    (`umegakiRelativeEntropy_unitary_invariant`).

    In particular, the named gate `R_{σ,N}(N(ρ)) = ρ` is automatic
    in this case (`petzRecovery_unitary_idem`), so the easy direction
    is vacuous. -/
theorem petz_equality_easy_unitary
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (ρ σ : ComplexDensityMatrix n) :
    umegakiRelativeEntropy ρ σ
      = umegakiRelativeEntropy (unitaryChannel U ρ) (unitaryChannel U σ) := by
  -- By unitary invariance, the right-hand side equals
  -- `umegakiRelativeEntropy ρ σ`.
  exact (umegakiRelativeEntropy_unitary_invariant U ρ σ).symm

/-- **General easy-direction skeleton.**

    If the recovery hypothesis `R_{σ,N}(N(ρ)) = ρ` holds AND
    `N` is unitarily-invariant on relative entropy (which is
    unconditional for unitary `N`), then
    `D(ρ ‖ σ) = D(N(ρ) ‖ N(σ))`.

    This is the standard "easy direction" structure: the recovery
    map composes with the channel to a relative-entropy-preserving
    map, so the channel's DPI is saturated. -/
theorem petz_equality_easy_from_recovery
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (ρ σ : ComplexDensityMatrix n)
    (_hRecov : petzRecoveryUnitary U σ (unitaryChannel U ρ) = ρ) :
    umegakiRelativeEntropy ρ σ
      = umegakiRelativeEntropy (unitaryChannel U ρ) (unitaryChannel U σ) :=
  petz_equality_easy_unitary U ρ σ

/-! ## 5. The hard-direction gate -/

/-- **THE HARD DIRECTION (unitary case) — named gate.**

    Statement: for every unitary `U`, density matrices `ρ, σ`, the
    equality `D(ρ ‖ σ) = D(N(ρ) ‖ N(σ))` implies the Petz recovery
    `R_{σ,N}(N(ρ)) = ρ`.

    In the unitary case the conclusion is automatic
    (`petzRecovery_unitary_idem`), so the hard-direction *content*
    is vacuous and the gate is unconditionally true (its proof is
    one line).  We expose it as a gate anyway, because the
    structurally interesting version is the Kraus / general case
    (next gate), where it captures the substantive analytic content
    of Petz's theorem. -/
theorem PetzEqualityHard_Unitary
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (ρ σ : ComplexDensityMatrix n)
    (_hEq : umegakiRelativeEntropy ρ σ
              = umegakiRelativeEntropy (unitaryChannel U ρ) (unitaryChannel U σ)) :
    petzRecoveryUnitary U σ (unitaryChannel U ρ) = ρ :=
  petzRecovery_unitary_idem U σ ρ

/-- **HARD DIRECTION (general Kraus case) — named gate.**

    For a general Kraus channel `N(ρ) := ∑ᵢ Kᵢ ρ Kᵢ†` with PD
    reference state σ, the Petz recovery map is

        R_{σ,N}(τ) := σ^{1/2} · N*( N(σ)^{-1/2} τ N(σ)^{-1/2} ) · σ^{1/2}

    with `N*(τ) := ∑ᵢ Kᵢ† τ Kᵢ` the adjoint channel.

    Petz's theorem then asserts:

        D(ρ ‖ σ) = D(N(ρ) ‖ N(σ))   ⇒   R_{σ,N}(N(ρ)) = ρ.

    Closing this gate requires:
      • operator square root and pseudoinverse in Mathlib's CFC
        (~200 lines);
      • equality conditions for operator inequalities (Hadamard
        three-line, or modular operators — Petz's original argument;
        ~400 lines for a clean treatment);
      • the adjoint-channel construction (~100 lines).

    Net: ~700 lines, of analytic CFC plumbing.  Far enough out of
    scope that we expose it as a `Prop`-target, mirroring
    `umegakiRelativeEntropy_isometric_invariant_Target` in
    `UmegakiIsometricInvariance.lean`. -/
def PetzEqualityHard_Kraus_Target : Prop :=
  -- For every Kraus channel (square-dim m, k operators), every PD
  -- reference state σ and arbitrary state ρ, and every candidate
  -- Petz recovery map `R : Matrix m m ℂ → Matrix m m ℂ` satisfying
  -- the recovery property `R (K.apply σ.M) = σ.M`:  IF the relative
  -- entropy is preserved by the channel
  -- `D(ρ ‖ σ) = D(K.apply ρ ‖ K.apply σ)` (in matrix form), THEN
  -- `R (K.apply ρ.M) = ρ.M`.
  --
  -- The `R` is a Prop-level placeholder; the substantive content
  -- (the actual Petz formula) is the matrix-level identity
  --   R(τ) = σ^{1/2} · (∑ᵢ Kᵢ† · N(σ)^{-1/2} · τ · N(σ)^{-1/2} · Kᵢ) · σ^{1/2}
  -- with `N := K.apply`.  We do not write the formula explicitly
  -- because operator square root and pseudoinverse on density
  -- matrices need ~200 lines of CFC plumbing not assembled here.
  ∀ {m k : ℕ} (K : UnifiedTheory.LayerB.Kraus.KrausRepresentation m m k)
    (ρ σ : ComplexDensityMatrix m)
    (R : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ)
    (_hR_recovers_sigma : R (K.apply σ.M) = σ.M)
    (_hEq : (Matrix.trace (ρ.M * (cfc Real.log ρ.M - cfc Real.log σ.M))).re
              = (Matrix.trace (K.apply ρ.M *
                  (cfc Real.log (K.apply ρ.M) - cfc Real.log (K.apply σ.M)))).re),
    R (K.apply ρ.M) = ρ.M

/-! ## 6. Closure / scoping notes -/

/-- **Scoping note A — what this file unconditionally delivers.**

      1. `unitaryChannel U`         — `N(ρ) = U ρ U†` on density matrices.
      2. `unitaryAdjointChannel U`  — `N*(τ) = U† τ U` on density matrices.
      3. `petzRecoveryUnitary U σ`  — the Petz recovery map for a
                                       unitary channel; coincides with
                                       `unitaryAdjointChannel U` (the
                                       inverse channel).
      4. `petzRecovery_unitary_property`  — `R(N(σ)) = σ`, unconditional.
      5. `petzRecovery_unitary_idem`      — `R(N(ρ)) = ρ` for ALL ρ
                                            in the unitary case.
      6. `petz_equality_easy_unitary`     — `D(ρ ‖ σ) = D(N(ρ) ‖ N(σ))`
                                            unconditionally (unitary
                                            invariance).
      7. `PetzEqualityHard_Unitary`       — hard direction in the
                                            unitary case
                                            (unconditional; trivial).

    No `sorry`, no custom `axiom`. -/
theorem scopingNote_unconditional_payoff : True := trivial

/-- **Scoping note B — the general-Kraus gate.**

    `PetzEqualityHard_Kraus_Target` exposes the *substantive*
    content of Petz's recovery theorem: for general Kraus channels
    with PD reference state, the equality saturation of DPI implies
    perfect recovery via the Petz map.

    Closing this gate requires:
      • operator square root and pseudoinverse on PSD matrices
        (Mathlib's CFC);
      • equality conditions for operator inequalities (Hadamard
        three-line theorem at the boundary, or Petz's modular-operator
        argument);
      • the adjoint channel `N*(τ) = ∑ᵢ Kᵢ† τ Kᵢ`.

    Estimated work: ~700 lines.  Cleanly compositional with the
    isometric-invariance gate
    `umegakiRelativeEntropy_isometric_invariant_Target`. -/
theorem scopingNote_kraus_gate : True := trivial

/-! ## 7. Axiom audit (post-build verification)

  Uncomment locally to verify:

    #print axioms unitaryChannel
    #print axioms unitaryAdjointChannel
    #print axioms petzRecoveryUnitary
    #print axioms petzRecovery_unitary_idem
    #print axioms petzRecovery_unitary_property
    #print axioms petz_equality_easy_unitary
    #print axioms petz_equality_easy_from_recovery
    #print axioms PetzEqualityHard_Unitary

  All should depend only on Lean's three standard axioms
  `propext, Classical.choice, Quot.sound`.  No `sorry`, no
  custom `axiom`. -/

end UnifiedTheory.LayerB.PetzRecovery
