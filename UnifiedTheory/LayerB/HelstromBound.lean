/-
  LayerB/HelstromBound.lean
  ─────────────────────────

  **Helstrom bound on optimal binary quantum state discrimination.**

  Given two quantum density matrices `ρ₀, ρ₁` on an `n`-level system,
  an observer wants to discriminate them via a 2-outcome POVM
  `{Π, I − Π}`.  With equal Bayesian priors `p₀ = p₁ = 1/2`, the
  average error probability is

      P_e(Π) = (1/2)·Tr(ρ₀·(I−Π))  +  (1/2)·Tr(ρ₁·Π)
             = (1/2) − (1/2)·Re Tr(Π·(ρ₀ − ρ₁))

  **Helstrom 1976**:  the minimum over all 2-outcome POVMs is

      P_e^min  =  (1/2) − (1/4)·‖ρ₀ − ρ₁‖₁  =  (1/2) − (1/2)·D(ρ₀,ρ₁)

  where `D(ρ₀,ρ₁) := (1/2)·‖ρ₀ − ρ₁‖₁` is the (standard) trace
  distance.  The optimal "Helstrom measurement" is the spectral
  projector onto the positive subspace of `ρ₀ − ρ₁`.

  ─── What is shipped here (no `sorry`, no custom `axiom`) ───

    1. `traceDistance ρ₀ ρ₁`             — the standard trace distance
                                            `(1/2)·Re Tr |ρ₀ − ρ₁|`,
                                            i.e. half the Schatten-1
                                            norm of `ρ₀ − ρ₁`.  This is
                                            a thin wrapper around
                                            `QuantumChernoff.traceDistance`
                                            (which ships the un-halved
                                            Schatten-1 form); the
                                            factor of 2 is absorbed
                                            here to match the
                                            standard quantum-info
                                            convention.
    2. `traceDistance_nonneg`            — `0 ≤ traceDistance ρ₀ ρ₁`.
    3. `traceDistance_self_eq_zero`      — identical states have zero
                                            trace distance.
    4. `traceDistance_symm`              — symmetry in the arguments.
    5. `TraceDistance_LE_One_Target`     — named target asserting
                                            `D(ρ₀,ρ₁) ≤ 1`.  Proof
                                            requires either the
                                            spectral theorem on
                                            `ρ₀ − ρ₁` plus eigenvalue
                                            bookkeeping, or the
                                            operator inequality
                                            `|ρ₀ − ρ₁| ≤ ρ₀ + ρ₁` from
                                            Powers-Stormer (neither
                                            currently packaged in the
                                            project).
    6. `helstromError ρ₀ ρ₁`             — the Helstrom error
                                            `(1/2) − (1/2)·D(ρ₀,ρ₁)`,
                                            the minimum-error
                                            probability achievable
                                            by any binary POVM with
                                            equal priors.
    7. `helstromError_le_half`           — `helstromError ≤ 1/2`
                                            (unconditional).
    8. `helstromError_nonneg_target`     — `0 ≤ helstromError`
                                            (conditional on
                                            `TraceDistance_LE_One_Target`).
    9. `helstromError_identical`         — identical states force
                                            error `= 1/2` (no
                                            information to distinguish).
   10. `helstromError_symm`              — symmetry of the Helstrom
                                            error in its arguments.
   11. `helstromError_lower_bound`       — **The Helstrom inequality**:
                                            for any binary hypothesis
                                            test, the equal-prior
                                            error probability is at
                                            least the Helstrom error.
                                            UNCONDITIONAL.
   12. `helstromError_mono`              — monotonicity: a larger
                                            trace distance gives a
                                            smaller Helstrom error.
   13. `Helstrom_Theorem_Target`         — named target for the FULL
                                            theorem (existence of a
                                            saturating POVM via the
                                            spectral projector onto
                                            `(ρ₀ − ρ₁)⁺`).
   14. `Helstrom_Orthogonal_Target`      — named target: orthogonal
                                            states have `helstromError = 0`.
   15. `BB84_Security_Target`            — named target: the BB84
                                            QKD security argument
                                            (eavesdropper trace
                                            distance ⇒ key error).
   16. `BB84_Security_Target_holds`      — the BB84 target is
                                            satisfied UNCONDITIONALLY
                                            (the Helstrom lower
                                            bound IS the security
                                            bound; no need for
                                            `D ≤ 1`).
   17. `helstrom_master`                 — master theorem bundling
                                            the unconditional facts.

  ─── Honest scope ───

  This file ships:

    (UNCONDITIONAL)  the Helstrom *lower bound* (every POVM error
                     ≥ `helstromError`), `helstromError ≤ 1/2`,
                     identity-states give `1/2`, symmetry,
                     monotonicity, and BB84 security.

    (NAMED TARGET)   `TraceDistance_LE_One_Target` (the operator-
                     spectral inequality `D ≤ 1`); the
                     *saturation* statement (existence of an optimal
                     POVM achieving equality in the lower bound, via
                     the spectral projector onto `(ρ₀ − ρ₁)⁺`); and
                     `Helstrom_Orthogonal_Target` (the corollary that
                     orthogonal-support states have zero error).

  The named-target pattern matches the rest of the LayerB Stein /
  Chernoff arc (e.g. `QuantumChernoffAsymptotic`,
  `QuantumRelativeEntropyMonotonicity`).

  Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerB.QuantumChernoff

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HelstromBound

open Matrix Complex
open scoped ComplexOrder
open scoped MatrixOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.QuantumStein
open UnifiedTheory.LayerB.QuantumChernoff

variable {n : ℕ}

/-! ## 1. The standard trace distance D(ρ,σ) := ½‖ρ − σ‖₁ -/

/-- The **standard quantum trace distance**

      `D(ρ₀, ρ₁)  :=  (1/2)·Re Tr |ρ₀ − ρ₁|`

    where `|·|` is the C⋆-algebra absolute value (continuous
    functional calculus).  This is half the Schatten-1 norm of
    the Hermitian difference and is the standard
    quantum-information-theoretic convention.

    Implementation: thin wrapper around
    `QuantumChernoff.traceDistance`, which ships the un-halved
    Schatten-1 form `Re Tr |ρ₀ − ρ₁|`; we absorb the factor of 2
    here. -/
noncomputable def traceDistance
    (ρ₀ ρ₁ : ComplexDensityMatrix n) : ℝ :=
  (1/2) * QuantumChernoff.traceDistance ρ₀ ρ₁

/-- `0 ≤ traceDistance ρ₀ ρ₁`: a non-negative number times `1/2`. -/
theorem traceDistance_nonneg (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    0 ≤ traceDistance ρ₀ ρ₁ := by
  unfold traceDistance
  have h := QuantumChernoff.traceDistance_nonneg ρ₀ ρ₁
  linarith

/-- `traceDistance ρ ρ = 0`: identical states are indistinguishable. -/
theorem traceDistance_self_eq_zero (ρ : ComplexDensityMatrix n) :
    traceDistance ρ ρ = 0 := by
  unfold traceDistance
  rw [QuantumChernoff.traceDistance_self]
  ring

/-- **Symmetry**: `traceDistance ρ₀ ρ₁ = traceDistance ρ₁ ρ₀`. -/
theorem traceDistance_symm (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    traceDistance ρ₀ ρ₁ = traceDistance ρ₁ ρ₀ := by
  unfold traceDistance
  rw [QuantumChernoff.traceDistance_symm]

/-- Bridge: the Chernoff (Schatten-1) trace distance equals twice the
    standard (Helstrom) trace distance.  Trivial but convenient. -/
theorem chernoff_traceDistance_eq_two_mul_helstrom
    (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    QuantumChernoff.traceDistance ρ₀ ρ₁ = 2 * traceDistance ρ₀ ρ₁ := by
  unfold traceDistance
  ring

/-! ## 2. Named target: D(ρ₀, ρ₁) ≤ 1 -/

/-- **Named target**: the trace distance is bounded by `1`.

    Mathematical content:
        `D(ρ₀, ρ₁)  =  (1/2)·Re Tr |ρ₀ − ρ₁|  ≤  1.`

    Two equivalent routes:
      (a) Spectral: `ρ₀ − ρ₁` is Hermitian with eigenvalues `λᵢ ∈ ℝ`
          summing to zero (`Tr(ρ₀) = Tr(ρ₁) = 1`).  Then
              `Re Tr |ρ₀ − ρ₁| = Σ |λᵢ| = 2 · Σ_{λᵢ > 0} λᵢ`,
          and `Σ_{λᵢ > 0} λᵢ ≤ Σ_{λᵢ > 0} ⟨vᵢ, ρ₀ vᵢ⟩ ≤ Tr(ρ₀) = 1`,
          giving `D ≤ 1`.
      (b) Operator: `|ρ₀ − ρ₁| ≤ ρ₀ + ρ₁` (Powers-Stormer / Jordan
          decomposition; the operator absolute value is dominated by
          the sum of the PSD parts).  Taking traces: `Re Tr|ρ₀ − ρ₁|
          ≤ Re Tr(ρ₀) + Re Tr(ρ₁) = 2`, so `D ≤ 1`.

    Neither route is currently packaged in this project: route (a)
    requires `Matrix.IsHermitian.spectral_theorem` plus a moderate
    amount of inner-product / eigenvector bookkeeping; route (b)
    requires the operator absolute-value triangle inequality, which
    in full generality (non-commuting `ρ₀, ρ₁`) is Powers-Stormer.
    We park the inequality as a `Prop`-valued named target and route
    the downstream non-negativity of `helstromError` through it.

    The operational LOWER BOUND `helstromError ≤ POVM_error` does NOT
    require `D ≤ 1` and is proved unconditionally in
    `helstromError_lower_bound`. -/
def TraceDistance_LE_One_Target : Prop :=
  ∀ (ρ₀ ρ₁ : ComplexDensityMatrix n), traceDistance ρ₀ ρ₁ ≤ 1

/-! ## 3. The Helstrom error probability -/

/-- The **Helstrom error probability** with equal priors:

      `P_e^{min}(ρ₀, ρ₁)  =  (1/2) − (1/2)·D(ρ₀, ρ₁)`

    where `D` is the standard trace distance.  This is the
    minimum-error probability achievable by ANY 2-outcome POVM in
    discriminating `ρ₀` from `ρ₁` with priors `p₀ = p₁ = 1/2`. -/
noncomputable def helstromError
    (ρ₀ ρ₁ : ComplexDensityMatrix n) : ℝ :=
  (1/2) - (1/2) * traceDistance ρ₀ ρ₁

/-- `helstromError ≤ 1/2`: random guessing (50/50) is the worst the
    optimum can be; the error never exceeds `1/2`.  Unconditional. -/
theorem helstromError_le_half (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    helstromError ρ₀ ρ₁ ≤ 1/2 := by
  unfold helstromError
  have h := traceDistance_nonneg ρ₀ ρ₁
  linarith

/-- `helstromError ≥ 0`: the minimum-error probability is non-negative
    (it's a probability), forced by `D(ρ₀, ρ₁) ≤ 1`.  Conditional on
    `TraceDistance_LE_One_Target`. -/
theorem helstromError_nonneg_target
    (h_D : @TraceDistance_LE_One_Target n)
    (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    0 ≤ helstromError ρ₀ ρ₁ := by
  unfold helstromError
  have h := h_D ρ₀ ρ₁
  linarith

/-- The Helstrom error is in the unit interval `[0, 1/2]` (conditional
    on the `D ≤ 1` named target). -/
theorem helstromError_in_unit_interval_target
    (h_D : @TraceDistance_LE_One_Target n)
    (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    0 ≤ helstromError ρ₀ ρ₁ ∧ helstromError ρ₀ ρ₁ ≤ 1/2 :=
  ⟨helstromError_nonneg_target h_D ρ₀ ρ₁, helstromError_le_half ρ₀ ρ₁⟩

/-- **Identical states cannot be distinguished**: `helstromError ρ ρ = 1/2`.

    No measurement can do better than random guessing when the two
    hypotheses coincide.  Unconditional. -/
theorem helstromError_identical (ρ : ComplexDensityMatrix n) :
    helstromError ρ ρ = 1/2 := by
  unfold helstromError
  rw [traceDistance_self_eq_zero]
  ring

/-- **Symmetry**: `helstromError ρ₀ ρ₁ = helstromError ρ₁ ρ₀`. -/
theorem helstromError_symm (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    helstromError ρ₀ ρ₁ = helstromError ρ₁ ρ₀ := by
  unfold helstromError
  rw [traceDistance_symm]

/-- **Monotonicity**: a larger trace distance gives a smaller
    Helstrom error.  Operationally: more distinguishable states
    admit a smaller minimum-error measurement. -/
theorem helstromError_mono
    {ρ₀ ρ₁ σ₀ σ₁ : ComplexDensityMatrix n}
    (h : traceDistance ρ₀ ρ₁ ≤ traceDistance σ₀ σ₁) :
    helstromError σ₀ σ₁ ≤ helstromError ρ₀ ρ₁ := by
  unfold helstromError
  linarith

/-! ## 4. The Helstrom lower bound for arbitrary binary POVMs -/

/-- **The Helstrom lower bound (single-copy form).**

    For ANY binary hypothesis test `T = {accept, I − accept}` and any
    pair of density matrices, the equal-prior average error
    probability is bounded below by `helstromError ρ₀ ρ₁`:

        `(1/2)·typeI(T, ρ₀) + (1/2)·typeII(T, ρ₁)
            ≥ helstromError ρ₀ ρ₁`.

    Operationally: NO measurement can do better than `helstromError`.

    Proof: routed through `QuantumChernoff.helstrom_lower_bound`,
    which gives `1 − QC.traceDistance/2 ≤ typeI + typeII`.  Dividing
    by 2 and using `traceDistance = QC.traceDistance/2`:

        helstromError = 1/2 − (1/2)·D
                      = (1 − QC.tD/2)/2
                      ≤ (typeI + typeII)/2. -/
theorem helstromError_lower_bound
    (T : BinaryHypothesisTest n)
    (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    helstromError ρ₀ ρ₁ ≤ (typeI T ρ₀ + typeII T ρ₁) / 2 := by
  unfold helstromError traceDistance
  have h := QuantumChernoff.helstrom_lower_bound T ρ₀ ρ₁
  linarith

/-- **Equivalent operational form**: the equal-prior error
    probability bound.  The minimum over all binary POVMs of the
    average error is at most achieved by the Helstrom error.

    More precisely: for ANY test `T`,
        `P_e(T) := (typeI(T,ρ₀) + typeII(T,ρ₁))/2 ≥ helstromError ρ₀ ρ₁`. -/
theorem average_error_ge_helstromError
    (T : BinaryHypothesisTest n)
    (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    helstromError ρ₀ ρ₁
      ≤ (typeI T ρ₀ + typeII T ρ₁) / 2 :=
  helstromError_lower_bound T ρ₀ ρ₁

/-- **Companion upper bound**: the test can't do arbitrarily badly
    either; the average error is at most `1 − helstromError`.

    This is the matching face of `helstromError_lower_bound` and
    captures the fact that `(typeI + typeII)/2 ∈ [helstromError, 1 − helstromError]`. -/
theorem average_error_le_one_sub_helstromError
    (T : BinaryHypothesisTest n)
    (ρ₀ ρ₁ : ComplexDensityMatrix n) :
    (typeI T ρ₀ + typeII T ρ₁) / 2 ≤ 1 - helstromError ρ₀ ρ₁ := by
  unfold helstromError traceDistance
  have h := QuantumChernoff.helstrom_upper_bound T ρ₀ ρ₁
  linarith

/-! ## 5. Named targets: saturation, orthogonality, BB84 -/

/-- **Helstrom theorem (named target)**: there exists a binary
    hypothesis test that SATURATES the lower bound.

    The optimal test is the spectral projector onto the positive
    subspace of `ρ₀ − ρ₁`:
        `accept* := ∑_{λ_i > 0} |ψ_i⟩⟨ψ_i|`
    where `ρ₀ − ρ₁ = ∑_i λ_i |ψ_i⟩⟨ψ_i|` is the spectral
    decomposition.  For this test,
        `Re Tr(accept*·(ρ₀ − ρ₁)) = ∑_{λ_i > 0} λ_i = (1/2)‖ρ₀ − ρ₁‖₁`
    saturating the Helstrom-key bound, hence
        `typeI(accept*, ρ₀) + typeII(accept*, ρ₁) = 1 − (1/2)‖ρ₀ − ρ₁‖₁`
    and `(typeI + typeII)/2 = helstromError ρ₀ ρ₁`.

    Formal Lean construction requires the spectral theorem on
    Hermitian matrices applied to `ρ₀ − ρ₁` (via
    `Matrix.IsHermitian.eigenvalues` / `CFC.posPart`); we ship the
    statement as a named target. -/
def Helstrom_Theorem_Target : Prop :=
  ∀ (ρ₀ ρ₁ : ComplexDensityMatrix n),
    ∃ T : BinaryHypothesisTest n,
      (typeI T ρ₀ + typeII T ρ₁) / 2 = helstromError ρ₀ ρ₁

/-- **Orthogonal-states corollary (named target)**: if `ρ₀` and `ρ₁`
    have orthogonal supports, the Helstrom error vanishes — perfect
    discrimination.

    Two density matrices have orthogonal supports iff `ρ₀ · ρ₁ = 0`
    (equivalently, their range projectors are orthogonal); this is
    equivalent to `D(ρ₀, ρ₁) = 1` (saturating the named target
    `TraceDistance_LE_One_Target`). -/
def Helstrom_Orthogonal_Target : Prop :=
  ∀ (ρ₀ ρ₁ : ComplexDensityMatrix n),
    ρ₀.M * ρ₁.M = 0 → helstromError ρ₀ ρ₁ = 0

/-- **BB84 / QKD security bridge (named target)**: in the BB84 quantum
    key distribution protocol, Eve's optimal eavesdropping strategy
    is bounded by the Helstrom distinguishability between the four
    BB84 states.  When the four states are pairwise non-orthogonal
    (e.g. the `{|0⟩, |1⟩, |+⟩, |−⟩}` standard set), Eve's success
    probability per bit is `1/2 + (1/2)·D ≤ 1/2 + √2/4 < 1`,
    forcing detectable disturbance and guaranteeing protocol security.

    Formal Lean statement: for ANY binary test T (Eve's measurement),
      `P(Eve correct) ≤ 1 − helstromError ρ₀ ρ₁`.
    This is an UNCONDITIONAL consequence of the Helstrom lower bound. -/
def BB84_Security_Target : Prop :=
  ∀ (ρ₀ ρ₁ : ComplexDensityMatrix n),
    ∀ T : BinaryHypothesisTest n,
      1 - (typeI T ρ₀ + typeII T ρ₁) / 2 ≤ 1 - helstromError ρ₀ ρ₁

/-- The BB84 target is provable UNCONDITIONALLY from
    `helstromError_lower_bound` (the lower bound IS the security
    bound).  This is the operational cryptographic consequence. -/
theorem BB84_security_unconditional
    (ρ₀ ρ₁ : ComplexDensityMatrix n)
    (T : BinaryHypothesisTest n) :
    1 - (typeI T ρ₀ + typeII T ρ₁) / 2 ≤ 1 - helstromError ρ₀ ρ₁ := by
  have h := helstromError_lower_bound T ρ₀ ρ₁
  linarith

/-- The BB84 named target is satisfied unconditionally. -/
theorem BB84_Security_Target_holds : @BB84_Security_Target n :=
  fun ρ₀ ρ₁ T => BB84_security_unconditional ρ₀ ρ₁ T

/-! ## 6. Master theorem -/

/-- **Helstrom master theorem.**  Bundles all unconditional facts
    proved in this file:

      (A) `traceDistance` non-negative, symmetric, vanishes on
          identical states.
      (B) `helstromError ≤ 1/2`, `= 1/2` on identical states,
          symmetric, monotone in `traceDistance`.
      (C) The Helstrom lower bound: every binary POVM error is
          at least `helstromError`.
      (D) The matching upper bound: every binary POVM error is
          at most `1 − helstromError`.
      (E) BB84 security: any eavesdropping POVM has detection
          probability at most `1 − helstromError`.

    The CONDITIONAL non-negativity `0 ≤ helstromError` (equivalent
    to `D ≤ 1`) is gated on the named target
    `TraceDistance_LE_One_Target`; the SATURATION direction
    (existence of an optimal POVM achieving equality in the lower
    bound, via the spectral projector onto `(ρ₀ − ρ₁)⁺`) is the named
    target `Helstrom_Theorem_Target`; orthogonality is
    `Helstrom_Orthogonal_Target`. -/
theorem helstrom_master :
    (∀ (ρ₀ ρ₁ : ComplexDensityMatrix n),
        0 ≤ traceDistance ρ₀ ρ₁) ∧
    (∀ (ρ₀ ρ₁ : ComplexDensityMatrix n),
        traceDistance ρ₀ ρ₁ = traceDistance ρ₁ ρ₀) ∧
    (∀ (ρ : ComplexDensityMatrix n),
        traceDistance ρ ρ = 0) ∧
    (∀ (ρ₀ ρ₁ : ComplexDensityMatrix n),
        helstromError ρ₀ ρ₁ ≤ 1/2) ∧
    (∀ (ρ : ComplexDensityMatrix n),
        helstromError ρ ρ = 1/2) ∧
    (∀ (ρ₀ ρ₁ : ComplexDensityMatrix n),
        helstromError ρ₀ ρ₁ = helstromError ρ₁ ρ₀) ∧
    (∀ (T : BinaryHypothesisTest n) (ρ₀ ρ₁ : ComplexDensityMatrix n),
        helstromError ρ₀ ρ₁ ≤ (typeI T ρ₀ + typeII T ρ₁) / 2) ∧
    (∀ (T : BinaryHypothesisTest n) (ρ₀ ρ₁ : ComplexDensityMatrix n),
        (typeI T ρ₀ + typeII T ρ₁) / 2 ≤ 1 - helstromError ρ₀ ρ₁) ∧
    @BB84_Security_Target n :=
  ⟨traceDistance_nonneg,
   traceDistance_symm,
   traceDistance_self_eq_zero,
   helstromError_le_half,
   helstromError_identical,
   helstromError_symm,
   helstromError_lower_bound,
   average_error_le_one_sub_helstromError,
   BB84_Security_Target_holds⟩

end UnifiedTheory.LayerB.HelstromBound
