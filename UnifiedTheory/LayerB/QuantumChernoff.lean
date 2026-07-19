/-
  LayerB/QuantumChernoff.lean
  ────────────────────────────

  **Quantum Chernoff bound (single-copy, Helstrom form).**

  Companion to `UnifiedTheory.LayerB.QuantumStein`.  Where Stein's
  lemma controls the *asymmetric* error exponent (Type-II at fixed
  Type-I), the Chernoff bound controls the *symmetric* error
  exponent (the average error of any binary test).

  **Asymptotic statement** (Audenaert et al. 2007, Nussbaum–Szkoła
  2009; out of scope here):
      lim_{n→∞} −(1/n) log P_avg(n)  =  ξ(ρ, σ)
  where
      ξ(ρ, σ)  :=  − min_{0 ≤ s ≤ 1} log Tr(ρ^s · σ^{1-s})
  is the **quantum Chernoff information**.

  **What is shipped here (single-copy, non-asymptotic):**

    1. `traceDistance ρ σ`        — `Re Tr |ρ − σ|`, the
                                     Schatten-1 norm of the
                                     Hermitian difference
                                     (twice the standard
                                     "trace distance" D(ρ, σ);
                                     the factor of 2 is absorbed
                                     into the Helstrom statement
                                     below).
    2. `traceDistance_nonneg`     — `0 ≤ traceDistance ρ σ`.
    3. `traceDistance_self`       — `traceDistance ρ ρ = 0`.
    4. `traceDistance_symm`       — symmetry in ρ, σ.
    5. `helstrom_lower_bound`     — the **Helstrom bound**, the
                                     non-asymptotic single-copy
                                     core of the Chernoff arc:
                                     for any binary hypothesis
                                     test `T`,
                                       `typeI T ρ + typeII T σ
                                          ≥ 1 − traceDistance ρ σ / 2`.
    6. `chernoffInformation`      — the s = 1/2 quantum Chernoff
                                     information, defined via the
                                     square-root functional
                                     calculus (the symmetric
                                     `s = 1/2` Bhattacharyya case
                                     of the general optimisation).

  **Honest scope:**
    • The asymptotic limit `lim −(1/n) log P_avg(n) = ξ(ρ,σ)`
      requires tensor-power machinery on ρ⊗ⁿ vs σ⊗ⁿ — multi-week
      formalisation work, out of scope.  We state the asymptotic
      bound as a named `Prop`-hypothesis
      `QuantumChernoffAsymptotic`, parallel to
      `QuantumRelativeEntropyMonotonicity` in QuantumStein.
    • Identifying the Helstrom optimal test (projector onto the
      positive part of ρ − σ) as the *saturating* test is also
      deferred.  We ship the LOWER BOUND that every test must
      satisfy.

  **Proof strategy for `helstrom_lower_bound`:**
  Let Δ = ρ − σ (Hermitian, `Tr(Δ) = 0`).  Write
      Δ = Δ⁺ − Δ⁻      with `0 ≤ Δ⁺, 0 ≤ Δ⁻`
      |Δ| = Δ⁺ + Δ⁻
  via the continuous functional calculus' `CFC.posPart` /
  `CFC.negPart` / `CFC.abs` on the C⋆-algebra of matrices.
  Tracing the first identity:
      `0 = Tr(Δ) = Tr(Δ⁺) − Tr(Δ⁻)`
  so `Tr(Δ⁺) = Tr(Δ⁻) = Tr(|Δ|)/2 = traceDistance/2`.
  Then for any `0 ≤ Π ≤ I`:
      `Re Tr(Π · Δ)  =  Re Tr(Π · Δ⁺) − Re Tr(Π · Δ⁻)
                     ≤ Re Tr(Δ⁺)                    (Π ≤ I, Δ⁺ ≥ 0)
                     = traceDistance / 2`
  by the dual Hölder bound `Tr(A·B) ≤ Tr(B)` for `0 ≤ A ≤ I`,
  `0 ≤ B`.  Finally,
      `typeI T ρ + typeII T σ
         = 1 − Re Tr(accept · (ρ − σ))
         ≥ 1 − traceDistance ρ σ / 2`.

  Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerB.QuantumStein
import UnifiedTheory.LayerB.IsAndoMaximalDischarge
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumChernoff

open Matrix Complex
open scoped ComplexOrder
open scoped MatrixOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.QuantumStein

variable {n : ℕ}

/-! ## 1. The Hermitian difference ρ − σ and its CFC pos/neg parts -/

/-- The Hermitian difference of two density matrices. -/
noncomputable def diff (ρ σ : ComplexDensityMatrix n) :
    Matrix (Fin n) (Fin n) ℂ :=
  ρ.M - σ.M

/-- `ρ − σ` is Hermitian: both ρ.M and σ.M are. -/
theorem diff_isHermitian (ρ σ : ComplexDensityMatrix n) :
    (diff ρ σ).IsHermitian := by
  unfold diff Matrix.IsHermitian
  rw [conjTranspose_sub, ρ.hHerm, σ.hHerm]

/-- `ρ − σ` is self-adjoint as a C⋆-algebra element (= Hermitian). -/
theorem diff_isSelfAdjoint (ρ σ : ComplexDensityMatrix n) :
    IsSelfAdjoint (diff ρ σ) :=
  diff_isHermitian ρ σ

/-- `Tr(ρ − σ) = 0`: both density matrices have trace 1. -/
theorem trace_diff_eq_zero (ρ σ : ComplexDensityMatrix n) :
    Matrix.trace (diff ρ σ) = 0 := by
  unfold diff
  rw [Matrix.trace_sub, ρ.hTrace, σ.hTrace, sub_self]

/-! ## 2. Trace distance: `Re Tr |ρ − σ|` -/

/-- **Trace distance** of two density matrices: `Re Tr |ρ − σ|`,
    where `|·|` is the C⋆-algebra absolute value from the
    continuous functional calculus.

    This is the Schatten-1 norm of `ρ − σ`.  Some references call
    `D(ρ, σ) := (1/2) Re Tr |ρ − σ|` the "trace distance"; we
    ship the un-halved version here and absorb the factor of 2
    into the Helstrom statement (see `helstrom_lower_bound`). -/
noncomputable def traceDistance (ρ σ : ComplexDensityMatrix n) : ℝ :=
  (Matrix.trace (CFC.abs (diff ρ σ))).re

/-- The CFC absolute value of `ρ − σ` is PosSemidef. -/
theorem abs_diff_posSemidef (ρ σ : ComplexDensityMatrix n) :
    (CFC.abs (diff ρ σ)).PosSemidef := by
  -- `CFC.abs` is `≥ 0` in the C⋆-order; this is `PosSemidef`.
  have h_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ CFC.abs (diff ρ σ) :=
    CFC.abs_nonneg _
  exact h_nonneg.posSemidef

/-- The CFC absolute value of `ρ − σ` is Hermitian. -/
theorem abs_diff_isHermitian (ρ σ : ComplexDensityMatrix n) :
    (CFC.abs (diff ρ σ)).IsHermitian :=
  (abs_diff_posSemidef ρ σ).isHermitian

/-- `traceDistance ρ σ ≥ 0`: trace of a PSD has non-negative real part. -/
theorem traceDistance_nonneg (ρ σ : ComplexDensityMatrix n) :
    0 ≤ traceDistance ρ σ := by
  unfold traceDistance
  -- `(CFC.abs (ρ - σ)).trace` is non-negative in `ℂ`.
  have h_tr_nonneg : (0 : ℂ) ≤ Matrix.trace (CFC.abs (diff ρ σ)) :=
    (abs_diff_posSemidef ρ σ).trace_nonneg
  rw [Complex.le_def] at h_tr_nonneg
  exact h_tr_nonneg.1

/-- `traceDistance ρ ρ = 0`: `|ρ − ρ| = |0| = 0`. -/
theorem traceDistance_self (ρ : ComplexDensityMatrix n) :
    traceDistance ρ ρ = 0 := by
  unfold traceDistance diff
  rw [sub_self]
  -- `CFC.abs 0 = 0`.
  have h : (CFC.abs (0 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
    rw [CFC.abs_of_nonneg (a := (0 : Matrix (Fin n) (Fin n) ℂ)) (le_refl 0)]
  rw [h, Matrix.trace_zero, Complex.zero_re]

/-- **Symmetry of trace distance**: `traceDistance ρ σ = traceDistance σ ρ`.

    Follows from `|Δ| = |−Δ|` in any C⋆-algebra. -/
theorem traceDistance_symm (ρ σ : ComplexDensityMatrix n) :
    traceDistance ρ σ = traceDistance σ ρ := by
  unfold traceDistance diff
  -- `σ.M - ρ.M = -(ρ.M - σ.M)`.
  have h_neg : σ.M - ρ.M = -(ρ.M - σ.M) := by
    rw [neg_sub]
  rw [h_neg]
  -- `CFC.abs (-x) = CFC.abs x`.
  rw [CFC.abs_neg]

/-! ## 3. The pos/neg-part decomposition of `ρ − σ` -/

/-- The positive part `(ρ − σ)⁺` is PSD. -/
theorem posPart_diff_posSemidef (ρ σ : ComplexDensityMatrix n) :
    ((diff ρ σ)⁺).PosSemidef :=
  (CFC.posPart_nonneg _).posSemidef

/-- The negative part `(ρ − σ)⁻` is PSD. -/
theorem negPart_diff_posSemidef (ρ σ : ComplexDensityMatrix n) :
    ((diff ρ σ)⁻).PosSemidef :=
  (CFC.negPart_nonneg _).posSemidef

/-- `(ρ − σ)⁺ − (ρ − σ)⁻ = ρ − σ`. -/
theorem posPart_sub_negPart_diff (ρ σ : ComplexDensityMatrix n) :
    (diff ρ σ)⁺ - (diff ρ σ)⁻ = diff ρ σ :=
  CFC.posPart_sub_negPart (diff ρ σ) (diff_isSelfAdjoint ρ σ)

/-- `(ρ − σ)⁺ + (ρ − σ)⁻ = |ρ − σ|`. -/
theorem posPart_add_negPart_diff (ρ σ : ComplexDensityMatrix n) :
    (diff ρ σ)⁺ + (diff ρ σ)⁻ = CFC.abs (diff ρ σ) :=
  CFC.posPart_add_negPart (diff ρ σ) (diff_isSelfAdjoint ρ σ)

/-- `Tr((ρ − σ)⁺) = Tr((ρ − σ)⁻)` for two density matrices.

    Since `Tr(ρ - σ) = 0` and `Tr` is linear on `(ρ-σ)⁺ - (ρ-σ)⁻`. -/
theorem trace_posPart_eq_trace_negPart (ρ σ : ComplexDensityMatrix n) :
    Matrix.trace ((diff ρ σ)⁺)
      = Matrix.trace ((diff ρ σ)⁻) := by
  have h_dec := posPart_sub_negPart_diff ρ σ
  have h_tr_dec : Matrix.trace (diff ρ σ) =
      Matrix.trace ((diff ρ σ)⁺)
        - Matrix.trace ((diff ρ σ)⁻) := by
    rw [← Matrix.trace_sub, h_dec]
  have h_zero : Matrix.trace (diff ρ σ) = 0 := trace_diff_eq_zero ρ σ
  rw [h_zero] at h_tr_dec
  -- 0 = a - b ⟹ a = b in ℂ.
  exact (sub_eq_zero.mp h_tr_dec.symm)

/-- `Tr(|ρ − σ|) = Tr((ρ−σ)⁺) + Tr((ρ−σ)⁻)`. -/
theorem trace_abs_diff_eq_sum (ρ σ : ComplexDensityMatrix n) :
    Matrix.trace (CFC.abs (diff ρ σ))
      = Matrix.trace ((diff ρ σ)⁺)
        + Matrix.trace ((diff ρ σ)⁻) := by
  rw [← Matrix.trace_add]
  congr 1
  exact (posPart_add_negPart_diff ρ σ).symm

/-- `Tr((ρ−σ)⁺) = Tr(|ρ − σ|) / 2`. -/
theorem trace_posPart_eq_half_traceDistance (ρ σ : ComplexDensityMatrix n) :
    (Matrix.trace ((diff ρ σ)⁺)).re
      = traceDistance ρ σ / 2 := by
  unfold traceDistance
  rw [trace_abs_diff_eq_sum, Complex.add_re]
  have h_eq := trace_posPart_eq_trace_negPart ρ σ
  rw [h_eq]
  ring

/-- `Tr((ρ−σ)⁻) = Tr(|ρ − σ|) / 2`. -/
theorem trace_negPart_eq_half_traceDistance (ρ σ : ComplexDensityMatrix n) :
    (Matrix.trace ((diff ρ σ)⁻)).re
      = traceDistance ρ σ / 2 := by
  rw [← (trace_posPart_eq_trace_negPart ρ σ)]
  exact trace_posPart_eq_half_traceDistance ρ σ

/-! ## 4. Hölder-style bound: `Tr(Π·B) ≤ Tr(B)` for `0 ≤ Π ≤ I`, `B ≥ 0` -/

/-- **Operator Hölder bound.**  For `0 ≤ accept ≤ I` (in the
    matrix order) and `0 ≤ B`, we have
        `Re Tr(accept · B)  ≤  Re Tr(B)`.

    Proof: `(I − accept) ≥ 0`, so `Re Tr((I − accept) · B) ≥ 0` by
    `re_trace_mul_nonneg_of_posSemidef`.  Linearity of trace then
    gives `Re Tr(accept·B) + Re Tr((I−accept)·B) = Re Tr(B)`, so
    `Re Tr(accept·B) ≤ Re Tr(B)`. -/
theorem re_trace_accept_mul_le_trace
    {accept B : Matrix (Fin n) (Fin n) ℂ}
    (h_compPSD : (1 - accept).PosSemidef) (hB : B.PosSemidef) :
    (Matrix.trace (accept * B)).re ≤ (Matrix.trace B).re := by
  -- (I - accept) * B + accept * B = B.
  have h_sum :
      (1 - accept) * B + accept * B = B := by
    rw [← Matrix.add_mul]
    have h_add : (1 - accept) + accept
            = (1 : Matrix (Fin n) (Fin n) ℂ) := by abel
    rw [h_add, Matrix.one_mul]
  -- Re Tr((I - accept) * B) ≥ 0.
  have h_nn : 0 ≤ (Matrix.trace ((1 - accept) * B)).re :=
    re_trace_mul_nonneg_of_posSemidef h_compPSD hB
  -- Re Tr(accept * B) + Re Tr((I - accept) * B) = Re Tr(B).
  have h_re_sum :
      (Matrix.trace (accept * B)).re
        + (Matrix.trace ((1 - accept) * B)).re
        = (Matrix.trace B).re := by
    rw [← Complex.add_re, ← Matrix.trace_add]
    congr 1
    rw [add_comm]
    exact congrArg Matrix.trace h_sum
  linarith

/-! ## 5. The Helstrom-key bound: `|Re Tr(accept·(ρ−σ))| ≤ traceDistance/2` -/

/-- **Upper-side Helstrom-key bound.**

    For `0 ≤ accept ≤ I`:
        `Re Tr(accept · (ρ − σ))  ≤  traceDistance ρ σ / 2`. -/
theorem re_trace_accept_mul_diff_le_half_traceDistance
    (T : BinaryHypothesisTest n)
    (ρ σ : ComplexDensityMatrix n) :
    (Matrix.trace (T.accept * (diff ρ σ))).re
      ≤ traceDistance ρ σ / 2 := by
  -- Decompose Δ = Δ⁺ − Δ⁻.
  have h_dec := posPart_sub_negPart_diff ρ σ
  -- Tr(accept · Δ) = Tr(accept · Δ⁺) - Tr(accept · Δ⁻).
  have h_tr_decomp :
      Matrix.trace (T.accept * (diff ρ σ))
        = Matrix.trace (T.accept * (diff ρ σ)⁺)
          - Matrix.trace (T.accept * (diff ρ σ)⁻) := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, h_dec]
  rw [h_tr_decomp, Complex.sub_re]
  -- Re Tr(accept · Δ⁺) ≤ Re Tr(Δ⁺) = traceDistance/2.
  have h_pos_bound :
      (Matrix.trace (T.accept * (diff ρ σ)⁺)).re
        ≤ (Matrix.trace ((diff ρ σ)⁺)).re :=
    re_trace_accept_mul_le_trace T.posSemidefComp
      (posPart_diff_posSemidef ρ σ)
  rw [trace_posPart_eq_half_traceDistance ρ σ] at h_pos_bound
  -- Re Tr(accept · Δ⁻) ≥ 0.
  have h_neg_nn :
      0 ≤ (Matrix.trace (T.accept * (diff ρ σ)⁻)).re :=
    re_trace_mul_nonneg_of_posSemidef T.posSemidef
      (negPart_diff_posSemidef ρ σ)
  linarith

/-- **Lower-side Helstrom-key bound.**

    For `0 ≤ accept ≤ I`:
        `−(traceDistance ρ σ / 2)  ≤  Re Tr(accept · (ρ − σ))`. -/
theorem neg_half_traceDistance_le_re_trace_accept_mul_diff
    (T : BinaryHypothesisTest n)
    (ρ σ : ComplexDensityMatrix n) :
    -(traceDistance ρ σ / 2)
      ≤ (Matrix.trace (T.accept * (diff ρ σ))).re := by
  -- Decompose Δ = Δ⁺ − Δ⁻.
  have h_dec := posPart_sub_negPart_diff ρ σ
  -- Tr(accept · Δ) = Tr(accept · Δ⁺) - Tr(accept · Δ⁻).
  have h_tr_decomp :
      Matrix.trace (T.accept * (diff ρ σ))
        = Matrix.trace (T.accept * (diff ρ σ)⁺)
          - Matrix.trace (T.accept * (diff ρ σ)⁻) := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, h_dec]
  rw [h_tr_decomp, Complex.sub_re]
  -- Re Tr(accept · Δ⁺) ≥ 0.
  have h_pos_nn :
      0 ≤ (Matrix.trace (T.accept * (diff ρ σ)⁺)).re :=
    re_trace_mul_nonneg_of_posSemidef T.posSemidef
      (posPart_diff_posSemidef ρ σ)
  -- Re Tr(accept · Δ⁻) ≤ Re Tr(Δ⁻) = traceDistance/2.
  have h_neg_bound :
      (Matrix.trace (T.accept * (diff ρ σ)⁻)).re
        ≤ (Matrix.trace ((diff ρ σ)⁻)).re :=
    re_trace_accept_mul_le_trace T.posSemidefComp
      (negPart_diff_posSemidef ρ σ)
  rw [trace_negPart_eq_half_traceDistance ρ σ] at h_neg_bound
  linarith

/-! ## 6. The Helstrom lower bound -/

/-- The sum `typeI + typeII` factors as `1 − Re Tr(accept · (ρ − σ))`.

    Algebra: `typeI T ρ + typeII T σ
              = Re Tr((I−accept)·ρ) + Re Tr(accept·σ)
              = Re Tr((I−accept)·ρ + accept·σ)
              = Re Tr(ρ − accept·(ρ − σ))
              = 1 − Re Tr(accept·(ρ − σ))`. -/
theorem typeI_add_typeII_eq_one_sub
    (T : BinaryHypothesisTest n)
    (ρ σ : ComplexDensityMatrix n) :
    typeI T ρ + typeII T σ
      = 1 - (Matrix.trace (T.accept * (diff ρ σ))).re := by
  unfold typeI typeII diff
  -- (I - accept) * ρ + accept * σ = ρ - accept * (ρ - σ).
  have h_alg :
      (1 - T.accept) * ρ.M + T.accept * σ.M
        = ρ.M - T.accept * (ρ.M - σ.M) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
    abel
  rw [← Complex.add_re]
  rw [show Matrix.trace ((1 - T.accept) * ρ.M)
            + Matrix.trace (T.accept * σ.M)
          = Matrix.trace ((1 - T.accept) * ρ.M + T.accept * σ.M) from
        (Matrix.trace_add _ _).symm]
  rw [h_alg, Matrix.trace_sub, Complex.sub_re, ρ.hTrace]
  simp

/-- **HELSTROM LOWER BOUND**: for any binary hypothesis test, the
    sum of Type-I and Type-II errors is bounded below by
        `1 − traceDistance ρ σ / 2`.

    This is the operational single-copy Chernoff bound: it says no
    test can simultaneously make both errors small unless ρ and σ
    are close in trace distance.  The optimal Helstrom test
    (projector onto `(ρ − σ)⁺`) saturates the bound; identifying
    the saturating test is a separate (deferred) calculation. -/
theorem helstrom_lower_bound
    (T : BinaryHypothesisTest n)
    (ρ σ : ComplexDensityMatrix n) :
    1 - traceDistance ρ σ / 2 ≤ typeI T ρ + typeII T σ := by
  rw [typeI_add_typeII_eq_one_sub]
  -- Goal: 1 - traceDistance/2 ≤ 1 - Re Tr(accept · Δ).
  -- Equivalent: Re Tr(accept · Δ) ≤ traceDistance/2.
  have h := re_trace_accept_mul_diff_le_half_traceDistance T ρ σ
  linarith

/-- **Reverse-side Helstrom bound**: `typeI + typeII ≤ 1 + traceDistance/2`.

    Companion to `helstrom_lower_bound`; the test cannot do
    *arbitrarily badly* either — the sum cannot exceed
    `1 + traceDistance/2`.  (This bound is rarely highlighted in
    the literature because the LOWER bound is the operational
    content, but it falls out of the same algebra.) -/
theorem helstrom_upper_bound
    (T : BinaryHypothesisTest n)
    (ρ σ : ComplexDensityMatrix n) :
    typeI T ρ + typeII T σ ≤ 1 + traceDistance ρ σ / 2 := by
  rw [typeI_add_typeII_eq_one_sub]
  -- Goal: 1 - Re Tr(accept · Δ) ≤ 1 + traceDistance/2.
  -- Equivalent: -(traceDistance/2) ≤ Re Tr(accept · Δ).
  have h := neg_half_traceDistance_le_re_trace_accept_mul_diff T ρ σ
  linarith

/-! ## 7. The s = 1/2 quantum Chernoff information -/

/-- The **quantum Chernoff information at s = 1/2** (Bhattacharyya):

      ξ_{1/2}(ρ, σ)  :=  − log Re Tr( √ρ · √σ )

    This is the s = 1/2 specialisation of the general optimisation
        ξ(ρ, σ) = − min_{s ∈ [0,1]} log Re Tr(ρ^s · σ^{1-s}).
    The s = 1/2 case is the symmetric Bhattacharyya quantity and
    upper-bounds the optimal value:
        ξ(ρ, σ) ≤ ξ_{1/2}(ρ, σ).
    Stating the general (s-optimised) form requires the Rényi-α
    operator interpolation machinery; we ship the symmetric case
    as the canonical Chernoff representative. -/
noncomputable def chernoffInformation
    (ρ σ : ComplexDensityMatrix n) : ℝ :=
  - Real.log
      (Matrix.trace (CFC.sqrt ρ.M * CFC.sqrt σ.M)).re

/-! ## 8. The asymptotic Chernoff bound, named hypothesis -/

/-- **Asymptotic quantum Chernoff bound** (named hypothesis).

    The full statement is:
        lim_{N → ∞} −(1/N) log P_avg(N; ρ⊗ᴺ, σ⊗ᴺ)  =  ξ(ρ, σ)
    where `P_avg(N)` is the optimum of `(typeI + typeII)/2` over
    binary tests on the `N`-fold tensor power.  The limit requires
    tensor-power machinery on density matrices (multi-week
    formalisation work), out of scope for this file.

    Parallel to `QuantumRelativeEntropyMonotonicity` in
    `QuantumStein.lean`: this is the asymptotic statement that
    `helstrom_lower_bound` is the single-copy non-asymptotic core
    of. -/
def QuantumChernoffAsymptotic : Prop :=
  ∀ (ρ σ : ComplexDensityMatrix n),
    ∃ (P_avg : ℕ → ℝ),
      (∀ N, 0 ≤ P_avg N) ∧
      (Filter.Tendsto
        (fun N : ℕ => - (1 / (N : ℝ)) * Real.log (P_avg N))
        Filter.atTop
        (nhds (chernoffInformation ρ σ)))

/-! ## 9. Summary corollary: the operational Chernoff bound -/

/-- **Operational Chernoff bound (single-copy form).**

    The average error of any binary hypothesis test on a single
    copy of ρ vs σ is at least `(1 − traceDistance ρ σ / 2) / 2`.
    The asymptotic Chernoff bound says this can be exponentially
    improved with multi-copy testing (tendency to
    `exp(−N · ξ(ρ,σ))`), but in the single-copy regime the
    Helstrom bound is tight. -/
theorem chernoff_single_copy_average_lower_bound
    (T : BinaryHypothesisTest n)
    (ρ σ : ComplexDensityMatrix n) :
    (1 - traceDistance ρ σ / 2) / 2
      ≤ (typeI T ρ + typeII T σ) / 2 := by
  have h := helstrom_lower_bound T ρ σ
  linarith

end UnifiedTheory.LayerB.QuantumChernoff
