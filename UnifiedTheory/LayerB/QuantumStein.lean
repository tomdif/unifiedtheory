/-
  LayerB/QuantumStein.lean
  ─────────────────────────

  **Quantum Stein's lemma — single-copy non-asymptotic form.**

  Hypothesis testing between two density matrices ρ and σ on an
  `n`-level system via a binary POVM `{Π, I − Π}` (in code: `{accept,
  1 − accept}` — `Π` is a Lean 4 reserved token).

    • Type-I error  α(accept, ρ)  :=  Re(Tr((I − accept) · ρ))
                                  — probability of saying "σ" when ρ.
    • Type-II error β(accept, σ)  :=  Re(Tr(accept · σ))
                                  — probability of saying "ρ" when σ.

  Both are probabilities in `[0,1]` (Sec. 4 below).  The post-
  measurement BINARY distribution on the two outcomes is

      p_ρ := (Re Tr(accept·ρ),  Re Tr((I−accept)·ρ))
      p_σ := (Re Tr(accept·σ),  Re Tr((I−accept)·σ))

  both `ProbabilityVector (Fin 2)`.

  **The single-copy Stein bound** (Hiai-Petz 1991, Ogawa-Nagaoka 2000;
  in the literature usually stated as the asymptotic limit
  `lim_{n→∞} −(1/n) log β_n = S(ρ‖σ)`, whose non-asymptotic
  single-copy core is the inequality below):

      KL(p_ρ ‖ p_σ)   ≤   S(ρ ‖ σ).

  This is precisely the Data-Processing Inequality (Lindblad–Uhlmann
  monotonicity) applied to the binary measurement channel.

  Two regimes are shipped:

  (A) **General (conditional)**: gated on
      `QuantumRelativeEntropyMonotonicity` (the named hypothesis from
      `HolevoBoundQuantum.lean` — the deep analytic content of full
      DPI for quantum-to-classical channels).  Theorem
      `stein_single_copy_of_monotonicity`.

  (B) **Diagonal (unconditional)**: when ρ and σ are diagonal in the
      canonical basis and the measurement is diagonal too, the DPI
      reduces to the classical log-sum / DPI inequality of
      `ClassicalChannelDPI.lean` — discharged using
      `klDivergence_contracts_under_stochastic_of_logsum` and
      `logSumInequality_holds`.  Theorem
      `stein_single_copy_diagonal`.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):

    1. `BinaryHypothesisTest n`           — structure (accept Hermitian,
                                            accept PSD, (I − accept) PSD).
    2. `typeI T ρ`, `typeII T σ`          — real-valued error probs.
    3. `typeI_in_unit_interval`,
       `typeII_in_unit_interval`          — both in [0, 1].
    4. `binaryOutcome T ρ`                — the binary distribution
                                            on `Fin 2` induced by the
                                            test on a state.
    5. `binaryMeasurement T`              — promotion of `T` to a
                                            `QuantumMeasurement n (Fin 2)`.
    6. `stein_single_copy_of_monotonicity` — gated single-copy Stein
                                            bound.
    7. `stein_single_copy_diagonal`       — unconditional diagonal
                                            single-copy Stein bound.

  HONEST SCOPE (what is NOT proven here):
    • The asymptotic limit `lim −(1/n) log β_n` is OUT OF SCOPE — it
      requires tensor-power machinery on ρ⊗ⁿ vs σ⊗ⁿ (multi-week
      formalisation work). What is shipped here is the single-copy
      INEQUALITY, which is the non-asymptotic core.
    • The general (non-diagonal) bound is conditional on the same
      Lindblad–Uhlmann hypothesis that gates every quantum DPI
      theorem in the framework.

  Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerB.HolevoDiagonalDischarge
import UnifiedTheory.LayerB.GibbsInequality
import Mathlib.Analysis.Matrix.Order

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumStein

open Matrix Complex
open scoped ComplexOrder
open scoped MatrixOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.LogSumInequality
open UnifiedTheory.LayerB.DiagonalDensityMatrix
open UnifiedTheory.LayerB.HolevoBoundQuantum
open UnifiedTheory.LayerB.HolevoDiagonalDischarge

variable {n : ℕ}

/-! ## 1. The binary hypothesis test -/

/-- A **binary hypothesis test** on an `n`-level quantum system: a
    Hermitian operator `accept` with `0 ≤ accept ≤ I`, i.e. both
    `accept` and `I − accept` are positive semidefinite.  Represents
    the POVM `{accept, I − accept}` whose outcomes are interpreted as
    "accept ρ" / "accept σ" in the hypothesis-testing problem.

    (Lean note: the natural mathematical name `Π` is a reserved token
    in Lean 4, so we use `accept` here.) -/
structure BinaryHypothesisTest (n : ℕ) where
  /-- The acceptance operator (PSD, ≤ I). -/
  accept : Matrix (Fin n) (Fin n) ℂ
  /-- The acceptance operator is Hermitian. -/
  isHerm : accept.IsHermitian
  /-- The acceptance operator is positive semidefinite. -/
  posSemidef : accept.PosSemidef
  /-- `I − accept` is positive semidefinite (i.e. accept ≤ I in the
      Löwner order). -/
  posSemidefComp : (1 - accept).PosSemidef

namespace BinaryHypothesisTest

/-- The complementary operator `I − accept` is Hermitian (immediate
    from `posSemidefComp`). -/
theorem complement_isHerm (T : BinaryHypothesisTest n) :
    (1 - T.accept).IsHermitian := T.posSemidefComp.isHermitian

end BinaryHypothesisTest

/-! ## 2. Type-I and Type-II errors -/

/-- **Type-I error**: probability of saying "σ" when the true state
    is ρ.  `α(accept, ρ) := Re(Tr((I − accept) · ρ))`. -/
noncomputable def typeI (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) : ℝ :=
  (Matrix.trace ((1 - T.accept) * ρ.M)).re

/-- **Type-II error**: probability of saying "ρ" when the true state
    is σ.  `β(accept, σ) := Re(Tr(accept · σ))`. -/
noncomputable def typeII (T : BinaryHypothesisTest n)
    (σ : ComplexDensityMatrix n) : ℝ :=
  (Matrix.trace (T.accept * σ.M)).re

/-! ## 3. Helper: `Tr(A · B)` is real and non-negative for PSD A, B -/

/-- **Trace-of-product nonnegativity.**  For two positive semidefinite
    matrices `A, B`, the trace `Tr(A · B)` has non-negative real part.
    Proof: write `A = X⋆ · X` (PSD factorisation via
    `CStarAlgebra.nonneg_iff_eq_star_mul_self`); then
    `Tr(A · B) = Tr(X⋆ X B) = Tr(X B X⋆)` by cyclicity, and
    `X B X⋆` is PSD (`PosSemidef.mul_mul_conjTranspose_same`), so its
    trace is non-negative real. -/
theorem re_trace_mul_nonneg_of_posSemidef
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  classical
  -- Factor A = X⋆ * X via the C-star algebra characterisation
  -- (matrix `star` is `conjTranspose`).
  obtain ⟨X, hXdef⟩ :=
    (CStarAlgebra.nonneg_iff_eq_star_mul_self
      (a := A)).mp hA.nonneg
  -- `star X` on matrices is `Xᴴ`.
  have hXdef' : A = X.conjTranspose * X := by
    rw [hXdef]; rfl
  -- Build X · B · X⋆ which is PSD.
  have h_PSD : (X * B * X.conjTranspose).PosSemidef :=
    hB.mul_mul_conjTranspose_same X
  -- Tr(A · B) = Tr(X⋆ · X · B) = Tr(X · B · X⋆) by cyclicity.
  have h_cyc :
      Matrix.trace (A * B) = Matrix.trace (X * B * X.conjTranspose) := by
    rw [hXdef']
    rw [show X.conjTranspose * X * B = X.conjTranspose * (X * B) from by
          rw [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
  rw [h_cyc]
  have h_tr_nonneg : (0 : ℂ) ≤ (X * B * X.conjTranspose).trace :=
    h_PSD.trace_nonneg
  rw [Complex.le_def] at h_tr_nonneg
  exact h_tr_nonneg.1

/-- **Trace of product of PSD is real.**  Companion of
    `re_trace_mul_nonneg_of_posSemidef`: the imaginary part of
    `Tr(A · B)` vanishes for two PSD A, B. -/
theorem im_trace_mul_eq_zero_of_posSemidef
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.trace (A * B)).im = 0 := by
  classical
  obtain ⟨X, hXdef⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hXdef' : A = X.conjTranspose * X := by
    rw [hXdef]; rfl
  have h_PSD : (X * B * X.conjTranspose).PosSemidef :=
    hB.mul_mul_conjTranspose_same X
  have h_cyc :
      Matrix.trace (A * B) = Matrix.trace (X * B * X.conjTranspose) := by
    rw [hXdef']
    rw [show X.conjTranspose * X * B = X.conjTranspose * (X * B) from by
          rw [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
  rw [h_cyc]
  have h_tr_nonneg : (0 : ℂ) ≤ (X * B * X.conjTranspose).trace :=
    h_PSD.trace_nonneg
  rw [Complex.le_def] at h_tr_nonneg
  exact h_tr_nonneg.2.symm

/-! ## 4. Type-I and Type-II are in `[0, 1]` -/

/-- The Type-II error is non-negative. -/
theorem typeII_nonneg (T : BinaryHypothesisTest n)
    (σ : ComplexDensityMatrix n) :
    0 ≤ typeII T σ :=
  re_trace_mul_nonneg_of_posSemidef T.posSemidef
    (posSemidef_of_ComplexDensityMatrix σ)

/-- The Type-I error is non-negative. -/
theorem typeI_nonneg (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) :
    0 ≤ typeI T ρ :=
  re_trace_mul_nonneg_of_posSemidef T.posSemidefComp
    (posSemidef_of_ComplexDensityMatrix ρ)

/-- **Acceptance + Type-I identity.**  For any state ρ,
      `Re(Tr(accept · ρ)) + Re(Tr((I − accept) · ρ))  =  Re(Tr(ρ)) = 1`. -/
theorem acceptance_plus_typeI_eq_one (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) :
    (Matrix.trace (T.accept * ρ.M)).re + typeI T ρ = 1 := by
  unfold typeI
  rw [← Complex.add_re]
  have h_sum_mul :
      T.accept * ρ.M + (1 - T.accept) * ρ.M = ρ.M := by
    rw [← Matrix.add_mul]
    have h_add : T.accept + (1 - T.accept)
            = (1 : Matrix (Fin n) (Fin n) ℂ) := by abel
    rw [h_add, Matrix.one_mul]
  rw [show Matrix.trace (T.accept * ρ.M)
          + Matrix.trace ((1 - T.accept) * ρ.M)
        = Matrix.trace (T.accept * ρ.M + (1 - T.accept) * ρ.M) from
        (Matrix.trace_add _ _).symm,
      h_sum_mul, ρ.hTrace]
  simp

/-- **Type-II error ≤ 1**: since `Tr(accept·σ) + Re(Tr((I−accept)·σ))
    = 1` and the second is non-negative. -/
theorem typeII_le_one (T : BinaryHypothesisTest n)
    (σ : ComplexDensityMatrix n) :
    typeII T σ ≤ 1 := by
  have h_sum := acceptance_plus_typeI_eq_one T σ
  have h_nn : 0 ≤ typeI T σ := typeI_nonneg T σ
  -- typeII T σ = (Tr(accept · σ)).re, which is the first summand.
  change (Matrix.trace (T.accept * σ.M)).re ≤ 1
  linarith

/-- **Type-I error ≤ 1**: same argument, swapping accept and (I − accept). -/
theorem typeI_le_one (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) :
    typeI T ρ ≤ 1 := by
  have h_sum := acceptance_plus_typeI_eq_one T ρ
  have h_nn : 0 ≤ (Matrix.trace (T.accept * ρ.M)).re :=
    re_trace_mul_nonneg_of_posSemidef T.posSemidef
      (posSemidef_of_ComplexDensityMatrix ρ)
  linarith

/-- **Type-I error is a probability**: `0 ≤ α ≤ 1`. -/
theorem typeI_in_unit_interval (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) :
    0 ≤ typeI T ρ ∧ typeI T ρ ≤ 1 :=
  ⟨typeI_nonneg T ρ, typeI_le_one T ρ⟩

/-- **Type-II error is a probability**: `0 ≤ β ≤ 1`. -/
theorem typeII_in_unit_interval (T : BinaryHypothesisTest n)
    (σ : ComplexDensityMatrix n) :
    0 ≤ typeII T σ ∧ typeII T σ ≤ 1 :=
  ⟨typeII_nonneg T σ, typeII_le_one T σ⟩

/-! ## 5. The binary outcome probability vector -/

/-- Pre-form: `Re(Tr(accept · ρ)) = 1 − typeI T ρ`. -/
theorem acceptance_eq_one_sub_typeI (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) :
    (Matrix.trace (T.accept * ρ.M)).re = 1 - typeI T ρ := by
  have h := acceptance_plus_typeI_eq_one T ρ
  linarith

/-- The **binary outcome distribution** of the test on a state ρ:
    coordinate 0 is the acceptance probability `Re(Tr(accept · ρ))`,
    coordinate 1 is the rejection probability `Re(Tr((I − accept)·ρ))`. -/
noncomputable def binaryOutcome (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) : ProbabilityVector (Fin 2) where
  p i := if i = 0 then (Matrix.trace (T.accept * ρ.M)).re else typeI T ρ
  nonneg i := by
    by_cases hi : i = 0
    · rw [if_pos hi]
      exact re_trace_mul_nonneg_of_posSemidef T.posSemidef
              (posSemidef_of_ComplexDensityMatrix ρ)
    · rw [if_neg hi]
      exact typeI_nonneg T ρ
  sum_one := by
    rw [Fin.sum_univ_two]
    change (if (0 : Fin 2) = 0 then (Matrix.trace (T.accept * ρ.M)).re
              else typeI T ρ)
          + (if (1 : Fin 2) = 0 then (Matrix.trace (T.accept * ρ.M)).re
              else typeI T ρ) = 1
    rw [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    exact acceptance_plus_typeI_eq_one T ρ

@[simp]
theorem binaryOutcome_apply_zero (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) :
    (binaryOutcome T ρ).p 0 = (Matrix.trace (T.accept * ρ.M)).re := by
  change (if (0 : Fin 2) = 0
            then (Matrix.trace (T.accept * ρ.M)).re else typeI T ρ)
       = (Matrix.trace (T.accept * ρ.M)).re
  rw [if_pos rfl]

@[simp]
theorem binaryOutcome_apply_one (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) :
    (binaryOutcome T ρ).p 1 = typeI T ρ := by
  change (if (1 : Fin 2) = 0
            then (Matrix.trace (T.accept * ρ.M)).re else typeI T ρ)
       = typeI T ρ
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-! ## 6. Promoting the test to a `QuantumMeasurement` -/

/-- A `BinaryHypothesisTest` packages into a
    `QuantumMeasurement n (Fin 2)` via the binary outcome
    distribution. -/
noncomputable def binaryMeasurement (T : BinaryHypothesisTest n) :
    QuantumMeasurement n (Fin 2) where
  apply ρ := binaryOutcome T ρ

@[simp]
theorem binaryMeasurement_apply (T : BinaryHypothesisTest n)
    (ρ : ComplexDensityMatrix n) :
    (binaryMeasurement T).apply ρ = binaryOutcome T ρ := rfl

/-! ## 7. The single-copy Stein bound (gated form) -/

/-- **Single-copy quantum Stein bound (general, conditional).**

    Under the named monotonicity hypothesis
    `QuantumRelativeEntropyMonotonicity n (Fin 2)` — the
    Lindblad-Uhlmann data-processing inequality applied to the
    binary-outcome measurement channel — the classical KL divergence
    of the post-measurement BINARY distributions is bounded above by
    Umegaki's quantum relative entropy:

      `KL(binaryOutcome T ρ ‖ binaryOutcome T σ)  ≤  S(ρ ‖ σ).`

    This is the single-copy non-asymptotic Stein inequality.  The
    asymptotic limit `lim_{n→∞} −(1/n) log β_n = S(ρ ‖ σ)` requires
    tensor-power machinery (out of scope for this file). -/
theorem stein_single_copy_of_monotonicity
    (T : BinaryHypothesisTest n)
    (ρ σ : ComplexDensityMatrix n)
    (hMono : QuantumRelativeEntropyMonotonicity n (Fin 2)) :
    klDivergence (binaryOutcome T ρ) (binaryOutcome T σ)
      ≤ umegakiRelativeEntropy ρ σ := by
  -- The monotonicity hypothesis applied to the binary measurement
  -- gives the bound for the post-measurement distributions, which are
  -- exactly our binary outcomes.
  exact hMono ρ σ (binaryMeasurement T)

/-! ## 8. The diagonal Stein bound (unconditional)

For diagonal states and diagonal tests in the canonical basis, the
binary outcome distribution factors through a stochastic 2×n channel,
so the bound becomes a direct consequence of the unconditional
classical DPI of `ClassicalChannelDPI.lean`. -/

/-- The stochastic 2 × n matrix sending basis index `k : Fin n` to
    the binary outcome distribution `(Pi k, 1 − Pi k)` on `Fin 2`. -/
noncomputable def diagonalBinaryStochastic
    (Pi : ProbabilityVector (Fin n)) : StochasticMatrix (Fin n) (Fin 2) where
  M b a := if b = 0 then Pi.p a else 1 - Pi.p a
  nonneg b a := by
    by_cases hb : b = 0
    · rw [if_pos hb]; exact Pi.nonneg a
    · rw [if_neg hb]; linarith [Pi.le_one a]
  col_sum_one a := by
    rw [Fin.sum_univ_two]
    change (if (0 : Fin 2) = 0 then Pi.p a else 1 - Pi.p a)
            + (if (1 : Fin 2) = 0 then Pi.p a else 1 - Pi.p a) = 1
    rw [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    ring

/-- The **diagonal binary hypothesis test** with acceptance operator
    `diag(Pi)`.  Both `diag(Pi)` and `I − diag(Pi) = diag(1 − Pi)` are
    diagonal with entries in `[0, 1]`, hence both PSD. -/
noncomputable def diagonalTest (Pi : ProbabilityVector (Fin n)) :
    BinaryHypothesisTest n where
  accept := Matrix.diagonal (fun i => (Pi.p i : ℂ))
  isHerm := by
    unfold Matrix.IsHermitian
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    rw [_root_.Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    have hi : (0 : ℝ) ≤ Pi.p i := Pi.nonneg i
    rw [show ((Pi.p i : ℂ)) = ((Pi.p i : ℝ) : ℂ) from rfl,
        Complex.le_def]
    refine ⟨?_, ?_⟩
    · simp only [Complex.zero_re, Complex.ofReal_re]; exact hi
    · simp only [Complex.zero_im, Complex.ofReal_im]
  posSemidefComp := by
    -- 1 - diag(Pi) = diag(1 - Pi)
    have h_eq :
        (1 : Matrix (Fin n) (Fin n) ℂ)
            - Matrix.diagonal (fun i => (Pi.p i : ℂ))
          = Matrix.diagonal (fun i => ((1 - Pi.p i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
            Matrix.diagonal_apply_eq]
        push_cast; ring
      · rw [Matrix.sub_apply, Matrix.one_apply_ne hij,
            Matrix.diagonal_apply_ne _ hij,
            Matrix.diagonal_apply_ne _ hij]
        ring
    rw [h_eq, Matrix.posSemidef_diagonal_iff]
    intro i
    have hi : Pi.p i ≤ 1 := Pi.le_one i
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · simp; linarith
    · simp

/-- The acceptance entry of the diagonal test on a diagonal state
    `diag(P)` equals the inner product `∑ k, Pi k · P k`. -/
theorem diagonalTest_acceptance
    (Pi P : ProbabilityVector (Fin n)) :
    (Matrix.trace ((diagonalTest Pi).accept
                    * (diagonalDensityMatrix P).M)).re
      = ∑ k, Pi.p k * P.p k := by
  change (Matrix.trace (Matrix.diagonal (fun i => (Pi.p i : ℂ))
                        * Matrix.diagonal (fun i => (P.p i : ℂ)))).re
        = ∑ k, Pi.p k * P.p k
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [show (∑ k, (Pi.p k : ℂ) * (P.p k : ℂ))
         = ((∑ k, Pi.p k * P.p k : ℝ) : ℂ) from by
        push_cast; rfl]
  rw [Complex.ofReal_re]

/-- The Type-I (rejection) entry of the diagonal test on a diagonal
    state `diag(P)` equals `∑ k, (1 − Pi k) · P k`. -/
theorem diagonalTest_typeI
    (Pi P : ProbabilityVector (Fin n)) :
    typeI (diagonalTest Pi) (diagonalDensityMatrix P)
      = ∑ k, (1 - Pi.p k) * P.p k := by
  unfold typeI
  change (Matrix.trace ((1 - Matrix.diagonal (fun i => (Pi.p i : ℂ)))
                        * Matrix.diagonal (fun i => (P.p i : ℂ)))).re
       = ∑ k, (1 - Pi.p k) * P.p k
  have h_eq :
      (1 : Matrix (Fin n) (Fin n) ℂ)
          - Matrix.diagonal (fun i => (Pi.p i : ℂ))
        = Matrix.diagonal (fun i => ((1 - Pi.p i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
          Matrix.diagonal_apply_eq]
      push_cast; ring
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij,
          Matrix.diagonal_apply_ne _ hij,
          Matrix.diagonal_apply_ne _ hij]
      ring
  rw [h_eq, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [show (∑ k, ((1 - Pi.p k : ℝ) : ℂ) * (P.p k : ℂ))
         = ((∑ k, (1 - Pi.p k) * P.p k : ℝ) : ℂ) from by
        push_cast; rfl]
  rw [Complex.ofReal_re]

/-- The binary outcome distribution of the diagonal test on a
    diagonal state coincides with the pushforward of the underlying
    probability vector through the `diagonalBinaryStochastic Pi`
    channel. -/
theorem binaryOutcome_diagonalTest_eq_push
    (Pi P : ProbabilityVector (Fin n)) :
    binaryOutcome (diagonalTest Pi) (diagonalDensityMatrix P)
      = (diagonalBinaryStochastic Pi).push P := by
  apply probabilityVector_ext
  intro i
  -- Two cases for i : Fin 2.
  match i with
  | ⟨0, _⟩ =>
    -- Coordinate 0: acceptance.
    change (binaryOutcome (diagonalTest Pi) (diagonalDensityMatrix P)).p 0
         = ((diagonalBinaryStochastic Pi).push P).p 0
    rw [binaryOutcome_apply_zero, diagonalTest_acceptance]
    change (∑ k, Pi.p k * P.p k)
            = ∑ a, (diagonalBinaryStochastic Pi).M 0 a * P.p a
    apply Finset.sum_congr rfl
    intro a _
    change Pi.p a * P.p a
            = (if (0 : Fin 2) = 0 then Pi.p a else 1 - Pi.p a) * P.p a
    rw [if_pos rfl]
  | ⟨1, _⟩ =>
    -- Coordinate 1: rejection.
    change (binaryOutcome (diagonalTest Pi) (diagonalDensityMatrix P)).p 1
         = ((diagonalBinaryStochastic Pi).push P).p 1
    rw [binaryOutcome_apply_one, diagonalTest_typeI]
    change (∑ k, (1 - Pi.p k) * P.p k)
            = ∑ a, (diagonalBinaryStochastic Pi).M 1 a * P.p a
    apply Finset.sum_congr rfl
    intro a _
    change (1 - Pi.p a) * P.p a
            = (if (1 : Fin 2) = 0 then Pi.p a else 1 - Pi.p a) * P.p a
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- **UNCONDITIONAL diagonal Stein bound.**

    For two probability vectors `P, Q : ProbabilityVector (Fin n)`
    (viewed as the diagonals of two diagonal density matrices) and
    any diagonal binary test `accept = diag(Pi)`, the classical KL
    divergence of the binary outcome distributions is bounded above
    by the **classical** KL divergence of `P` and `Q`:

      `KL(binaryOutcome (diagonalTest Pi) (diagDM P) ‖
          binaryOutcome (diagonalTest Pi) (diagDM Q))
            ≤  klDivergence P Q.`

    The right-hand side is the diagonal-case Umegaki relative entropy
    (it equals `umegakiRelativeEntropy (diagDM P) (diagDM Q)` once the
    diagonal-bridge identity is in scope; the bound as stated here
    is the **classical-DPI form** that the framework can deliver
    UNCONDITIONALLY).

    Proof: factor through the stochastic 2×n channel
    `diagonalBinaryStochastic Pi` and apply
    `klDivergence_contracts_under_stochastic_of_logsum`
    (the unconditional classical DPI of `ClassicalChannelDPI.lean`,
    discharged by `logSumInequality_holds`). -/
theorem stein_single_copy_diagonal
    (Pi P Q : ProbabilityVector (Fin n))
    (hAC : IsAbsolutelyContinuous P Q) :
    klDivergence
        (binaryOutcome (diagonalTest Pi) (diagonalDensityMatrix P))
        (binaryOutcome (diagonalTest Pi) (diagonalDensityMatrix Q))
      ≤ klDivergence P Q := by
  rw [binaryOutcome_diagonalTest_eq_push Pi P,
      binaryOutcome_diagonalTest_eq_push Pi Q]
  exact klDivergence_contracts_under_stochastic_of_logsum
          (diagonalBinaryStochastic Pi) P Q hAC logSumInequality_holds

/-! ## 9. Operational lower bound on the Type-II error

In the literature, the operational form of the single-copy Stein
bound expresses the Type-II error as bounded below by an exponential
in the quantum relative entropy.  The non-asymptotic form that holds
unconditionally on the diagonal (and conditionally in general) is:

  binaryKL(typeII T σ, 1 − typeII T σ ‖ typeII T ρ, 1 − typeII T ρ)
    ≤ KL(binaryOutcome T ρ ‖ binaryOutcome T σ)   [classical DPI / Stein]
    ≤ S(ρ‖σ)                                       [Lindblad–Uhlmann]

Below we expose the gated and the diagonal corollaries in their
inequality form; the explicit `exp(−S)` lower bound on `β` follows
by exponentiating after isolating the dominant term in the KL — an
algebraic manipulation that is standard but bulky in Lean.  We ship
the inequality form (the operational headline) and leave the
exponentiation step to downstream callers. -/

/-- **Operational Stein corollary (gated form).** Under the
    monotonicity hypothesis, the classical binary KL of the
    post-measurement distributions of ρ vs σ is bounded above by
    the quantum relative entropy.  This is the same inequality as
    `stein_single_copy_of_monotonicity` packaged as an "operational"
    statement: it says that any test discriminating ρ from σ pays at
    most `S(ρ ‖ σ)` worth of distinguishability in the binary KL. -/
theorem stein_operational_of_monotonicity
    (T : BinaryHypothesisTest n)
    (ρ σ : ComplexDensityMatrix n)
    (hMono : QuantumRelativeEntropyMonotonicity n (Fin 2)) :
    klDivergence (binaryOutcome T ρ) (binaryOutcome T σ)
      ≤ umegakiRelativeEntropy ρ σ :=
  stein_single_copy_of_monotonicity T ρ σ hMono

/-- **Operational Stein corollary (diagonal unconditional form).**
    No `QuantumRelativeEntropyMonotonicity` hypothesis required for
    diagonal states with diagonal tests. -/
theorem stein_operational_diagonal
    (Pi P Q : ProbabilityVector (Fin n))
    (hAC : IsAbsolutelyContinuous P Q) :
    klDivergence
        (binaryOutcome (diagonalTest Pi) (diagonalDensityMatrix P))
        (binaryOutcome (diagonalTest Pi) (diagonalDensityMatrix Q))
      ≤ klDivergence P Q :=
  stein_single_copy_diagonal Pi P Q hAC

end UnifiedTheory.LayerB.QuantumStein
