/-
  LayerB/UmegakiDiagonalBridge.lean
  ──────────────────────────────────

  **Diagonal Umegaki = classical KL** — the bridge identifying
  Umegaki's quantum relative entropy on two diagonal density
  matrices with the classical KL divergence of their diagonals.

  The identity is

      umegakiRelativeEntropy (diagonalDensityMatrix P)
                             (diagonalDensityMatrix Q)
        = klDivergence P Q

  under absolute continuity `P ≪ Q`.

  The proof works modulo one analytic input: the continuous
  functional calculus on a diagonal matrix is itself diagonal,

      cfc f (diagonal d)  =  diagonal (f ∘ d).

  This is true but non-trivial in Mathlib because
  `Matrix.IsHermitian.cfc` is defined through the spectral theorem
  with eigenvalues sorted antitone, which differs from the diagonal
  entries by a permutation that has to be unwound.  We isolate the
  analytic input as a `Prop`-valued hypothesis
  `CFCOnDiagonalIsEntrywise Real.log` (Margolus-Levitin pattern),
  prove the bridge unconditionally from it, and leave the
  permutation-unwinding discharge to a follow-up.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `CFCOnDiagonalIsEntrywise f`        — the hypothesis.
    2. `umegakiRelativeEntropy_diagonal_eq_klDivergence`
                                            — the conditional bridge.

  DEFERRED:
    * Discharging `CFCOnDiagonalIsEntrywise Real.log` (and more
      generally for any `f : ℝ → ℝ`) requires reconciling
      `Mathlib.Matrix.IsHermitian.cfc`'s sorted-eigenvalue
      construction with the entry-wise interpretation on a
      diagonal matrix.
-/

import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.DiagonalDensityMatrix
import UnifiedTheory.LayerB.ClassicalRelativeEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.UmegakiDiagonalBridge

open Matrix Complex
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.DiagonalDensityMatrix
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy

variable {n : ℕ}

/-! ## 1. The analytic-input hypothesis -/

/-- **Hypothesis**: the continuous functional calculus of `f : ℝ → ℝ`
    on a diagonal complex matrix is itself diagonal, with `f`
    applied entry-wise:

      `cfc f (diagonal (ofReal ∘ d)) = diagonal (ofReal ∘ f ∘ d)`.

    This statement is true (every diagonal Hermitian matrix's CFC
    is again diagonal), but its Mathlib proof requires reconciling
    `IsHermitian.cfc`'s spectral-theorem construction with the
    fact that eigenvalues of a diagonal matrix are a *sorted*
    permutation of the diagonal entries.  We carry it as a
    hypothesis in the Margolus-Levitin pattern, exactly as
    `LogSumInequality` and `QuantumRelativeEntropyMonotonicity`
    are carried elsewhere in this stack. -/
def CFCOnDiagonalIsEntrywise (n : ℕ) (f : ℝ → ℝ) : Prop :=
  ∀ (d : Fin n → ℝ),
    cfc f (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)))
      = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ))

/-! ## 2. The diagonal-Umegaki = classical-KL bridge -/

/-- **Conditional diagonal Umegaki = KL.**  Under absolute
    continuity `P ≪ Q` and the diagonal-CFC hypothesis, the
    Umegaki quantum relative entropy of the diagonal embeddings
    of two probability vectors equals the classical KL divergence:

      S(diag(P) ‖ diag(Q))  =  KL(P ‖ Q).

    Proof outline (modulo `hCFC`):
      log(diag(P)) = diag(log ∘ P),
      log(diag(P)) − log(diag(Q)) = diag(log P − log Q),
      diag(P) · diag(log P − log Q) = diag(P · (log P − log Q)),
      Trace = ∑ P_i (log P_i − log Q_i),
      Real part = same,
      = ∑ P_i log(P_i / Q_i)  (by `Real.log_div` under AC,
                                trivially at zero summands),
      = ∑ klTerm P_i Q_i = KL(P ‖ Q). -/
theorem umegakiRelativeEntropy_diagonal_eq_klDivergence
    (P Q : ProbabilityVector (Fin n))
    (hAC : IsAbsolutelyContinuous P Q)
    (hCFC : CFCOnDiagonalIsEntrywise n Real.log) :
    umegakiRelativeEntropy (diagonalDensityMatrix P)
                           (diagonalDensityMatrix Q)
      = klDivergence P Q := by
  -- Step 1: unfold and identify the diagonal forms of log ρ, log σ.
  unfold umegakiRelativeEntropy operatorLog cfcρ
  -- (diagonalDensityMatrix P).M = diagonal (fun i => (P.p i : ℂ))
  have h_ρM : (diagonalDensityMatrix P).M
                = Matrix.diagonal (fun i => ((P.p i : ℝ) : ℂ)) := rfl
  have h_σM : (diagonalDensityMatrix Q).M
                = Matrix.diagonal (fun i => ((Q.p i : ℝ) : ℂ)) := rfl
  rw [h_ρM, h_σM]
  -- Apply the hypothesis to identify cfc Real.log of each diagonal.
  rw [hCFC P.p, hCFC Q.p]
  -- Combine diag - diag into diag and then diag · diag.
  rw [Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal]
  -- Trace of diagonal = sum of diagonal entries.
  rw [Matrix.trace_diagonal]
  -- Per-summand identification.
  rw [Complex.re_sum]
  unfold klDivergence
  apply Finset.sum_congr rfl
  intro i _
  -- LHS: ( (P.p i : ℂ) · ((log P.p i : ℂ) − (log Q.p i : ℂ)) ).re
  -- RHS: klTerm (P.p i) (Q.p i)
  -- Rewrite the LHS as a single real cast, then take real part.
  have h_lhs :
      (((P.p i : ℝ) : ℂ) *
        ((((Real.log (P.p i)) : ℝ) : ℂ) - (((Real.log (Q.p i)) : ℝ) : ℂ))).re
        = P.p i * (Real.log (P.p i) - Real.log (Q.p i)) := by
    simp [Complex.mul_re]
  rw [h_lhs, klTerm_eq]
  -- Goal: P.p i * (log P.p i - log Q.p i) = P.p i * log (P.p i / Q.p i)
  by_cases hpi : P.p i = 0
  · rw [hpi]; ring
  · have hqi : Q.p i ≠ 0 := hAC i hpi
    rw [Real.log_div hpi hqi]

end UnifiedTheory.LayerB.UmegakiDiagonalBridge
