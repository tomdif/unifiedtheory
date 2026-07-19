/-
  LayerB/DiagonalQuantumDPI.lean
  ───────────────────────────────

  **Diagonal quantum Data-Processing Inequality**, obtained as a
  thin lift of `ClassicalChannelDPI` to the diagonal and
  common-spectrum quantum vocabulary.  No new analytic content; the
  log-sum inequality is still carried as a hypothesis.

  The whole purpose of this file is to lock the bridge

      classical stochastic DPI
        ≡ diagonal quantum DPI
        ≡ commuting / common-spectrum spectral DPI

  so downstream measurement-channel / Holevo statements can refer
  to any layer of this stack uniformly.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `diagonal_relative_entropy_contracts_under_stochastic_of_logsum`
         — DPI in `relativeEntropyDiagonal` form.
    2. `spectral_relative_entropy_diagonal_channel_DPI_of_logsum`
         — same content rephrased for `commonPairOfDiagonal`
           (spectral vocabulary).
    3. `id_diagonal_relative_entropy_eq`
         — sanity check: pushing both arguments through the
           identity channel does not change the relative entropy.
-/

import UnifiedTheory.LayerB.ClassicalChannelDPI
import UnifiedTheory.LayerB.DiagonalRelativeEntropy
import UnifiedTheory.LayerB.SpectralRelativeEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.DiagonalQuantumDPI

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.DiagonalRelativeEntropy
open UnifiedTheory.LayerB.SpectralRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. DPI in diagonal-quantum vocabulary -/

/-- **Diagonal quantum DPI (conditional on log-sum).**  Pushing two
    diagonal density matrices through a column-stochastic channel
    cannot increase their relative entropy:

      S_diag(T·P ‖ T·Q)   ≤   S_diag(P ‖ Q),

    provided `P ≪ Q` (without absolute continuity the Mathlib
    `Real.log 0 = 0` convention can artificially shrink the RHS
    and break the inequality).

    This is exactly the classical DPI rephrased in the diagonal
    quantum vocabulary; `relativeEntropyDiagonal` is definitionally
    `klDivergence`. -/
theorem diagonal_relative_entropy_contracts_under_stochastic_of_logsum
    (T : StochasticMatrix α β)
    (P Q : ProbabilityVector α)
    (hAC : IsAbsolutelyContinuous P Q)
    (hLogSum : LogSumInequality α) :
    relativeEntropyDiagonal (T.push P) (T.push Q)
      ≤ relativeEntropyDiagonal P Q :=
  klDivergence_contracts_under_stochastic_of_logsum T P Q hAC hLogSum

/-! ## 2. DPI in spectral / common-eigenbasis vocabulary -/

/-- **Spectral DPI for diagonal-embedding pairs (conditional on
    log-sum).**  Identical content to the diagonal version, but
    phrased through `commonPairOfDiagonal` so downstream
    measurement-channel statements can quote the spectral name. -/
theorem spectral_relative_entropy_diagonal_channel_DPI_of_logsum
    {n : ℕ}
    (T : StochasticMatrix (Fin n) (Fin n))
    (P Q : ProbabilityVector (Fin n))
    (hAC : IsAbsolutelyContinuous P Q)
    (hLogSum : LogSumInequality (Fin n)) :
    relativeEntropySpectral
        (commonPairOfDiagonal (T.push P) (T.push Q))
      ≤
    relativeEntropySpectral
        (commonPairOfDiagonal P Q) :=
  klDivergence_contracts_under_stochastic_of_logsum T P Q hAC hLogSum

/-! ## 3. Sanity check: identity channel -/

/-- Pushing both arguments through the identity stochastic channel
    leaves the diagonal relative entropy unchanged. -/
theorem id_diagonal_relative_entropy_eq [DecidableEq α]
    (P Q : ProbabilityVector α) :
    relativeEntropyDiagonal ((StochasticMatrix.id α).push P)
                            ((StochasticMatrix.id α).push Q)
      = relativeEntropyDiagonal P Q := by
  unfold relativeEntropyDiagonal klDivergence
  apply Finset.sum_congr rfl
  intro i _
  rw [StochasticMatrix.id_push, StochasticMatrix.id_push]

end UnifiedTheory.LayerB.DiagonalQuantumDPI
