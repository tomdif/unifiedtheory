/-
  LayerB/MeasurementChannel.lean
  ───────────────────────────────

  **Measurement channels on diagonal / common-spectrum quantum
  states**, packaged as classical stochastic pushforwards of the
  eigenvalue probability vector.

  Conceptually:
      A measurement with classical outcome distribution is, on the
      diagonal of the density matrix, exactly a column-stochastic
      map acting on the eigenvalue probabilities.  This file fixes
      that identification and lifts the diagonal DPI to a quantum-
      to-classical statement *without* invoking full Umegaki
      relative entropy.

  Still conditional on the log-sum inequality.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `diagonalMeasurementChannel`
         — `T·P` as a "measurement of P with readout T".
    2. `measureSpectral`
         — same, taking the spectrum of a `SpectralDensityMatrix`.
    3. `measure_commonPair`
         — measurement of both members of a `CommonSpectralPair`.
    4. `measureSpectral_apply`             (definitional rfl).
    5. `measurement_channel_preserves_probability_total`
         — Σ outcome probabilities = 1 (trivially).
    6. `measurement_relative_entropy_DPI_of_logsum`
         — quantum-to-classical DPI for `CommonSpectralPair`:
           KL on outcomes ≤ S_spectral.
    7. `measurement_diagonal_DPI_of_logsum`
         — same lifted from `relativeEntropyDiagonal`.
-/

import UnifiedTheory.LayerB.DiagonalQuantumDPI

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.MeasurementChannel

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.DiagonalRelativeEntropy
open UnifiedTheory.LayerB.SpectralRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.Spectral

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. Diagonal measurement channel -/

/-- A *diagonal measurement channel*: viewing a column-stochastic
    matrix `T : α → β` as the readout statistics of measuring a
    diagonal density matrix with classical outcomes in `β`.
    The output is the probability vector of measurement outcomes. -/
noncomputable def diagonalMeasurementChannel
    (T : StochasticMatrix α β) (P : ProbabilityVector α) :
    ProbabilityVector β :=
  T.push P

@[simp]
theorem diagonalMeasurementChannel_apply
    (T : StochasticMatrix α β) (P : ProbabilityVector α) (b : β) :
    (diagonalMeasurementChannel T P).p b = ∑ a, T.M b a * P.p a := rfl

/-- The measurement outcome distribution sums to one (trivially, by
    `ProbabilityVector`). -/
theorem measurement_channel_preserves_probability_total
    (T : StochasticMatrix α β) (P : ProbabilityVector α) :
    ∑ b, (diagonalMeasurementChannel T P).p b = 1 :=
  (diagonalMeasurementChannel T P).sum_one

/-! ## 2. Measurement of a spectral density matrix -/

/-- Measure a `SpectralDensityMatrix n` with classical readout `T`,
    returning the outcome probability vector.  Operationally: read
    off the spectrum, then push it through the stochastic readout. -/
noncomputable def measureSpectral {n : ℕ}
    (T : StochasticMatrix (Fin n) β)
    (ρ : SpectralDensityMatrix n) : ProbabilityVector β :=
  T.push ρ.spectrum

@[simp]
theorem measureSpectral_apply {n : ℕ}
    (T : StochasticMatrix (Fin n) β)
    (ρ : SpectralDensityMatrix n) (b : β) :
    (measureSpectral T ρ).p b = ∑ i, T.M b i * ρ.spectrum.p i := rfl

/-! ## 3. Measurement of a common-spectral pair -/

/-- Measure both members of a `CommonSpectralPair` with the same
    readout, producing two outcome distributions on `β`. -/
noncomputable def measure_commonPair {n : ℕ}
    (T : StochasticMatrix (Fin n) β)
    (S : CommonSpectralPair n) :
    ProbabilityVector β × ProbabilityVector β :=
  (measureSpectral T S.ρ, measureSpectral T S.σ)

/-! ## 4. Quantum-to-classical DPI (conditional on log-sum) -/

/-- **Quantum-to-classical DPI for a common-spectral pair (conditional
    on log-sum).**  Given absolute continuity of the eigenvalue
    spectra of `ρ` and `σ`, the KL divergence between the two
    measurement outcome distributions cannot exceed the spectral
    relative entropy of the pair:

      KL( T·ρ.spectrum ‖ T·σ.spectrum )   ≤   S_spectral(ρ, σ). -/
theorem measurement_relative_entropy_DPI_of_logsum {n : ℕ}
    (T : StochasticMatrix (Fin n) β)
    (S : CommonSpectralPair n)
    (hAC : IsAbsolutelyContinuous S.ρ.spectrum S.σ.spectrum)
    (hLogSum : LogSumInequality (Fin n)) :
    klDivergence (measureSpectral T S.ρ) (measureSpectral T S.σ)
      ≤ relativeEntropySpectral S :=
  klDivergence_contracts_under_stochastic_of_logsum T S.ρ.spectrum S.σ.spectrum
    hAC hLogSum

/-- **Quantum-to-classical DPI in diagonal vocabulary (conditional
    on log-sum).**  Same content as
    `measurement_relative_entropy_DPI_of_logsum`, phrased directly
    in terms of `relativeEntropyDiagonal`. -/
theorem measurement_diagonal_DPI_of_logsum
    (T : StochasticMatrix α β)
    (P Q : ProbabilityVector α)
    (hAC : IsAbsolutelyContinuous P Q)
    (hLogSum : LogSumInequality α) :
    relativeEntropyDiagonal (diagonalMeasurementChannel T P)
                            (diagonalMeasurementChannel T Q)
      ≤ relativeEntropyDiagonal P Q :=
  DiagonalQuantumDPI.diagonal_relative_entropy_contracts_under_stochastic_of_logsum
    T P Q hAC hLogSum

end UnifiedTheory.LayerB.MeasurementChannel
