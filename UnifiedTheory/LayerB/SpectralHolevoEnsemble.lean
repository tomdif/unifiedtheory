/-
  LayerB/SpectralHolevoEnsemble.lean
  ───────────────────────────────────

  **Spectral / common-eigenbasis Holevo χ.**  A vocabulary wrapper
  that lifts the classical Holevo precursor to a quantum-facing
  layer: a `SpectralEnsemble` is a probability-weighted family of
  `SpectralDensityMatrix`s sharing an opaque common-eigenbasis
  witness, and its χ is the classical χ of the underlying
  eigenvalue probability vectors.

  EXPLICIT SCOPE (same boundary as `SpectralRelativeEntropy.lean`):
    * classical / commuting / simultaneously-diagonalised states only,
    * NOT the full Holevo bound for arbitrary noncommuting
      quantum ensembles,
    * NOT Umegaki relative entropy,
    * NOT operator log or spectral functional calculus.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `SpectralEnsemble α n`
         — bundle (weights, state-family in `SpectralDensityMatrix n`,
            opaque `commonEigenbasis : Prop`).
    2. `toClassicalEnsemble S`
         — extract the eigenvalue probability vectors as a
           classical ensemble.
    3. `holevoChiSpectral S`        := classical χ on the extracted
                                       eigenvalue ensemble.
    4. `holevoChiSpectral_eq_classical`              (definitional).
    5. `holevoChiSpectral_nonneg`                    (Gibbs).
    6. `mapSpectralEnsemble`        — pushforward to a classical
                                       ensemble in `β`.
    7. `spectral_measurement_mutualInformation_le_holevoChi`
                                                       — the spectral
                                                         post-processing
                                                         bound.
    8. `mapSpectralEnsembleSpectral`
         — when the channel maps into `Fin m`, re-wrap as a
           SpectralEnsemble via the canonical diagonal embedding.
    9. `holevoChiSpectral_contracts_under_stochastic`
         — χ(E after T) ≤ χ(E) in pure spectral vocabulary
           (for channels into `Fin m`).
-/

import UnifiedTheory.LayerB.HolevoChi
import UnifiedTheory.LayerB.SpectralDensityMatrix

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.SpectralHolevo

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.Ensemble
open UnifiedTheory.LayerB.HolevoChi
open UnifiedTheory.LayerB.Spectral

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. Spectral ensemble bundle -/

/-- A finite labelled ensemble of `SpectralDensityMatrix`s sharing
    an opaque common-eigenbasis witness. -/
structure SpectralEnsemble (α : Type*) [Fintype α] (n : ℕ) where
  /-- Label weights `p(a)`. -/
  weight : ProbabilityVector α
  /-- Component spectral density matrices `ρ_a`. -/
  state : α → SpectralDensityMatrix n
  /-- Opaque witness that all `state a` are simultaneously
      diagonalizable.  Intentionally unconstrained at this stage
      of the development; a later refinement may tighten it. -/
  commonEigenbasis : Prop

/-! ## 2. Extraction to a classical ensemble of eigenvalues -/

/-- Extract the classical ensemble of eigenvalue probability vectors. -/
noncomputable def toClassicalEnsemble {n : ℕ}
    (S : SpectralEnsemble α n) : ClassicalEnsemble α (Fin n) where
  weight := S.weight
  state a := (S.state a).spectrum

@[simp]
theorem toClassicalEnsemble_weight {n : ℕ} (S : SpectralEnsemble α n) :
    (toClassicalEnsemble S).weight = S.weight := rfl

@[simp]
theorem toClassicalEnsemble_state {n : ℕ}
    (S : SpectralEnsemble α n) (a : α) :
    (toClassicalEnsemble S).state a = (S.state a).spectrum := rfl

/-! ## 3. Spectral Holevo χ -/

/-- **Spectral / common-eigenbasis Holevo χ.**  The Holevo χ of a
    common-eigenbasis ensemble is the classical χ of its
    eigenvalue ensemble.  Full quantum χ for non-commuting states
    is intentionally NOT defined here. -/
noncomputable def holevoChiSpectral {n : ℕ}
    (S : SpectralEnsemble α n) : ℝ :=
  holevoChiClassical (toClassicalEnsemble S)

/-- Definitional bridge. -/
theorem holevoChiSpectral_eq_classical {n : ℕ}
    (S : SpectralEnsemble α n) :
    holevoChiSpectral S = holevoChiClassical (toClassicalEnsemble S) :=
  rfl

/-! ## 4. Non-negativity -/

/-- **`χ_spectral(E) ≥ 0`.**  Gibbs corollary in spectral
    vocabulary. -/
theorem holevoChiSpectral_nonneg {n : ℕ} (S : SpectralEnsemble α n) :
    0 ≤ holevoChiSpectral S :=
  holevoChiClassical_nonneg (toClassicalEnsemble S)

/-! ## 5. Measurement of a spectral ensemble -/

/-- Pushforward of the eigenvalue ensemble through a stochastic
    channel.  Produces a classical ensemble in `β`. -/
noncomputable def mapSpectralEnsemble {n : ℕ}
    (S : SpectralEnsemble α n) (T : StochasticMatrix (Fin n) β) :
    ClassicalEnsemble α β :=
  mapStates (toClassicalEnsemble S) T

/-- **Spectral measurement bound.**  The mutual information of the
    post-measurement classical ensemble cannot exceed the spectral
    Holevo χ of the source:

      I(spectral E after T)   ≤   χ_spectral(E). -/
theorem spectral_measurement_mutualInformation_le_holevoChi {n : ℕ}
    (S : SpectralEnsemble α n) (T : StochasticMatrix (Fin n) β) :
    mutualInformation (mapSpectralEnsemble S T) ≤ holevoChiSpectral S := by
  unfold mapSpectralEnsemble holevoChiSpectral
  exact classical_measurement_mutualInformation_le_source_chi
    (toClassicalEnsemble S) T

/-! ## 6. Re-wrapping the post-processed ensemble -/

/-- When the channel target is `Fin m`, re-wrap the post-processed
    ensemble as a `SpectralEnsemble m` via the canonical diagonal
    embedding (each component becomes a diagonal density matrix
    whose spectrum is the pushed eigenvalue distribution). -/
noncomputable def mapSpectralEnsembleSpectral {n m : ℕ}
    (S : SpectralEnsemble α n) (T : StochasticMatrix (Fin n) (Fin m)) :
    SpectralEnsemble α m where
  weight := S.weight
  state a := spectralOfDiagonalDensity (T.push (S.state a).spectrum)
  commonEigenbasis := True

@[simp]
theorem mapSpectralEnsembleSpectral_state_spectrum {n m : ℕ}
    (S : SpectralEnsemble α n) (T : StochasticMatrix (Fin n) (Fin m))
    (a : α) :
    ((mapSpectralEnsembleSpectral S T).state a).spectrum
      = T.push (S.state a).spectrum := rfl

/-- **Spectral χ contracts under stochastic post-processing**
    (channel target `Fin m`):

      χ_spectral(E after T)   ≤   χ_spectral(E).

    Same content as `spectral_measurement_mutualInformation_le_holevoChi`,
    phrased in pure χ-on-both-sides form. -/
theorem holevoChiSpectral_contracts_under_stochastic {n m : ℕ}
    (S : SpectralEnsemble α n) (T : StochasticMatrix (Fin n) (Fin m)) :
    holevoChiSpectral (mapSpectralEnsembleSpectral S T)
      ≤ holevoChiSpectral S := by
  -- The two underlying classical ensembles are definitionally equal:
  --   (toClassicalEnsemble ∘ mapSpectralEnsembleSpectral)(S, T)
  --     and  mapStates (toClassicalEnsemble S) T
  -- both produce weight = S.weight and state a = T.push (S.state a).spectrum,
  -- because spectralOfDiagonalDensity's .spectrum field is the input
  -- probability vector by definition.  Hence the mutual informations
  -- coincide by `rfl`, and the result is the classical contraction theorem.
  calc holevoChiSpectral (mapSpectralEnsembleSpectral S T)
      = mutualInformation (mapStates (toClassicalEnsemble S) T) := rfl
    _ ≤ mutualInformation (toClassicalEnsemble S) :=
          mutualInformation_contracts_under_stochastic _ _
    _ = holevoChiSpectral S := rfl

end UnifiedTheory.LayerB.SpectralHolevo
