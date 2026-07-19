/-
  LayerB/SpectralRelativeEntropy.lean
  ────────────────────────────────────

  **Relative entropy for two density matrices that are simultaneously
   diagonalized (commuting-basis case).**  This is NOT the full
   Umegaki quantum relative entropy `Tr ρ(log ρ - log σ)` — operator
   log is intentionally not yet developed in this framework.  In the
   commuting case the full quantity collapses to the classical
   Kullback–Leibler divergence of the eigenvalue probability
   vectors, and that is what we package here.

  We bundle two `SpectralDensityMatrix`s with an *opaque* common-
  eigenbasis witness, mirroring the `diagonalizes : Prop` placeholder
  inside `SpectralDensityMatrix`.  A later refinement may tighten
  `commonEigenbasis` to a real predicate (e.g. existence of a single
  unitary diagonalizing both ρ and σ) without breaking this interface.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `CommonSpectralPair n`            — the (ρ, σ, witness) bundle.
    2. `relativeEntropySpectral S`       — KL of the supplied spectra.
    3. `spectralRelativeEntropy_eq_kl`   — definitional rfl.
    4. `spectralRelativeEntropy_self_eq_zero`
                                          — S(ρ‖ρ) = 0 (using the
                                            canonical self-pair).
    5. `spectralOfDiagonalDensity_commonPair`
                                          — canonical embedding of a
                                            single probability vector
                                            into a (P, P, True) pair.
    6. `spectralRelativeEntropy_diagonal_eq`
                                          — the spectral entropy of
                                            the diagonal embedding
                                            equals the diagonal
                                            quantum relative entropy.

  Full quantum relative entropy and DPI for the non-commuting case
  are intentionally deferred to a separate, harder file.
-/

import UnifiedTheory.LayerB.SpectralDensityMatrix
import UnifiedTheory.LayerB.DiagonalRelativeEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.SpectralRelativeEntropy

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.DiagonalRelativeEntropy
open UnifiedTheory.LayerB.Spectral

variable {n : ℕ}

/-! ## 1. The common-spectral-pair bundle -/

/-- A *commuting-basis* pair of density matrices: two
    `SpectralDensityMatrix`s together with an opaque witness that
    they share an eigenbasis.  The current stage carries no
    semantic content on `commonEigenbasis`; later work may tighten
    it. -/
structure CommonSpectralPair (n : ℕ) where
  /-- The first ("argument") spectral density matrix. -/
  ρ : SpectralDensityMatrix n
  /-- The second ("reference") spectral density matrix. -/
  σ : SpectralDensityMatrix n
  /-- Opaque witness that ρ and σ are simultaneously diagonalisable
      in the basis that produced both spectra.  Intentionally
      unconstrained at this stage of the development. -/
  commonEigenbasis : Prop

/-! ## 2. Spectral relative entropy -/

/-- The relative entropy of a common-spectral pair: the classical
    KL divergence between the two eigenvalue probability vectors.

    Equivalent to `Tr ρ(log ρ − log σ)` in the simultaneously-
    diagonalisable case, but defined here purely scalar-side; no
    operator log is invoked. -/
noncomputable def relativeEntropySpectral (S : CommonSpectralPair n) : ℝ :=
  klDivergence S.ρ.spectrum S.σ.spectrum

/-- The bridge identity (definitional). -/
theorem spectralRelativeEntropy_eq_kl (S : CommonSpectralPair n) :
    relativeEntropySpectral S = klDivergence S.ρ.spectrum S.σ.spectrum :=
  rfl

/-! ## 3. Self-relative-entropy is zero -/

/-- The canonical self-pair of a spectral density matrix (used to
    state `S(ρ‖ρ) = 0`). -/
noncomputable def selfPair (ρ : SpectralDensityMatrix n) :
    CommonSpectralPair n where
  ρ := ρ
  σ := ρ
  commonEigenbasis := True

/-- **S(ρ‖ρ) = 0** for any spectral density matrix. -/
theorem spectralRelativeEntropy_self_eq_zero
    (ρ : SpectralDensityMatrix n) :
    relativeEntropySpectral (selfPair ρ) = 0 :=
  klDivergence_self_eq_zero ρ.spectrum

/-! ## 4. Canonical diagonal embedding -/

/-- Two probability vectors give rise to a common-spectral pair via
    the canonical diagonal embedding.  Both eigenbases are
    automatically diagonal, so `commonEigenbasis := True`. -/
noncomputable def commonPairOfDiagonal
    (P Q : ProbabilityVector (Fin n)) : CommonSpectralPair n where
  ρ := spectralOfDiagonalDensity P
  σ := spectralOfDiagonalDensity Q
  commonEigenbasis := True

/-- **Spectral relative entropy of two diagonal embeddings equals
    the diagonal quantum relative entropy of the underlying
    probability vectors.** -/
theorem spectralRelativeEntropy_diagonal_eq
    (P Q : ProbabilityVector (Fin n)) :
    relativeEntropySpectral (commonPairOfDiagonal P Q)
      = relativeEntropyDiagonal P Q := rfl

/-- The same identity in terms of the underlying KL divergence. -/
theorem spectralRelativeEntropy_diagonal_eq_kl
    (P Q : ProbabilityVector (Fin n)) :
    relativeEntropySpectral (commonPairOfDiagonal P Q)
      = klDivergence P Q := rfl

/-! ## 5. Spectrum accessors (boilerplate) -/

@[simp]
theorem selfPair_ρ_spectrum (ρ : SpectralDensityMatrix n) :
    (selfPair ρ).ρ.spectrum = ρ.spectrum := rfl

@[simp]
theorem selfPair_σ_spectrum (ρ : SpectralDensityMatrix n) :
    (selfPair ρ).σ.spectrum = ρ.spectrum := rfl

@[simp]
theorem commonPairOfDiagonal_ρ_spectrum
    (P Q : ProbabilityVector (Fin n)) :
    (commonPairOfDiagonal P Q).ρ.spectrum = P := rfl

@[simp]
theorem commonPairOfDiagonal_σ_spectrum
    (P Q : ProbabilityVector (Fin n)) :
    (commonPairOfDiagonal P Q).σ.spectrum = Q := rfl

end UnifiedTheory.LayerB.SpectralRelativeEntropy
