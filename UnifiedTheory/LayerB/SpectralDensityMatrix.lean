/-
  LayerB/SpectralDensityMatrix.lean
  ──────────────────────────────────

  A conservative *spectral-data wrapper* around a density matrix.
  We do NOT attempt to derive an arbitrary spectral decomposition of
  a Hermitian density matrix from scratch — that is a separate
  (harder) theorem about `Matrix.IsHermitian.spectralTheorem`-style
  diagonalization.  Instead, we *bundle* a density matrix with a
  supplied eigenvalue probability vector, and define the von Neumann
  entropy of that bundle as the Shannon entropy of the spectrum.

  This establishes a stable interface

        SpectralDensityMatrix n   ↔   eigenvalue probability vector

  so that all downstream entropy / relative-entropy / DPI / Holevo
  work can refer to "the spectral entropy of ρ" with a single name,
  independently of how the spectral data was obtained.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `SpectralDensityMatrix n` — bundle (ρ, spectrum, diagonalizes).
    2. `vonNeumannEntropySpectral S := shannonEntropy S.spectrum`.
    3. `spectral_entropy_nonneg`                    (S ≥ 0).
    4. `spectralOfDiagonalDensity P` — the canonical embedding from
       `ProbabilityVector (Fin n)` into `SpectralDensityMatrix n`
       via the diagonal density matrix construction.
    5. `diagonal_spectral_entropy_eq_shannon`       (compatibility:
       the spectral entropy of the diagonal embedding equals the
       Shannon entropy of the underlying probability vector).
    6. `spectral_entropy_delta_eq_zero`             (pure-state delta).
    7. `spectral_entropy_uniform_eq_log_n`          (max-mixed = log n).
    8. `spectral_entropy_eq_vonNeumannEntropyDiagonal`
       (compatibility with `DiagonalVonNeumannEntropy`).

  The `diagonalizes` field is intentionally an opaque `Prop`: we are
  deliberately NOT defining unitary diagonalization here.  The
  canonical diagonal embedding simply supplies `True`.  Later files
  may tighten this to an actual diagonalization predicate of the
  form `∃ U unitary, ρ = U† · diag(p) · U` without breaking the
  current interface.
-/

import UnifiedTheory.LayerB.DiagonalDensityMatrix

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Spectral

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.DiagonalVonNeumannEntropy
open UnifiedTheory.LayerB.DiagonalDensityMatrix

/-! ## 1. The spectral-data bundle -/

/-- A density matrix bundled with its eigenvalue probability vector.
    The `diagonalizes` field is an opaque `Prop` placeholder — a later
    refinement may tighten it to an actual unitary-diagonalization
    predicate. -/
structure SpectralDensityMatrix (n : ℕ) where
  /-- The underlying density matrix. -/
  ρ : ComplexDensityMatrix n
  /-- The probability vector of eigenvalues (in some chosen ordering). -/
  spectrum : ProbabilityVector (Fin n)
  /-- Opaque diagonalization witness, intentionally unconstrained
      at this stage of the development. -/
  diagonalizes : Prop

/-! ## 2. Spectral von Neumann entropy -/

/-- The von Neumann entropy of a spectral density matrix, defined as
    the Shannon entropy of its eigenvalue probability vector. -/
noncomputable def vonNeumannEntropySpectral {n : ℕ}
    (S : SpectralDensityMatrix n) : ℝ :=
  shannonEntropy S.spectrum

/-- Spectral entropy is non-negative. -/
theorem spectral_entropy_nonneg {n : ℕ} (S : SpectralDensityMatrix n) :
    0 ≤ vonNeumannEntropySpectral S :=
  entropy_nonneg S.spectrum

/-! ## 3. Canonical embedding from a probability vector -/

/-- The canonical spectral density matrix obtained from a probability
    vector: the diagonal density matrix carrying the probabilities as
    its eigenvalues.  This is the only constructor we provide at this
    stage; an arbitrary-Hermitian spectral decomposition is deferred. -/
noncomputable def spectralOfDiagonalDensity {n : ℕ}
    (P : ProbabilityVector (Fin n)) : SpectralDensityMatrix n where
  ρ := diagonalDensityMatrix P
  spectrum := P
  diagonalizes := True

/-! ## 4. Compatibility theorems -/

/-- **The spectral entropy of the diagonal embedding equals the
    Shannon entropy of the underlying probability vector.**  This is
    the key bridge: it ties the spectral interface back to the
    classical scalar one for the only case we currently know how to
    build by hand. -/
theorem diagonal_spectral_entropy_eq_shannon {n : ℕ}
    (P : ProbabilityVector (Fin n)) :
    vonNeumannEntropySpectral (spectralOfDiagonalDensity P)
      = shannonEntropy P := rfl

/-- The spectral entropy of the diagonal embedding equals the
    diagonal von Neumann entropy, closing the chain
    `ProbabilityVector → diagonalDM → vNE_diag` and
    `ProbabilityVector → spectralDM → vNE_spectral`
    at the entropy layer. -/
theorem spectral_entropy_eq_vonNeumannEntropyDiagonal {n : ℕ}
    (P : ProbabilityVector (Fin n)) :
    vonNeumannEntropySpectral (spectralOfDiagonalDensity P)
      = vonNeumannEntropyDiagonal P := rfl

/-! ## 5. Inherited scalar identities (pure / uniform) -/

/-- **Spectral entropy of a pure state (delta eigenvalue distribution)
    is zero.** -/
theorem spectral_entropy_delta_eq_zero {n : ℕ} (i₀ : Fin n) :
    vonNeumannEntropySpectral (spectralOfDiagonalDensity (delta (Fin n) i₀))
      = 0 :=
  entropy_delta_eq_zero i₀

/-- **Spectral entropy of the maximally-mixed state on n levels is log n.** -/
theorem spectral_entropy_uniform_eq_log_n (n : ℕ) (hn : 0 < n) :
    vonNeumannEntropySpectral (spectralOfDiagonalDensity (uniform n hn))
      = Real.log n :=
  entropy_uniform_eq_log_n n hn

/-! ## 6. Underlying density-matrix structure is preserved -/

/-- The underlying density matrix of the canonical diagonal spectral
    embedding really is the diagonal density matrix. -/
@[simp]
theorem spectralOfDiagonalDensity_ρ {n : ℕ}
    (P : ProbabilityVector (Fin n)) :
    (spectralOfDiagonalDensity P).ρ = diagonalDensityMatrix P := rfl

/-- The spectrum of the canonical diagonal spectral embedding is the
    original probability vector. -/
@[simp]
theorem spectralOfDiagonalDensity_spectrum {n : ℕ}
    (P : ProbabilityVector (Fin n)) :
    (spectralOfDiagonalDensity P).spectrum = P := rfl

end UnifiedTheory.LayerB.Spectral
