/-
  LayerB/SpectralFunctionalCalculus.lean
  ───────────────────────────────────────

  **Continuous Functional Calculus on a complex Hermitian density
  matrix.**  First step toward true Umegaki relative entropy and
  the full quantum Holevo bound.

  Built directly on top of Mathlib's
  `Matrix.IsHermitian.cfc : (ℝ → ℝ) → Matrix n n 𝕜` and the
  abstract `_root_.cfc` machinery from `CStarAlgebra`.  We wrap
  these for the `ComplexDensityMatrix` interface used elsewhere
  in `LayerB`, so that downstream files can write `f(ρ)` directly.

  EXPLICIT SCOPE:
    * builds `f(ρ)` as a `Matrix (Fin n) (Fin n) ℂ`;
    * carries Hermitian preservation;
    * bridges to the spectral-theorem definition `ρ.hHerm.cfc f`,
      which expresses `f(ρ) = U · diag(f ∘ eigenvalues) · U⁻¹`;
    * does NOT yet define `log ρ` as a member of a special
      density-matrix-like class;
    * does NOT yet prove the trace formula `Tr f(ρ) = ∑ f(λ_i)`
      (deferred to a follow-up; the cyclic-conjugation argument
      requires more `conjStarAlgAut` lemmas).

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `cfcρ f ρ`                       — `f(ρ)` via the generic CFC.
    2. `cfcρ_isHermitian`               — Hermitian preservation.
    3. `cfcρ_eq_spectralCFC`            — bridge to the
                                          spectral-theorem definition.
    4. `cfcρ_diagonalForm`              — `f(ρ) = U · diag(ofReal ∘ f ∘ λ) · U⁻¹`
                                          where U is the eigenvector unitary
                                          (an explicit-form lemma exposing
                                          Mathlib's `IsHermitian.cfc`
                                          construction).
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.SpectralFC

open Matrix Complex Unitary
open UnifiedTheory.LayerB.RobertsonSchrodinger

variable {n : ℕ}

/-! ## 1. The CFC on a density matrix -/

/-- The continuous functional calculus of a real function `f : ℝ → ℝ`
    applied to a complex Hermitian density matrix `ρ`, producing the
    matrix `f(ρ)`. -/
noncomputable def cfcρ (f : ℝ → ℝ) (ρ : ComplexDensityMatrix n) :
    Matrix (Fin n) (Fin n) ℂ :=
  cfc f ρ.M

/-! ## 2. Hermitian preservation -/

/-- `f(ρ)` is Hermitian whenever `ρ` is, for any real `f`.  This
    follows from the `cfc_predicate` lemma: the CStarAlgebra cfc
    instance for matrices automatically preserves the
    `IsSelfAdjoint` predicate, and for matrices `IsSelfAdjoint`
    and `IsHermitian` are definitionally equal. -/
theorem cfcρ_isHermitian (f : ℝ → ℝ) (ρ : ComplexDensityMatrix n) :
    (cfcρ f ρ).IsHermitian :=
  cfc_predicate (R := ℝ) f ρ.M

/-! ## 3. Bridge to the spectral-theorem definition -/

/-- The wrapped CFC agrees with Mathlib's spectral-theorem definition
    of `IsHermitian.cfc`, which writes `f(ρ)` as a unitary
    conjugation of the diagonal-of-eigenvalues matrix. -/
theorem cfcρ_eq_spectralCFC (f : ℝ → ℝ) (ρ : ComplexDensityMatrix n) :
    cfcρ f ρ = ρ.hHerm.cfc f :=
  Matrix.IsHermitian.cfc_eq ρ.hHerm f

/-! ## 4. Explicit diagonal form -/

/-- **Explicit eigen-diagonalisation form** of `f(ρ)`:

      `f(ρ) = conjStarAlgAut U (diagonal (ofReal ∘ f ∘ eigenvalues))`,

    where `U = ρ.hHerm.eigenvectorUnitary` is the unitary whose
    columns are the eigenvectors of `ρ`.  This is just the unfolded
    definition of `IsHermitian.cfc`, but stated in our vocabulary
    so downstream files can compute with it. -/
theorem cfcρ_diagonalForm (f : ℝ → ℝ) (ρ : ComplexDensityMatrix n) :
    cfcρ f ρ
      = conjStarAlgAut ℂ _ ρ.hHerm.eigenvectorUnitary
          (diagonal (RCLike.ofReal ∘ f ∘ ρ.hHerm.eigenvalues)) := by
  rw [cfcρ_eq_spectralCFC]
  rfl

end UnifiedTheory.LayerB.SpectralFC
