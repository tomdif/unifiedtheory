/-
  LayerB/SpectralFunctionalCalculusTrace.lean
  ────────────────────────────────────────────

  **Trace formula for the continuous functional calculus on a
  complex Hermitian density matrix.**

  Sequel to `LayerB/SpectralFunctionalCalculus.lean`.  Establishes
  the standard spectral identity

      Tr f(ρ) = ∑ᵢ f(λᵢ),

  where `λᵢ` ranges over the (real) eigenvalues of `ρ`, by combining
  the explicit unitary-diagonal form `cfcρ_diagonalForm` with the
  cyclicity of the matrix trace and the diagonal-trace identity.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `trace_cfcρ`         — `Tr f(ρ) = ∑ᵢ (ofReal (f λᵢ) : ℂ)`.
    2. `re_trace_cfcρ`      — `(Tr f(ρ)).re = ∑ᵢ f λᵢ`.
    3. `trace_cfcρ_one`     — `Tr (cfcρ (fun _ => 1) ρ) = n`.
    4. `trace_cfcρ_id`      — `Tr (cfcρ id ρ) = 1`
                              (using `ρ.hTrace` and
                              `IsHermitian.trace_eq_sum_eigenvalues`).
-/

import UnifiedTheory.LayerB.SpectralFunctionalCalculus
import Mathlib.Algebra.Star.UnitaryStarAlgAut

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.SpectralFCTrace

open Matrix Complex Unitary
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC

variable {n : ℕ}

/-! ## 1. Auxiliary: trace is invariant under unitary conjugation -/

/-- For any unitary `U` in `Matrix n n ℂ` and any matrix `M`,

      `Tr (U · M · star U) = Tr M`.

    This is the standard cyclicity computation used to evaluate the
    trace of `f(ρ)` from its eigen-diagonal form. -/
theorem trace_conj_unitary
    (U : Matrix.unitaryGroup (Fin n) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((U : Matrix (Fin n) (Fin n) ℂ) * M * star (U : Matrix (Fin n) (Fin n) ℂ))
      = Matrix.trace M := by
  -- cyclicity: Tr(U·M·star U) = Tr(star U · U · M) = Tr(M)
  rw [Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self U, Matrix.one_mul]

/-! ## 2. The trace formula for `cfcρ f ρ` -/

/-- **Trace formula for the CFC on a density matrix.**

    For a complex Hermitian density matrix `ρ` and a real function
    `f : ℝ → ℝ`,

        Tr f(ρ) = ∑ᵢ (ofReal (f (λᵢ)) : ℂ),

    where `λᵢ = ρ.hHerm.eigenvalues i` are the real eigenvalues of `ρ`.

    Strategy: apply `cfcρ_diagonalForm` to rewrite `f(ρ)` as
    `U · diag(ofReal ∘ f ∘ λ) · star U` (using the explicit action of
    `conjStarAlgAut`), then apply `trace_conj_unitary` and
    `Matrix.trace_diagonal`. -/
theorem trace_cfcρ (f : ℝ → ℝ) (ρ : ComplexDensityMatrix n) :
    (cfcρ f ρ).trace
      = ∑ i, ((RCLike.ofReal (f (ρ.hHerm.eigenvalues i)) : ℂ)) := by
  -- 1. Unfold to the unitary-diagonal form.
  rw [cfcρ_diagonalForm]
  -- 2. Unfold `conjStarAlgAut` to its explicit triple-product.
  rw [Unitary.conjStarAlgAut_apply]
  -- 3. Cyclicity kills the unitary conjugation.
  rw [trace_conj_unitary]
  -- 4. Diagonal trace.
  rw [Matrix.trace_diagonal]
  rfl

/-! ## 3. Real-part version -/

/-- The real part of the CFC trace is the elementary real sum
    `∑ᵢ f (λᵢ)`.  This is the form most often used in entropy
    inequalities, where one wants a real-valued expression. -/
theorem re_trace_cfcρ (f : ℝ → ℝ) (ρ : ComplexDensityMatrix n) :
    (cfcρ f ρ).trace.re = ∑ i, f (ρ.hHerm.eigenvalues i) := by
  rw [trace_cfcρ]
  -- Sum of ofReal values: its real part is the sum of real parts.
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.ofReal_re _

/-! ## 4. Specializations: `f = 1` and `f = id` -/

/-- `Tr 1(ρ) = n`: the trace of the constant-`1` CFC is the
    dimension.  This is the spectral expression of the identity. -/
theorem trace_cfcρ_one (ρ : ComplexDensityMatrix n) :
    (cfcρ (fun _ => 1) ρ).trace = (n : ℂ) := by
  rw [trace_cfcρ]
  -- ∑ i : Fin n, ofReal 1 = ∑ i : Fin n, 1 = n
  simp

/-- `Tr (id ρ) = Tr ρ = 1`: the trace of `cfcρ id ρ` recovers the
    density-matrix normalization.  Uses
    `IsHermitian.trace_eq_sum_eigenvalues` to identify the spectral
    sum with the matrix trace. -/
theorem trace_cfcρ_id (ρ : ComplexDensityMatrix n) :
    (cfcρ id ρ).trace = 1 := by
  rw [trace_cfcρ]
  -- ∑ ofReal (id (λᵢ)) = ∑ (λᵢ : ℂ) = Tr ρ = 1
  have h_sum : ∑ i, ((RCLike.ofReal (id (ρ.hHerm.eigenvalues i)) : ℂ))
              = ∑ i, ((ρ.hHerm.eigenvalues i : ℂ)) := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [h_sum]
  have h_trace : ρ.M.trace = ∑ i, ((ρ.hHerm.eigenvalues i : ℂ)) :=
    ρ.hHerm.trace_eq_sum_eigenvalues
  rw [← h_trace, ρ.hTrace]

end UnifiedTheory.LayerB.SpectralFCTrace
