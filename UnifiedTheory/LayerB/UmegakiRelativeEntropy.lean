/-
  LayerB/UmegakiRelativeEntropy.lean
  ───────────────────────────────────

  **Umegaki's quantum relative entropy** for two complex Hermitian
  density matrices ρ, σ ∈ `ComplexDensityMatrix n`:

      S(ρ‖σ)  :=  Re Tr ( ρ · ( log ρ − log σ ) ) .

  The operator log is the (real) continuous functional calculus
  `cfcρ Real.log` from `SpectralFunctionalCalculus.lean`, which
  produces a Hermitian matrix for any Hermitian ρ.  Because ρ and
  `log ρ − log σ` are both Hermitian, the trace `Tr(ρ · (log ρ −
  log σ))` is real (its imaginary part is zero); we project onto
  the real part to expose Umegaki's formula as a single `ℝ`.

  This file re-uses the canonical `operatorLog` from
  `OperatorEntropy.lean` (previously inlined here during the parallel
  swarm; the inlined copies were removed in the consolidation pass).

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `umegakiRelativeEntropy ρ σ : ℝ`             — Umegaki's formula.
    2. `trace_rho_hermitian_im_zero`                — imag. part of
                                                       Tr(ρ · H) is 0
                                                       when ρ, H are
                                                       Hermitian
                                                       (justifies `.re`).
    3. `umegakiRelativeEntropy_self_eq_zero`        — S(ρ‖ρ) = 0.

  DEFERRED:
    * The diagonal-bridge identity
        `umegakiRelativeEntropy (diagonalDensityMatrix P)
                                (diagonalDensityMatrix Q) = klDivergence P Q`
      requires identifying `cfcρ Real.log (diagonal d) = diagonal (log ∘ d)`,
      which in turn requires reconciling Mathlib's spectral-theorem
      construction of `IsHermitian.cfc` (a sort-dependent unitary
      conjugation of `diagonal (f ∘ eigenvalues)`) with the
      "obvious" identity on already-diagonal matrices.  This is
      genuinely involved (eigenvalues are NOT definitionally the
      diagonal entries even for diagonal matrices: Mathlib sorts
      them), and is left as a follow-up.  All ingredients are in
      place: see `cfcρ_diagonalForm` and `diagonalDensityMatrix`.

  SCOPE:
    * Finite-dimensional n × n complex matrices.
    * No infinite-dimensional / unbounded-operator content.
    * `Real.log` is used unconditionally; the standard
      `0 · log 0 = 0` convention is inherited from Mathlib.
-/

import UnifiedTheory.LayerB.OperatorEntropy
import UnifiedTheory.LayerB.RobertsonSchrodinger
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.UmegakiRelativeEntropy

open Matrix Complex
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy

variable {n : ℕ}

/-! ## 1. The imaginary part of `Tr(ρ · H)` vanishes for Hermitian ρ, H -/

/-- **Helper:** for any two Hermitian matrices ρ and H,
    `(Tr(ρ · H)).im = 0`, i.e. the trace is real.

    Proof: Tr(ρ·H) = Tr((ρ·H)†) = Tr(H† · ρ†) = Tr(H · ρ) = Tr(ρ·H),
    and the conjugate relation `Tr(ρ·H) = star (Tr(ρ·H))` forces the
    imaginary part to be zero.  We follow the same star-conjugation
    pattern as `trace_isHermitian_im_zero` in
    `RobertsonSchrodinger.lean`. -/
theorem trace_rho_hermitian_im_zero
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).im = 0 := by
  -- z := Tr(A · B).  Show z = star z, hence Im z = 0.
  set z := Matrix.trace (A * B) with hz_def
  have h_eq_star : z = star z := by
    rw [hz_def, ← Matrix.trace_conjTranspose]
    rw [conjTranspose_mul, hA, hB]
    -- Goal: Tr(A * B) = Tr(B * A)
    exact Matrix.trace_mul_comm _ _
  have h_im := congrArg Complex.im h_eq_star
  rw [Complex.star_def, Complex.conj_im] at h_im
  linarith

/-! ## 2. Umegaki's quantum relative entropy -/

/-- **Umegaki's quantum relative entropy.**

    `S(ρ‖σ) := Re Tr ( ρ · (log ρ − log σ) )`.

    For Hermitian ρ and Hermitian `log ρ − log σ` the trace
    `Tr(ρ · (log ρ − log σ))` is real (`trace_rho_hermitian_im_zero`),
    so `Re(·)` simply exposes its real value as an `ℝ`. -/
noncomputable def umegakiRelativeEntropy
    (ρ σ : ComplexDensityMatrix n) : ℝ :=
  (Matrix.trace (ρ.M * (operatorLog ρ - operatorLog σ))).re

/-! ## 3. Self-relative-entropy is zero -/

/-- **S(ρ‖ρ) = 0** for any complex density matrix.

    When σ = ρ, `log ρ − log σ = 0`, so the whole trace is 0. -/
theorem umegakiRelativeEntropy_self_eq_zero (ρ : ComplexDensityMatrix n) :
    umegakiRelativeEntropy ρ ρ = 0 := by
  unfold umegakiRelativeEntropy
  rw [sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

/-! ## 4. Diagonal-bridge identity — DEFERRED.

    The classical identity
        `umegakiRelativeEntropy (diagonalDensityMatrix P)
                                 (diagonalDensityMatrix Q)
           = klDivergence P Q`
    would require showing
        `cfcρ Real.log (diagonalDensityMatrix P) =
            diagonal (fun i => ((Real.log (P.p i) : ℝ) : ℂ))`,
    i.e. that the (real) functional calculus on a diagonal density
    matrix is itself diagonal with `log` applied entry-wise.

    `cfcρ_diagonalForm` writes `cfc f` as a unitary conjugation of
    `diagonal (ofReal ∘ f ∘ hHerm.eigenvalues)`.  For a diagonal
    matrix the "eigenvalues" produced by Mathlib's
    `IsHermitian.eigenvalues` are NOT definitionally the diagonal
    entries — Mathlib uses an arbitrary diagonalisation routine
    which permutes them — so the identification requires a
    non-trivial sort-permutation argument that is not in scope for
    this pass.

    All ingredients are imported and ready for the follow-up.
-/

end UnifiedTheory.LayerB.UmegakiRelativeEntropy
