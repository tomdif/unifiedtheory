/-
  LayerB/OperatorEntropy.lean
  ────────────────────────────

  **Operator logarithm and von Neumann entropy of a complex
  Hermitian density matrix.**

  Builds on:
    * `SpectralFunctionalCalculus` (`cfcρ f ρ`, `cfcρ_isHermitian`, …)
    * `SpectralFunctionalCalculusTrace` (trace formula for the CFC)
    * `RobertsonSchrodinger.ComplexDensityMatrix`
    * `ClassicalEntropy.ProbabilityVector` / `shannonEntropy`

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `operatorLog ρ := cfcρ Real.log ρ`           — operator logarithm.
    2. `operatorLog_isHermitian`                    — Hermitian preservation.
    3. `operatorXLogX ρ := cfcρ (fun x ↦ x * log x) ρ`
                                                    — operator `x·log x`.
    4. `operatorXLogX_isHermitian`                  — Hermitian preservation.
    5. `vonNeumannEntropy ρ := −∑ᵢ λᵢ · log λᵢ`     — direct definition.
    6. `posSemidef_of_ComplexDensityMatrix`         — bridges
       `hTracePSD : ∀ X, 0 ≤ Re(Tr(ρ X† X))` to `ρ.M.PosSemidef`
       via the quadratic-form identity
       `Tr(ρ · X† · X) = star x ⬝ᵥ ρ *ᵥ x` for a single-column X.
    7. `eigenvalues_nonneg`                         — λᵢ ≥ 0.
    8. `eigenvaluesAsProbabilityVector ρ`           — eigenvalues as
                                                      a `ProbabilityVector`.
    9. `vonNeumannEntropy_eq_shannonEntropy`        — bridge to scalar
                                                      Shannon entropy.
   10. `vonNeumannEntropy_eq_neg_re_trace_xlogx`    — trace-form
                                                      identity using
                                                      the parallel
                                                      `SpectralFCTrace`.
   11. `vonNeumannEntropy_nonneg`                   — Gibbs corollary via
                                                      Shannon entropy.

  SCOPE:
    – Finite-dimensional Hermitian density matrices over ℂ.
    – Mathlib's convention `Real.log 0 = 0` makes the zero-eigenvalue
      term contribute nothing (so we never have to special-case the
      kernel of ρ).
-/

import UnifiedTheory.LayerB.SpectralFunctionalCalculus
import UnifiedTheory.LayerB.SpectralFunctionalCalculusTrace
import UnifiedTheory.LayerB.ClassicalEntropy
import Mathlib.Analysis.Matrix.PosDef

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.OperatorEntropy

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.SpectralFCTrace
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector

variable {n : ℕ}

/-! ## 1. Operator logarithm -/

/-- Operator logarithm of a complex Hermitian density matrix,
    `log ρ := cfc (Real.log) ρ`.  Mathlib's `Real.log 0 = 0`
    convention means this is well-defined even when ρ has
    zero eigenvalues. -/
noncomputable def operatorLog (ρ : ComplexDensityMatrix n) :
    Matrix (Fin n) (Fin n) ℂ :=
  cfcρ Real.log ρ

/-- The operator logarithm of a Hermitian density matrix is Hermitian. -/
theorem operatorLog_isHermitian (ρ : ComplexDensityMatrix n) :
    (operatorLog ρ).IsHermitian :=
  cfcρ_isHermitian Real.log ρ

/-! ## 2. Operator x log x -/

/-- The operator `ρ · log ρ`, computed via the CFC of the real
    function `x ↦ x · log x`.  Direct construction; we do not
    decompose into the product `ρ * operatorLog ρ` here (which
    would require additional CFC-product lemmas). -/
noncomputable def operatorXLogX (ρ : ComplexDensityMatrix n) :
    Matrix (Fin n) (Fin n) ℂ :=
  cfcρ (fun x => x * Real.log x) ρ

/-- `operatorXLogX ρ` is Hermitian. -/
theorem operatorXLogX_isHermitian (ρ : ComplexDensityMatrix n) :
    (operatorXLogX ρ).IsHermitian :=
  cfcρ_isHermitian (fun x => x * Real.log x) ρ

/-! ## 3. von Neumann entropy (direct, via eigenvalues) -/

/-- **von Neumann entropy** of a complex Hermitian density matrix,
    defined directly via its eigenvalues:

        S(ρ) := − ∑ᵢ λᵢ · log λᵢ.

    Mathlib's convention `0 · log 0 = 0 · 0 = 0` makes the
    kernel-of-ρ terms harmless. -/
noncomputable def vonNeumannEntropy (ρ : ComplexDensityMatrix n) : ℝ :=
  - ∑ i, (ρ.hHerm.eigenvalues i) * Real.log (ρ.hHerm.eigenvalues i)

/-! ## 4. Bridge: `hTracePSD` ⟹ `PosSemidef` -/

/-- **From the trace-PSD field to full `Matrix.PosSemidef`.**

    The `hTracePSD` field of `ComplexDensityMatrix` asserts
    `0 ≤ Re(Tr(ρ · X† · X))` for every n×n matrix X.  Specialising
    X to the matrix whose first row is `star x` (and all other
    rows zero) gives `Tr(ρ · X† · X) = star x ⬝ᵥ ρ *ᵥ x`, the
    standard PSD quadratic form.  Since ρ is Hermitian, this
    quadratic form is real, so its real part equals the form itself.

    This bridge then lets us call `PosSemidef.eigenvalues_nonneg`. -/
theorem posSemidef_of_ComplexDensityMatrix
    (ρ : ComplexDensityMatrix n) : ρ.M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ρ.hHerm ?_
  intro x
  -- For the empty case (n = 0), the quadratic form is the empty
  -- sum, i.e., 0 ≤ 0.
  by_cases hn : Nonempty (Fin n)
  · -- Build X : Matrix (Fin n) (Fin n) ℂ with row i₀ = star x,
    --   other rows zero, for some fixed i₀ : Fin n.
    classical
    obtain ⟨i₀⟩ := hn
    let X : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of (fun i j => if i = i₀ then star (x j) else 0)
    -- We will show: star x ⬝ᵥ ρ.M *ᵥ x  equals  Tr(ρ.M · X† · X)
    -- in real part, then invoke ρ.hTracePSD on X.
    -- Step A. Compute X† and X† * X.
    have hXt : X.conjTranspose =
        Matrix.of (fun i j => if j = i₀ then x i else 0) := by
      ext i j
      change star (X j i) = if j = i₀ then x i else 0
      simp only [X, Matrix.of_apply]
      split_ifs with h
      · simp
      · simp
    -- Step B. Compute (X† * X) i j = x i * star (x j).
    have hXtX : ∀ i j, (X.conjTranspose * X) i j = x i * star (x j) := by
      intro i j
      rw [Matrix.mul_apply]
      simp only [hXt, Matrix.of_apply, X]
      -- = ∑ k, (if k = i₀ then x i else 0) * (if k = i₀ then star (x j) else 0)
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro k _ hk
        simp [hk]
      · intro h
        exact absurd (Finset.mem_univ _) h
    -- Step C. Tr(ρ.M · (X† * X)) = ∑_{i,j} ρ.M_{i,j} · x_j · star (x_i)
    --                            = star x ⬝ᵥ ρ.M *ᵥ x.
    set z : ℂ := star x ⬝ᵥ ρ.M *ᵥ x with hz_def
    have h_tr_eq : Matrix.trace (ρ.M * (X.conjTranspose * X)) = z := by
      rw [Matrix.trace]
      simp only [Matrix.diag_apply]
      have h_per : ∀ i, (ρ.M * (X.conjTranspose * X)) i i
                      = ∑ j, ρ.M i j * x j * star (x i) := by
        intro i
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [hXtX]
        ring
      simp_rw [h_per]
      rw [hz_def]
      -- z = star x ⬝ᵥ ρ.M *ᵥ x = ∑ i, star (x i) * ∑ j, ρ.M i j * x j
      --                        = ∑ i, ∑ j, star (x i) * (ρ.M i j * x j)
      -- compare to ∑ i, ∑ j, ρ.M i j * x j * star (x i): same by ring.
      change ∑ i, ∑ j, ρ.M i j * x j * star (x i)
           = star x ⬝ᵥ ρ.M *ᵥ x
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    -- Step D. Tr(ρ.M · X† · X) = z via associativity.
    have h_assoc :
        Matrix.trace (ρ.M * X.conjTranspose * X) = z := by
      rw [Matrix.mul_assoc]; exact h_tr_eq
    -- Step E. Apply hTracePSD: 0 ≤ Re(Tr(ρ.M · X† · X)) = Re z.
    have h_psd := ρ.hTracePSD X
    rw [h_assoc] at h_psd
    -- Step F. z is real because ρ is Hermitian.  Use `nonneg_iff`.
    have h_z_im : z.im = 0 := ρ.hHerm.im_star_dotProduct_mulVec_self x
    rw [Complex.nonneg_iff]
    exact ⟨h_psd, h_z_im.symm⟩
  · -- n = 0: the dotProduct over an empty type is 0.
    have hempty : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    have h0 : star x ⬝ᵥ ρ.M *ᵥ x = 0 := by
      simp [dotProduct]
    rw [h0]

/-! ## 5. Eigenvalues are non-negative -/

/-- **Eigenvalues of a complex Hermitian density matrix are
    non-negative.**  Immediate corollary of
    `posSemidef_of_ComplexDensityMatrix` via
    `PosSemidef.eigenvalues_nonneg`. -/
theorem eigenvalues_nonneg (ρ : ComplexDensityMatrix n) (i : Fin n) :
    0 ≤ ρ.hHerm.eigenvalues i :=
  (posSemidef_of_ComplexDensityMatrix ρ).eigenvalues_nonneg i

/-! ## 6. Eigenvalues sum to 1 -/

/-- **Eigenvalues of a normalised density matrix sum to 1.**
    From `IsHermitian.trace_eq_sum_eigenvalues` and the
    `hTrace : Tr ρ = 1` field. -/
theorem sum_eigenvalues_eq_one (ρ : ComplexDensityMatrix n) :
    ∑ i, ρ.hHerm.eigenvalues i = 1 := by
  -- Tr ρ = ∑ ofReal(λᵢ); equate real parts and use Tr ρ = 1.
  have h1 : ρ.M.trace = ∑ i, ((ρ.hHerm.eigenvalues i : ℂ)) :=
    ρ.hHerm.trace_eq_sum_eigenvalues
  have h2 : (1 : ℂ) = ∑ i, ((ρ.hHerm.eigenvalues i : ℂ)) := by
    rw [← ρ.hTrace, h1]
  -- Cast back to ℝ.
  have h3 := congrArg Complex.re h2
  rw [Complex.one_re, Complex.re_sum] at h3
  -- h3 : 1 = ∑ i, (ofReal (λᵢ)).re = ∑ i, λᵢ
  have h4 : ∑ i, (((ρ.hHerm.eigenvalues i : ℂ))).re = ∑ i, ρ.hHerm.eigenvalues i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Complex.ofReal_re _
  rw [h4] at h3
  linarith

/-! ## 7. Eigenvalues as a probability vector -/

/-- **Wrap the eigenvalues of ρ as a `ProbabilityVector (Fin n)`.**

    Non-negativity comes from `eigenvalues_nonneg`; the sum-to-one
    constraint comes from `sum_eigenvalues_eq_one`. -/
noncomputable def eigenvaluesAsProbabilityVector
    (ρ : ComplexDensityMatrix n) : ProbabilityVector (Fin n) where
  p := ρ.hHerm.eigenvalues
  nonneg := eigenvalues_nonneg ρ
  sum_one := sum_eigenvalues_eq_one ρ

/-! ## 8. The bridge to scalar Shannon entropy -/

/-- **von Neumann entropy of ρ equals Shannon entropy of its
    eigenvalue probability vector.**  Both sides unfold to
    `−∑ᵢ λᵢ · log λᵢ` (and the `ProbabilityVector` carrier is
    definitionally `ρ.hHerm.eigenvalues`). -/
theorem vonNeumannEntropy_eq_shannonEntropy (ρ : ComplexDensityMatrix n) :
    vonNeumannEntropy ρ = shannonEntropy (eigenvaluesAsProbabilityVector ρ) := by
  unfold vonNeumannEntropy shannonEntropy eigenvaluesAsProbabilityVector
  rfl

/-! ## 9. Trace-form identity -/

/-- **von Neumann entropy = −Re Tr(ρ · log ρ).**  We state this in
    the `operatorXLogX` form because `operatorXLogX ρ` is literally
    `cfc (x ↦ x · log x) ρ`, whose trace—by the parallel
    `re_trace_cfcρ` theorem—is exactly `∑ᵢ λᵢ · log λᵢ`.

    The decomposition `operatorXLogX ρ = ρ · operatorLog ρ` would
    require additional CFC-product lemmas (`cfc_mul`), which are
    not yet wired through.  We use the direct CFC form, which is
    the standard mathematical definition. -/
theorem vonNeumannEntropy_eq_neg_re_trace_xlogx
    (ρ : ComplexDensityMatrix n) :
    vonNeumannEntropy ρ = -((operatorXLogX ρ).trace.re) := by
  unfold vonNeumannEntropy operatorXLogX
  rw [re_trace_cfcρ]

/-! ## 10. Gibbs: von Neumann entropy is non-negative -/

/-- **von Neumann entropy is non-negative** (the Gibbs inequality
    on its weakest form: `H ≥ 0` for any probability distribution).
    Immediate via the Shannon-entropy bridge. -/
theorem vonNeumannEntropy_nonneg (ρ : ComplexDensityMatrix n) :
    0 ≤ vonNeumannEntropy ρ := by
  rw [vonNeumannEntropy_eq_shannonEntropy]
  exact ProbabilityVector.entropy_nonneg (eigenvaluesAsProbabilityVector ρ)

end UnifiedTheory.LayerB.OperatorEntropy
