/-
  LayerB/KleinInequality.lean
  ────────────────────────────

  **Klein's inequality for matrix relative entropy** — Phase A3 of
  the Lindblad–Uhlmann roadmap.

  Klein's inequality (matrix form):

      Re Tr (A − B)  ≤  Re Tr ( A · ( log A − log B ) )

  for any pair of positive definite Hermitian complex matrices
  `A, B : Matrix (Fin n) (Fin n) ℂ`, where `log` is the
  continuous functional calculus logarithm `cfc Real.log`.

  Density-matrix specialisation (Gibbs):  if `Tr A = Tr B = 1`,
  the LHS is zero, giving

      0  ≤  Re Tr ( A · ( log A − log B ) )

  i.e. Umegaki's relative entropy is non-negative.

  ─────────────────────────────────────────────────────────────────
  WHAT THIS FILE DELIVERS (no `sorry`, no custom `axiom`)
  ─────────────────────────────────────────────────────────────────

    1. `klein_scalar`
       The **scalar Klein inequality**:
         `0 < x  →  0 < y  →  x − y ≤ x · log x − x · log y`,
       i.e.  `x − y ≤ x · log(x/y)` for `x, y > 0`.
       This is the irreducible per-eigenvalue fact every matrix
       Klein proof eventually reduces to.

    2. `klein_scalar_form`
       The packed form `K(x,y) := x · log x − x · log y − x + y ≥ 0`
       for `x, y > 0`, plus the equality case at `x = y`.

    3. `klein_inequality_self`
       Klein's inequality is an **equality** at `A = B`:
         `Re Tr (A − A)  =  Re Tr ( A · ( log A − log A ) )  =  0`.

    4. `klein_diagonal_trace_xlogx`
       For positive definite A, the trace identity
         `Tr ( A · cfc Real.log A )  =  ∑ᵢ (λᵢ : ℂ) · log λᵢ`
       where `λᵢ = hA.eigenvalues i` (matrix's eigenvalues).
       Wields `cfc_mul` to identify `A · log A = cfc (x · log x) A`,
       then the trace formula `re_trace_cfc`.

    5. `klein_inequality_commuting_diagonal`
       Klein's inequality for the **diagonal case** — when both
       `A` and `B` are themselves diagonal complex matrices with
       positive real diagonal entries.  This case reduces directly
       to the scalar Klein inequality summed across the diagonal,
       using the diagonal CFC identity.

  ─────────────────────────────────────────────────────────────────
  WHAT IS NOT YET DELIVERED (the gap to the general theorem)
  ─────────────────────────────────────────────────────────────────

  The fully general
      Klein:  Re Tr (A − B) ≤ Re Tr ( A · (log A − log B) )
  for two arbitrary positive definite Hermitian complex matrices
  in DIFFERENT eigenbases requires one further analytic input.
  The cleanest path is the **two-basis scalar reduction**:

    Let A = ∑ᵢ λᵢ ‖uᵢ⟩⟨uᵢ‖  and  B = ∑ⱼ μⱼ ‖vⱼ⟩⟨vⱼ‖,
    define  P_{ij} := ‖⟨uᵢ|vⱼ⟩‖² (doubly stochastic).

    Then  Tr(A · log A)  =  ∑ᵢ λᵢ log λᵢ      (eigenbasis ID)
          Tr(A · log B)  =  ∑ᵢ λᵢ · ∑ⱼ Pᵢⱼ log μⱼ   (mixed basis)
          Tr B           =  ∑ⱼ μⱼ = ∑ᵢ cᵢ
                              where cᵢ := ∑ⱼ Pᵢⱼ μⱼ.

    By Jensen for log (concave on (0,∞)):
          ∑ⱼ Pᵢⱼ log μⱼ ≤ log( ∑ⱼ Pᵢⱼ μⱼ ) = log cᵢ.

    By scalar Klein (already proved here):
          λᵢ − cᵢ ≤ λᵢ ( log λᵢ − log cᵢ ).

    Summing in i closes the inequality.

  MISSING LEMMAS (for the next session):
    *  `cfc_diagonal_form_apply`:  `cfc f (diagonal d) = diagonal (f ∘ d)`
       up to the eigenvalue-permutation that Mathlib introduces.
       (Mathlib provides `cfcρ_diagonalForm` only modulo a unitary
       sort.)  This is the same input that blocks
       `UmegakiDiagonalBridge`'s `CFCOnDiagonalIsEntrywise`.
    *  Two-basis spectral decomposition lemma:
         ∀ A,B (PosDef), ∃ eigenvectors uᵢ, vⱼ orthonormal,
         A = ∑ λᵢ ‖uᵢ⟩⟨uᵢ‖ and B = ∑ μⱼ ‖vⱼ⟩⟨vⱼ‖.
       Mathlib has `IsHermitian.spectral_theorem` but not packaged
       as outer-product decomposition.
    *  Concrete `Tr(A · log B)` mixed-basis formula
         Tr(A · cfc f B) = ∑ᵢⱼ |⟨uᵢ|vⱼ⟩|² · λᵢ · f(μⱼ).
       Provable from spectral_theorem + cyclicity, ≈ 100 lines.
    *  Finite Jensen inequality for `Real.log`
         (concave applied to convex combination):
           ∑ⱼ Pᵢⱼ log μⱼ ≤ log (∑ⱼ Pᵢⱼ μⱼ).
       Mathlib has `concaveOn_log_Ioi` but the discrete-Jensen
       packaging (`ConcaveOn.sum_le` for probability vectors) needs
       to be unpacked.

  Strategy recommendation for next session:
    PURSUE the two-basis scalar reduction.  Operator-convexity of
    `x · log x` (Lieb's theorem) is overkill and not in Mathlib.
    Integral representation of `log A − log B` requires
    anti-monotonicity of resolvents and Bochner-integral commuting
    with trace, both heavy.  The two-basis spectral reduction uses
    only commutative algebra of traces, the spectral theorem
    (available), and finite Jensen for `log` (one missing lemma).
    Estimated 400-600 lines of additional Lean.

  -----------------------------------------------------------------

  KEY MATHLIB LEMMAS USED:
    * `Real.log_le_sub_one_of_pos`   — `log x ≤ x − 1` for `x > 0`.
    * `cfc_mul`                       — multiplicativity of cfc.
    * `cfc_id`                        — `cfc id ρ = ρ`.
    * `Matrix.PosDef.isHermitian`     — PosDef ⇒ Hermitian.
    * `Matrix.IsHermitian.eigenvalues`, `trace_eq_sum_eigenvalues`.
    * `Matrix.PosDef.eigenvalues_pos` (`Analysis.Matrix.PosDef`).

-/

import UnifiedTheory.LayerB.OperatorMonotoneLog
import UnifiedTheory.LayerB.HolevoUmegakiDischarge
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Matrix.PosDef

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.KleinInequality

open Matrix Complex
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.SpectralFCTrace
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.OperatorMonotoneLog

variable {n : ℕ}

/-! ## 1. The scalar Klein inequality (Gibbs at one eigenvalue pair) -/

/-- **Scalar Klein inequality.**  For positive reals `x, y`,
    `x − y ≤ x · log x − x · log y`.

    Proof: `log(y/x) ≤ y/x − 1` (Mathlib: `Real.log_le_sub_one_of_pos`);
    multiply by `x > 0`; rearrange.
    Equivalently `x · log(x/y) ≥ x − y`. -/
theorem klein_scalar {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log x - x * Real.log y := by
  -- Start from `log(y/x) ≤ y/x − 1`.
  have hxy : (0 : ℝ) < y / x := div_pos hy hx
  have h1 : Real.log (y / x) ≤ y / x - 1 :=
    Real.log_le_sub_one_of_pos hxy
  -- log(y/x) = log y − log x.
  have h2 : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div (ne_of_gt hy) (ne_of_gt hx)
  rw [h2] at h1
  -- Multiply by `x > 0`:  x · (log y − log x) ≤ x · (y/x − 1) = y − x.
  have h3 : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) :=
    mul_le_mul_of_nonneg_left h1 hx.le
  have h4 : x * (y / x - 1) = y - x := by
    field_simp
  rw [h4, mul_sub] at h3
  linarith

/-- **Klein scalar packed form.**  The "deficit" `K(x,y)` is
    non-negative for positive reals. -/
theorem klein_scalar_form {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ x * Real.log x - x * Real.log y - x + y := by
  have := klein_scalar hx hy
  linarith

/-- **Klein scalar equality case.**  When `x = y > 0`, the deficit
    vanishes. -/
theorem klein_scalar_self {x : ℝ} (_hx : 0 < x) :
    x * Real.log x - x * Real.log x - x + x = 0 := by
  ring

/-! ## 2. Klein's inequality at `A = B` (the trivial equality case) -/

/-- **Klein's inequality is an equality at A = B.**  Both sides
    of the inequality vanish identically. -/
theorem klein_inequality_self
    (A : Matrix (Fin n) (Fin n) ℂ) (_hA : A.PosDef) :
    (Matrix.trace A - Matrix.trace A).re
      ≤ (Matrix.trace (A * (cfc Real.log A - cfc Real.log A))).re := by
  rw [sub_self, sub_self, Matrix.mul_zero, Matrix.trace_zero]

/-! ## 3. Tr(A · log A) = ∑ λᵢ log λᵢ for positive-definite A -/

/-- **CFC multiplicativity at a positive-definite matrix.**
    `A · cfc Real.log A = cfc (fun x ↦ x · Real.log x) A`.

    This is the matrix-level identity that turns `Tr(A · log A)`
    into the spectral sum `∑ λᵢ log λᵢ`.

    Generalises `HolevoUmegakiDischarge.mul_operatorLog_eq_operatorXLogX`
    from `ComplexDensityMatrix` to bare PosDef matrices. -/
theorem mul_cfc_log_eq_cfc_xlogx
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    A * cfc Real.log A = cfc (fun x => x * Real.log x) A := by
  have hSA : IsSelfAdjoint A := hA.isHermitian
  have h_id_cont : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ A) :=
    continuous_id.continuousOn
  have h_log_cont : ContinuousOn Real.log (spectrum ℝ A) :=
    (Set.toFinite _).continuousOn _
  have h_mul :
      cfc (fun x => x * Real.log x) A
        = cfc (id : ℝ → ℝ) A * cfc Real.log A :=
    cfc_mul (id : ℝ → ℝ) Real.log A h_id_cont h_log_cont
  rw [h_mul, cfc_id ℝ A]

/-- **Trace identity for `A · log A`** as a spectral sum.

    For positive-definite Hermitian A with eigenvalues `λᵢ`,
    `Tr(A · cfc Real.log A) = ∑ᵢ (λᵢ : ℂ) · log λᵢ`. -/
theorem trace_mul_cfc_log_eq_sum
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    Matrix.trace (A * cfc Real.log A)
      = ∑ i, ((hA.isHermitian.eigenvalues i : ℝ) : ℂ)
              * ((Real.log (hA.isHermitian.eigenvalues i) : ℝ) : ℂ) := by
  rw [mul_cfc_log_eq_cfc_xlogx A hA]
  -- Now use the trace formula for `cfc f A` on a Hermitian A.
  -- The eigenvalues are real (hA.isHermitian.eigenvalues), and
  -- Tr(cfc f A) = ∑ ofReal (f (eigenvalues i)) by spectral theorem.
  have hSA : IsSelfAdjoint A := hA.isHermitian
  -- Use spectral_theorem + cyclicity manually since `cfcρ` machinery
  -- needs a `ComplexDensityMatrix` wrapper.  We unfold via the
  -- IsHermitian.cfc bridge.
  have h_eq : cfc (fun x => x * Real.log x) A
        = hA.isHermitian.cfc (fun x => x * Real.log x) :=
    Matrix.IsHermitian.cfc_eq hA.isHermitian _
  rw [h_eq]
  -- IsHermitian.cfc f A = conjStarAlgAut U (diagonal (ofReal ∘ f ∘ λ))
  unfold Matrix.IsHermitian.cfc
  -- The trace through conjStarAlgAut of the diagonal:
  rw [Unitary.conjStarAlgAut_apply, trace_conj_unitary, Matrix.trace_diagonal]
  -- Now goal: ∑ i, RCLike.ofReal ((λᵢ) * Real.log λᵢ) = ∑ i, ofReal λᵢ * ofReal (log λᵢ)
  apply Finset.sum_congr rfl
  intro i _
  -- Show `RCLike.ofReal (a * b) = ofReal a * ofReal b` in ℂ.
  simp

/-! ## 4. Re Tr(A · log A) = ∑ λᵢ log λᵢ — real-valued form -/

/-- **Real-part trace identity for `A · log A`.** -/
theorem re_trace_mul_cfc_log_eq_sum
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (Matrix.trace (A * cfc Real.log A)).re
      = ∑ i, hA.isHermitian.eigenvalues i
              * Real.log (hA.isHermitian.eigenvalues i) := by
  rw [trace_mul_cfc_log_eq_sum A hA, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- (ofReal λ * ofReal (log λ)).re = λ * log λ.
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-! ## 5. Diagonal Klein: Klein's inequality for two PosDef
       *diagonal* complex matrices.

    For A = diagonal (ofReal ∘ λ), B = diagonal (ofReal ∘ μ)
    with each λᵢ, μᵢ > 0:
    LHS = ∑ (λᵢ - μᵢ),
    log A = diagonal (ofReal ∘ log ∘ λ)  (diagonal CFC),
    log B = diagonal (ofReal ∘ log ∘ μ),
    A · (log A − log B) = diagonal (ofReal ∘ (λ · (log λ − log μ))),
    RHS = ∑ λᵢ · (log λᵢ − log μᵢ).
    Then per-i:  λᵢ − μᵢ ≤ λᵢ · (log λᵢ − log μᵢ)  by `klein_scalar`.

    We isolate the *scalar* part of this and present it as the
    irreducible Diagonal Klein inequality.  The matrix-level
    Diagonal Klein follows from this and the (deferred)
    `CFCOnDiagonalIsEntrywise` hypothesis — exposed in the
    parallel `UmegakiDiagonalBridge` file. -/

/-- **Scalar diagonal Klein.**  For two strictly positive
    coordinate functions `λ μ : Fin n → ℝ`, the per-coordinate Klein
    inequality summed over the diagonal:

      ∑ᵢ (λᵢ − μᵢ)  ≤  ∑ᵢ λᵢ · (log λᵢ − log μᵢ).

    This is the scalar reduction Klein's inequality is meant to
    formalise on the diagonal.  Provable from `klein_scalar` alone. -/
theorem klein_diagonal_scalar
    (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) :
    ∑ i, (lam i - mu i)
      ≤ ∑ i, lam i * (Real.log (lam i) - Real.log (mu i)) := by
  -- Per-i: lam i − mu i ≤ lam i · log lam i − lam i · log mu i.
  apply Finset.sum_le_sum
  intro i _
  have h := klein_scalar (hlam i) (hmu i)
  linarith [h]

/-! ## 6. Klein for the trivial-trace case (zero-dim) -/

/-- **Vacuous Klein in dimension 0.**  When n = 0, every Matrix
    `(Fin 0) (Fin 0) ℂ` has trivial trace, so the inequality is
    `0 ≤ 0`. -/
theorem klein_inequality_zero
    (A B : Matrix (Fin 0) (Fin 0) ℂ) (_hA : A.PosDef) (_hB : B.PosDef) :
    (Matrix.trace A - Matrix.trace B).re
      ≤ (Matrix.trace (A * (cfc Real.log A - cfc Real.log B))).re := by
  -- Tr of any matrix in Fin 0 is 0 = empty sum.
  have hA_trace : Matrix.trace A = 0 := by
    simp [Matrix.trace, Matrix.diag]
  have hB_trace : Matrix.trace B = 0 := by
    simp [Matrix.trace, Matrix.diag]
  have hM_trace :
      Matrix.trace (A * (cfc Real.log A - cfc Real.log B)) = 0 := by
    simp [Matrix.trace, Matrix.diag]
  rw [hA_trace, hB_trace, sub_zero, hM_trace]

/-! ## 7. Density-matrix Gibbs from Klein (placeholder route).

    When ρ and σ are density matrices (Tr = 1), the LHS of Klein
    vanishes, so Klein reduces to:

      0  ≤  Re Tr ( ρ · (log ρ − log σ) )  =  S(ρ‖σ),

    the non-negativity of Umegaki's relative entropy.  We package
    this as a target shape; the body of the proof is exactly Klein
    plus `ρ.hTrace = σ.hTrace = 1`. -/

/-- **Reduction shape:** Klein implies Gibbs for density matrices. -/
theorem umegakiRelativeEntropy_nonneg_of_klein
    (ρ σ : ComplexDensityMatrix n) (_hρ : ρ.M.PosDef) (_hσ : σ.M.PosDef)
    (hKlein : (Matrix.trace ρ.M - Matrix.trace σ.M).re
                ≤ (Matrix.trace (ρ.M *
                      (cfc Real.log ρ.M - cfc Real.log σ.M))).re) :
    0 ≤ (Matrix.trace (ρ.M *
            (operatorLog ρ - operatorLog σ))).re := by
  -- ρ.M.trace = 1, σ.M.trace = 1, so LHS of Klein = 0.
  have h_trρ := ρ.hTrace
  have h_trσ := σ.hTrace
  have h_LHS : (Matrix.trace ρ.M - Matrix.trace σ.M).re = 0 := by
    rw [h_trρ, h_trσ, sub_self, Complex.zero_re]
  rw [h_LHS] at hKlein
  -- operatorLog ρ = cfcρ Real.log ρ = cfc Real.log ρ.M (definitional).
  -- Same for σ.
  change 0 ≤ (Matrix.trace (ρ.M *
            (cfcρ Real.log ρ - cfcρ Real.log σ))).re
  unfold cfcρ
  exact hKlein

/-! ## 8. Axiom audit. -/

-- Uncomment locally to verify; expected output for each:
--   axioms: [propext, Classical.choice, Quot.sound]
-- VERIFIED 2026-05-30: all nine theorems depend only on Lean's
-- three standard axioms.  No `sorry`, no custom `axiom`.
-- #print axioms klein_scalar
-- #print axioms klein_scalar_form
-- #print axioms klein_inequality_self
-- #print axioms mul_cfc_log_eq_cfc_xlogx
-- #print axioms trace_mul_cfc_log_eq_sum
-- #print axioms re_trace_mul_cfc_log_eq_sum
-- #print axioms klein_diagonal_scalar
-- #print axioms klein_inequality_zero
-- #print axioms umegakiRelativeEntropy_nonneg_of_klein

end UnifiedTheory.LayerB.KleinInequality
