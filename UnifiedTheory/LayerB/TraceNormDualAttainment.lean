/-
  LayerB/TraceNormDualAttainment.lean
  ────────────────────────────────────

  **Discharging `TraceNormDualAttained` — the trace-norm dual is
  ATTAINED at the sign of the Hermitian difference.**

  `TraceDistanceContractivity.lean` reduces partial-trace contractivity
  of the trace distance to a single named hypothesis,

      `TraceNormDualAttained ρ σ` :
        ∃ M, (1 - M).PosSemidef ∧ (M + 1).PosSemidef ∧
             traceDistance (Tr_B ρ) (Tr_B σ)
               ≤ Re Tr(M · (Tr_B ρ − Tr_B σ)),

  i.e. the variational LOWER bound: the trace norm of the marginal
  Hermitian difference is *attained* by some Hermitian contraction
  `−I ≤ M ≤ I`.  Combined with the unconditional variational UPPER
  bound `re_trace_marginal_test_le_traceDistance`, this closes
  partial-trace (and hence CPTP) contractivity UNCONDITIONALLY.

  **The construction.**  For a Hermitian matrix `Y`, the optimal
  contraction is the *sign* `M = sgn(Y) = cfc Real.sign Y`:

    • `Mᴴ = M`            — CFC of a real function is self-adjoint;
    • `−I ⪯ M ⪯ I`        — `spectrum(M) = sign '' spectrum(Y) ⊆ {−1,0,1}`;
    • `M · Y = |Y|`       — because `sign t · t = |t|` pointwise, so
                            `cfc sign Y · cfc id Y = cfc (sign·id) Y
                             = cfc |·| Y = CFC.abs Y` (`cfc_mul`);
    • hence `Re Tr(M · Y) = Re Tr |Y| = traceDistance`, ATTAINED.

  The sign function is discontinuous at `0`, but a matrix has a FINITE
  real spectrum, on which every function is continuous (`Set.Finite.
  continuousOn`) — the same device used by `cfcAbs_unitary_conj`.

  STANDING CONSTRAINT: zero `sorry`, zero custom `axiom`.  Everything
  here is a spectral-decomposition (continuous functional calculus)
  argument.

  ## Build

      lake build UnifiedTheory.LayerB.TraceNormDualAttainment
-/

import UnifiedTheory.LayerB.TraceDistanceContractivity
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.Matrix.Spectrum

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.TraceNormDualAttainment

open Matrix Complex
open scoped ComplexOrder MatrixOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.QuantumChernoff
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.PartialTraceDPI
open UnifiedTheory.LayerB.TraceDistanceContractivity

variable {k : ℕ}

/-- Re-declare the matrix `CStarAlgebra` instance (mirrors the pattern
    in `TraceDistanceContractivity.lean` / `UnitaryInvariance.lean`),
    needed for `CFC.abs` / `cfc`. -/
noncomputable scoped instance matrixCStarAlgebra :
    CStarAlgebra (Matrix (Fin k) (Fin k) ℂ) where

/-! ## 1.  The optimal contraction `M = sgn(Y)` for Hermitian `Y`. -/

/-- The **sign** of a Hermitian matrix, `sgn(Y) := cfc Real.sign Y`,
    the optimal dual contraction for the trace norm. -/
noncomputable def signMatrix (Y : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  cfc (Real.sign) Y

/-- `Real.sign` is continuous on the (finite) real spectrum of any
    matrix.  Any function is continuous on a finite set. -/
theorem continuousOn_sign_spectrum (Y : Matrix (Fin k) (Fin k) ℂ) :
    ContinuousOn (Real.sign) (spectrum ℝ Y) :=
  (Set.toFinite _).continuousOn _

/-- `sgn(Y)` is self-adjoint (Hermitian): it is the CFC of a real
    function applied to a self-adjoint element. -/
theorem signMatrix_isSelfAdjoint (Y : Matrix (Fin k) (Fin k) ℂ) :
    IsSelfAdjoint (signMatrix Y) :=
  IsSelfAdjoint.cfc

/-- **`sgn(Y)` is a contraction from above**, `sgn(Y) ⪯ I`.

    Its spectrum is `Real.sign '' spectrum(Y) ⊆ {−1,0,1} ⊆ (−∞, 1]`. -/
theorem signMatrix_le_one (Y : Matrix (Fin k) (Fin k) ℂ) :
    signMatrix Y ≤ 1 := by
  refine cfc_le_one (Real.sign) Y ?_
  intro x _
  rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

/-- **`sgn(Y)` is a contraction from below**, `−I ⪯ sgn(Y)`.

    Its spectrum is `Real.sign '' spectrum(Y) ⊆ {−1,0,1} ⊆ [−1, ∞)`. -/
theorem neg_one_le_signMatrix
    (Y : Matrix (Fin k) (Fin k) ℂ) (hY : IsSelfAdjoint Y) :
    (-1 : Matrix (Fin k) (Fin k) ℂ) ≤ signMatrix Y := by
  have h : (algebraMap ℝ (Matrix (Fin k) (Fin k) ℂ) (-1)) ≤ signMatrix Y := by
    refine algebraMap_le_cfc (Real.sign) (-1) Y ?_ (continuousOn_sign_spectrum Y) hY
    intro x _
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
  simpa using h

/-- `sgn(Y)` is a Hermitian contraction in the form the contractivity
    file consumes: `(1 − sgn Y)` and `(sgn Y + 1)` are PSD. -/
theorem signMatrix_contraction
    (Y : Matrix (Fin k) (Fin k) ℂ) (hY : IsSelfAdjoint Y) :
    (1 - signMatrix Y).PosSemidef ∧ (signMatrix Y + 1).PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- 0 ≤ 1 - sgn Y  ⟺  sgn Y ≤ 1.
    rw [← Matrix.nonneg_iff_posSemidef, sub_nonneg]
    exact signMatrix_le_one Y
  · -- 0 ≤ sgn Y + 1  ⟺  -1 ≤ sgn Y.
    rw [← Matrix.nonneg_iff_posSemidef]
    have h := neg_one_le_signMatrix Y hY
    -- -1 ≤ sgn Y  →  0 ≤ sgn Y + 1.
    have : (0 : Matrix (Fin k) (Fin k) ℂ) ≤ signMatrix Y - (-1) := by
      rwa [sub_nonneg]
    simpa [sub_neg_eq_add] using this

/-! ## 2.  Attainment: `sgn(Y) · Y = |Y|`. -/

/-- **The sign attains the absolute value**: `sgn(Y) · Y = |Y|`.

    Pointwise `Real.sign t · t = |t|`; pushing this through the
    multiplicativity of the continuous functional calculus
    (`cfc_mul`, `cfc_id`) and `CFC.abs = cfc ‖·‖` gives the operator
    identity. -/
theorem signMatrix_mul_self_eq_abs
    (Y : Matrix (Fin k) (Fin k) ℂ) (hY : IsSelfAdjoint Y) :
    signMatrix Y * Y = CFC.abs Y := by
  have hcont := continuousOn_sign_spectrum Y
  -- sgn Y * Y = cfc sign Y * cfc id Y = cfc (fun t => sign t * t) Y.
  have h_mul : signMatrix Y * Y
      = cfc (fun t : ℝ => Real.sign t * t) Y := by
    rw [signMatrix,
        cfc_mul (Real.sign) (fun t : ℝ => t) Y hcont (by fun_prop),
        cfc_id' ℝ Y]
  rw [h_mul]
  -- CFC.abs Y = cfc ‖·‖ Y = cfc |·| Y, and sign t * t = |t| pointwise.
  rw [CFC.abs_eq_cfc_norm Y hY]
  refine cfc_congr ?_
  intro x _
  simp only []
  -- Real.sign x * x = ‖x‖ = |x|.
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, Real.norm_eq_abs, abs_of_neg hx]; ring
  · rw [hx, Real.sign_zero]; simp
  · rw [Real.sign_of_pos hx, Real.norm_eq_abs, abs_of_pos hx]; ring

/-- **Attainment of the trace-norm dual** for a single Hermitian `Y`.

    `Re Tr(sgn(Y) · Y) = Re Tr |Y|`. -/
theorem re_trace_signMatrix_mul_eq
    (Y : Matrix (Fin k) (Fin k) ℂ) (hY : IsSelfAdjoint Y) :
    (Matrix.trace (signMatrix Y * Y)).re
      = (Matrix.trace (CFC.abs Y)).re := by
  rw [signMatrix_mul_self_eq_abs Y hY]

/-! ## 3.  Discharge `TraceNormDualAttained`. -/

variable {n_A n_B : ℕ}

/-- **MAIN: the trace-norm dual on the marginal is ATTAINED.**

    The named hypothesis `TraceNormDualAttained ρ σ` of
    `TraceDistanceContractivity.lean` holds for ALL `ρ σ`, witnessed by
    `M = sgn(Tr_B ρ − Tr_B σ)`.  The construction is a continuous
    functional calculus (spectral) argument: `M` is Hermitian, a
    contraction `−I ⪯ M ⪯ I`, and `M · (Tr_B ρ − Tr_B σ) =
    |Tr_B ρ − Tr_B σ|`, so `Re Tr(M · ·) = Re Tr |·| =
    traceDistance (Tr_B ρ) (Tr_B σ)`. -/
theorem traceNormDualAttained
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) :
    TraceNormDualAttained ρ σ := by
  -- The marginal Hermitian difference.
  set Y : Matrix (Fin n_A) (Fin n_A) ℂ :=
    diff (partialTraceDensity_right ρ) (partialTraceDensity_right σ) with hY
  have hYsa : IsSelfAdjoint Y := diff_isSelfAdjoint _ _
  -- Y = partialTrace_right (reindexFactor (diff ρ σ)).
  have hYeq : Y = partialTrace_right (reindexFactor (diff ρ σ)) :=
    diff_partialTraceDensity_right_eq ρ σ
  refine ⟨signMatrix Y, ?_, ?_, ?_⟩
  · exact (signMatrix_contraction Y hYsa).1
  · exact (signMatrix_contraction Y hYsa).2
  · -- traceDistance (Tr_B ρ) (Tr_B σ) = Re Tr |Y| = Re Tr(sgn Y · Y).
    have h_td :
        traceDistance (partialTraceDensity_right ρ)
                      (partialTraceDensity_right σ)
          = (Matrix.trace (CFC.abs Y)).re := by
      rw [traceDistance, hY]
    rw [h_td, ← re_trace_signMatrix_mul_eq Y hYsa]
    -- Rewrite Y inside the trace as the partial trace, to match the goal.
    rw [hYeq]

/-! ## 4.  UNCONDITIONAL partial-trace / CPTP contractivity.

With the dual-attainment hypothesis discharged, the contractivity
results of `TraceDistanceContractivity.lean` become unconditional. -/

/-- **Partial-trace contractivity of the trace distance, UNCONDITIONAL.**

        `traceDistance (Tr_B ρ) (Tr_B σ)  ≤  traceDistance ρ σ`.

    This is `traceDistance_partialTrace_contractive` with its
    dual-attainment hypothesis closed by `traceNormDualAttained`.
    No named hypotheses remain. -/
theorem traceDistance_partialTrace_contractive_unconditional
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) :
    traceDistance (partialTraceDensity_right ρ) (partialTraceDensity_right σ)
      ≤ traceDistance ρ σ :=
  traceDistance_partialTrace_contractive ρ σ (traceNormDualAttained ρ σ)

/-- **Distinguishability is non-increasing under the partial trace,
    UNCONDITIONAL.**

    The Helstrom optimal success probability `½(1 + ½·traceDistance)`
    cannot rise under the partial-trace stage — the monotonicity behind
    Helstrom / BB84.  Closed via `traceNormDualAttained`. -/
theorem distinguishability_nonincreasing_partialTrace_unconditional
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) :
    (1 / 2 : ℝ)
        * traceDistance (partialTraceDensity_right ρ)
                         (partialTraceDensity_right σ)
      ≤ (1 / 2 : ℝ) * traceDistance ρ σ :=
  distinguishability_nonincreasing_partialTrace ρ σ (traceNormDualAttained ρ σ)

/-! ## 5.  Axiom audit. -/

#print axioms traceNormDualAttained
#print axioms traceDistance_partialTrace_contractive_unconditional
#print axioms distinguishability_nonincreasing_partialTrace_unconditional

end UnifiedTheory.LayerB.TraceNormDualAttainment
