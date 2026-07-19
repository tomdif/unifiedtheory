/-
  LayerB/GoldenThompsonClosed.lean
  ────────────────────────────────

  **The commutator trace lemma (Step 1) — the load-bearing elementary
  estimate of the Lie–Trotter route to Golden–Thompson.**

  For Hermitian matrices `X, Y`,

      Re Tr(X Y X Y) ≤ Re Tr(X² Y²).

  PROOF (fully elementary, zero `sorry`, zero custom axiom).
  Let `C := X*Y − Y*X` be the commutator.  Since `X, Y` are
  Hermitian, `C` is **anti-Hermitian**: `Cᴴ = −C`.  Hence
  `Cᴴ * C = (−C) * C = −(C*C)`, and `Cᴴ * C` is positive semidefinite
  (`Mᴴ M ≥ 0` for any `M`), so it has nonnegative real trace.  Thus

      0 ≤ Re Tr(Cᴴ C) = −Re Tr(C²).

  Expanding `C² = (XY−YX)²` and using cyclicity of trace
  (`Tr(XYYX) = Tr(X²Y²)`, `Tr(YXXY) = Tr(X²Y²)`,
  `Tr(YXYX) = Tr(XYXY)`) gives

      Tr(C²) = 2 Tr(XYXY) − 2 Tr(X²Y²),

  whence `Re Tr(XYXY) ≤ Re Tr(X²Y²)`.

  This is exactly the `n = 1` (k = 2) instance of the per-step trace
  inequality `PerStep_TraceInequality_NormedExp_Target` that the
  Lie–Trotter route to Golden–Thompson consumes:  with
  `P = exp(A/2)`, `Q = exp(B/2)` (positive semidefinite) it gives
  `Re Tr((PQ)²) ≤ Re Tr(P²Q²) = Re Tr(exp A · exp B)`.

  ## Honest scope of this file

  The commutator trace lemma below is the genuinely elementary atom
  of the route, and it is proved here UNCONDITIONALLY.  It supplies
  the `k = 2` per-step bound directly.

  The per-step bound at the higher powers of two `k = 2ⁿ` (`n ≥ 2`)
  required to run the Lie–Trotter limit is the Araki–Lieb–Thirring
  trace inequality `Tr((PQ)^{2ⁿ}) ≤ Tr(P^{2ⁿ} Q^{2ⁿ})`; this does
  NOT reduce to the commutator lemma plus cyclicity alone (the
  naive trace induction provably fails to compose — see the negative
  weighted-peel analysis in the project notes), and Mathlib does not
  expose the matrix log-majorization / antisymmetric-tensor machinery
  it requires.  We therefore package the higher-`k` per-step bound as
  the named residual `PerStep_TraceInequality_NormedExp_Target`
  (defined upstream in `LiebSubgateProgress`), and record honestly:

    * the Lie–Trotter half is closed unconditionally
      (`LieTrotterProduct.LieTrotter_NormedExp_Target_holds`);
    * the `k = 2` per-step bound is closed here;
    * `GoldenThompson_Target` follows the instant the higher-`k`
      per-step residual is supplied (the reduction is recorded), but
      it is NOT discharged unconditionally, because that residual is
      the genuinely non-elementary Araki–Lieb–Thirring estimate.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-03.
-/

import UnifiedTheory.LayerB.LieTrotterProduct
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.GoldenThompsonClosed

open Matrix Complex
open scoped ComplexOrder

/-! ## 1. The commutator trace lemma (Step 1). -/

section Step1

variable {n : ℕ}

/-- `Tr(Mᴴ * M)` has nonnegative real part, for any complex matrix `M`. -/
private lemma re_trace_conjTranspose_mul_self_nonneg
    (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (Matrix.trace (Mᴴ * M)).re := by
  have hpsd : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have h0 : (0 : ℂ) ≤ Matrix.trace (Mᴴ * M) := hpsd.trace_nonneg
  exact (Complex.le_def.mp h0).1.trans_eq (by simp)

/-- **Commutator trace lemma (Step 1).**

    For Hermitian `X, Y : Matrix (Fin n) (Fin n) ℂ`,

        `Re Tr(X Y X Y) ≤ Re Tr(X² Y²)`.

    Equivalently `Re Tr((XY)²) ≤ Re Tr(X²Y²)`.  The load-bearing
    elementary estimate; the `k = 2` per-step bound of the Lie–Trotter
    route to Golden–Thompson. -/
theorem re_trace_XYXY_le
    (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (Matrix.trace (X * Y * X * Y)).re
      ≤ (Matrix.trace (X * X * Y * Y)).re := by
  -- The commutator `C := X*Y − Y*X`.
  set C : Matrix (Fin n) (Fin n) ℂ := X * Y - Y * X with hC
  -- `C` is anti-Hermitian: `Cᴴ = −C`.
  have hCH : Cᴴ = -C := by
    rw [hC]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hX.eq, hY.eq]
    abel
  -- Hence `Cᴴ * C = −(C * C)`.
  have hCHC : Cᴴ * C = -(C * C) := by rw [hCH, Matrix.neg_mul]
  -- `Re Tr(Cᴴ C) ≥ 0`.
  have hnonneg : 0 ≤ (Matrix.trace (Cᴴ * C)).re :=
    re_trace_conjTranspose_mul_self_nonneg C
  -- So `Re Tr(−(C*C)) ≥ 0`, i.e. `Re Tr(C*C) ≤ 0`.
  rw [hCHC, Matrix.trace_neg, Complex.neg_re, le_neg, neg_zero] at hnonneg
  -- Expand `C * C` and take real parts via cyclicity.
  -- `C*C = (X*Y - Y*X)*(X*Y - Y*X)`.
  have hexpand : C * C
      = X * Y * (X * Y) - X * Y * (Y * X) - Y * X * (X * Y) + Y * X * (Y * X) := by
    rw [hC]; noncomm_ring
  -- Real-trace of each cyclic block.
  -- Tr(X*Y*(Y*X)) = Tr(X*X*Y*Y) by cyclicity.
  have hc1 : Matrix.trace (X * Y * (Y * X)) = Matrix.trace (X * X * Y * Y) := by
    calc Matrix.trace (X * Y * (Y * X))
        = Matrix.trace ((X * Y * Y) * X) := by congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace (X * (X * Y * Y)) := Matrix.trace_mul_comm (X * Y * Y) X
      _ = Matrix.trace (X * X * Y * Y) := by congr 1; simp only [Matrix.mul_assoc]
  -- Tr(Y*X*(X*Y)) = Tr(X*X*Y*Y) by cyclicity.
  have hc2 : Matrix.trace (Y * X * (X * Y)) = Matrix.trace (X * X * Y * Y) := by
    calc Matrix.trace (Y * X * (X * Y))
        = Matrix.trace (Y * (X * X * Y)) := by congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * X * Y) * Y) := Matrix.trace_mul_comm Y (X * X * Y)
      _ = Matrix.trace (X * X * Y * Y) := rfl
  -- Tr(Y*X*(Y*X)) = Tr(X*Y*X*Y) by cyclicity.
  have hc3 : Matrix.trace (Y * X * (Y * X)) = Matrix.trace (X * Y * X * Y) := by
    calc Matrix.trace (Y * X * (Y * X))
        = Matrix.trace (Y * (X * Y * X)) := by congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * Y * X) * Y) := Matrix.trace_mul_comm Y (X * Y * X)
      _ = Matrix.trace (X * Y * X * Y) := rfl
  -- Assemble:  Tr(C*C) = Tr(XYXY) - Tr(XXYY) - Tr(XXYY) + Tr(XYXY).
  have htr : Matrix.trace (C * C)
      = 2 * Matrix.trace (X * Y * X * Y) - 2 * Matrix.trace (X * X * Y * Y) := by
    rw [hexpand]
    rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
    rw [hc1, hc2, hc3]
    have hxyxy : Matrix.trace (X * Y * (X * Y)) = Matrix.trace (X * Y * X * Y) := by
      rw [← Matrix.mul_assoc]
    rw [hxyxy]
    ring
  -- Take real parts.
  rw [htr] at hnonneg
  have h2re : ((2 : ℂ)).re = 2 := by norm_num
  have h2im : ((2 : ℂ)).im = 0 := by norm_num
  simp only [Complex.sub_re, Complex.mul_re, h2re, h2im,
    zero_mul, sub_zero] at hnonneg
  linarith

/-- **`(XY)²` form of Step 1.** `Re Tr((XY)²) ≤ Re Tr(X²Y²)`. -/
theorem re_trace_sq_XY_le
    (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (Matrix.trace ((X * Y) ^ 2)).re ≤ (Matrix.trace (X ^ 2 * Y ^ 2)).re := by
  have h := re_trace_XYXY_le X Y hX hY
  have e1 : (X * Y) ^ 2 = X * Y * X * Y := by
    rw [pow_two, ← Matrix.mul_assoc]
  have e2 : X ^ 2 * Y ^ 2 = X * X * Y * Y := by
    rw [pow_two, pow_two, ← Matrix.mul_assoc]
  rw [e1, e2]
  exact h

end Step1

/-! ## 2. The `k = 2` per-step bound for the exponential factors. -/

section PerStepTwo

variable {n : ℕ}

open NormedSpace

/-- `NormedSpace.exp` of a self-adjoint matrix is Hermitian (self-adjoint). -/
private lemma isHermitian_normedExp
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsSelfAdjoint M) :
    (NormedSpace.exp M).IsHermitian :=
  hM.exp

/-- **The `k = 2` per-step trace bound, exponential form.**

    For Hermitian `A, B`,
    `Re Tr((exp(A/2) · exp(B/2))²) ≤ Re Tr(exp(A/2)² · exp(B/2)²)`.

    Immediate from Step 1 with `X = exp(A/2)`, `Y = exp(B/2)` (both
    Hermitian since `A/2, B/2` are self-adjoint). -/
theorem perStep_two_normedExp
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace
        ((NormedSpace.exp ((1 / (2 : ℂ)) • A)
            * NormedSpace.exp ((1 / (2 : ℂ)) • B)) ^ 2)).re
      ≤ (Matrix.trace
          (NormedSpace.exp ((1 / (2 : ℂ)) • A) ^ 2
            * NormedSpace.exp ((1 / (2 : ℂ)) • B) ^ 2)).re := by
  have hstar2 : star (1 / (2 : ℂ)) = 1 / (2 : ℂ) := by
    rw [star_div₀, star_one]; norm_num
  have hsaA : IsSelfAdjoint ((1 / (2 : ℂ)) • A) := by
    have hA' : IsSelfAdjoint A := hA
    rw [IsSelfAdjoint, star_smul, hstar2, hA'.star_eq]
  have hsaB : IsSelfAdjoint ((1 / (2 : ℂ)) • B) := by
    have hB' : IsSelfAdjoint B := hB
    rw [IsSelfAdjoint, star_smul, hstar2, hB'.star_eq]
  have hXH : (NormedSpace.exp ((1 / (2 : ℂ)) • A)).IsHermitian :=
    isHermitian_normedExp (hsaA)
  have hYH : (NormedSpace.exp ((1 / (2 : ℂ)) • B)).IsHermitian :=
    isHermitian_normedExp (hsaB)
  exact re_trace_sq_XY_le _ _ hXH hYH

end PerStepTwo

/-! ## 3. State of the Lie–Trotter route after Step 1.

The Lie–Trotter half of the Golden–Thompson route is closed
unconditionally (`LieTrotterProduct.LieTrotter_NormedExp_Target_holds`).
Step 1 closes the per-step trace bound at `k = 2`.  We record here the
exact conditional propagation: the moment the per-step bound is
supplied at **all** powers of two (packaged upstream as
`PerStep_TraceInequality_NormedExp_Target`), the whole
Golden–Thompson target and the downstream Lieb tracial subgate
follow — the Lie–Trotter analytic core is no longer a gap. -/

section Cascade

open UnifiedTheory.LayerB.LiebSubgateProgress
open UnifiedTheory.LayerB.GoldenThompsonInequality
open UnifiedTheory.LayerB.LiebGoldenThompson
open UnifiedTheory.LayerB.AndoInterpolation
open UnifiedTheory.LayerB.LieTrotterProduct

/-- **`GoldenThompson_Target` from the per-step residual** (Lie–Trotter
    half already discharged in `LieTrotterProduct`).

    This is a re-statement, in this module, of the fact that the entire
    Golden–Thompson inequality `Re Tr(e^{A+B}) ≤ Re Tr(e^A e^B)` follows
    the instant the per-step trace bound is available at every power of
    two.  The Lie–Trotter limit `(e^{A/k} e^{B/k})^k → e^{A+B}` is
    already proved unconditionally. -/
theorem goldenThompson_target_of_perStep_residual
    (hPer : PerStep_TraceInequality_NormedExp_Target) :
    GoldenThompson_Target :=
  goldenThompson_target_of_perStep hPer

/-- **Downstream Lieb-1973 tracial subgate** from the per-step residual
    plus the Carlen–Lieb integral reduction.  Records how far the
    closure of Golden–Thompson reaches up the Lieb / SSA chain. -/
theorem lieb_tracial_subgate_of_perStep_residual
    (hPer : PerStep_TraceInequality_NormedExp_Target)
    (h_red : CarlenLieb_Integral_Reduction_Target) :
    Lieb1973_Tracial_NonCommuting_Subgate :=
  lieb_tracial_subgate_from_GT_route
    (goldenThompson_target_of_perStep hPer) h_red

end Cascade

/-! ## 4. Honest scope and cascade reach.

  **UNCONDITIONAL (this file)**

    * `re_trace_XYXY_le` / `re_trace_sq_XY_le` — the commutator trace
      lemma (Step 1): `Re Tr(X Y X Y) ≤ Re Tr(X² Y²)` for Hermitian
      `X, Y`.  Proved from anti-Hermiticity of the commutator and the
      positive-semidefiniteness of `Mᴴ M`, plus cyclicity.  This is the
      genuine elementary atom of the Lie–Trotter route.

    * `perStep_two_normedExp` — the `k = 2` per-step trace bound for the
      exponential factors, an immediate consequence of Step 1.

  **ALREADY UNCONDITIONAL (upstream `LieTrotterProduct`)**

    * The Lie–Trotter product formula
      `(e^{A/k} e^{B/k})^k → e^{A+B}` (`LieTrotter_NormedExp_Target_holds`).

  **STILL OPEN — the single remaining analytic core**

    * `PerStep_TraceInequality_NormedExp_Target`, the per-step trace
      bound at the higher powers of two `k = 2ⁿ` (`n ≥ 2`):
      `Re Tr((PQ)^{2ⁿ}) ≤ Re Tr(P^{2ⁿ} Q^{2ⁿ})` for positive
      semidefinite `P, Q`.  This is the **Araki–Lieb–Thirring** trace
      inequality.  It is TRUE (verified numerically across thousands of
      random PSD pairs) but does NOT reduce to Step 1 + cyclicity: the
      naive trace induction provably fails to compose (a fixed-PSD-weight
      peel step is false in general; only the `k = 2` base is Step 1),
      and every elementary reduction bottoms out on the same
      `Tr((QP)^k (AB)^k) ≤ Tr(A^{2k} B^{2k})` residual for `k ≥ 2`,
      which is exactly Araki–Lieb–Thirring / matrix log-majorization.
      Mathlib v4.28 exposes no matrix majorization, antisymmetric-tensor
      (compound-matrix), or Lieb–Thirring machinery, so this estimate is
      a multi-week formalisation in its own right and is NOT discharged
      here.  (Re-confirmed not invoking the project's own unproven
      `LiebThirring_Target`.)

  **CASCADE REACH (HONEST)**

    Golden–Thompson `Re Tr(e^{A+B}) ≤ Re Tr(e^A e^B)` does **NOT**
    close unconditionally in this pass: the Lie–Trotter half is closed
    and the `k = 2` per-step bound is closed, but the higher-`k`
    per-step bound (Araki–Lieb–Thirring) remains the one open core.

    Conditional on that single residual, the propagation is fully wired:
    `goldenThompson_target_of_perStep_residual` discharges
    `GoldenThompson_Target`, and
    `lieb_tracial_subgate_of_perStep_residual` carries it (with the
    separately-open Carlen–Lieb integral reduction) to
    `Lieb1973_Tracial_NonCommuting_Subgate`.  Full quantum strong
    subadditivity remains blocked by the same Araki–Lieb–Thirring core
    PLUS the independently-open Carlen–Lieb integral reduction and the
    `Lieb1973_Tracial → Lieb1973_Corrected → SSA` bridges.
-/

end UnifiedTheory.LayerB.GoldenThompsonClosed
