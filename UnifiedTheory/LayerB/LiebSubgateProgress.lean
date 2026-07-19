/-
  LayerB/LiebSubgateProgress.lean
  ────────────────────────────────

  **Sharpening of the residual non-commuting Lieb-1973 / Golden–Thompson
  subgate.**

  The non-commuting Golden–Thompson subgate
  (`GoldenThompsonNonCommuting.GoldenThompson_NonCommuting_Subgate`)
  was already reduced in the library to the conjunction of two named
  analytic targets stated at the **continuous-functional-calculus**
  level (`cfc Real.exp`):

    * `LieTrotter_Target`              — the Lie–Trotter product formula
                                          `(e^{A/k} e^{B/k})^k → e^{A+B}`;
    * `PerStep_TraceInequality_Target` — the per-`k` Re-trace bound.

  This file performs a **strict sharpening** of that residual: it
  removes the CFC layer entirely.  Using Mathlib's bridge

      `CFC.real_exp_eq_normedSpace_exp :
          IsSelfAdjoint a → cfc Real.exp a = NormedSpace.exp a`,

  we show that the two CFC-level targets are **definitionally equivalent**
  (provably `↔`) to two strictly cleaner targets stated purely in terms
  of the power-series matrix exponential `NormedSpace.exp ℝ`:

    * `LieTrotter_NormedExp_Target`
    * `PerStep_TraceInequality_NormedExp_Target`

  The point of the sharpening is that the residual analytic core is now a
  **pure `NormedSpace.exp` statement** — exactly the classical Lie product
  formula for the Banach-algebra exponential — with no continuous
  functional calculus wrapped around it.  This is the genuinely
  Mathlib-adjacent form: any future Mathlib `NormedSpace.exp` Lie–Trotter
  lemma discharges it directly, without CFC bookkeeping.

  ## What is proven here (zero `sorry`, zero custom axiom)

    * `cfc_exp_smul_eq_normedExp`     — the per-matrix CFC→power-series
                                         bridge for `(1/k) • A` with `A`
                                         Hermitian.
    * `lieTrotter_target_iff_normedExp`
                                       — `LieTrotter_Target ↔
                                          LieTrotter_NormedExp_Target`.
    * `perStep_target_iff_normedExp`   — `PerStep_TraceInequality_Target ↔
                                          PerStep_TraceInequality_NormedExp_Target`.
    * `goldenThompson_nonCommuting_from_normedExp_subgates`
                                       — the non-commuting GT subgate from
                                          the two **sharpened** targets.
    * `lieTrotterRoute_target_iff_normedExp`
                                       — the bundled `∧`-form equivalence.

  Net effect on the master reduction: the GT route's residual obligation
  `LieTrotter_Route_Target` is shown to be **equivalent** to a CFC-free
  obligation `LieTrotter_Route_NormedExp_Target`, so the irreducible core
  of the whole Lieb chain along the GT route is now a single pair of
  pure power-series-exponential facts.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-02.
-/

import UnifiedTheory.LayerB.GoldenThompsonNonCommuting
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Matrix.Normed

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LiebSubgateProgress

open Matrix Complex Filter Topology
open UnifiedTheory.LayerB.GoldenThompsonNonCommuting
open UnifiedTheory.LayerB.GoldenThompsonInequality
open UnifiedTheory.LayerB.LiebGoldenThompson

/-! ## 1. Self-adjointness bookkeeping. -/

section SelfAdjoint

variable {n : ℕ}

/-- `(1/k : ℂ) • A` is self-adjoint whenever `A` is Hermitian, because
    the scalar `1/k` is real (its `star` is itself). -/
private lemma isSelfAdjoint_invNat_smul
    (k : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    IsSelfAdjoint ((1 / (k : ℂ)) • A) := by
  have hsa : IsSelfAdjoint A := hA
  have hstar : star (1 / (k : ℂ)) = 1 / (k : ℂ) := by
    rw [star_div₀, star_one, Complex.star_def, Complex.conj_natCast]
  -- self-adjoint elements are closed under scaling by a self-conjugate scalar
  rw [IsSelfAdjoint]
  rw [star_smul, hstar, hsa.star_eq]

/-- `A` Hermitian ↔ `A` self-adjoint (matrix `IsHermitian` is defeq to
    `IsSelfAdjoint` but we provide an explicit bridge). -/
private lemma hermitian_isSelfAdjoint
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : IsSelfAdjoint A := hA

end SelfAdjoint

/-! ## 2. The per-matrix CFC → power-series bridge. -/

section Bridge

variable {n : ℕ}

/-- For Hermitian `A`, `cfc Real.exp ((1/k) • A) = NormedSpace.exp ((1/k) • A)`. -/
lemma cfc_exp_smul_eq_normedExp
    (k : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    cfc Real.exp ((1 / (k : ℂ)) • A)
      = NormedSpace.exp ((1 / (k : ℂ)) • A) :=
  CFC.real_exp_eq_normedSpace_exp (isSelfAdjoint_invNat_smul k A hA)

/-- For Hermitian `A`, `cfc Real.exp A = NormedSpace.exp A`. -/
lemma cfc_exp_eq_normedExp
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    cfc Real.exp A = NormedSpace.exp A :=
  CFC.real_exp_eq_normedSpace_exp (hermitian_isSelfAdjoint hA)

/-- For Hermitian `A, B`, `cfc Real.exp (A + B) = NormedSpace.exp (A + B)`. -/
lemma cfc_exp_add_eq_normedExp
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc Real.exp (A + B) = NormedSpace.exp (A + B) :=
  CFC.real_exp_eq_normedSpace_exp (hermitian_isSelfAdjoint (hA.add hB))

end Bridge

/-! ## 3. The sharpened (CFC-free) named targets. -/

/-- **Sharpened Lie–Trotter target** — pure `NormedSpace.exp ℝ` form.

    For all Hermitian `A, B`,

        `(exp(A/k) · exp(B/k))^k  →  exp(A + B)`   as `k → ∞`,

    where `exp = NormedSpace.exp ℝ` is the Banach-algebra power-series
    exponential.  No continuous functional calculus appears. -/
def LieTrotter_NormedExp_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → B.IsHermitian →
      Filter.Tendsto
        (fun k : ℕ =>
          (NormedSpace.exp ((1 / (k : ℂ)) • A)
            * NormedSpace.exp ((1 / (k : ℂ)) • B)) ^ k)
        Filter.atTop
        (nhds (NormedSpace.exp (A + B)))

/-- **Sharpened per-step trace inequality** — pure `NormedSpace.exp ℝ`
    form.

    For all Hermitian `A, B` and all `k ≥ 1`,

        `Re Tr((exp(A/k) · exp(B/k))^k)  ≤  Re Tr(exp A · exp B)`. -/
def PerStep_TraceInequality_NormedExp_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → B.IsHermitian →
      ∀ k : ℕ, 1 ≤ k →
        (Matrix.trace
          ((NormedSpace.exp ((1 / (k : ℂ)) • A)
              * NormedSpace.exp ((1 / (k : ℂ)) • B)) ^ k)).re
          ≤ (Matrix.trace
                (NormedSpace.exp A * NormedSpace.exp B)).re

/-! ## 4. Equivalence of CFC-level and sharpened targets. -/

/-- **The Lie–Trotter target is equivalent to its CFC-free form.** -/
theorem lieTrotter_target_iff_normedExp :
    LieTrotter_Target ↔ LieTrotter_NormedExp_Target := by
  unfold LieTrotter_Target LieTrotter_NormedExp_Target
  constructor
  · intro h n A B hA hB
    have := h A B hA hB
    -- rewrite every `cfc Real.exp` to `NormedSpace.exp ℝ`
    simpa only [cfc_exp_smul_eq_normedExp _ A hA,
      cfc_exp_smul_eq_normedExp _ B hB,
      cfc_exp_add_eq_normedExp A B hA hB] using this
  · intro h n A B hA hB
    have := h A B hA hB
    simpa only [cfc_exp_smul_eq_normedExp _ A hA,
      cfc_exp_smul_eq_normedExp _ B hB,
      cfc_exp_add_eq_normedExp A B hA hB] using this

/-- **The per-step target is equivalent to its CFC-free form.** -/
theorem perStep_target_iff_normedExp :
    PerStep_TraceInequality_Target
      ↔ PerStep_TraceInequality_NormedExp_Target := by
  unfold PerStep_TraceInequality_Target PerStep_TraceInequality_NormedExp_Target
  constructor
  · intro h n A B hA hB k hk
    have := h A B hA hB k hk
    simpa only [cfc_exp_smul_eq_normedExp _ A hA,
      cfc_exp_smul_eq_normedExp _ B hB,
      cfc_exp_eq_normedExp A hA, cfc_exp_eq_normedExp B hB] using this
  · intro h n A B hA hB k hk
    have := h A B hA hB k hk
    simpa only [cfc_exp_smul_eq_normedExp _ A hA,
      cfc_exp_smul_eq_normedExp _ B hB,
      cfc_exp_eq_normedExp A hA, cfc_exp_eq_normedExp B hB] using this

/-! ## 5. The non-commuting GT subgate from the sharpened targets. -/

/-- **Non-commuting Golden–Thompson subgate from the two sharpened
    (CFC-free) targets.**

    Combines the equivalences of §4 with the existing composite
    `goldenThompson_nonCommuting_from_subgates`. -/
theorem goldenThompson_nonCommuting_from_normedExp_subgates
    (hLT : LieTrotter_NormedExp_Target)
    (hPerN : PerStep_TraceInequality_NormedExp_Target) :
    GoldenThompson_NonCommuting_Subgate :=
  goldenThompson_nonCommuting_from_subgates
    (lieTrotter_target_iff_normedExp.mpr hLT)
    (perStep_target_iff_normedExp.mpr hPerN)

/-! ## 6. Bundled equivalence and master propagation. -/

/-- **Bundled sharpened route target.** -/
def LieTrotter_Route_NormedExp_Target : Prop :=
  LieTrotter_NormedExp_Target ∧ PerStep_TraceInequality_NormedExp_Target

/-- **The bundled GT-route residual is equivalent to its CFC-free
    form.**  This is the headline sharpening: the entire residual
    obligation of the Lie–Trotter route to Golden–Thompson is shown to
    coincide with a pair of pure power-series-exponential statements. -/
theorem lieTrotterRoute_target_iff_normedExp :
    LieTrotter_Route_Target ↔ LieTrotter_Route_NormedExp_Target := by
  unfold LieTrotter_Route_Target LieTrotter_Route_NormedExp_Target
  rw [lieTrotter_target_iff_normedExp, perStep_target_iff_normedExp]

/-- **Golden–Thompson target from the sharpened bundled route.** -/
theorem goldenThompson_target_from_normedExp_route
    (h : LieTrotter_Route_NormedExp_Target) :
    GoldenThompson_Target :=
  goldenThompson_target_from_lieTrotter_route_target
    (lieTrotterRoute_target_iff_normedExp.mpr h)

/-! ## 7. Honest scope summary.

    **UNCONDITIONAL (this file)**:

      * `cfc_exp_smul_eq_normedExp`, `cfc_exp_eq_normedExp`,
        `cfc_exp_add_eq_normedExp` — the CFC → `NormedSpace.exp ℝ`
        bridge for the Hermitian arguments appearing in the Lie–Trotter
        route.

      * `lieTrotter_target_iff_normedExp`,
        `perStep_target_iff_normedExp`,
        `lieTrotterRoute_target_iff_normedExp` — the CFC-level targets
        are PROVABLY EQUIVALENT to strictly cleaner targets stated in
        terms of the power-series matrix exponential.

      * `goldenThompson_nonCommuting_from_normedExp_subgates`,
        `goldenThompson_target_from_normedExp_route` — the GT subgate /
        target discharged from the sharpened (CFC-free) targets.

    **SHARPENED RESIDUAL CORE**:

      The irreducible analytic content of the GT route is now the pair

        `LieTrotter_NormedExp_Target`
        `PerStep_TraceInequality_NormedExp_Target`

      stated entirely in `NormedSpace.exp ℝ`.  The first is exactly the
      classical Lie product formula for the Banach-algebra exponential;
      the second the finite-`k` Schatten/Hölder trace bound.  Neither is
      currently in Mathlib, but both are now in the cleanest possible
      Mathlib-adjacent form — a future Mathlib Lie–Trotter lemma for
      `NormedSpace.exp` closes the first directly.
-/

/-! ## 8. Axiom audit (commented). -/

-- #print axioms cfc_exp_smul_eq_normedExp
-- #print axioms lieTrotter_target_iff_normedExp
-- #print axioms perStep_target_iff_normedExp
-- #print axioms goldenThompson_nonCommuting_from_normedExp_subgates
-- #print axioms lieTrotterRoute_target_iff_normedExp
-- #print axioms goldenThompson_target_from_normedExp_route

end UnifiedTheory.LayerB.LiebSubgateProgress
