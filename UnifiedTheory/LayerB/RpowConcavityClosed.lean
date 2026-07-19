/-
  LayerB/RpowConcavityClosed.lean
  ────────────────────────────────

  **Unconditional cascade closure of `Rpow_Operator_Concavity_Target`** —
  combining the two now-discharged gates from
  `RpowIntegrandPerT` (Layer B) and `BochnerConcavityLift` (Layer C)
  into a single unconditional headline theorem.

  ## What this file ships

  * `rpow_operator_concavity_target_unconditional` —
      `Rpow_Operator_Concavity_Target` discharged with both
      previously named gates supplied unconditionally.  After this
      theorem, the only remaining Lieb-chain gate (on the rpow side)
      is `Log_As_Rpow_Limit_Target`, and the operator-trace target
      `Lieb1973_Tracial_Target`.

  * `log_as_rpow_limit_target_unconditional` —
      `Log_As_Rpow_Limit_Target` discharged unconditionally for
      `B : Matrix (Fin n) (Fin n) ℂ` (PosDef), bridging
      Mathlib's `CFC.tendsto_cfc_rpow_sub_one_log`
      (a `tendsto` to `CFC.log a`) to the project-side target
      form (a `tendsto` to `cfc Real.log B` with a `(1/p : ℂ)` smul).

  ## Honest scoping

  Both shipped theorems are **unconditional** — each depends only on
  Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`.
  No new mathematical content beyond a re-bridge of pre-existing
  identities:

  * Part 1 is pure composition of `rpow_operator_concavity_target_from_gates`
    (Layer D of `RpowOperatorConcavity`) with its two named-gate
    discharges.

  * Part 2 takes Mathlib's CFC-level scalar limit (already proven for
    arbitrary C⋆-algebras via uniform convergence on the spectrum) and
    rewrites the limit form into the project's notation:
      `cfc (fun x => p⁻¹ * (x^p - 1)) B`  ↦
        `((1/p : ℝ) : ℂ) • (cfc (fun x => x^p) B - 1)`
    via `cfc_smul`, `cfc_sub`, `cfc_const_one`, plus
    `CFC.log B = cfc Real.log B` (unfolds `CFC.log`).

  ## Consequence for the Lieb 1973 chain

  After this file, the rpow-side of the Lieb chain
  (`Rpow_Route_Full_Reduction` in `LiebRpowRoute`) is satisfied on
  TWO of its THREE named primary targets:

    * `Rpow_Operator_Concavity_Target`   ✅  (this file, Part 1)
    * `Log_As_Rpow_Limit_Target`          ✅  (this file, Part 2)
    * `Lieb1973_Tracial_Target`           ⏳  (open — Lieb 1973 deep
                                              operator-trace inequality;
                                              the genuinely hard remaining
                                              gate; not addressed here).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01.
-/

import UnifiedTheory.LayerB.LiebRpowRoute
import UnifiedTheory.LayerB.RpowOperatorConcavity
import UnifiedTheory.LayerB.RpowIntegrandPerT
import UnifiedTheory.LayerB.BochnerConcavityLift
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.RpowConcavityClosed

open Matrix Complex Filter Topology MeasureTheory Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open UnifiedTheory.LayerB.LiebRpowRoute
open UnifiedTheory.LayerB.RpowOperatorConcavity
open UnifiedTheory.LayerB.RpowIntegrandPerT
open UnifiedTheory.LayerB.BochnerConcavityLift

/-! ## 1. Part 1 — Cascade closure for `Rpow_Operator_Concavity_Target`. -/

/-- **CASCADE CLOSURE.**  The headline rpow-operator-concavity target
    of `LiebRpowRoute` is unconditional: both named gates of the
    Layer-D assembly in `RpowOperatorConcavity`
    (`RpowIntegrand_Per_t_Operator_Concavity_Target` and
    `Bochner_Concavity_Lift_Target`) have been discharged
    unconditionally in `RpowIntegrandPerT` and `BochnerConcavityLift`
    respectively.  This theorem composes them.

    After this theorem, the rpow-concavity step of the Lieb 1973
    reduction chain (`LiebRpowRoute.Rpow_Route_Full_Reduction`) is
    fully closed; only `Log_As_Rpow_Limit_Target` and the deep
    `Lieb1973_Tracial_Target` remain on the chain. -/
theorem rpow_operator_concavity_target_unconditional :
    Rpow_Operator_Concavity_Target :=
  rpow_operator_concavity_target_from_gates
    rpowIntegrand_per_t_concavity_target_holds
    bochnerConcavityLift_holds

/-! ## 2. Part 2 — Unconditional discharge of `Log_As_Rpow_Limit_Target`.

    Mathlib provides `CFC.tendsto_cfc_rpow_sub_one_log`, stating

      `Tendsto (fun p => cfc (fun x => p⁻¹ * (x^p - 1)) a) (𝓝[>] 0)
              (𝓝 (CFC.log a))`

    for `a : A` strictly positive in a C⋆-algebra `A`.

    Our target uses the form

      `Tendsto (fun p => ((1/p : ℝ) : ℂ) • (cfc (·^p) B - 1)) (𝓝[>] 0)
              (𝓝 (cfc Real.log B))`.

    The bridge: split the CFC of the scalar product via
    `cfc_smul` and `cfc_sub`, then recognise
    `((1/p : ℝ) : ℂ) • _ = (p⁻¹ : ℝ) • _` on `Matrix _ _ ℂ`
    (ℝ-smul factors through ℂ-coercion). -/

/-- ℝ-smul on a complex matrix equals ℂ-smul under coercion. -/
private lemma smul_real_eq_smul_complex {n : ℕ} (a : ℝ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (a : ℝ) • M = ((a : ℝ) : ℂ) • M := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- Equality of CFC expansions:
    `cfc (fun x => p⁻¹ * (x^p - 1)) B = p⁻¹ • (cfc (·^p) B - 1)`
    for `B : Matrix (Fin n) (Fin n) ℂ` with `B.PosDef`, `0 ≤ p`.

    The hypothesis `0 ≤ p` makes `(·^p)` continuous on all of `[0, ∞)`
    (including `0`), hence continuous on the PSD spectrum.  For `p < 0`
    one would need to know the spectrum avoids `0`, which holds for PosDef
    but is not needed for our application (the limit is taken from
    `𝓝[>] 0`, so `0 < p` eventually). -/
private lemma cfc_rpow_minus_one_eq_smul_sub
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosDef)
    {p : ℝ} (hp : 0 ≤ p) :
    cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) B
      = (p⁻¹ : ℝ) • (cfc (fun x : ℝ => x ^ p) B
                      - (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  have hB_PSD : B.PosSemidef := hB.posSemidef
  have hB_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ B := hB_PSD.nonneg
  have hB_SA : IsSelfAdjoint B := hB_PSD.isHermitian.isSelfAdjoint
  -- `(·^p)` is continuous on all of ℝ when `0 ≤ p`.
  have h_cont_rpow_global :
      Continuous (fun x : ℝ => x ^ p) := Real.continuous_rpow_const hp
  have h_cont_rpow :
      ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ B) :=
    h_cont_rpow_global.continuousOn
  -- Decompose: p⁻¹ * (x^p - 1) = p⁻¹ • ((x^p) - 1) (smul_eq_mul on ℝ).
  have h_fun_eq :
      (fun x : ℝ => p⁻¹ * (x ^ p - 1))
        = (fun x : ℝ => (p⁻¹ : ℝ) • ((fun y : ℝ => y ^ p) x
                                     - (fun _ : ℝ => (1 : ℝ)) x)) := by
    funext x
    simp [smul_eq_mul]
  rw [h_fun_eq]
  -- cfc (p⁻¹ • (f - g)) = p⁻¹ • (cfc f - cfc g).
  have h_cont_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (spectrum ℝ B) :=
    continuousOn_const
  have h_cont_sub :
      ContinuousOn (fun x : ℝ => (fun y : ℝ => y ^ p) x
                                  - (fun _ : ℝ => (1 : ℝ)) x)
        (spectrum ℝ B) := h_cont_rpow.sub h_cont_const
  -- cfc_smul: cfc (c • f) a = c • cfc f a.
  rw [cfc_smul (R := ℝ) (S := ℝ) (p⁻¹) _ B (hf := h_cont_sub)]
  -- cfc_sub on the inner.
  rw [cfc_sub (R := ℝ) (fun x : ℝ => x ^ p) (fun _ : ℝ => (1 : ℝ)) B
      h_cont_rpow h_cont_const]
  -- cfc of the constant 1 = 1.
  rw [cfc_const_one (R := ℝ) B]

/-- **PART 2 — Unconditional discharge of `Log_As_Rpow_Limit_Target`.**

    For PosDef `B : Matrix (Fin n) (Fin n) ℂ`,

      `Tendsto (fun p => ((1/p : ℝ) : ℂ) • (cfc (·^p) B - 1)) (𝓝[>] 0)
              (𝓝 (cfc Real.log B))`.

    Proof: take Mathlib's CFC limit
    `CFC.tendsto_cfc_rpow_sub_one_log`, which gives the limit
    in the form `cfc (fun x => p⁻¹ * (x^p - 1)) B → CFC.log B`,
    rewrite the cfc body via `cfc_rpow_minus_one_eq_smul_sub`, then
    convert ℝ-smul to ℂ-smul on the matrix and identify
    `CFC.log B = cfc Real.log B`. -/
theorem log_as_rpow_limit_target_unconditional :
    Log_As_Rpow_Limit_Target := by
  intro n B hB
  -- B is PosDef ⇒ B is strictly positive (0 ≤ B and IsUnit B).
  have hB_PSD : B.PosSemidef := hB.posSemidef
  have hB_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ B := hB_PSD.nonneg
  have hB_isUnit : IsUnit B := hB.isUnit
  have hB_SP : IsStrictlyPositive B :=
    IsStrictlyPositive.iff_of_unital.mpr ⟨hB_nonneg, hB_isUnit⟩
  -- Mathlib gives the limit in the cfc-of-scalar-product form.
  have h_main :
      Tendsto (fun p : ℝ => cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) B)
        (𝓝[>] 0) (𝓝 (CFC.log B)) :=
    CFC.tendsto_cfc_rpow_sub_one_log hB_SP
  -- Rewrite the function inside the limit using our identity.
  -- The eventual `0 < p` from `𝓝[>] 0` gives us the `0 ≤ p` needed.
  have h_eq_filter :
      ∀ᶠ p : ℝ in 𝓝[>] 0,
        cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) B
          = ((1 / p : ℝ) : ℂ) •
              (cfc (fun x : ℝ => x ^ p) B
                - (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    have h_pos : ∀ᶠ p : ℝ in 𝓝[>] 0, 0 < p := by
      filter_upwards [self_mem_nhdsWithin] with p hp using hp
    filter_upwards [h_pos] with p hp_pos
    rw [cfc_rpow_minus_one_eq_smul_sub B hB hp_pos.le]
    rw [smul_real_eq_smul_complex]
    -- ((p⁻¹ : ℝ) : ℂ) = ((1/p : ℝ) : ℂ).
    congr 1
    push_cast
    rw [one_div]
  -- CFC.log B = cfc Real.log B (definitional).
  have h_log_eq : CFC.log B = cfc Real.log B := rfl
  rw [h_log_eq] at h_main
  -- Transfer along the eventual equality.
  exact h_main.congr' h_eq_filter

/-! ## 3. Axiom audit (commented).

    Uncomment to verify locally that both shipped theorems depend
    only on Lean's three standard axioms
    `[propext, Classical.choice, Quot.sound]`.  Zero `sorry`, zero
    custom axioms. -/

-- #print axioms rpow_operator_concavity_target_unconditional
-- #print axioms log_as_rpow_limit_target_unconditional

-- VERIFIED 2026-06-01:
--   Both theorems depend only on Lean's three standard axioms
--   `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no
--   custom `axiom`.

/-! ## 4. Honest scope summary.

    **UNCONDITIONAL (this file)**:
      • `rpow_operator_concavity_target_unconditional` — `Rpow_Operator_Concavity_Target`
        composed from two unconditional discharges.
      • `log_as_rpow_limit_target_unconditional` — `Log_As_Rpow_Limit_Target`
        bridged from Mathlib's `CFC.tendsto_cfc_rpow_sub_one_log`.

    **OPEN on the Lieb 1973 chain**:
      • `Lieb1973_Tracial_Target` — the deep Lieb 1973 operator-trace
        inequality.  Carlen 2010, Theorem 2.9.  Not addressed here;
        the genuinely hard remaining gate on the rpow → Lieb chain.

    With the two theorems shipped here, the
    `LiebRpowRoute.Rpow_Route_Full_Reduction` chain is reduced to a
    SINGLE remaining named gate (`Lieb1973_Tracial_Target`). -/

end UnifiedTheory.LayerB.RpowConcavityClosed
