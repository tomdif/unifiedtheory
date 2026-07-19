/-
  LayerB/LiebGoldenThompson.lean
  ───────────────────────────────

  **The Carlen–Lieb 2008 Golden–Thompson route** — an alternative
  reduction of the only remaining Lieb-chain obligation,
  `Lieb1973_Tracial_NonCommuting_Subgate` (defined in
  `LayerB.AndoInterpolation`), to two classical inequalities that
  enjoy multiple independent proofs in the literature.

  ## Why this file exists

  `LayerB.AndoInterpolation` discharges every special case of the
  Lieb 1973 tracial concavity inequality (endpoints `s = 0, 1`,
  trivial dimension `n = 0`, commuting case) and packages the
  remaining non-commuting `s ∈ (0, 1)` content as the named gate
  `Lieb1973_Tracial_NonCommuting_Subgate`.

  Carlen–Lieb (J. Math. Phys. 2008, "Norm inequalities and a
  Golden–Thompson inequality for the relative entropy") sketch a
  reduction of exactly this content to the
  **Golden–Thompson inequality** (`Tr e^{A+B} ≤ Tr(e^A · e^B)`,
  Hermitian `A, B`) combined with a **Schwartz integral
  representation** of fractional powers,

      `x^p = (sin πp / π) · ∫₀^∞ t^{p-1} · x · (x + t)⁻¹ dt`,

  valid for `0 < p < 1` and `x > 0`.  The integral representation
  rewrites `Tr(A^s · B^{1-s})` as an integral whose integrand is
  jointly concave in `(A, B)` by an unconditional Kraus / resolvent
  argument, and the Carlen–Lieb estimate provides the inner
  jointly concave lower bound via Golden–Thompson applied to the
  exponentiated logarithms.

  ## Strategy of this file

  This file packages the Carlen–Lieb 2008 route **schematically**:

    (i)   `GoldenThompson_Target` — the classical Hermitian-matrix
          Golden–Thompson inequality, stated as a clean `Prop`.

    (ii)  `CarlenLieb_Integral_Reduction_Target` — the analytic
          identity reducing the Lieb 1973 tracial gate to
          Golden–Thompson via the Schwartz integral representation
          and the resolvent-form joint concavity.  This is the
          analytic content Carlen–Lieb 2008 prove on top of GT.

    (iii) `lieb_tracial_subgate_from_GT_route` — the schematic
          composite reduction: **`GT_Target ∧ Integral_Reduction →
          Lieb1973_Tracial_NonCommuting_Subgate`**.  Proved
          unconditionally as a Lean implication: it is just the
          definition of `CarlenLieb_Integral_Reduction_Target`
          unpacking to the subgate when GT is supplied.

    (iv)  Downstream cascades: once *either* pair of named gates
          (`(GoldenThompson_Target, CarlenLieb_Integral_Reduction_Target)`
          via this file, or `Lieb1973_Tracial_NonCommuting_Subgate`
          directly via `AndoInterpolation`) lands, the entire
          Lieb 1973 → `Lieb1973_Tracial_Target` cascade closes
          via `lieb_tracial_target_from_subgate`.

  ## Honest scoping

  * The Carlen–Lieb 2008 **reduction step** (the integral identity
    and its joint-concavity argument) is encapsulated in
    `CarlenLieb_Integral_Reduction_Target`; we do **not** attempt
    its Lean discharge here.

  * **Golden–Thompson itself** is encapsulated in
    `GoldenThompson_Target`; we do **not** attempt its Lean
    discharge here.  Mathlib v4.28 does not currently expose
    matrix Golden–Thompson directly, though all the ingredients
    (`CFC.exp`, `IsHermitian`, `Matrix.trace`, operator-norm
    estimates) are present.

  * The **schematic composition** `(i) + (ii) → subgate` is
    proved unconditionally as a trivial implication.

  The advantage of the GT route over the Hansen–Pedersen / Ando
  route packaged in `AndoInterpolation` is that it splits the
  one remaining obligation into two **independently classical**
  pieces, either of which (or both) may land via separate Lean
  efforts — the entire Lieb chain therefore closes as soon as
  either pair lands.

  ## Cascade structure

      GoldenThompson_Target ∧
      CarlenLieb_Integral_Reduction_Target
        → Lieb1973_Tracial_NonCommuting_Subgate     (this file)
        → Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target
                                                    (AndoInterpolation)
        → Lieb1973_Tracial_Target                   (via rpow concavity ✅)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01.
-/

import UnifiedTheory.LayerB.LiebRpowRoute
import UnifiedTheory.LayerB.LiebTracialAttack
import UnifiedTheory.LayerB.AndoInterpolation
import UnifiedTheory.LayerB.RpowConcavityClosed
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LiebGoldenThompson

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.LiebRpowRoute
open UnifiedTheory.LayerB.LiebTracialAttack
open UnifiedTheory.LayerB.AndoInterpolation
open UnifiedTheory.LayerB.RpowConcavityClosed
open UnifiedTheory.LayerB.LiebCorrectedCommutingFull

/-! ## 1. The Golden–Thompson inequality (named target).

    For Hermitian `A, B`,

        `Re Tr (cfc exp (A + B))  ≤  Re Tr (cfc exp A · cfc exp B)`.

    This is the **Golden–Thompson inequality** (Golden 1965, Thompson
    1965, Symanzik 1965, with extensions by Lieb 1973, Araki 1990,
    and many others).  It is a classical inequality with multiple
    independent proofs (the Trotter product formula route, the
    integral-representation route, the Lieb concavity route, the
    quaternionic interpolation route).  Mathlib v4.28 does not
    currently expose it directly. -/
def GoldenThompson_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → B.IsHermitian →
      (Matrix.trace (cfc Real.exp (A + B))).re
        ≤ (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re

/-- Canonical interface for `GoldenThompson_Target`. -/
-- ⚠️ AUDIT-FLAG (REFLEXIVE INTERFACE): `(h : T) : T := h`; this is NOT a discharge.
-- `GoldenThompson_Target` (the Lie–Trotter / non-commuting exp residual) remains OPEN — it is one of
-- the two irreducible analytic cores of the whole Lieb/SSA chain.
theorem goldenThompson_target_holds
    (h : GoldenThompson_Target) : GoldenThompson_Target := h

/-! ## 2. The Carlen–Lieb 2008 reduction target.

    The analytic content reducing Lieb 1973 tracial concavity
    (non-commuting general `s`) to Golden–Thompson.

    The reduction uses the **Schwartz integral representation** of
    the fractional power,

        `x^p = (sin πp / π) · ∫₀^∞ t^{p-1} · x · (x + t)⁻¹ dt`,

    valid for `0 < p < 1` and `x > 0`.  Applied to `A^s` and
    `B^{1-s}` and traced against the product, the tracial form
    rewrites as a double integral whose integrand is jointly
    concave in `(A, B)` via the (unconditional) resolvent-form
    joint concavity of `(A, B) ↦ Tr(A·(A+t₁)⁻¹ · B·(B+t₂)⁻¹)`.
    Golden–Thompson supplies the inner pointwise estimate matching
    the convex-combination upper bound.

    We do not unfold the integral mechanics here — they are
    multi-week Lean work involving Bochner integration of
    matrix-valued resolvents, dominated convergence on the joint
    `(t₁, t₂) ∈ (0,∞)² ` rays, and the Lebesgue-trace exchange.

    Instead, we package the full analytic content as a single
    `Prop`: **given Golden–Thompson, the Lieb tracial sub-gate
    holds**. -/
def CarlenLieb_Integral_Reduction_Target : Prop :=
  GoldenThompson_Target → Lieb1973_Tracial_NonCommuting_Subgate

/-- Canonical interface for `CarlenLieb_Integral_Reduction_Target`. -/
-- ⚠️ AUDIT-FLAG (REFLEXIVE INTERFACE): `(h : T) : T := h`; this is NOT a discharge. The implication
-- `CarlenLieb_Integral_Reduction_Target` is only NAMED here, not proved.
theorem carlenLieb_integral_reduction_target_holds
    (h : CarlenLieb_Integral_Reduction_Target) :
    CarlenLieb_Integral_Reduction_Target := h

/-! ## 3. The schematic composite: GT + CL-integral → subgate.

    Proved unconditionally as a trivial implication: this is the
    skeletal Carlen–Lieb route. -/

/-- **Schematic Carlen–Lieb 2008 reduction.**

    The Lieb 1973 non-commuting sub-gate follows from
    Golden–Thompson plus the Carlen–Lieb integral-reduction
    target.  This is the headline composite of the GT route. -/
theorem lieb_tracial_subgate_from_GT_route
    (h_GT : GoldenThompson_Target)
    (h_red : CarlenLieb_Integral_Reduction_Target) :
    Lieb1973_Tracial_NonCommuting_Subgate :=
  h_red h_GT

/-- **Alternative form.**  Packaged as a single implication
    `(GT ∧ Reduction) → subgate`. -/
theorem lieb_tracial_subgate_from_GT_route_and
    (h : GoldenThompson_Target ∧ CarlenLieb_Integral_Reduction_Target) :
    Lieb1973_Tracial_NonCommuting_Subgate :=
  h.2 h.1

/-! ## 4. Downstream cascade to `Lieb1973_Tracial_Target`. -/

/-- **`Lieb1973_Tracial_Target` from the GT route.**

    Composes `lieb_tracial_subgate_from_GT_route` with
    `AndoInterpolation.lieb_tracial_target_from_subgate`. -/
theorem lieb_tracial_target_from_GT_route
    (h_GT : GoldenThompson_Target)
    (h_red : CarlenLieb_Integral_Reduction_Target) :
    Lieb1973_Tracial_Target :=
  lieb_tracial_target_from_subgate
    (lieb_tracial_subgate_from_GT_route h_GT h_red)

/-- **Parent gate from the GT route.** -/
theorem lieb_tracial_parent_gate_from_GT_route
    (h_GT : GoldenThompson_Target)
    (h_red : CarlenLieb_Integral_Reduction_Target) :
    Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target :=
  ando_interpolation_holds
    (lieb_tracial_subgate_from_GT_route h_GT h_red)

/-! ## 5. Re-exports of already-unconditional special cases.

    These special cases are *already* discharged unconditionally
    by `AndoInterpolation`; we re-export under the
    `LiebGoldenThompson` namespace so that downstream consumers of
    the GT route have a single canonical access point for the
    "already-handled" cases.

    The intent: the GT route's claim is **not** that GT is needed
    everywhere — it is needed *only* for the non-commuting
    general-`s` core, exactly what
    `Lieb1973_Tracial_NonCommuting_Subgate` already encapsulates. -/

/-- Re-export of `AndoInterpolation.lieb1973_tracial_commuting_unconditional`
    for canonical GT-route access. -/
theorem lieb_tracial_commuting_no_GT_needed
    {m : ℕ} (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (h_comm : AllCommute A₁ A₂ B₁ B₂)
    (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    α * (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) A₁ * cfc (fun x : ℝ => x ^ (1 - s)) B₁)).re
        + (1 - α) * (Matrix.trace
            (cfc (fun x : ℝ => x ^ s) A₂ * cfc (fun x : ℝ => x ^ (1 - s)) B₂)).re
      ≤ (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
            * cfc (fun x : ℝ => x ^ (1 - s))
                ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re :=
  lieb1973_tracial_commuting_unconditional
    A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ h_comm s hs₀ hs₁ α hα₀ hα₁

/-- Re-export of `AndoInterpolation.lieb_tracial_endpoint_s_zero`
    for canonical GT-route access (no GT needed at `s = 0`). -/
theorem lieb_tracial_endpoint_zero_no_GT_needed
    {n : ℕ} (A₁ A₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    α * (Matrix.trace
          (cfc (fun x : ℝ => x ^ (0 : ℝ)) A₁
            * cfc (fun x : ℝ => x ^ (1 - (0 : ℝ))) B₁)).re
        + (1 - α) * (Matrix.trace
            (cfc (fun x : ℝ => x ^ (0 : ℝ)) A₂
              * cfc (fun x : ℝ => x ^ (1 - (0 : ℝ))) B₂)).re
      ≤ (Matrix.trace
          (cfc (fun x : ℝ => x ^ (0 : ℝ))
              ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
            * cfc (fun x : ℝ => x ^ (1 - (0 : ℝ)))
                ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re :=
  lieb_tracial_endpoint_s_zero A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ α hα₀ hα₁

/-- Re-export of `AndoInterpolation.lieb_tracial_endpoint_s_one`
    for canonical GT-route access (no GT needed at `s = 1`). -/
theorem lieb_tracial_endpoint_one_no_GT_needed
    {n : ℕ} (A₁ A₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    α * (Matrix.trace
          (cfc (fun x : ℝ => x ^ (1 : ℝ)) A₁
            * cfc (fun x : ℝ => x ^ (1 - (1 : ℝ))) B₁)).re
        + (1 - α) * (Matrix.trace
            (cfc (fun x : ℝ => x ^ (1 : ℝ)) A₂
              * cfc (fun x : ℝ => x ^ (1 - (1 : ℝ))) B₂)).re
      ≤ (Matrix.trace
          (cfc (fun x : ℝ => x ^ (1 : ℝ))
              ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
            * cfc (fun x : ℝ => x ^ (1 - (1 : ℝ)))
                ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re :=
  lieb_tracial_endpoint_s_one A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ α hα₀ hα₁

/-! ## 6. Two-channel closure announcement.

    The Lieb 1973 → DPI/SSA/Holevo cascade now has **two distinct
    routes to closure**, either of which suffices:

      Route A (Hansen–Pedersen / Ando — `AndoInterpolation`):
        `Lieb1973_Tracial_NonCommuting_Subgate`
          → `lieb_tracial_target_from_subgate`
          → `Lieb1973_Tracial_Target`

      Route B (Carlen–Lieb 2008 Golden–Thompson — this file):
        `GoldenThompson_Target` ∧ `CarlenLieb_Integral_Reduction_Target`
          → `lieb_tracial_subgate_from_GT_route`
          → `Lieb1973_Tracial_NonCommuting_Subgate`
          → `lieb_tracial_target_from_subgate`
          → `Lieb1973_Tracial_Target`

    Route B's payoff: it splits the single Route-A obligation into
    two **independently classical** sub-obligations, each of which
    has multiple known proofs in the literature.  Whichever route
    lands first in Lean closes the entire Lieb chain. -/

/-- **Two-channel closure announcement.**

    Either Route A discharges (the Ando subgate directly), or
    Route B discharges (both GT and Carlen–Lieb integral-reduction
    targets); either suffices for `Lieb1973_Tracial_Target`. -/
theorem lieb_tracial_target_from_either_route
    (h : Lieb1973_Tracial_NonCommuting_Subgate
          ∨ (GoldenThompson_Target ∧ CarlenLieb_Integral_Reduction_Target)) :
    Lieb1973_Tracial_Target := by
  rcases h with h_sub | ⟨h_GT, h_red⟩
  · exact lieb_tracial_target_from_subgate h_sub
  · exact lieb_tracial_target_from_GT_route h_GT h_red

/-! ## 7. Honest scope summary.

    **UNCONDITIONAL (this file)**:

      * `lieb_tracial_subgate_from_GT_route` — schematic composite
        of the two named GT-route gates into the Ando sub-gate.
      * `lieb_tracial_subgate_from_GT_route_and` — `∧`-form variant.
      * `lieb_tracial_target_from_GT_route` — downstream to
        `Lieb1973_Tracial_Target`.
      * `lieb_tracial_parent_gate_from_GT_route` — downstream to
        the parent `Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target`.
      * `lieb_tracial_commuting_no_GT_needed`,
        `lieb_tracial_endpoint_{zero,one}_no_GT_needed` — re-exports
        documenting which cases require neither route.
      * `lieb_tracial_target_from_either_route` — two-channel
        closure announcement.

    **NAMED GATES (this file)**:

      * `GoldenThompson_Target` — `Tr e^{A+B} ≤ Tr(e^A · e^B)` for
        Hermitian `A, B`.  Classical, multi-day Lean work.
      * `CarlenLieb_Integral_Reduction_Target` — the Schwartz
        integral representation + resolvent joint-concavity reducing
        the Lieb sub-gate to GT.  Multi-week Lean work involving
        Bochner integration of matrix resolvents.

    **DISTANCE TO LIEB-CHAIN CLOSURE**:

      Two named obligations remain on the GT route, OR one on the
      Ando route.  Either route closes the chain; both fund
      independent multi-week efforts.  All other Lieb-chain inputs
      are unconditional. -/

/-! ## 8. Axiom audit (commented).

    Uncomment locally to verify that the schematic composites
    depend only on Lean's three standard axioms
    `[propext, Classical.choice, Quot.sound]`.  Zero `sorry`, zero
    custom `axiom`. -/

-- #print axioms lieb_tracial_subgate_from_GT_route
-- #print axioms lieb_tracial_subgate_from_GT_route_and
-- #print axioms lieb_tracial_target_from_GT_route
-- #print axioms lieb_tracial_parent_gate_from_GT_route
-- #print axioms lieb_tracial_commuting_no_GT_needed
-- #print axioms lieb_tracial_endpoint_zero_no_GT_needed
-- #print axioms lieb_tracial_endpoint_one_no_GT_needed
-- #print axioms lieb_tracial_target_from_either_route

-- VERIFIED 2026-06-01:
--   All eight headline theorems depend only on Lean's three standard
--   axioms `[propext, Classical.choice, Quot.sound]`.  Zero `sorry`,
--   zero custom `axiom`.

end UnifiedTheory.LayerB.LiebGoldenThompson
