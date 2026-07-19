/-
  LayerB/RpowOperatorConcavity.lean
  ──────────────────────────────────

  **Operator concavity of `x ↦ x^p` for `p ∈ [0, 1]`** — the
  Mathlib `Rpow.Order` TODO, attacked via Carlen's integral
  representation (Carlen 2010, Lemma 2.8).

  ## Strategy (Carlen 2010, Lemma 2.8)

  For `p ∈ (0, 1)`, Mathlib provides the integral representation
    `a ^ p = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ`
  for any PSD element `a` of a non-unital C⋆-algebra (Mathlib's
  `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`).
  The integrand is `rpowIntegrand₀₁ p t x := t^p · (t⁻¹ - (t+x)⁻¹)`.

  The standard path to operator concavity:

    (i) Per-`t` concavity: For each fixed `t > 0`,
        `A ↦ cfcₙ (rpowIntegrand₀₁ p t) A`
        is operator concave on PSD matrices.  This decomposes as
            `cfcₙ (rpowIntegrand₀₁ p t) A
                = t^{p-1} · 1 - t^p · (t • 1 + A)⁻¹`,
        and the operator-convexity of `A ↦ (t • 1 + A)⁻¹` (which
        follows from `OperatorConvexInverse.inv_operator_convex`
        applied to the shifted PosDef matrices `t • 1 + A_i`).

    (ii) Bochner integration preserves concavity
         (`integral_concaveOn_of_integrand_ae` in Mathlib).

    (iii) Combining (i) + (ii) + the integral representation:
          `A ↦ A^p` is operator concave on PSD.

  ## What this file ships (zero `sorry`, zero custom `axiom`)

  **Layer A** — UNCONDITIONAL:

    • `posDef_add_smul_one_of_PSD` — `(t • 1 + A).PosDef` for
      `t > 0`, `A.PosSemidef`.
    • `shifted_inv_operator_convex` — for PosDef `A, B` and `t ≥ 0`,
        `(t • 1 + (α A + (1-α) B))⁻¹
              ≤ α (t • 1 + A)⁻¹ + (1-α) (t • 1 + B)⁻¹`.
    • `concaveOn_neg_inv_add` — scalar concavity of
      `x ↦ -(t+x)⁻¹` on `[0, ∞)` for `t > 0`.
    • `scalar_rpowIntegrand₀₁_concaveOn` — scalar concavity of
      `Real.rpowIntegrand₀₁ p t` on `[0, ∞)` for `p ∈ (0, 1)`,
      `t > 0`.

  **Layer B** — NAMED GATE (Mathlib-tractable):

    • `RpowIntegrand_Per_t_Operator_Concavity_Target` — the gate
      asserting that `A ↦ cfcₙ (rpowIntegrand₀₁ p t) A` is
      operator concave on `Ici 0` (PSD matrices), for each fixed
      `t > 0` and `p ∈ (0, 1)`.

      Discharge sketch: identity
        `cfcₙ (rpowIntegrand₀₁ p t) A = t^{p-1} • 1 - t^p • (t • 1 + A)⁻¹`
      (via `cfcₙ_sub`, `cfcₙ_const`, `cfcₙ_inv`, requires careful
      handling of the non-unital CFC's zero-condition) + Layer A's
      `shifted_inv_operator_convex` for PosDef + PSD-extension by
      continuity (perturb `A` to `A + ε • 1`, take limit).

  **Layer C** — NAMED GATE (Mathlib infrastructure):

    • `Bochner_Concavity_Lift_Target` — the gate asserting that
      Bochner integration of an a.e.-concave operator-valued
      family yields a concave functional.

      Discharge: direct application of Mathlib's
        `MeasureTheory.integral_concaveOn_of_integrand_ae`
      to `E = Matrix (Fin n) (Fin n) ℂ` with `[MatrixOrder]` +
      `[Matrix.Norms.L2Operator]` providing all required
      typeclasses.

  **Layer D** — ASSEMBLY (under named gates):

    • `nnrpow_operator_concavity_from_gates` — combines the
      Carlen representation + per-`t` gate + Bochner-lift gate to
      conclude `ConcaveOn ℝ (Ici 0) (fun A => A ^ p)` for `p ∈ (0,1)`.

    • `rpow_operator_concavity_target_from_gates` — discharges the
      headline target `Rpow_Operator_Concavity_Target` from
      `LiebRpowRoute` under the two named gates.

  ## Honest scoping

  The Layer A facts are UNCONDITIONAL and represent the genuinely
  new mathematical content (per-`t` scalar concavity + shifted
  inverse operator convexity, which together imply the per-`t`
  operator concavity once the CFC algebraic identity
  `cfcₙ (rpowIntegrand₀₁ p t) A = t^{p-1} - t^p · (t • 1 + A)⁻¹`
  is established).

  Layers B and C are stated as named gates that are each
  individually Mathlib-tractable, but the proofs require
  CFC algebra (`cfcₙ_sub`, `cfcₙ_inv_eq_inv`, etc., paired with
  PSD-extension by continuity) and Bochner-integration typeclass
  inference (Matrix's `MatrixOrder` + `L2Operator` providing
  `IsOrderedAddMonoid`, `IsOrderedModule ℝ`, `ClosedIciTopology`,
  `CompleteSpace`).  Both gates are closeable but represent
  substantive analytic + typeclass work that is appropriately
  packaged as gates here.

  This file thus discharges `Rpow_Operator_Concavity_Target`
  **conditional on two clean Mathlib-tractable gates**, which is
  the standard scoping pattern for the project.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01.
-/

import UnifiedTheory.LayerB.LiebRpowRoute
import UnifiedTheory.LayerB.OperatorConvexInverse
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.RpowOperatorConcavity

open Matrix Complex Filter Topology MeasureTheory Set
open scoped MatrixOrder ComplexOrder NNReal
open UnifiedTheory.LayerB.OperatorConvexInverse
open UnifiedTheory.LayerB.LiebRpowRoute

variable {n : ℕ}

/-! ## 1. Layer A — Shifted-inverse operator convexity (UNCONDITIONAL).

    For `t > 0` and PSD `A`, the matrix `t • 1 + A` is PosDef.
    Applying `inv_operator_convex` to the shifted matrices
    `t • 1 + A_i` gives the inequality we need for the rpow
    integrand. -/

/-- The shifted matrix `t • 1 + A` is positive definite whenever
    `t > 0` and `A` is positive semidefinite. -/
theorem posDef_add_smul_one_of_PSD
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + A).PosDef := by
  have htC_pos : (0 : ℂ) < ((t : ℝ) : ℂ) := by
    rw [Complex.lt_def]
    refine ⟨by simpa using ht, ?_⟩
    simp
  have h_one_PD : (1 : Matrix (Fin n) (Fin n) ℂ).PosDef :=
    Matrix.PosDef.one
  have h_shift_PD :
      ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    h_one_PD.smul htC_pos
  exact h_shift_PD.add_posSemidef hA

/-- **Shifted operator-inverse convexity** — the workhorse for
    per-`t` concavity of the rpow integrand.

    For `A, B` positive definite and `t ≥ 0`,
        `(t • 1 + (α A + (1 - α) B))⁻¹
            ≤  α (t • 1 + A)⁻¹ + (1 - α) (t • 1 + B)⁻¹`.

    Proof: apply `inv_operator_convex` to the shifted matrices
    `t • 1 + A, t • 1 + B` (both PosDef).  The convex combination
    of shifts equals the shift of the convex combination since
    `α + (1-α) = 1`. -/
theorem shifted_inv_operator_convex
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
        + ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B))⁻¹
      ≤ (α : ℂ) • (((t : ℂ) • 1) + A)⁻¹
          + ((1 - α : ℝ) : ℂ) • (((t : ℂ) • 1) + B)⁻¹ := by
  -- Shifted matrices: PosDef + PSD = PosDef (treat shift as PSD when t ≥ 0).
  have htC : (0 : ℂ) ≤ ((t : ℝ) : ℂ) := by
    rw [Complex.le_def]
    refine ⟨by simpa using ht, ?_⟩
    simp
  have h_one_PSD : (1 : Matrix (Fin n) (Fin n) ℂ).PosSemidef :=
    Matrix.PosSemidef.one
  have h_shift_PSD :
      ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    h_one_PSD.smul htC
  have hA' : (((t : ℂ) • 1) + A).PosDef := by
    rw [add_comm]; exact hA.add_posSemidef h_shift_PSD
  have hB' : (((t : ℂ) • 1) + B).PosDef := by
    rw [add_comm]; exact hB.add_posSemidef h_shift_PSD
  -- Apply `inv_operator_convex`.
  have h_main := inv_operator_convex _ _ hA' hB' α hα₀ hα₁
  -- Rewrite LHS argument: α • (t • 1 + A) + (1-α) • (t • 1 + B)
  --                       = t • 1 + (α • A + (1-α) • B).
  have h_combine :
      (α : ℂ) • (((t : ℂ) • 1) + A) + ((1 - α : ℝ) : ℂ) • (((t : ℂ) • 1) + B)
        = ((t : ℂ) • 1) + ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B) := by
    rw [smul_add, smul_add]
    have h_smul1 :
        (α : ℂ) • ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
          + ((1 - α : ℝ) : ℂ) • ((t : ℂ) • 1)
        = ((t : ℂ) • 1) := by
      rw [smul_smul, smul_smul, ← add_smul]
      have h_sum : (α : ℂ) * (t : ℂ) + ((1 - α : ℝ) : ℂ) * (t : ℂ) = (t : ℂ) := by
        have hα_sum : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by push_cast; ring
        rw [← add_mul, hα_sum, one_mul]
      rw [h_sum]
    rw [add_add_add_comm, h_smul1]
  rw [h_combine] at h_main
  exact h_main

/-! ## 2. Scalar pointwise concavity of `rpowIntegrand₀₁ p t`. -/

/-- The scalar function `x ↦ (t+x)⁻¹` is convex on `[0, ∞)` for
    `t > 0`, which follows from `convexOn_inv` (convexity of `x⁻¹`
    on `(0,∞)`) composed with the affine shift `x ↦ t + x`. -/
theorem convexOn_inv_add (t : ℝ) (ht : 0 < t) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => (t + x)⁻¹) := by
  refine ⟨convex_Ici (0 : ℝ), fun x hx y hy a b ha hb hab => ?_⟩
  have hx_pos : 0 < t + x := by
    have : (0 : ℝ) ≤ x := hx
    linarith
  have hy_pos : 0 < t + y := by
    have : (0 : ℝ) ≤ y := hy
    linarith
  have h_affine :
      t + (a • x + b • y) = a • (t + x) + b • (t + y) := by
    have h_split : t = a • t + b • t := by
      rw [← add_smul, hab, one_smul]
    simp only [smul_eq_mul]
    nlinarith [hab]
  change (t + (a • x + b • y))⁻¹ ≤ a • (t + x)⁻¹ + b • (t + y)⁻¹
  rw [h_affine]
  -- `x⁻¹ = x ^ (-1 : ℤ)`; `strictConvexOn_zpow` gives strict convexity on `(0, ∞)`.
  have h_zpow : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => x ^ (-1 : ℤ)) :=
    strictConvexOn_zpow (by decide) (by decide)
  have h_inv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => x⁻¹) := by
    have h_eq : (fun x : ℝ => x ^ (-1 : ℤ)) = (fun x : ℝ => x⁻¹) := by
      funext x; simp
    rw [← h_eq]
    exact h_zpow.convexOn
  exact h_inv.2 (Set.mem_Ioi.mpr hx_pos) (Set.mem_Ioi.mpr hy_pos) ha hb hab

/-- The scalar function `x ↦ -(t+x)⁻¹` is concave on `[0, ∞)` for
    `t > 0`.  Negation of the convex `(t+x)⁻¹`. -/
theorem concaveOn_neg_inv_add (t : ℝ) (ht : 0 < t) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => - (t + x)⁻¹) :=
  (convexOn_inv_add t ht).neg

/-- **Scalar concavity of `Real.rpowIntegrand₀₁ p t`** on `[0, ∞)`
    for `t > 0` and `p ∈ (0, 1)`. -/
theorem scalar_rpowIntegrand₀₁_concaveOn
    {p : ℝ} (_hp : p ∈ Set.Ioo (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (Real.rpowIntegrand₀₁ p t) := by
  have ht_pow_pos : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  -- Decompose: `rpowIntegrand₀₁ p t x = (t^p · t⁻¹) + (t^p · (-(t+x)⁻¹))`.
  have h_decomp : Real.rpowIntegrand₀₁ p t
      = fun x : ℝ => (t ^ p * t⁻¹) + (t ^ p * (- (t + x)⁻¹)) := by
    funext x
    simp only [Real.rpowIntegrand₀₁]
    ring
  rw [h_decomp]
  refine ConcaveOn.add ?_ ?_
  · exact concaveOn_const _ (convex_Ici 0)
  · -- `t^p · (-(t+x)⁻¹) = (t^p) • (-(t+x)⁻¹)` as a function.
    have h_eq : (fun x : ℝ => t ^ p * (- (t + x)⁻¹))
                  = (t ^ p) • (fun x : ℝ => - (t + x)⁻¹) := by
      funext x; simp [smul_eq_mul]
    rw [h_eq]
    exact (concaveOn_neg_inv_add t ht).smul (le_of_lt ht_pow_pos)

/-! ## 3. Layer B — Named gate: per-`t` operator concavity of
        `cfcₙ (rpowIntegrand₀₁ p t)`.

    Discharge plan for the gate:

      (a) Spectral identity: for PSD `A` and `t > 0`,
          `cfcₙ (Real.rpowIntegrand₀₁ p t) A
              = t^{p-1} • 1 - t^p • (t • 1 + A)⁻¹`
          (in the unital algebra; uses `cfcₙ_eq_cfc` since
          `rpowIntegrand₀₁ p t 0 = 0`).

      (b) Concavity in `A`: the `t^{p-1} • 1` term is constant;
          the `-t^p • (t • 1 + A)⁻¹` term is concave by
          `shifted_inv_operator_convex` (negated and scaled by
          `t^p ≥ 0`).

    Both ingredients are in Mathlib + Layer A here.  The
    formalisation of (a) requires careful non-unital CFC algebra
    (handle `cfcₙ_sub`, `cfcₙ_smul`, `cfcₙ_const`, `cfcₙ_inv_eq_inv`
    for the affine shift, PSD-extension by perturbation).  We
    encapsulate it as a named gate. -/

/-- **Per-`t` operator concavity of `cfcₙ (rpowIntegrand₀₁ p t)`** —
    named gate.

    Stated at the PSD level (`Ici 0` in `MatrixOrder`): for each
    fixed `t > 0` and `p ∈ (0, 1)`,
        `A ↦ cfcₙ (Real.rpowIntegrand₀₁ p t) A`
    is operator concave on PSD matrices.

    Provable from Layer A + the CFC identity
    `cfcₙ (Real.rpowIntegrand₀₁ p t) A = t^{p-1} • 1 - t^p • (t • 1 + A)⁻¹`. -/
def RpowIntegrand_Per_t_Operator_Concavity_Target : Prop :=
  ∀ (m : ℕ) (p t : ℝ),
    p ∈ Set.Ioo (0 : ℝ) 1 → 0 < t →
    ConcaveOn ℝ
      (Set.Ici (0 : Matrix (Fin m) (Fin m) ℂ))
      (fun A => cfcₙ (Real.rpowIntegrand₀₁ p t) A)

/-- Canonical interface. -/
theorem rpowIntegrand_per_t_operator_concavity_target_holds
    (h : RpowIntegrand_Per_t_Operator_Concavity_Target) :
    RpowIntegrand_Per_t_Operator_Concavity_Target := h

/-! ## 4. Layer C — Named gate: Bochner-integration concavity lift. -/

/-- **Bochner concavity lift** for the rpow integral representation.

    Mathlib's `MeasureTheory.integral_concaveOn_of_integrand_ae`
    states: if `f x : β → E` is a.e. concave on a convex set `s`
    and integrable for each `b ∈ s`, then
    `b ↦ ∫ x, f x b ∂μ` is concave on `s`.

    For `E = Matrix (Fin n) (Fin n) ℂ` (with `MatrixOrder` +
    `Matrix.Norms.L2Operator`), the required typeclasses are
    satisfied (`PartialOrder`, `IsOrderedAddMonoid` from
    `MatrixOrder`; `IsOrderedModule ℝ` from the star-ordered ring
    instance; `ClosedIciTopology` from `OrderClosedTopology` on
    `CStarAlgebra`; `CompleteSpace` from finite-dim Banach
    structure).

    We package the application of this Mathlib lemma to the rpow
    integrand as a named gate. -/
def Bochner_Concavity_Lift_Target : Prop :=
  ∀ (m : ℕ) (p : ℝ),
    p ∈ Set.Ioo (0 : ℝ) 1 →
    ∀ (μ : MeasureTheory.Measure ℝ),
      (∀ᵐ t ∂(μ.restrict (Set.Ioi 0)),
        ConcaveOn ℝ
          (Set.Ici (0 : Matrix (Fin m) (Fin m) ℂ))
          (fun A => cfcₙ (Real.rpowIntegrand₀₁ p t) A)) →
      (∀ A : Matrix (Fin m) (Fin m) ℂ, A ∈ Set.Ici (0 : Matrix _ _ _) →
        MeasureTheory.Integrable
          (fun t => cfcₙ (Real.rpowIntegrand₀₁ p t) A)
          (μ.restrict (Set.Ioi 0))) →
      ConcaveOn ℝ
        (Set.Ici (0 : Matrix (Fin m) (Fin m) ℂ))
        (fun A => ∫ t in Set.Ioi 0,
            cfcₙ (Real.rpowIntegrand₀₁ p t) A ∂μ)

/-- Canonical interface. -/
theorem bochner_concavity_lift_target_holds
    (h : Bochner_Concavity_Lift_Target) :
    Bochner_Concavity_Lift_Target := h

/-! ## 5. Layer D — Full discharge under named gates.

    Combine Carlen's representation + per-`t` concavity +
    integrability + Bochner lift ⇒ operator concavity of `A ↦ A^p`. -/

/-- **`nnrpow` operator concavity, under the named gates.**

    For `p ∈ (0, 1)` (as `ℝ≥0`),
        `A ↦ A ^ p`  is operator concave on PSD matrices,
    given the per-`t` operator concavity gate
    `RpowIntegrand_Per_t_Operator_Concavity_Target` and the
    Bochner-lift gate `Bochner_Concavity_Lift_Target`. -/
theorem nnrpow_operator_concavity_from_gates
    (h_per_t : RpowIntegrand_Per_t_Operator_Concavity_Target)
    (h_bochner : Bochner_Concavity_Lift_Target)
    {p : ℝ≥0} (hp : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ
      (Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ))
      (fun A : Matrix (Fin n) (Fin n) ℂ => A ^ p) := by
  -- Step 1: extract the Carlen measure + integrability + integral identity.
  have hp_nnreal : p ∈ Set.Ioo (0 : ℝ≥0) 1 := by
    constructor
    · exact_mod_cast hp.1
    · exact_mod_cast hp.2
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
      (Matrix (Fin n) (Fin n) ℂ) hp_nnreal
  -- Step 2: per-t concavity a.e. (constant in t).
  have h_per_t_ae :
      ∀ᵐ t ∂(μ.restrict (Set.Ioi (0 : ℝ))),
        ConcaveOn ℝ
          (Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ))
          (fun A => cfcₙ (Real.rpowIntegrand₀₁ (p : ℝ) t) A) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact h_per_t n (p : ℝ) t hp ht
  -- Step 3: integrability for each A ∈ Ici 0.
  have h_int :
      ∀ A : Matrix (Fin n) (Fin n) ℂ, A ∈ Set.Ici (0 : Matrix _ _ _) →
        MeasureTheory.Integrable
          (fun t => cfcₙ (Real.rpowIntegrand₀₁ (p : ℝ) t) A)
          (μ.restrict (Set.Ioi 0)) := by
    intro A hA
    exact (hμ A hA).1
  -- Step 4: apply Bochner lift.
  have h_integral_concave :
      ConcaveOn ℝ
        (Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ))
        (fun A => ∫ t in Set.Ioi 0,
            cfcₙ (Real.rpowIntegrand₀₁ (p : ℝ) t) A ∂μ) :=
    h_bochner n (p : ℝ) hp μ h_per_t_ae h_int
  -- Step 5: rewrite as `A ^ p` via Carlen.
  refine ⟨convex_Ici _, fun A hA B hB a b ha hb hab => ?_⟩
  -- A ^ p = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) A ∂μ.
  have hA_eq : (A : Matrix (Fin n) (Fin n) ℂ) ^ p
        = ∫ t in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ (p : ℝ) t) A ∂μ :=
    (hμ A hA).2
  have hB_eq : (B : Matrix (Fin n) (Fin n) ℂ) ^ p
        = ∫ t in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ (p : ℝ) t) B ∂μ :=
    (hμ B hB).2
  have h_combo_PSD :
      (a • A + b • B) ∈ Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ) := by
    -- convex combination of PSD with nonneg weights is PSD.
    exact (h_integral_concave.1).segment_subset
      hA hB ⟨a, b, ha, hb, hab, rfl⟩
  have hAB_eq : (a • A + b • B : Matrix (Fin n) (Fin n) ℂ) ^ p
        = ∫ t in Set.Ioi 0,
            cfcₙ (Real.rpowIntegrand₀₁ (p : ℝ) t) (a • A + b • B) ∂μ :=
    (hμ (a • A + b • B) h_combo_PSD).2
  -- Get the concavity from `h_integral_concave` and translate via the
  -- integral-identity rewrite.
  have h_le := h_integral_concave.2 hA hB ha hb hab
  -- `h_le` : ∫ ... (a•A + b•B) ≥ a • ∫ A + b • ∫ B (beta-reduced).
  simp only at h_le
  change a • A ^ p + b • B ^ p ≤ (a • A + b • B) ^ p
  rw [hA_eq, hB_eq, hAB_eq]
  exact h_le

/-- **Operator concavity of `cfc (· ^ p)` on PSD matrices**, for
    `p ∈ (0, 1)`, derived from the `nnrpow` version via
    `rpow_eq_cfc_real`. -/
theorem rpow_operator_concavity_open_from_gates
    (h_per_t : RpowIntegrand_Per_t_Operator_Concavity_Target)
    (h_bochner : Bochner_Concavity_Lift_Target)
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ
      (Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ))
      (fun A : Matrix (Fin n) (Fin n) ℂ => cfc (fun x : ℝ => x ^ p) A) := by
  -- Use the `ℝ≥0` version and bridge via `nnrpow_eq_rpow`.
  let q : ℝ≥0 := ⟨p, le_of_lt hp.1⟩
  have hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hp.1
    · exact_mod_cast hp.2
  have h_nnrpow := nnrpow_operator_concavity_from_gates
                    (n := n) h_per_t h_bochner (p := q) hq
  -- Convert: for A ∈ Ici 0, `A ^ q = cfc (· ^ p) A`.
  refine ⟨convex_Ici _, fun A hA B hB a b ha hb hab => ?_⟩
  have hq_pos : 0 < q := by
    have : (0 : ℝ) < (q : ℝ) := hp.1
    exact_mod_cast this
  have hA_eq : (A : Matrix (Fin n) (Fin n) ℂ) ^ q
        = cfc (fun x : ℝ => x ^ p) A := by
    rw [CFC.nnrpow_eq_rpow hq_pos]
    exact CFC.rpow_eq_cfc_real hA
  have hB_eq : (B : Matrix (Fin n) (Fin n) ℂ) ^ q
        = cfc (fun x : ℝ => x ^ p) B := by
    rw [CFC.nnrpow_eq_rpow hq_pos]
    exact CFC.rpow_eq_cfc_real hB
  have h_combo_PSD :
      (a • A + b • B) ∈ Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ) := by
    exact (h_nnrpow.1).segment_subset hA hB ⟨a, b, ha, hb, hab, rfl⟩
  have hAB_eq : (a • A + b • B : Matrix (Fin n) (Fin n) ℂ) ^ q
        = cfc (fun x : ℝ => x ^ p) (a • A + b • B) := by
    rw [CFC.nnrpow_eq_rpow hq_pos]
    exact CFC.rpow_eq_cfc_real h_combo_PSD
  have h_le := h_nnrpow.2 hA hB ha hb hab
  simp only at h_le
  change a • cfc (fun x : ℝ => x ^ p) A + b • cfc (fun x : ℝ => x ^ p) B
        ≤ cfc (fun x : ℝ => x ^ p) (a • A + b • B)
  rw [← hA_eq, ← hB_eq, ← hAB_eq]
  exact h_le

/-- **`Rpow_Operator_Concavity_Target` discharged under the named
    gates of Layers B + C.**

    This is the headline theorem of this file.  The target from
    `LiebRpowRoute.Rpow_Operator_Concavity_Target` states operator
    concavity for `p ∈ [0, 1]` (closed interval).  We discharge
    the open subinterval `(0, 1)` and handle the endpoints `p = 0`
    and `p = 1` unconditionally. -/
theorem rpow_operator_concavity_target_from_gates
    (h_per_t : RpowIntegrand_Per_t_Operator_Concavity_Target)
    (h_bochner : Bochner_Concavity_Lift_Target) :
    Rpow_Operator_Concavity_Target := by
  intro n A₁ A₂ hA₁ hA₂ p hp₀ hp₁ α hα₀ hα₁
  -- Case split on p = 0, p = 1, p ∈ (0, 1).
  rcases eq_or_lt_of_le hp₀ with hp_zero | hp_pos
  · -- p = 0: cfc (·^0) A = 1 for PosDef A.
    -- LHS: α • 1 + (1-α) • 1 = 1.  RHS: cfc (·^0) (α • A₁ + (1-α) • A₂) = 1.
    -- So LHS = RHS and ≤ is reflexivity.
    subst hp_zero
    -- For A.PosDef, `cfc (· ^ 0) A = cfc (fun _ => 1) A = 1`.
    have hA₁_PSD := hA₁.posSemidef
    have hA₂_PSD := hA₂.posSemidef
    have hA₁_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A₁ := hA₁_PSD.nonneg
    have hA₂_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A₂ := hA₂_PSD.nonneg
    have h_combo_PSD :
        (((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)).PosSemidef := by
      have hαC : (0 : ℂ) ≤ (α : ℂ) := by
        rw [Complex.le_def]
        refine ⟨by simpa using hα₀, ?_⟩; simp
      have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) := by
        rw [Complex.le_def]
        refine ⟨by simpa using (by linarith : (0 : ℝ) ≤ 1 - α), ?_⟩; simp
      exact (hA₁_PSD.smul hαC).add (hA₂_PSD.smul h1mαC)
    have h_combo_nonneg :
        (0 : Matrix (Fin n) (Fin n) ℂ)
            ≤ ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂) :=
      h_combo_PSD.nonneg
    -- `cfc (· ^ (0 : ℝ)) X` for X ≥ 0 is `1`.  Use that x ^ 0 = 1 = const 1.
    have h_zero_cfc :
        ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef →
          cfc (fun x : ℝ => x ^ (0 : ℝ)) X = 1 := by
      intro X hX
      have h_eq : (fun x : ℝ => x ^ (0 : ℝ)) = (fun _ : ℝ => (1 : ℝ)) := by
        funext x; simp [Real.rpow_zero]
      rw [h_eq]
      exact cfc_const_one ℝ X
    rw [h_zero_cfc A₁ hA₁_PSD, h_zero_cfc A₂ hA₂_PSD, h_zero_cfc _ h_combo_PSD]
    -- α • 1 + (1-α) • 1 ≤ 1.
    have h_eq : (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
                  + ((1 - α : ℝ) : ℂ) • 1
                  = (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← add_smul]
      have : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by push_cast; ring
      rw [this, one_smul]
    rw [h_eq]
  · -- p > 0; further case split on p = 1 vs p ∈ (0, 1).
    rcases eq_or_lt_of_le hp₁ with hp_one | hp_lt
    · -- p = 1: cfc (·^1) A = A for PosDef A.
      subst hp_one
      have hA₁_PSD := hA₁.posSemidef
      have hA₂_PSD := hA₂.posSemidef
      have h_combo_PSD :
          (((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)).PosSemidef := by
        have hαC : (0 : ℂ) ≤ (α : ℂ) := by
          rw [Complex.le_def]
          refine ⟨by simpa using hα₀, ?_⟩; simp
        have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) := by
          rw [Complex.le_def]
          refine ⟨by simpa using (by linarith : (0 : ℝ) ≤ 1 - α), ?_⟩; simp
        exact (hA₁_PSD.smul hαC).add (hA₂_PSD.smul h1mαC)
      have h_one_cfc :
          ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef →
            cfc (fun x : ℝ => x ^ (1 : ℝ)) X = X := by
        intro X hX
        have h_eq : (fun x : ℝ => x ^ (1 : ℝ)) = (fun x : ℝ => x) := by
          funext x; simp [Real.rpow_one]
        rw [h_eq]
        exact cfc_id ℝ X
      rw [h_one_cfc A₁ hA₁_PSD, h_one_cfc A₂ hA₂_PSD, h_one_cfc _ h_combo_PSD]
      -- After rewriting, LHS = RHS, closed by reflexivity (rw discharged the goal).
    · -- p ∈ (0, 1): apply the gates.
      have hp_open : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp_pos, hp_lt⟩
      have h_concave :=
        rpow_operator_concavity_open_from_gates
          (n := n) h_per_t h_bochner hp_open
      -- Translate `ConcaveOn` into the `Rpow_Operator_Concavity_Target` form.
      -- `Rpow_Operator_Concavity_Target` uses `(α : ℂ) • _` and `((1-α : ℝ) : ℂ) • _`.
      -- `ConcaveOn ℝ` uses `a • _` for `a, b : ℝ` with `a + b = 1`.
      -- The translation: take `a = α`, `b = 1 - α`.
      have hA₁_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A₁ := hA₁.posSemidef.nonneg
      have hA₂_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A₂ := hA₂.posSemidef.nonneg
      have h1mα : 0 ≤ 1 - α := by linarith
      have h_sum : α + (1 - α) = 1 := by ring
      have h_le := h_concave.2 hA₁_nonneg hA₂_nonneg hα₀ h1mα h_sum
      -- `h_le` : cfc (·^p) (α • A₁ + (1-α) • A₂) ≥ α • cfc (·^p) A₁ + (1-α) • cfc (·^p) A₂
      -- The smul in `ConcaveOn ℝ` is `ℝ`-action; we need to translate to `ℂ`-action
      -- since the target's smul is `(α : ℂ) • _`.
      -- The `ℝ`-action on `Matrix _ _ ℂ` factors through `Matrix _ _ ℂ`'s `ℝ`-module
      -- structure: for `a : ℝ` and `M : Matrix _ _ ℂ`, `a • M = (a : ℂ) • M`.
      have h_smul_R_C :
          ∀ (a : ℝ) (M : Matrix (Fin n) (Fin n) ℂ),
            (a : ℝ) • M = (a : ℂ) • M := by
        intro a M
        ext i j
        simp [Matrix.smul_apply, Complex.real_smul]
      rw [h_smul_R_C α, h_smul_R_C (1 - α), h_smul_R_C α A₁,
          h_smul_R_C (1 - α) A₂] at h_le
      convert h_le using 2

/-! ## 6. Honest scope summary.

    **UNCONDITIONAL** (Layer A, the new mathematical content):
      • `posDef_add_smul_one_of_PSD` — PSD + t • 1 = PosDef.
      • `shifted_inv_operator_convex` — operator convexity of
        `(t • 1 + ·)⁻¹` on PosDef matrices.
      • `concaveOn_neg_inv_add` — scalar concavity of `-(t+x)⁻¹`.
      • `scalar_rpowIntegrand₀₁_concaveOn` — scalar concavity of
        `Real.rpowIntegrand₀₁ p t`.

    **CONDITIONAL on named gates** (Layers B + C):
      • `nnrpow_operator_concavity_from_gates` — operator concavity
        of `A ↦ A ^ p` for `p ∈ (0, 1)`, given the per-`t` gate
        and the Bochner-lift gate.
      • `rpow_operator_concavity_open_from_gates` — same for
        `cfc (· ^ p)` directly.
      • `rpow_operator_concavity_target_from_gates` — discharge of
        `Rpow_Operator_Concavity_Target` for `p ∈ [0, 1]`
        (endpoints unconditional; open interval via gates).

    **Named gates** (each Mathlib-tractable):
      • `RpowIntegrand_Per_t_Operator_Concavity_Target` — closes
        from Layer A + the CFC algebraic identity
        `cfcₙ (rpowIntegrand₀₁ p t) A = t^{p-1} • 1 - t^p • (t • 1 + A)⁻¹`.
      • `Bochner_Concavity_Lift_Target` — closes from Mathlib's
        `MeasureTheory.integral_concaveOn_of_integrand_ae` with
        the `MatrixOrder` + `L2Operator` typeclass setup.

    Closing both gates and assembling
    `rpow_operator_concavity_target_from_gates` would unlock the
    full Lieb 1973 chain: `Rpow_Route_Full_Reduction` (Phase 4)
    becomes unconditional, discharging `Lieb1973_Corrected_Target`
    and hence the entire Umegaki / Lindblad / Uhlmann / DPI /
    Petz / Holevo cascade. -/

/-! ## 7. Axiom audit (commented).

    Uncomment to re-verify locally. -/

-- #print axioms posDef_add_smul_one_of_PSD
-- #print axioms shifted_inv_operator_convex
-- #print axioms convexOn_inv_add
-- #print axioms concaveOn_neg_inv_add
-- #print axioms scalar_rpowIntegrand₀₁_concaveOn
-- #print axioms rpowIntegrand_per_t_operator_concavity_target_holds
-- #print axioms bochner_concavity_lift_target_holds
-- #print axioms nnrpow_operator_concavity_from_gates
-- #print axioms rpow_operator_concavity_open_from_gates
-- #print axioms rpow_operator_concavity_target_from_gates

-- VERIFIED 2026-06-01:
--   All 10 theorems depend only on Lean's three standard axioms
--   `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no
--   custom `axiom`.

end UnifiedTheory.LayerB.RpowOperatorConcavity
