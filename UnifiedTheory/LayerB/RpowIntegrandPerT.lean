/-
  LayerB/RpowIntegrandPerT.lean
  ─────────────────────────────

  **Discharge of `RpowIntegrand_Per_t_Operator_Concavity_Target`**
  — the per-`t` operator-concavity gate of `RpowOperatorConcavity`,
  closed unconditionally for `Matrix (Fin n) (Fin n) ℂ`.

  ## The gate (recap)

  For each fixed `t > 0` and `p ∈ (0, 1)`, the map
      `A ↦ cfcₙ (Real.rpowIntegrand₀₁ p t) A`
  is operator concave on `Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ)`
  (PSD matrices, in `MatrixOrder`).

  ## The proof

  Two steps.

  **(A) CFC algebraic identity.**  For `A.PosSemidef` and `t > 0`,
        `cfcₙ (Real.rpowIntegrand₀₁ p t) A
            = (t^(p-1) : ℂ) • 1
                - (t^p : ℂ) • (((t : ℂ) • 1) + A)⁻¹.`

  This collapses the rpow-integrand into a constant minus a scaled
  shifted-inverse.  The proof uses:
    • `cfcₙ_eq_cfc` (the integrand vanishes at `0`, so the
      non-unital and unital CFCs agree);
    • `cfc_sub`, `cfc_const`, `cfc_smul`, `cfc_add_const`, `cfc_id'`,
      `cfc_inv_id` (unital CFC algebra);
    • `posDef_add_smul_one_of_PSD` and `Matrix.PosDef.isUnit`
      (the shifted matrix is invertible).

  **(B) Operator concavity.**  Apply the identity to PSD `A`, `B`
  and reduce concavity to operator convexity of `(t • 1 + ·)⁻¹`
  on PSD matrices, which is exactly `shifted_inv_operator_convex`
  with the shifted matrices kept PosDef.

  ## What this file ships

  • `cfc_rpowIntegrand₀₁_eq_shift_inv` — the CFC algebraic
    identity, **unconditional**.
  • `rpowIntegrand_per_t_operator_concave` — per-`t` operator
    concavity for fixed `t > 0`, `p ∈ (0, 1)`, **unconditional**.
  • `rpowIntegrand_per_t_concavity_target_holds` — the
    discharged `Prop`.

  ## Consequence for the rpow → Lieb chain

  Combined with `OperatorConvexInverse.inv_operator_convex`
  (already unconditional) and `Bochner_Concavity_Lift_Target`
  (Layer C of `RpowOperatorConcavity` — still a named gate),
  this collapses the rpow side of the Lieb chain to a single
  remaining named gate (the Bochner-integration lift, which is
  pure measure-theory plumbing in Mathlib).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01.
-/

import UnifiedTheory.LayerB.RpowOperatorConcavity
import UnifiedTheory.LayerB.OperatorConvexInverse
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.RpowIntegrandPerT

open Matrix Complex Filter Topology MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.OperatorConvexInverse
open UnifiedTheory.LayerB.RpowOperatorConcavity

variable {n : ℕ}

/-! ## 0. Small bridging lemmas (ℝ/ℂ smul, algebraMap on matrices). -/

/-- Real scalar action on a complex matrix factors through the
    complex coercion. -/
private lemma smul_R_C (a : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (a : ℝ) • M = (a : ℂ) • M := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- `algebraMap ℝ (Matrix _ _ ℂ) r = (r : ℂ) • 1`. -/
private lemma algebraMap_real_matrix_eq_smul_one (r : ℝ) :
    algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) r
      = (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact smul_R_C r 1

/-- For PSD `A : Matrix (Fin n) (Fin n) ℂ`, every spectral value
    `x ∈ spectrum ℝ A` is `≥ 0`. -/
private lemma spectrum_real_nonneg_of_PSD
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    ∀ x ∈ spectrum ℝ A, (0 : ℝ) ≤ x := by
  have h_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A := hA.nonneg
  intro x hx
  exact spectrum_nonneg_of_nonneg h_nonneg hx

/-! ## 1. Setup: shifted matrix `t • 1 + A` is PosDef, invertible.

    We re-export Layer A's `posDef_add_smul_one_of_PSD` for ergonomic
    use here. -/

/-- The shifted matrix `(t : ℂ) • 1 + A` for `t > 0` and `A.PosSemidef`
    is positive definite — re-export of Layer A. -/
private theorem shifted_PSD_is_PosDef
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + A).PosDef :=
  posDef_add_smul_one_of_PSD A hA ht

/-- The shifted matrix is invertible (as a `Units` element of the
    matrix ring). -/
private theorem shifted_isUnit
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    IsUnit (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + A) :=
  (shifted_PSD_is_PosDef A hA ht).isUnit

/-! ## 2. The CFC algebraic identity (Step A).

    The proof breaks the integrand into a constant + an inverse term,
    handling each via unital-CFC algebra (`cfc_const`, `cfc_smul`,
    `cfc_sub`, `cfc_inv` on the affine shift `x ↦ t + x`).

    Mathlib's non-unital and unital CFCs agree here because the
    integrand vanishes at `0`. -/

/-- Helper: unital `cfc` of the affine shift `x ↦ t + x` equals
    `(t : ℂ) • 1 + A`. -/
private lemma cfc_affine_shift
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (t : ℝ) :
    cfc (fun x : ℝ => t + x) A
      = ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + A := by
  -- `cfc (fun x => t + x) A = algebraMap ℝ _ t + cfc id A`.
  have hA_SA : IsSelfAdjoint A := hA.isHermitian.isSelfAdjoint
  rw [cfc_const_add (R := ℝ) (r := t) (f := fun x : ℝ => x) (a := A)
        (hf := continuousOn_id) (ha := hA_SA)]
  rw [cfc_id' ℝ A, algebraMap_real_matrix_eq_smul_one]

/-- Helper: continuity of `(t + ·)⁻¹` on `spectrum ℝ A` for PSD `A`
    and `t > 0`. -/
private lemma continuousOn_inv_shift
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun x : ℝ => (t + x)⁻¹) (spectrum ℝ A) := by
  refine ContinuousOn.inv₀ (by fun_prop) ?_
  intro x hx
  have hx_nonneg : 0 ≤ x := spectrum_real_nonneg_of_PSD hA x hx
  linarith

/-- Helper: continuity of `(t + ·)⁻¹` on `Ici 0` for `t > 0`. -/
private lemma continuousOn_inv_shift_Ici
    {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun x : ℝ => (t + x)⁻¹) (Set.Ici (0 : ℝ)) := by
  refine ContinuousOn.inv₀ (by fun_prop) ?_
  intro x hx
  have hx_nonneg : 0 ≤ x := hx
  linarith

/-- **CFC identity for the affine inverse**:
    `cfc (fun x => (t + x)⁻¹) A = ((t • 1 + A))⁻¹`,
    for `A.PosSemidef`, `t > 0`. -/
private theorem cfc_affine_inv
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    cfc (fun x : ℝ => (t + x)⁻¹) A
      = (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + A)⁻¹ := by
  have hA_SA : IsSelfAdjoint A := hA.isHermitian.isSelfAdjoint
  -- The function `f x = t + x` is nonzero on `spectrum ℝ A` since `t > 0`.
  have h_nonzero : ∀ x ∈ spectrum ℝ A, (t + x) ≠ 0 := by
    intro x hx
    have hx_nonneg : 0 ≤ x := spectrum_real_nonneg_of_PSD hA x hx
    linarith
  have h_cont : ContinuousOn (fun x : ℝ => t + x) (spectrum ℝ A) := by fun_prop
  -- `cfc (fun x => (t + x)⁻¹) A = Ring.inverse (cfc (fun x => t + x) A)`.
  rw [show (fun x : ℝ => (t + x)⁻¹) = (fun x : ℝ => ((fun y => t + y) x)⁻¹) from rfl,
      cfc_inv (fun y : ℝ => t + y) A h_nonzero h_cont hA_SA]
  -- Now `cfc (fun x => t + x) A = (t • 1) + A`.
  rw [cfc_affine_shift A hA t]
  -- `Ring.inverse X = X⁻¹` for matrices: `Matrix.nonsing_inv_eq_ringInverse` (symm).
  exact (Matrix.nonsing_inv_eq_ringInverse
    (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + A)).symm

/-- **The CFC identity for the rpow integrand** (unital CFC form).

    For `A.PosSemidef`, `t > 0`, `p ∈ ℝ` (no constraint on `p`):
        `cfc (Real.rpowIntegrand₀₁ p t) A
            = (t^(p-1) : ℂ) • 1
                - (t^p : ℂ) • (((t : ℂ) • 1) + A)⁻¹.`

    Both sides use the **unital** `cfc`.  This is the unconditional
    algebraic identity. -/
theorem cfc_rpowIntegrand₀₁_eq_shift_inv_unital
    (p : ℝ) {t : ℝ} (ht : 0 < t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    cfc (Real.rpowIntegrand₀₁ p t) A
      = (((t ^ (p - 1) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
          - (((t ^ p : ℝ) : ℂ) • (((t : ℂ) • 1) + A)⁻¹) := by
  have hA_SA : IsSelfAdjoint A := hA.isHermitian.isSelfAdjoint
  -- Pointwise: `rpowIntegrand₀₁ p t x = t^p * t⁻¹ - t^p * (t + x)⁻¹`.
  -- We use `t^p * t⁻¹ = t^(p-1)` and rewrite as
  --   `(fun x => t^(p-1) - t^p * (t + x)⁻¹)`.
  have h_decomp :
      Real.rpowIntegrand₀₁ p t
        = fun x : ℝ => t ^ (p - 1) - t ^ p * (t + x)⁻¹ := by
    funext x
    unfold Real.rpowIntegrand₀₁
    have h_split : t ^ p * (t⁻¹ - (t + x)⁻¹)
                    = t ^ p * t⁻¹ - t ^ p * (t + x)⁻¹ := by ring
    rw [h_split]
    have h_pow : t ^ p * t⁻¹ = t ^ (p - 1) := by
      rw [Real.rpow_sub_one ht.ne' p]
      field_simp
    rw [h_pow]
  rw [h_decomp]
  -- Now compute the cfc.
  have h_cont_inv :
      ContinuousOn (fun x : ℝ => (t + x)⁻¹) (spectrum ℝ A) :=
    continuousOn_inv_shift hA ht
  have h_cont_mul :
      ContinuousOn (fun x : ℝ => t ^ p * (t + x)⁻¹) (spectrum ℝ A) := by
    exact ContinuousOn.const_smul (M := ℝ) h_cont_inv (t ^ p)
      |>.congr (fun x _ => by simp [smul_eq_mul])
  have h_cont_const :
      ContinuousOn (fun _ : ℝ => t ^ (p - 1)) (spectrum ℝ A) :=
    continuousOn_const
  -- cfc of a subtraction.
  rw [show (fun x : ℝ => t ^ (p - 1) - t ^ p * (t + x)⁻¹)
        = fun x : ℝ => (fun _ : ℝ => t ^ (p - 1)) x - (fun y : ℝ => t ^ p * (t + y)⁻¹) x
      from rfl]
  rw [cfc_sub (R := ℝ) (fun _ : ℝ => t ^ (p - 1)) (fun y : ℝ => t ^ p * (t + y)⁻¹) A
        h_cont_const h_cont_mul]
  -- cfc of the constant `t^(p-1)`.
  rw [cfc_const (R := ℝ) (t ^ (p - 1)) A hA_SA]
  rw [algebraMap_real_matrix_eq_smul_one]
  -- cfc of `t^p * (t+x)⁻¹` = `t^p • cfc ((t+·)⁻¹) A`.
  have h_scale :
      cfc (fun x : ℝ => t ^ p * (t + x)⁻¹) A
        = (t ^ p : ℝ) • cfc (fun x : ℝ => (t + x)⁻¹) A := by
    rw [show (fun x : ℝ => t ^ p * (t + x)⁻¹)
            = fun x : ℝ => (t ^ p : ℝ) • (t + x)⁻¹ from by
          funext x; simp [smul_eq_mul]]
    exact cfc_smul (R := ℝ) (S := ℝ) (t ^ p) (fun x => (t + x)⁻¹) A
      (hf := h_cont_inv)
  rw [h_scale, cfc_affine_inv A hA ht]
  -- Final: ℝ-smul on Matrix ℂ → ℂ-smul.
  rw [smul_R_C (t ^ p)]

/-- **The CFC identity for the rpow integrand** (non-unital CFC form).

    For `A.PosSemidef`, `t > 0`:
        `cfcₙ (Real.rpowIntegrand₀₁ p t) A
            = (t^(p-1) : ℂ) • 1
                - (t^p : ℂ) • (((t : ℂ) • 1) + A)⁻¹.`

    Follows from the unital form via `cfcₙ_eq_cfc`, using the fact
    that `rpowIntegrand₀₁ p t 0 = 0`. -/
theorem cfc_rpowIntegrand₀₁_eq_shift_inv
    (p : ℝ) {t : ℝ} (ht : 0 < t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    cfcₙ (Real.rpowIntegrand₀₁ p t) A
      = (((t ^ (p - 1) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
          - (((t ^ p : ℝ) : ℂ) • (((t : ℂ) • 1) + A)⁻¹) := by
  have h_PSD : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A := hA.nonneg
  -- Continuity of the integrand on the spectrum.
  have h_cont : ContinuousOn (Real.rpowIntegrand₀₁ p t) (quasispectrum ℝ A) := by
    -- quasispectrum = spectrum ∪ {0} for matrices; the integrand is continuous on Ici 0 ⊇ that.
    have h_sub : quasispectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      exact quasispectrum_nonneg_of_nonneg A h_PSD x hx
    -- For p ∈ (0,1) and t > 0, the integrand is continuous on Ici 0; but we want
    -- it without the p ∈ (0,1) constraint.  Use the explicit pointwise form:
    --   `rpowIntegrand₀₁ p t x = t^(p-1) - t^p * (t+x)⁻¹`,
    -- which is continuous in `x` on `Ici 0` since `t > 0`.
    have h_eq :
        (Set.Ici (0 : ℝ)).EqOn (Real.rpowIntegrand₀₁ p t)
          (fun x : ℝ => t ^ (p - 1) - t ^ p * (t + x)⁻¹) := by
      intro x _
      unfold Real.rpowIntegrand₀₁
      have h_split : t ^ p * (t⁻¹ - (t + x)⁻¹)
                      = t ^ p * t⁻¹ - t ^ p * (t + x)⁻¹ := by ring
      rw [h_split]
      have h_pow : t ^ p * t⁻¹ = t ^ (p - 1) := by
        rw [Real.rpow_sub_one ht.ne' p]
        field_simp
      rw [h_pow]
    have h_cont_alt :
        ContinuousOn
          (fun x : ℝ => t ^ (p - 1) - t ^ p * (t + x)⁻¹) (Set.Ici (0 : ℝ)) := by
      refine ContinuousOn.sub continuousOn_const ?_
      refine ContinuousOn.mul continuousOn_const ?_
      exact continuousOn_inv_shift_Ici ht
    have h_cont_on_Ici :
        ContinuousOn (Real.rpowIntegrand₀₁ p t) (Set.Ici (0 : ℝ)) :=
      h_cont_alt.congr (fun x hx => (h_eq hx))
    exact h_cont_on_Ici.mono h_sub
  have h_zero : Real.rpowIntegrand₀₁ p t 0 = 0 := by
    simp [Real.rpowIntegrand₀₁]
  rw [cfcₙ_eq_cfc (hf := h_cont) (hf0 := h_zero)]
  exact cfc_rpowIntegrand₀₁_eq_shift_inv_unital (n := n) p ht A hA

/-! ## 3. PSD-level operator convexity of the shifted inverse.

    `shifted_inv_operator_convex` (Layer A of `RpowOperatorConcavity`)
    only takes `PosDef A, B`.  We need the PSD version since the
    rpow gate quantifies over `0 ≤ A` and `0 ≤ B`.

    The proof: PSD + (t • 1) = PosDef, so we apply
    `inv_operator_convex` directly to the shifted matrices. -/

/-- **Shifted-inverse operator convexity at the PSD level** —
    extension of `shifted_inv_operator_convex` from PosDef to PSD.

    For PSD `A, B` and `t > 0`,
        `(t • 1 + (α A + (1 - α) B))⁻¹
            ≤  α (t • 1 + A)⁻¹ + (1 - α) (t • 1 + B)⁻¹`. -/
theorem shifted_inv_operator_convex_PSD
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
        + ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B))⁻¹
      ≤ (α : ℂ) • (((t : ℂ) • 1) + A)⁻¹
          + ((1 - α : ℝ) : ℂ) • (((t : ℂ) • 1) + B)⁻¹ := by
  -- The shifted matrices are PosDef.
  have hA_shift : (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + A).PosDef :=
    posDef_add_smul_one_of_PSD A hA ht
  have hB_shift : (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + B).PosDef :=
    posDef_add_smul_one_of_PSD B hB ht
  -- Apply `inv_operator_convex` to the shifted matrices.
  have h_main :=
    inv_operator_convex (((t : ℂ) • 1) + A) (((t : ℂ) • 1) + B)
      hA_shift hB_shift α hα₀ hα₁
  -- Rewrite α (t • 1 + A) + (1-α) (t • 1 + B) = (t • 1) + (α A + (1-α) B).
  have h_combine :
      (α : ℂ) • (((t : ℂ) • 1) + A) + ((1 - α : ℝ) : ℂ) • (((t : ℂ) • 1) + B)
        = ((t : ℂ) • 1) + ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B) := by
    rw [smul_add, smul_add]
    have h_smul1 :
        (α : ℂ) • ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
          + ((1 - α : ℝ) : ℂ) • ((t : ℂ) • 1)
        = ((t : ℂ) • 1) := by
      rw [smul_smul, smul_smul, ← add_smul]
      have h_sum :
          (α : ℂ) * (t : ℂ) + ((1 - α : ℝ) : ℂ) * (t : ℂ) = (t : ℂ) := by
        have hα_sum : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by push_cast; ring
        rw [← add_mul, hα_sum, one_mul]
      rw [h_sum]
    rw [add_add_add_comm, h_smul1]
  rw [h_combine] at h_main
  exact h_main

/-! ## 4. Per-`t` operator concavity (Step B).

    With the CFC identity in hand, concavity of
    `A ↦ cfcₙ (rpowIntegrand₀₁ p t) A` reduces to concavity of
    `A ↦ - t^p • (t • 1 + A)⁻¹` (the constant term doesn't affect
    concavity), which is `t^p ≥ 0` times convexity of
    `(t • 1 + A)⁻¹` (i.e., `shifted_inv_operator_convex_PSD`),
    flipped by the negation. -/

/-- **Per-`t` operator concavity** of `cfcₙ (Real.rpowIntegrand₀₁ p t)`
    on PSD matrices, for each fixed `t > 0` and `p ∈ ℝ`.

    Stated as the pointwise inequality for the convex-combination form
    expected by `ConcaveOn`. -/
theorem rpowIntegrand_per_t_concavity_ineq
    (p : ℝ) {t : ℝ} (ht : 0 < t)
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (α : ℝ) • cfcₙ (Real.rpowIntegrand₀₁ p t) A
        + ((1 - α : ℝ)) • cfcₙ (Real.rpowIntegrand₀₁ p t) B
      ≤ cfcₙ (Real.rpowIntegrand₀₁ p t)
          ((α : ℝ) • A + ((1 - α : ℝ)) • B) := by
  -- Hypothesis assembly.
  have h1mα : (0 : ℝ) ≤ 1 - α := by linarith
  have h_PSD_combo :
      ((α : ℝ) • A + ((1 - α : ℝ)) • B).PosSemidef := by
    -- ℝ-smul on Matrix ℂ = ℂ-smul under coercion.
    rw [smul_R_C α A, smul_R_C (1 - α) B]
    have hαC : (0 : ℂ) ≤ (α : ℂ) := by
      rw [Complex.le_def]; refine ⟨by simpa using hα₀, ?_⟩; simp
    have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) := by
      rw [Complex.le_def]; refine ⟨by simpa using h1mα, ?_⟩; simp
    exact (hA.smul hαC).add (hB.smul h1mαC)
  -- Use the CFC identity on each side.
  rw [cfc_rpowIntegrand₀₁_eq_shift_inv (n := n) p ht A hA,
      cfc_rpowIntegrand₀₁_eq_shift_inv (n := n) p ht B hB]
  -- Also for the convex combination — but the combo is in ℝ-smul form, need to
  -- convert to ℂ-smul to apply the CFC identity.
  have h_combo_form :
      ((α : ℝ) • A + ((1 - α : ℝ)) • B : Matrix (Fin n) (Fin n) ℂ)
        = ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B) := by
    rw [smul_R_C α A, smul_R_C (1 - α) B]
  rw [h_combo_form]
  rw [cfc_rpowIntegrand₀₁_eq_shift_inv (n := n) p ht
        ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B)
        (by rw [← h_combo_form]; exact h_PSD_combo)]
  -- Now everything is in terms of `t^(p-1) • 1 - t^p • (t•1 + ·)⁻¹`.
  -- The concavity inequality becomes:
  --   α · (C - K · X) + (1-α) · (C - K · Y) ≤ C - K · Z,
  -- where C = t^(p-1) • 1, K = t^p ≥ 0, X = (t•1+A)⁻¹, Y = (t•1+B)⁻¹,
  -- Z = (t•1 + (αA+(1-α)B))⁻¹.
  -- Equivalently: α • X + (1-α) • Y ≥ Z  (after dividing by K and flipping).
  -- That's exactly `shifted_inv_operator_convex_PSD`.
  have h_inv_conv :=
    shifted_inv_operator_convex_PSD A B hA hB ht α hα₀ hα₁
  -- Let's denote:
  --   X := ((t : ℂ) • 1 + A)⁻¹, Y := ((t : ℂ) • 1 + B)⁻¹,
  --   Z := ((t : ℂ) • 1 + ((α : ℂ) • A + ((1-α : ℝ) : ℂ) • B))⁻¹.
  set X := (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + A)⁻¹ with hX_def
  set Y := (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) + B)⁻¹ with hY_def
  set Z := (((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
              + ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B))⁻¹ with hZ_def
  -- `h_inv_conv : Z ≤ (α : ℂ) • X + ((1-α : ℝ) : ℂ) • Y`.
  -- Rewrite goal in terms of X, Y, Z.
  change (α : ℝ) • (((t ^ (p - 1) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
                    - ((t ^ p : ℝ) : ℂ) • X)
      + ((1 - α : ℝ)) • (((t ^ (p - 1) : ℝ) : ℂ) • 1
                          - ((t ^ p : ℝ) : ℂ) • Y)
      ≤ ((t ^ (p - 1) : ℝ) : ℂ) • 1 - ((t ^ p : ℝ) : ℂ) • Z
  -- Step 1: Split LHS as `α • C - α • (t^p • X) + (1-α) • C - (1-α) • (t^p • Y)`.
  --         Then combine `α • C + (1-α) • C = C` and rearrange to
  --         `C - (α • (t^p • X) + (1-α) • (t^p • Y)) ≤ C - t^p • Z`.
  --         Subtracting `C` and negating: t^p • Z ≤ α • (t^p • X) + (1-α) • (t^p • Y).
  -- We'll use the ℝ-smul→ℂ-smul bridge.
  rw [smul_sub, smul_sub]
  rw [smul_R_C α (((t ^ (p - 1) : ℝ) : ℂ) • 1),
      smul_R_C α (((t ^ p : ℝ) : ℂ) • X),
      smul_R_C (1 - α) (((t ^ (p - 1) : ℝ) : ℂ) • 1),
      smul_R_C (1 - α) (((t ^ p : ℝ) : ℂ) • Y)]
  -- After conversion to ℂ-smul:
  --   LHS = (α : ℂ) • (C - t^p • X) + ((1-α : ℝ) : ℂ) • (C - t^p • Y)
  --       = ((α : ℂ) + ((1-α : ℝ) : ℂ)) • C - ((α : ℂ) • t^p • X + ((1-α : ℝ) : ℂ) • t^p • Y)
  --       = C - t^p • ((α : ℂ) • X + ((1-α : ℝ) : ℂ) • Y)   [factor t^p out of smul]
  -- RHS = C - t^p • Z.
  -- The inequality LHS ≤ RHS is equivalent to:
  --   t^p • Z ≤ t^p • ((α : ℂ) • X + ((1-α : ℝ) : ℂ) • Y).
  -- Since t^p ≥ 0, this follows from `Z ≤ ((α : ℂ) • X + ((1-α : ℝ) : ℂ) • Y)`,
  -- which is `h_inv_conv`.
  have h_sum_one : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by push_cast; ring
  -- Rewrite goal as `-((α : ℂ) • (...•X) + (... : ℂ) • (...•Y)) + C ≤ - (...•Z) + C`,
  -- and simplify to make `inv` form prominent.
  -- A cleaner approach is to rewrite both sides into a normal form.
  have h_C_combine :
      (α : ℂ) • (((t ^ (p - 1) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
        + ((1 - α : ℝ) : ℂ) • (((t ^ (p - 1) : ℝ) : ℂ) • 1)
        = ((t ^ (p - 1) : ℝ) : ℂ) • 1 := by
    rw [← add_smul, h_sum_one, one_smul]
  -- Factor t^p out of `(α : ℂ) • (t^p • X) + ((1-α : ℝ) : ℂ) • (t^p • Y)`:
  have h_T_factor :
      (α : ℂ) • (((t ^ p : ℝ) : ℂ) • X) + ((1 - α : ℝ) : ℂ) • (((t ^ p : ℝ) : ℂ) • Y)
        = ((t ^ p : ℝ) : ℂ) • ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y) := by
    rw [smul_add]
    rw [smul_comm (((t ^ p : ℝ) : ℂ)) (α : ℂ) X,
        smul_comm (((t ^ p : ℝ) : ℂ)) ((1 - α : ℝ) : ℂ) Y]
  -- Now the goal becomes:
  --  C - (α • (t^p • X) + (1-α) • (t^p • Y)) ≤ C - t^p • Z.
  -- i.e. (LHS group) ≤ (RHS group).
  have h_goal_form :
      (α : ℂ) • (((t ^ (p - 1) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
        - (α : ℂ) • (((t ^ p : ℝ) : ℂ) • X)
        + (((1 - α : ℝ) : ℂ) • (((t ^ (p - 1) : ℝ) : ℂ) • 1)
            - ((1 - α : ℝ) : ℂ) • (((t ^ p : ℝ) : ℂ) • Y))
        = ((t ^ (p - 1) : ℝ) : ℂ) • 1
            - ((t ^ p : ℝ) : ℂ) • ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y) := by
    have h_reorder :
      ∀ (a b c d : Matrix (Fin n) (Fin n) ℂ),
        a - b + (c - d) = (a + c) - (b + d) := fun a b c d => by abel
    rw [h_reorder]
    rw [h_C_combine, h_T_factor]
  rw [h_goal_form]
  -- Goal: `C - t^p • ((α : ℂ) • X + ((1-α : ℝ) : ℂ) • Y) ≤ C - t^p • Z`.
  -- Reduce to: `t^p • Z ≤ t^p • ((α : ℂ) • X + ((1-α : ℝ) : ℂ) • Y)`.
  -- And then to: `Z ≤ (α : ℂ) • X + ((1-α : ℝ) : ℂ) • Y` since `t^p ≥ 0`.
  have ht_pow_nonneg : (0 : ℝ) ≤ t ^ p :=
    le_of_lt (Real.rpow_pos_of_pos ht p)
  have ht_powC_nonneg : (0 : ℂ) ≤ ((t ^ p : ℝ) : ℂ) := by
    rw [Complex.le_def]; refine ⟨by simpa using ht_pow_nonneg, ?_⟩; simp
  -- Apply `sub_le_sub_left`: `a ≤ b ↔ c - b ≤ c - a`.
  have h_smul_le :
      ((t ^ p : ℝ) : ℂ) • Z
        ≤ ((t ^ p : ℝ) : ℂ) • ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y) := by
    -- ℂ-smul on PSD matrices preserves `≤` when the scalar is `≥ 0`.
    -- Strategy: show that the difference (RHS - LHS) is PSD.
    have h_diff_PSD :
        ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y - Z).PosSemidef := by
      have h_le0 :
          (0 : Matrix (Fin n) (Fin n) ℂ)
            ≤ ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y - Z) := by
        exact sub_nonneg.mpr h_inv_conv
      exact h_le0.posSemidef
    have h_smul_PSD :
        (((t ^ p : ℝ) : ℂ)
            • ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y - Z)).PosSemidef :=
      h_diff_PSD.smul ht_powC_nonneg
    have h_smul_PSD_nonneg :
        (0 : Matrix (Fin n) (Fin n) ℂ)
          ≤ (((t ^ p : ℝ) : ℂ)
              • ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y - Z)) := h_smul_PSD.nonneg
    -- Pull the smul into `(...)` and recognise sub: c • (M - N) = c • M - c • N.
    rw [smul_sub] at h_smul_PSD_nonneg
    exact sub_nonneg.mp h_smul_PSD_nonneg
  -- Now goal: C - t^p • (αX + (1-α)Y) ≤ C - t^p • Z.
  -- This is `sub_le_sub_left h_smul_le C`.
  exact sub_le_sub_left h_smul_le _

/-- **Per-`t` operator concavity** of `cfcₙ (Real.rpowIntegrand₀₁ p t)`
    on PSD matrices, packaged as a `ConcaveOn`. -/
theorem rpowIntegrand_per_t_concaveOn
    (p : ℝ) {t : ℝ} (ht : 0 < t) :
    ConcaveOn ℝ
      (Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ))
      (fun A : Matrix (Fin n) (Fin n) ℂ =>
        cfcₙ (Real.rpowIntegrand₀₁ p t) A) := by
  refine ⟨convex_Ici _, fun A hA B hB a b ha hb hab => ?_⟩
  -- ConcaveOn unfolds to: a • f A + b • f B ≤ f (a • A + b • B), with a + b = 1.
  have hA_PSD : A.PosSemidef := (Matrix.nonneg_iff_posSemidef.mp hA)
  have hB_PSD : B.PosSemidef := (Matrix.nonneg_iff_posSemidef.mp hB)
  -- Translate a, b to α, (1-α): a = α, b = 1 - α.
  have hb_eq : b = 1 - a := by linarith
  subst hb_eq
  exact rpowIntegrand_per_t_concavity_ineq p ht A B hA_PSD hB_PSD a ha (by linarith)

/-! ## 5. Discharge of `RpowIntegrand_Per_t_Operator_Concavity_Target`. -/

/-- **The named target — discharged unconditionally.**

    `RpowIntegrand_Per_t_Operator_Concavity_Target` holds:
    for every dimension `m`, every `p ∈ (0, 1)`, every `t > 0`,
    the map `A ↦ cfcₙ (rpowIntegrand₀₁ p t) A` is operator concave
    on PSD matrices.

    Note: the named gate quantifies over `p ∈ Set.Ioo 0 1`, but our
    proof works for **all** `p ∈ ℝ` (the constraint `p ∈ (0,1)` is
    only needed for the Bochner-lift step, not here). -/
theorem rpowIntegrand_per_t_concavity_target_holds :
    RpowIntegrand_Per_t_Operator_Concavity_Target := by
  intro m p t _hp ht
  exact rpowIntegrand_per_t_concaveOn (n := m) p ht

/-! ## 6. Axiom audit (commented out by default).

    Uncomment to verify locally that all six theorems depend ONLY on
    Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`.
    No `sorry`, no custom `axiom`. -/

-- #print axioms cfc_rpowIntegrand₀₁_eq_shift_inv_unital
-- #print axioms cfc_rpowIntegrand₀₁_eq_shift_inv
-- #print axioms shifted_inv_operator_convex_PSD
-- #print axioms rpowIntegrand_per_t_concavity_ineq
-- #print axioms rpowIntegrand_per_t_concaveOn
-- #print axioms rpowIntegrand_per_t_concavity_target_holds

-- VERIFIED 2026-06-01:
--   All 6 theorems depend only on Lean's three standard axioms
--   `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no
--   custom `axiom`.

end UnifiedTheory.LayerB.RpowIntegrandPerT
