/-
  LayerB/AndoInterpolation.lean
  ──────────────────────────────

  **The Hansen–Pedersen / Ando interpolation gate** — partial
  discharge of `Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target`,
  the final residual obligation on the Lieb 1973 / Carlen 2010
  reduction chain.

  ## Headline target

  The gate (defined in `LiebTracialAttack.lean`):

      def Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target : Prop :=
        Rpow_Operator_Concavity_Target → Lieb1973_Tracial_Target

  i.e., "given operator concavity of `rpow` on `[0, 1]`, derive joint
  concavity of `(A, B) ↦ Re Tr(A^s · B^{1-s})` for general `s ∈ [0, 1]`
  and general PosDef `A, B` (not assumed to commute)."

  This is the Carlen 2010 Theorem 2.9 interpolation step (Hansen–Pedersen
  / Ando interpolation chain).  Even with both unconditional inputs in
  hand — the rpow operator concavity and the `s = 1/2` Ando joint
  concavity — the bridge to general `s` requires a Stinespring-type
  purification + partial-trace lift (the Effros / Choi block-matrix
  construction).  This is genuinely multi-week Lean work.

  ## What this file ships UNCONDITIONALLY (zero `sorry`, zero `axiom`)

  Phase A — **Endpoint discharges** for `s = 0` and `s = 1`.
    At each endpoint, the tracial form `Tr(A^s · B^{1-s})` is **linear**
    in one of `A, B` (and the cfc reduces to identity or unity), so the
    joint-concavity inequality collapses to reflexivity of the trace.

  Phase B — **`n = 0` trivial dimension** (already in
    `LiebTracialAttack.lieb_tracial_n_zero`; re-export and use).

  Phase C — **Commuting-case discharge** via joint diagonalisation.
    Given that all four PosDef matrices pairwise commute, they admit
    a shared unitary diagonalisation (`jointDiagonalisation_exists_of_allCommute`
    from `JointDiagonalisationCommuting`).  The tracial form is
    unitary-invariant (Phase 3.A trace cycling + `cfc_unitary_conj`),
    so we reduce to the diagonal case
    `LiebTracialAttack.lieb1973_tracial_target_diagonal_holds`.

  Phase D — **The residual non-commuting sub-gate**, packaged
    explicitly as a named `Prop` obligation
    `Lieb1973_Tracial_NonCommuting_Subgate`.  This is the genuinely
    deep remaining content (the Ando interpolation / Hansen–Pedersen
    chain for non-commuting PosDef matrices at general `s`).

  Phase E — **The composite reduction**:
      `ando_interpolation_holds`:  given the non-commuting sub-gate,
      `Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target` holds.
    This is the "conditional cascade closure" form.  When the sub-gate
    is later supplied, the entire Lieb chain closes.

  Phase F — **Downstream cascade**:
      `lieb_tracial_target_unconditional_of_subgate`:
      `Lieb1973_Tracial_Target` follows from the non-commuting sub-gate
      (and the unconditional rpow concavity).

  ## Honest scoping summary

  This file **does not unconditionally discharge** the final gate.
  The full discharge of `Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target`
  requires Carlen 2010 Theorem 2.9's Stinespring purification — a multi-
  week Lean obligation that is the only remaining analytic content on
  the entire Lieb chain.

  Instead, this file ships:

    1. Three unconditional **special-case discharges** (endpoints,
       `n = 0`, commuting).
    2. One named **residual sub-gate** for the non-commuting general-`s`
       case, packaged as a clean `Prop`.
    3. A **composite reduction** showing that the full gate follows
       from the named sub-gate.
    4. A **downstream cascade** showing `Lieb1973_Tracial_Target` and
       `Lieb1973_Corrected_Target` both follow from the sub-gate.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01.
-/

import UnifiedTheory.LayerB.LiebTracialAttack
import UnifiedTheory.LayerB.LiebRpowRoute
import UnifiedTheory.LayerB.RpowConcavityClosed
import UnifiedTheory.LayerB.IsAndoMaximalDischarge
import UnifiedTheory.LayerB.JointDiagonalisationCommuting
import UnifiedTheory.LayerB.LiebCorrectedCommutingFull
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.CFCDiagonalDischarge

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.AndoInterpolation

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.LiebRpowRoute
open UnifiedTheory.LayerB.LiebTracialAttack
open UnifiedTheory.LayerB.RpowConcavityClosed
open UnifiedTheory.LayerB.IsAndoMaximalDischarge
open UnifiedTheory.LayerB.JointDiagonalisationCommuting
open UnifiedTheory.LayerB.LiebCorrectedCommutingFull
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.CFCDiagonalDischarge

/-! ## 1. Endpoint discharges: `s = 0` and `s = 1`. -/

section Endpoints

variable {n : ℕ}

/-- `cfc (fun x => x^0) A = 1` for a PosDef matrix `A`. -/
private lemma cfc_rpow_zero_eq_one
    (A : Matrix (Fin n) (Fin n) ℂ) (_ : A.PosDef) :
    cfc (fun x : ℝ => x ^ (0 : ℝ)) A = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h_fun_eq : (fun x : ℝ => x ^ (0 : ℝ)) = fun _ : ℝ => (1 : ℝ) := by
    funext x; exact Real.rpow_zero _
  rw [h_fun_eq]
  exact cfc_const_one (R := ℝ) A

/-- `cfc (fun x => x^1) A = A` for a PosDef matrix `A`. -/
private lemma cfc_rpow_one_eq_self
    (A : Matrix (Fin n) (Fin n) ℂ) (_ : A.PosDef) :
    cfc (fun x : ℝ => x ^ (1 : ℝ)) A = A := by
  have h_fun_eq : (fun x : ℝ => x ^ (1 : ℝ)) = fun x : ℝ => x := by
    funext x; exact Real.rpow_one _
  rw [h_fun_eq]
  exact cfc_id ℝ A

/-- **Endpoint `s = 0`** of the Lieb tracial target.

    At `s = 0`, `A^s = 1` and `B^{1-s} = B`, so `Tr(A^s · B^{1-s}) = Tr B`,
    which is linear in `B` and independent of `A`.  The joint-concavity
    inequality collapses to reflexivity of the trace under linear combination. -/
theorem lieb_tracial_endpoint_s_zero
    (A₁ A₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
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
                ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re := by
  -- Combination matrices are PosDef.
  have hα_compl : (((1 - α : ℝ)) : ℂ) = ((1 - α : ℝ) : ℂ) := rfl
  -- Reduce the cfc applications.
  have h_A₁_zero := cfc_rpow_zero_eq_one A₁ hA₁
  have h_A₂_zero := cfc_rpow_zero_eq_one A₂ hA₂
  have h_B₁_one_sub : (1 - (0 : ℝ)) = 1 := by ring
  rw [h_B₁_one_sub] at *
  rw [h_A₁_zero, h_A₂_zero]
  -- For the RHS A-side, need PosDef of convex combination — but cfc_rpow_zero_eq_one
  -- is stated for any input via cfc_const_one, no PosDef needed.
  have h_A_comb_zero :
      cfc (fun x : ℝ => x ^ (0 : ℝ))
            ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
        = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h_fun_eq : (fun x : ℝ => x ^ (0 : ℝ)) = fun _ : ℝ => (1 : ℝ) := by
      funext x; exact Real.rpow_zero _
    rw [h_fun_eq]
    exact cfc_const_one (R := ℝ) _
  rw [h_A_comb_zero]
  -- For the B factors at s=1, cfc reduces to identity.
  have h_B₁_one := cfc_rpow_one_eq_self B₁ hB₁
  have h_B₂_one := cfc_rpow_one_eq_self B₂ hB₂
  rw [h_B₁_one, h_B₂_one]
  have h_B_comb_one :
      cfc (fun x : ℝ => x ^ (1 : ℝ))
            ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂)
        = (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂ := by
    have h_fun_eq : (fun x : ℝ => x ^ (1 : ℝ)) = fun x : ℝ => x := by
      funext x; exact Real.rpow_one _
    rw [h_fun_eq]
    exact cfc_id ℝ _
  rw [h_B_comb_one]
  -- Now LHS = α · Re Tr(B₁) + (1-α) · Re Tr(B₂), RHS = Re Tr(α • B₁ + (1-α) • B₂).
  -- These are EQUAL by linearity of Re ∘ trace.
  rw [Matrix.one_mul, Matrix.one_mul, Matrix.one_mul]
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  rw [Complex.add_re, smul_eq_mul, smul_eq_mul]
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- **Endpoint `s = 1`** of the Lieb tracial target.

    At `s = 1`, `A^s = A` and `B^{1-s} = 1`, so `Tr(A^s · B^{1-s}) = Tr A`,
    which is linear in `A` and independent of `B`. -/
theorem lieb_tracial_endpoint_s_one
    (A₁ A₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
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
                ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re := by
  -- `1 - 1 = 0`, so the B-cfc reduces to 1.
  have h_sub : (1 - (1 : ℝ)) = 0 := by ring
  rw [h_sub]
  -- Reduce A-cfcs to identities.
  have h_A₁_one := cfc_rpow_one_eq_self A₁ hA₁
  have h_A₂_one := cfc_rpow_one_eq_self A₂ hA₂
  rw [h_A₁_one, h_A₂_one]
  have h_A_comb_one :
      cfc (fun x : ℝ => x ^ (1 : ℝ))
            ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
        = (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂ := by
    have h_fun_eq : (fun x : ℝ => x ^ (1 : ℝ)) = fun x : ℝ => x := by
      funext x; exact Real.rpow_one _
    rw [h_fun_eq]
    exact cfc_id ℝ _
  rw [h_A_comb_one]
  -- Reduce B-cfcs to 1.
  have h_B₁_zero := cfc_rpow_zero_eq_one B₁ hB₁
  have h_B₂_zero := cfc_rpow_zero_eq_one B₂ hB₂
  rw [h_B₁_zero, h_B₂_zero]
  have h_B_comb_zero :
      cfc (fun x : ℝ => x ^ (0 : ℝ))
            ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂)
        = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h_fun_eq : (fun x : ℝ => x ^ (0 : ℝ)) = fun _ : ℝ => (1 : ℝ) := by
      funext x; exact Real.rpow_zero _
    rw [h_fun_eq]
    exact cfc_const_one (R := ℝ) _
  rw [h_B_comb_zero]
  -- LHS = α · Re Tr(A₁) + (1-α) · Re Tr(A₂), RHS = Re Tr(α • A₁ + (1-α) • A₂).
  rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_one]
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  rw [Complex.add_re, smul_eq_mul, smul_eq_mul]
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]

end Endpoints

/-! ## 2. Trivial dimension `n = 0`. -/

/-- For `n = 0`, the entire tracial inequality collapses to `0 ≤ 0`.
    Re-export of `LiebTracialAttack.lieb_tracial_n_zero` for canonical
    access from this module. -/
theorem lieb_tracial_dim_zero
    (A₁ A₂ B₁ B₂ : Matrix (Fin 0) (Fin 0) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
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
  lieb_tracial_n_zero A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ s hs₀ hs₁ α hα₀ hα₁

/-! ## 3. Commuting case via joint diagonalisation.

    For PosDef `A₁, A₂, B₁, B₂` that pairwise commute, the
    `JointDiagonalisation` structure provides a shared unitary `U`
    diagonalising all four.  The tracial form is unitary-invariant
    (via `cfc_unitary_conj` + trace cycling), so we reduce to the
    diagonal case and discharge via
    `lieb1973_tracial_target_diagonal_holds`. -/

section Commuting

variable {m : ℕ}

/-- Helper: `Tr(U · X · star U) = Tr(X)`. -/
private lemma trace_unitary_conj
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (U.val * X * (star U.val)) = Matrix.trace X := by
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.mem_unitaryGroup_iff'.mp U.property, Matrix.one_mul]

/-- `cfc (·^p) (U · X · star U) = U · cfc (·^p) X · star U` for
    Hermitian `X` and `0 ≤ p`. -/
private lemma cfc_rpow_unitary_conj
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) (hX : IsSelfAdjoint X)
    (p : ℝ) (hp : 0 ≤ p) :
    cfc (fun x : ℝ => x ^ p) (U.val * X * (star U.val))
      = U.val * (cfc (fun x : ℝ => x ^ p) X) * (star U.val) := by
  -- `(·^p)` is continuous on all of ℝ when `0 ≤ p`.
  have h_cont : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ X) :=
    (Real.continuous_rpow_const hp).continuousOn
  exact cfc_unitary_conj U X (fun x => x ^ p) hX h_cont

/-- The mixed-product trace identity for `cfc (·^p)` and `cfc (·^q)`:
        `Re Tr((U X Uᴴ)^p · (U Y Uᴴ)^q) = Re Tr(X^p · Y^q)`
    for self-adjoint `X, Y` and `0 ≤ p, q`. -/
private lemma re_trace_unitary_cfc_rpow
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (X Y : Matrix (Fin m) (Fin m) ℂ)
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (Matrix.trace
        (cfc (fun x : ℝ => x ^ p) (U.val * X * (star U.val))
          * cfc (fun x : ℝ => x ^ q) (U.val * Y * (star U.val)))).re
      = (Matrix.trace
          (cfc (fun x : ℝ => x ^ p) X
            * cfc (fun x : ℝ => x ^ q) Y)).re := by
  rw [cfc_rpow_unitary_conj U X hX p hp]
  rw [cfc_rpow_unitary_conj U Y hY q hq]
  have h_alg :
      (U.val * cfc (fun x : ℝ => x ^ p) X * (star U.val)) *
        (U.val * cfc (fun x : ℝ => x ^ q) Y * (star U.val))
        = U.val * (cfc (fun x : ℝ => x ^ p) X
                    * cfc (fun x : ℝ => x ^ q) Y) * (star U.val) := by
    have hUstarU : star U.val * U.val = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp U.property
    calc (U.val * cfc (fun x : ℝ => x ^ p) X * (star U.val)) *
          (U.val * cfc (fun x : ℝ => x ^ q) Y * (star U.val))
        = U.val * cfc (fun x : ℝ => x ^ p) X *
            ((star U.val) * U.val) * cfc (fun x : ℝ => x ^ q) Y *
              (star U.val) := by
            simp only [Matrix.mul_assoc]
      _ = U.val * cfc (fun x : ℝ => x ^ p) X * 1 *
            cfc (fun x : ℝ => x ^ q) Y * (star U.val) := by rw [hUstarU]
      _ = U.val * (cfc (fun x : ℝ => x ^ p) X
                    * cfc (fun x : ℝ => x ^ q) Y) * (star U.val) := by
            rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h_alg, trace_unitary_conj]

/-- Helper: convex combination of unitary-conjugates equals unitary-conjugate
    of the convex combination. -/
private lemma convex_combination_unitary_conj_aux
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (Da Db : Matrix (Fin m) (Fin m) ℂ) (α : ℝ) :
    (α : ℂ) • (U.val * Da * (star U.val))
      + ((1 - α : ℝ) : ℂ) • (U.val * Db * (star U.val))
        = U.val * ((α : ℂ) • Da + ((1 - α : ℝ) : ℂ) • Db) * (star U.val) := by
  calc (α : ℂ) • (U.val * Da * (star U.val))
        + ((1 - α : ℝ) : ℂ) • (U.val * Db * (star U.val))
      = U.val * ((α : ℂ) • Da) * (star U.val)
          + U.val * (((1 - α : ℝ) : ℂ) • Db) * (star U.val) := by
        rw [Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_smul (a := ((1 - α : ℝ) : ℂ)),
            Matrix.smul_mul (a := ((1 - α : ℝ) : ℂ))]
    _ = U.val * ((α : ℂ) • Da + ((1 - α : ℝ) : ℂ) • Db) * (star U.val) := by
        rw [← Matrix.add_mul, ← Matrix.mul_add]

/-- If `X = U * diag(ofReal ∘ d) * star U` is PosDef, then every entry of
    `d` is positive.  (Re-derivation of the corresponding lemma in
    `LiebCorrectedCommutingFull`.) -/
private lemma diag_pos_of_posDef_conj_local
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (d : Fin m → ℝ)
    (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef)
    (h_eq : U.val * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * (star U.val) = X) :
    ∀ i, 0 < d i := by
  intro i
  set D : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun j => ((d j : ℝ) : ℂ)) with hD_def
  have hUUstar : U.val * (star U.val) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.property
  have hUstarU : (star U.val) * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  have hD_eq : D = (star U.val) * X * U.val := by
    rw [← h_eq]
    calc D = 1 * D * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (star U.val * U.val) * D * (star U.val * U.val) := by rw [hUstarU]
      _ = (star U.val) * (U.val * D * (star U.val)) * U.val := by
            simp only [Matrix.mul_assoc]
  have hU_unit : IsUnit (U.val : Matrix (Fin m) (Fin m) ℂ) := by
    refine ⟨⟨U.val, star U.val, ?_, ?_⟩, rfl⟩
    · exact hUUstar
    · exact hUstarU
  have hU_inj : Function.Injective (U.val : Matrix (Fin m) (Fin m) ℂ).mulVec :=
    Matrix.mulVec_injective_of_isUnit hU_unit
  have h_conjTranspose : (U.val).conjTranspose = star U.val := rfl
  have hD_PD : D.PosDef := by
    rw [hD_eq]
    have key := hX.conjTranspose_mul_mul_same (B := U.val) hU_inj
    rw [h_conjTranspose] at key
    exact key
  have h_pos_complex : ∀ j, (0 : ℂ) < ((d j : ℝ) : ℂ) :=
    Matrix.posDef_diagonal_iff.mp (hD_def ▸ hD_PD)
  exact_mod_cast h_pos_complex i

/-- **Commuting-case discharge** of the Lieb 1973 tracial form.

    Given a `JointDiagonalisation` `J` of four PosDef matrices, the
    tracial form inequality reduces to the per-coordinate inequality
    `lieb_tracial_diagonal_data` after applying unitary invariance
    (via `re_trace_unitary_cfc_rpow`). -/
theorem lieb1973_tracial_of_jointDiag
    (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (J : JointDiagonalisation A₁ A₂ B₁ B₂)
    (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    α * (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) A₁ * cfc (fun x : ℝ => x ^ (1 - s)) B₁)).re
        + (1 - α) * (Matrix.trace
            (cfc (fun x : ℝ => x ^ s) A₂ * cfc (fun x : ℝ => x ^ (1 - s)) B₂)).re
      ≤ (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
            * cfc (fun x : ℝ => x ^ (1 - s))
                ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re := by
  have h_1ms : 0 ≤ 1 - s := by linarith
  -- Abstract diagonal-data and unitary out of J so they don't depend on A₁ A₂ B₁ B₂.
  -- Use `set ... with` so subsequent `rw` doesn't trip the motive check.
  set dA : Fin m → ℝ := J.dA with hdA_def
  set dB : Fin m → ℝ := J.dB with hdB_def
  set dC : Fin m → ℝ := J.dC with hdC_def
  set dD : Fin m → ℝ := J.dD with hdD_def
  set U := J.U.val with hU_def
  set sU := star J.U.val with hsU_def
  set DA : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun i => ((dA i : ℝ) : ℂ)) with hDA_def
  set DB : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun i => ((dB i : ℝ) : ℂ)) with hDB_def
  set DC : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun i => ((dC i : ℝ) : ℂ)) with hDC_def
  set DD : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun i => ((dD i : ℝ) : ℂ)) with hDD_def
  -- Positivity of diagonal entries (uses the abstracted vars).
  have hpos_A₁ : ∀ i, 0 < dA i :=
    diag_pos_of_posDef_conj_local J.U dA A₁ hA₁ J.hA
  have hpos_A₂ : ∀ i, 0 < dB i :=
    diag_pos_of_posDef_conj_local J.U dB A₂ hA₂ J.hB
  have hpos_B₁ : ∀ i, 0 < dC i :=
    diag_pos_of_posDef_conj_local J.U dC B₁ hB₁ J.hC
  have hpos_B₂ : ∀ i, 0 < dD i :=
    diag_pos_of_posDef_conj_local J.U dD B₂ hB₂ J.hD
  -- Diagonalisation identities.
  have hA₁_eq : A₁ = U * DA * sU := J.hA.symm
  have hA₂_eq : A₂ = U * DB * sU := J.hB.symm
  have hB₁_eq : B₁ = U * DC * sU := J.hC.symm
  have hB₂_eq : B₂ = U * DD * sU := J.hD.symm
  -- Self-adjointness of each diagonal.
  have hDA_sa : IsSelfAdjoint DA := isSelfAdjoint_diagonal_ofReal dA
  have hDB_sa : IsSelfAdjoint DB := isSelfAdjoint_diagonal_ofReal dB
  have hDC_sa : IsSelfAdjoint DC := isSelfAdjoint_diagonal_ofReal dC
  have hDD_sa : IsSelfAdjoint DD := isSelfAdjoint_diagonal_ofReal dD
  -- Self-adjointness of convex combinations of diagonals.
  have hDA_conv_sa : IsSelfAdjoint ((α : ℂ) • DA + ((1 - α : ℝ) : ℂ) • DB) := by
    have h1 : IsSelfAdjoint ((α : ℂ) • DA) := by
      have hα : star (α : ℂ) = (α : ℂ) := Complex.conj_ofReal _
      unfold IsSelfAdjoint
      rw [star_smul, hα, hDA_sa.star_eq]
    have h2 : IsSelfAdjoint (((1 - α : ℝ) : ℂ) • DB) := by
      have hα : star ((1 - α : ℝ) : ℂ) = ((1 - α : ℝ) : ℂ) :=
        Complex.conj_ofReal _
      unfold IsSelfAdjoint
      rw [star_smul, hα, hDB_sa.star_eq]
    exact h1.add h2
  have hDB_conv_sa : IsSelfAdjoint ((α : ℂ) • DC + ((1 - α : ℝ) : ℂ) • DD) := by
    have h1 : IsSelfAdjoint ((α : ℂ) • DC) := by
      have hα : star (α : ℂ) = (α : ℂ) := Complex.conj_ofReal _
      unfold IsSelfAdjoint
      rw [star_smul, hα, hDC_sa.star_eq]
    have h2 : IsSelfAdjoint (((1 - α : ℝ) : ℂ) • DD) := by
      have hα : star ((1 - α : ℝ) : ℂ) = ((1 - α : ℝ) : ℂ) :=
        Complex.conj_ofReal _
      unfold IsSelfAdjoint
      rw [star_smul, hα, hDD_sa.star_eq]
    exact h1.add h2
  -- Convex combinations: A_t = U * (α • DA + (1-α) • DB) * sU.
  have h_At_eq :
      (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂
        = U * ((α : ℂ) • DA + ((1 - α : ℝ) : ℂ) • DB) * sU := by
    calc (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂
        = (α : ℂ) • (U * DA * sU) + ((1 - α : ℝ) : ℂ) • (U * DB * sU) := by
          rw [hA₁_eq, hA₂_eq]
      _ = U * ((α : ℂ) • DA + ((1 - α : ℝ) : ℂ) • DB) * sU :=
          convex_combination_unitary_conj_aux J.U DA DB α
  have h_Bt_eq :
      (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂
        = U * ((α : ℂ) • DC + ((1 - α : ℝ) : ℂ) • DD) * sU := by
    calc (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂
        = (α : ℂ) • (U * DC * sU) + ((1 - α : ℝ) : ℂ) • (U * DD * sU) := by
          rw [hB₁_eq, hB₂_eq]
      _ = U * ((α : ℂ) • DC + ((1 - α : ℝ) : ℂ) • DD) * sU :=
          convex_combination_unitary_conj_aux J.U DC DD α
  -- Trace identities via re_trace_unitary_cfc_rpow.
  have hT_A₁B₁ :
      (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) A₁ * cfc (fun x : ℝ => x ^ (1 - s)) B₁)).re
        = (Matrix.trace
            (cfc (fun x : ℝ => x ^ s) DA * cfc (fun x : ℝ => x ^ (1 - s)) DC)).re := by
    rw [hA₁_eq, hB₁_eq]
    exact re_trace_unitary_cfc_rpow J.U DA DC hDA_sa hDC_sa s (1 - s) hs₀ h_1ms
  have hT_A₂B₂ :
      (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) A₂ * cfc (fun x : ℝ => x ^ (1 - s)) B₂)).re
        = (Matrix.trace
            (cfc (fun x : ℝ => x ^ s) DB * cfc (fun x : ℝ => x ^ (1 - s)) DD)).re := by
    rw [hA₂_eq, hB₂_eq]
    exact re_trace_unitary_cfc_rpow J.U DB DD hDB_sa hDD_sa s (1 - s) hs₀ h_1ms
  have hT_combo :
      (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
            * cfc (fun x : ℝ => x ^ (1 - s))
                ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re
        = (Matrix.trace
            (cfc (fun x : ℝ => x ^ s) ((α : ℂ) • DA + ((1 - α : ℝ) : ℂ) • DB)
              * cfc (fun x : ℝ => x ^ (1 - s))
                  ((α : ℂ) • DC + ((1 - α : ℝ) : ℂ) • DD))).re := by
    rw [h_At_eq, h_Bt_eq]
    exact re_trace_unitary_cfc_rpow J.U _ _ hDA_conv_sa hDB_conv_sa s (1 - s) hs₀ h_1ms
  rw [hT_A₁B₁, hT_A₂B₂, hT_combo]
  -- Apply the diagonal-case discharge.  The diagonal target's RHS expects
  -- the same convex-combination form, so we unfold the DA, DB, DC, DD definitions.
  change α * (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) DA * cfc (fun x : ℝ => x ^ (1 - s)) DC)).re
        + (1 - α) * (Matrix.trace
            (cfc (fun x : ℝ => x ^ s) DB * cfc (fun x : ℝ => x ^ (1 - s)) DD)).re
      ≤ (Matrix.trace
          (cfc (fun x : ℝ => x ^ s) ((α : ℂ) • DA + ((1 - α : ℝ) : ℂ) • DB)
            * cfc (fun x : ℝ => x ^ (1 - s))
                ((α : ℂ) • DC + ((1 - α : ℝ) : ℂ) • DD))).re
  exact lieb1973_tracial_target_diagonal_holds
    dA dB dC dD hpos_A₁ hpos_A₂ hpos_B₁ hpos_B₂ s hs₀ hs₁ α hα₀ hα₁

/-- **Lieb 1973 tracial concavity for the COMMUTING case** — unconditional. -/
theorem lieb1973_tracial_commuting_unconditional
    (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ)
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
                ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re := by
  -- Get the joint diagonalisation existence.
  have hExists := jointDiagonalisation_exists_of_allCommute
    A₁ A₂ B₁ B₂ hA₁.isHermitian hA₂.isHermitian hB₁.isHermitian hB₂.isHermitian h_comm
  obtain ⟨J⟩ := hExists
  exact lieb1973_tracial_of_jointDiag
    A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ J s hs₀ hs₁ α hα₀ hα₁

end Commuting

/-! ## 4. The residual non-commuting sub-gate.

    The remaining content of the Ando interpolation chain is the
    non-commuting general-`s` case.  We package it as a named sub-gate
    to make the residual obligation explicit.

    The full Carlen 2010 / Hansen–Pedersen / Ando route uses a
    Stinespring-type purification + partial-trace argument to reduce
    the non-commuting case to a higher-dimensional commuting case
    (in an enlarged Hilbert space).  This is the missing analytic
    content that future work needs to discharge. -/

/-- **The residual non-commuting sub-gate.**

    Given operator concavity of `rpow` on `[0, 1]` (the hypothesis of
    the parent gate), the Lieb 1973 tracial form for non-commuting
    PosDef matrices and general `s ∈ [0, 1]`.

    All other cases (endpoints, `n = 0`, commuting) are unconditionally
    discharged above; this sub-gate captures exactly the residual
    Hansen–Pedersen / Ando interpolation step. -/
def Lieb1973_Tracial_NonCommuting_Subgate : Prop :=
  Rpow_Operator_Concavity_Target →
    ∀ {n : ℕ} (A₁ A₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ),
      A₁.PosDef → A₂.PosDef → B₁.PosDef → B₂.PosDef →
      ¬ AllCommute A₁ A₂ B₁ B₂ →
      ∀ (s : ℝ), 0 < s → s < 1 →
      ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
        α * (Matrix.trace
              (cfc (fun x : ℝ => x ^ s) A₁
                * cfc (fun x : ℝ => x ^ (1 - s)) B₁)).re
            + (1 - α) * (Matrix.trace
                (cfc (fun x : ℝ => x ^ s) A₂
                  * cfc (fun x : ℝ => x ^ (1 - s)) B₂)).re
          ≤ (Matrix.trace
              (cfc (fun x : ℝ => x ^ s) ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
                * cfc (fun x : ℝ => x ^ (1 - s))
                    ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))).re

/-- Canonical interface. -/
theorem lieb1973_tracial_nonCommuting_subgate_holds
    (h : Lieb1973_Tracial_NonCommuting_Subgate) :
    Lieb1973_Tracial_NonCommuting_Subgate := h

/-! ## 5. Composite reduction: full target from the sub-gate.

    We assemble the four discharges (endpoints, `n = 0`, commuting,
    non-commuting sub-gate) into the full target. -/

/-- **The composite reduction.**

    Given the named non-commuting sub-gate
    `Lieb1973_Tracial_NonCommuting_Subgate`, the headline parent gate
    `Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target` holds.

    Proof sketch:
    * Decompose on `s ∈ {0, 1}` vs `0 < s < 1`: endpoints discharged
      by `lieb_tracial_endpoint_s_zero` / `lieb_tracial_endpoint_s_one`.
    * Decompose on `n = 0` vs `n ≥ 1`: trivial by
      `lieb_tracial_dim_zero`.
    * Decompose on commuting vs non-commuting: commuting by
      `lieb1973_tracial_commuting_unconditional`; non-commuting by
      the sub-gate. -/
theorem ando_interpolation_from_subgate
    (h_sub : Lieb1973_Tracial_NonCommuting_Subgate) :
    Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target := by
  intro h_rpow
  intro n A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ s hs₀ hs₁ α hα₀ hα₁
  -- Split on endpoints of s.
  by_cases hs_zero : s = 0
  · subst hs_zero
    exact lieb_tracial_endpoint_s_zero A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ α hα₀ hα₁
  by_cases hs_one : s = 1
  · subst hs_one
    exact lieb_tracial_endpoint_s_one A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ α hα₀ hα₁
  -- Now `0 < s < 1`.
  have hs_pos : 0 < s := lt_of_le_of_ne hs₀ (Ne.symm hs_zero)
  have hs_lt_one : s < 1 := lt_of_le_of_ne hs₁ hs_one
  -- Split on commuting vs non-commuting.
  by_cases h_comm : AllCommute A₁ A₂ B₁ B₂
  · -- Commuting case: discharged unconditionally.
    exact lieb1973_tracial_commuting_unconditional
      A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ h_comm s hs₀ hs₁ α hα₀ hα₁
  · -- Non-commuting case: invoke the sub-gate.
    exact h_sub h_rpow A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ h_comm s hs_pos hs_lt_one α hα₀ hα₁

/-! ## 6. Downstream cascade: full Lieb chain from the sub-gate. -/

/-- **`Lieb1973_Tracial_Target` is unconditional given the sub-gate.**

    Composes `ando_interpolation_from_subgate` with the unconditional
    `rpow_operator_concavity_target_unconditional`. -/
theorem lieb_tracial_target_from_subgate
    (h_sub : Lieb1973_Tracial_NonCommuting_Subgate) :
    Lieb1973_Tracial_Target :=
  (ando_interpolation_from_subgate h_sub) rpow_operator_concavity_target_unconditional

/-! ## 7. The headline composite. -/

/-- **Headline composite reduction**: the parent gate
    `Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target` reduces to
    the single named sub-gate `Lieb1973_Tracial_NonCommuting_Subgate`.

    This is the cleanest "skeleton + named residual" form of the
    Hansen–Pedersen / Ando interpolation gate.  All other cases
    (endpoints, `n = 0`, commuting general-`s`) are discharged
    unconditionally in this file. -/
theorem ando_interpolation_holds
    (h_sub : Lieb1973_Tracial_NonCommuting_Subgate) :
    Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target :=
  ando_interpolation_from_subgate h_sub

/-! ## 8. Honest scope summary.

    **UNCONDITIONAL (this file)**:

      * `lieb_tracial_endpoint_s_zero` — `s = 0` discharge.
      * `lieb_tracial_endpoint_s_one`  — `s = 1` discharge.
      * `lieb_tracial_dim_zero`         — `n = 0` discharge.
      * `lieb1973_tracial_of_jointDiag` — commuting via joint diag.
      * `lieb1973_tracial_commuting_unconditional` — commuting case
        (combines existence of joint diagonalisation with above).
      * `re_trace_unitary_cfc_rpow` — unitary invariance of the tracial form.

    **NAMED RESIDUAL SUB-GATE**:

      * `Lieb1973_Tracial_NonCommuting_Subgate` — the Hansen–Pedersen
        / Ando interpolation step for non-commuting PosDef inputs and
        `s ∈ (0, 1)`.  This is the single remaining analytic obligation.

    **COMPOSITE REDUCTIONS**:

      * `ando_interpolation_from_subgate` — full parent gate from
        sub-gate.
      * `ando_interpolation_holds`        — headline alias.
      * `lieb_tracial_target_from_subgate` — `Lieb1973_Tracial_Target`
        from sub-gate.

    **DISTANCE TO LIEB-CHAIN CLOSURE**:

      One single named obligation remains:
      `Lieb1973_Tracial_NonCommuting_Subgate`.

      Once this sub-gate is dispatched (Carlen 2010 Theorem 2.9 /
      Hansen–Pedersen via Stinespring purification + partial-trace
      lift), the entire Lieb chain runs to completion via:

        sub-gate → ando_interpolation_holds
                     → Lieb1973_Tracial_From_Half_And_Rpow_Concavity_Target
                     → lieb1973_tracial_target_from_interpolation
                       (with rpow_operator_concavity_target_unconditional)
                     → Lieb1973_Tracial_Target
                     → (via Tracial_To_Corrected_Reduction_Target)
                     → Lieb1973_Corrected_Target.

      All non-sub-gate inputs to this final cascade are already
      unconditional:

        * `Rpow_Operator_Concavity_Target`      ✅
        * `Log_As_Rpow_Limit_Target`             ✅
        * `OperatorEntropy_Convexity_Target`     ✅
        * `IsAndoMaximal`                        ✅
        * `JointDiagonalisation` existence       ✅
        * Endpoint, dim-0, commuting cases       ✅ (this file).
-/

/-! ## 9. Axiom audit (commented). -/

-- #print axioms lieb_tracial_endpoint_s_zero
-- #print axioms lieb_tracial_endpoint_s_one
-- #print axioms lieb_tracial_dim_zero
-- #print axioms lieb1973_tracial_of_jointDiag
-- #print axioms lieb1973_tracial_commuting_unconditional
-- #print axioms ando_interpolation_from_subgate
-- #print axioms ando_interpolation_holds
-- #print axioms lieb_tracial_target_from_subgate

-- VERIFIED 2026-06-01:
--   All 8 headline theorems depend ONLY on Lean's three standard axioms
--   `[propext, Classical.choice, Quot.sound]`.  Zero `sorry`, zero
--   custom `axiom`.

end UnifiedTheory.LayerB.AndoInterpolation
