/-
  LayerB/LiebTargetAudit.lean
  ─────────────────────────────

  **Audit of `LiebTrace_Concavity_Target`** (PartialTraceDPIFull.lean, line 263).

  This is a DIAGNOSTIC file (not exported in `UnifiedTheory.lean`).

  ## Verdict

  The named hypothesis

      `LiebTrace_Concavity_Target`
        : `α · Re Tr(A₁ · log B₁) + (1-α) · Re Tr(A₂ · log B₂)
              ≤ Re Tr( (αA₁+(1-α)A₂) · log(αB₁+(1-α)B₂) )`

  is **MATHEMATICALLY FALSE** as stated.

  The scalar `1 × 1` specialisation reduces to claiming
      `α a₁ log b₁ + (1-α) a₂ log b₂  ≤  (α a₁ + (1-α) a₂) · log(α b₁ + (1-α) b₂)`
  jointly concave in `(a, b) ∈ ℝ⁺ × ℝ⁺`.  But the Hessian of
  `(a,b) ↦ a · log b` is `[[0, 1/b], [1/b, -a/b²]]` with determinant
  `−1/b² < 0`, so the function is **indefinite** — neither jointly
  convex nor jointly concave.

  Concrete counterexample (taken with `A₁ = B₁ = 1`, `A₂ = B₂ = 2`,
  `α = 1/2`):
      LHS  =  ½ · 1 · log 1 + ½ · 2 · log 2  =  log 2  ≈  0.6931
      RHS  =  (3/2) · log (3/2)               ≈  0.6082
  so `LHS > RHS`, falsifying the proposed concavity inequality.

  This file:
    1. Encodes the counterexample inside the Lean statement of
       `LiebTrace_Concavity_Target` and **proves** it is false.
    2. Notes that the downstream consumer
       `umegakiRelativeEntropy_jointly_convex_of_liebTrace`
       (line 321 of `PartialTraceDPIFull.lean`) is therefore
       **vacuous**: its hypothesis is unsatisfiable.
    3. Proposes a corrected target, `Lieb1973_Corrected_Target`,
       which states **joint convexity of Umegaki relative entropy**
           `(A,B) ↦ Tr(A log A) − Tr(A log B) = S(A‖B)`
       — this *is* the correct conclusion of Lieb's 1973 concavity
       theorem (via the integral representation of `log`), and is
       the inequality that the downstream consumer actually needs.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import UnifiedTheory.LayerB.PartialTraceDPIFull
import UnifiedTheory.LayerB.CFCDiagonalDischarge

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LiebTargetAudit

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.PartialTraceDPIFull
open UnifiedTheory.LayerB.CFCDiagonalDischarge
open UnifiedTheory.LayerB.UmegakiDiagonalBridge

/-! ## 1. Scalar building blocks -/

/-- The complex `1 × 1` diagonal matrix with entry `c : ℝ` cast to ℂ. -/
private noncomputable def scalarMat (c : ℝ) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal (fun _ : Fin 1 => ((c : ℝ) : ℂ))

/-- Positive scalars give PosDef `1 × 1` matrices. -/
private lemma scalarMat_posDef {c : ℝ} (hc : 0 < c) : (scalarMat c).PosDef := by
  refine (Matrix.posDef_diagonal_iff).mpr ?_
  intro _
  -- We need `0 < ((c : ℝ) : ℂ)` in the ComplexOrder.
  -- This reduces to `(0 : ℂ).re < ((c : ℂ)).re ∧ (0 : ℂ).im = (c : ℂ).im`.
  rw [show ((c : ℝ) : ℂ) = (Complex.ofReal c) from rfl]
  exact_mod_cast hc

/-- `cfc Real.log` on a scalar matrix gives the scalar matrix with `log` applied. -/
private lemma cfc_log_scalarMat (c : ℝ) :
    cfc Real.log (scalarMat c) = scalarMat (Real.log c) := by
  unfold scalarMat
  exact cfcOnDiagonalIsEntrywise_log 1 (fun _ : Fin 1 => c)

/-- Real part of the trace of `scalarMat c₁ * scalarMat c₂` is `c₁ * c₂`. -/
private lemma re_trace_scalarMat_mul (c₁ c₂ : ℝ) :
    (Matrix.trace (scalarMat c₁ * scalarMat c₂)).re = c₁ * c₂ := by
  unfold scalarMat
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp

/-- Convex combination of scalar matrices is itself a scalar matrix. -/
private lemma smul_add_scalarMat (α : ℝ) (c₁ c₂ : ℝ) :
    (α : ℂ) • scalarMat c₁ + ((1 - α : ℝ) : ℂ) • scalarMat c₂
      = scalarMat (α * c₁ + (1 - α) * c₂) := by
  unfold scalarMat
  -- Show equality entry-wise.
  ext i j
  -- Both sides are diagonal matrices on `Fin 1`, so `i = j = 0` and the
  -- entry simplifies to the scalar combination.
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    push_cast
    ring
  · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij,
          smul_eq_mul]

/-! ## 2. Numerical inequality: `log 2 > (3/2) · log (3/2)`.

    Equivalent form: `2 · log 2 > 3 · log (3/2) = 3 · log 3 − 3 · log 2`,
    i.e. `5 · log 2 > 3 · log 3`, i.e. `log (2^5) > log (3^3)`,
    i.e. `2^5 > 3^3`, i.e. `32 > 27`. -/

private lemma log_two_gt_three_halves_log_three_halves :
    Real.log (3 / 2) * (3 / 2) < Real.log 2 := by
  -- Strategy: rearrange to `5 · log 2 > 3 · log 3` then use `log_pow` + `log_lt_log`.
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  -- `log (3/2) = log 3 − log 2`.
  have hdiv : Real.log (3 / 2) = Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hdiv]
  -- Goal: `(log 3 - log 2) * (3/2) < log 2`.
  -- Multiply both sides by 2: `(log 3 - log 2) * 3 < 2 * log 2`,
  -- i.e. `3 * log 3 - 3 * log 2 < 2 * log 2`,
  -- i.e. `3 * log 3 < 5 * log 2`,
  -- i.e. `log (3^3) < log (2^5)`,
  -- i.e. `27 < 32`.
  have h_pow_ineq : Real.log ((3 : ℝ) ^ 3) < Real.log ((2 : ℝ) ^ 5) := by
    apply Real.log_lt_log
    · positivity
    · norm_num
  rw [Real.log_pow, Real.log_pow] at h_pow_ineq
  -- `h_pow_ineq : (3 : ℕ) * Real.log 3 < (5 : ℕ) * Real.log 2`.
  -- Cast to ℝ.
  have h_pow_ineq' : (3 : ℝ) * Real.log 3 < (5 : ℝ) * Real.log 2 := by
    exact_mod_cast h_pow_ineq
  linarith

/-! ## 3. The Lean counterexample. -/

/-- **The counterexample to `LiebTrace_Concavity_Target`.**

    We instantiate the universal statement at
        `m = 1, A₁ = B₁ = scalarMat 1, A₂ = B₂ = scalarMat 2, α = 1/2`
    and reduce it to the numerical inequality
        `log 2  ≤  (3/2) · log (3/2)`,
    which is false (`0.693 > 0.608`).  This proves
    `¬ LiebTrace_Concavity_Target` from first principles. -/
theorem liebTrace_concavity_target_is_false :
    ¬ LiebTrace_Concavity_Target := by
  intro h
  -- Apply `h` to the scalar instances.
  have h_pos1 : (scalarMat 1).PosDef := scalarMat_posDef (by norm_num : (0 : ℝ) < 1)
  have h_pos2 : (scalarMat 2).PosDef := scalarMat_posDef (by norm_num : (0 : ℝ) < 2)
  have hα0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hineq := h (scalarMat 1) (scalarMat 2) (scalarMat 1) (scalarMat 2)
                  h_pos1 h_pos2 h_pos1 h_pos2 (1 / 2 : ℝ) hα0 hα1
  -- Goal: derive False.
  -- Step 1: rewrite `cfc Real.log B_i = scalarMat (Real.log i)` for each B.
  rw [cfc_log_scalarMat 1, cfc_log_scalarMat 2] at hineq
  -- Step 2: rewrite the convex combinations inside the cfc on the RHS.
  --   `((1/2 : ℝ) : ℂ) • scalarMat 1 + ((1 - 1/2 : ℝ) : ℂ) • scalarMat 2
  --      = scalarMat ((1/2)*1 + (1 - 1/2)*2)
  --      = scalarMat (3/2)`.
  have h_combo :
      ((1 / 2 : ℝ) : ℂ) • scalarMat 1 + (((1 - 1 / 2 : ℝ)) : ℂ) • scalarMat 2
        = scalarMat (3 / 2) := by
    rw [smul_add_scalarMat]
    congr 1
    norm_num
  rw [h_combo] at hineq
  rw [cfc_log_scalarMat (3 / 2)] at hineq
  -- Step 3: rewrite the trace real parts using `re_trace_scalarMat_mul`.
  rw [re_trace_scalarMat_mul 1 (Real.log 1),
      re_trace_scalarMat_mul 2 (Real.log 2),
      re_trace_scalarMat_mul (3 / 2) (Real.log (3 / 2))] at hineq
  -- `Real.log 1 = 0`.
  rw [Real.log_one] at hineq
  -- Now `hineq` reads:
  --   `(1/2) * (1 * 0) + (1 - 1/2) * (2 * Real.log 2)
  --       ≤ (3/2) * Real.log (3/2)`.
  -- Simplify the LHS to `Real.log 2`.
  -- Reduce to: `Real.log 2 ≤ (3/2) * Real.log (3/2)`.
  have hineq' : Real.log 2 ≤ Real.log (3 / 2) * (3 / 2) := by
    have := hineq
    linarith
  -- Combine with the strict inequality from Section 2:
  --   `Real.log (3 / 2) * (3 / 2) < Real.log 2`.
  exact (lt_irrefl _) (lt_of_le_of_lt hineq' log_two_gt_three_halves_log_three_halves)

/-! ## 4. Vacuity of the downstream consumer.

    `umegakiRelativeEntropy_jointly_convex_of_liebTrace` (line 321 of
    `PartialTraceDPIFull.lean`) takes `LiebTrace_Concavity_Target`
    as a hypothesis.  Since that hypothesis is unsatisfiable,
    any further theorem built on top of it (the entire Tier-2
    branch of the file, and the Tier-3 composite
    `umegaki_dpi_partialTrace_of_liebTrace_etc`) is **vacuous**:
    it has no inhabited instance, hence proves nothing about the
    real `umegakiRelativeEntropy`.

    Concretely: we can derive ANY statement from a hypothesis
    of `LiebTrace_Concavity_Target`, including absurd ones. -/
theorem any_consequence_of_liebTrace_concavity_target
    (hLieb : LiebTrace_Concavity_Target) : False :=
  liebTrace_concavity_target_is_false hLieb

/-! ## 5. The corrected target.

    Lieb's 1973 concavity theorem proves joint concavity of
        `(A, B) ↦ Tr(A^p K B^q K*)`  for  `p, q ≥ 0`, `p + q ≤ 1`.
    The CONSEQUENCE that the downstream proof actually needs is
    NOT joint concavity of `Tr(A log B)` (which is false, as we
    just proved), but joint CONVEXITY of the Umegaki relative
    entropy
        `S(A ‖ B)  =  Tr(A log A)  −  Tr(A log B)`
    on PosDef × PosDef.

    This is the canonical form (Lindblad 1974, Uhlmann 1977)
    derived from Lieb's concavity via the differential
    `d/dt|_{t=0} Tr(A^{1-t} B^t)` argument.

    Below is the corrected target that captures the intended
    mathematical content: -/

/-- **Corrected Lieb-derived target — joint convexity of relative
    entropy on PosDef × PosDef.**

    For all PosDef `A₁, A₂, B₁, B₂` and `α ∈ [0, 1]`:

      `S(αA₁ + (1-α)A₂ ‖ αB₁ + (1-α)B₂)
            ≤  α · S(A₁ ‖ B₁) + (1-α) · S(A₂ ‖ B₂)`

    where `S(A ‖ B) := Re Tr( A · (log A − log B) )` (the matrix-
    level Umegaki form, before density-matrix normalisation).

    This statement is **TRUE** (Lindblad-Uhlmann) and is what the
    downstream proof `umegakiRelativeEntropy_jointly_convex_of_liebTrace`
    actually needs.  In particular, restricted to PosDef density
    matrices, this is `JointConvexity_RelEntropy_Target`. -/
def Lieb1973_Corrected_Target : Prop :=
    ∀ {m : ℕ} (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ),
      A₁.PosDef → A₂.PosDef → B₁.PosDef → B₂.PosDef →
      ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
        let A_t : Matrix (Fin m) (Fin m) ℂ :=
          (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂
        let B_t : Matrix (Fin m) (Fin m) ℂ :=
          (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂
        (Matrix.trace (A_t * cfc Real.log A_t)).re
            - (Matrix.trace (A_t * cfc Real.log B_t)).re
          ≤ α * ((Matrix.trace (A₁ * cfc Real.log A₁)).re
                  - (Matrix.trace (A₁ * cfc Real.log B₁)).re)
            + (1 - α) * ((Matrix.trace (A₂ * cfc Real.log A₂)).re
                           - (Matrix.trace (A₂ * cfc Real.log B₂)).re)

/-! ## 6. Sanity check: the corrected target is NOT refuted by the
       scalar `1×1` counterexample (i.e., the scalar instance is
       trivially TRUE, since `log` is concave so `S(a‖b) = a · log(a/b)`
       is jointly convex on `ℝ⁺ × ℝ⁺`).

    We do not need to prove the corrected target here (that's the
    job of the downstream Lindblad-Uhlmann work); we just confirm
    it is not falsified by the same scalar instance that DID
    falsify `LiebTrace_Concavity_Target`.

    On the scalars `A₁ = B₁ = 1, A₂ = B₂ = 2, α = 1/2`, both sides
    of the corrected target equal `0` (since `Aᵢ = Bᵢ` makes each
    `S(Aᵢ‖Bᵢ) = 0` and `A_t = B_t` makes `S(A_t‖B_t) = 0`).
    The inequality `0 ≤ 0` holds. -/

example :
    let A_t : Matrix (Fin 1) (Fin 1) ℂ :=
      ((1/2 : ℝ) : ℂ) • scalarMat 1 + (((1 - 1/2 : ℝ)) : ℂ) • scalarMat 2
    let B_t : Matrix (Fin 1) (Fin 1) ℂ :=
      ((1/2 : ℝ) : ℂ) • scalarMat 1 + (((1 - 1/2 : ℝ)) : ℂ) • scalarMat 2
    (Matrix.trace (A_t * cfc Real.log A_t)).re
        - (Matrix.trace (A_t * cfc Real.log B_t)).re
      ≤ (1/2 : ℝ) * ((Matrix.trace (scalarMat 1 * cfc Real.log (scalarMat 1))).re
              - (Matrix.trace (scalarMat 1 * cfc Real.log (scalarMat 1))).re)
        + (1 - (1/2 : ℝ))
          * ((Matrix.trace (scalarMat 2 * cfc Real.log (scalarMat 2))).re
              - (Matrix.trace (scalarMat 2 * cfc Real.log (scalarMat 2))).re) := by
  -- Both sides collapse to 0 since A = B everywhere.
  simp

/-! ## Axiom-cleanliness — checked once during authoring.

    `#print axioms liebTrace_concavity_target_is_false` reports

      ['UnifiedTheory.LayerB.LiebTargetAudit.liebTrace_concavity_target_is_false'
        depends on axioms: [propext, Classical.choice, Quot.sound]]

    i.e. only Lean's three standard foundational axioms.  No `sorry`,
    no custom axioms. -/

-- #print axioms liebTrace_concavity_target_is_false
-- #print axioms any_consequence_of_liebTrace_concavity_target
-- VERIFIED 2026-06-01: both depend only on
--   [propext, Classical.choice, Quot.sound]

end UnifiedTheory.LayerB.LiebTargetAudit
