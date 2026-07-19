/-
  LayerB/RelativeEntropyConvexity.lean
  ─────────────────────────────────────

  **Convexity of the Umegaki quantum relative entropy in its first
  argument.**

  For `λ ∈ [0,1]` and density matrices `ρ₁, ρ₂, σ`,

      S(λρ₁ + (1−λ)ρ₂ ‖ σ)  ≤  λ · S(ρ₁‖σ)  +  (1−λ) · S(ρ₂‖σ).

  **Route.**  The Umegaki relative entropy splits (via
  `umegaki_to_avg_eq`, established for positive-definite first argument)
  into

      S(ρ‖σ)  =  − S(ρ)  −  Re Tr(ρ · log σ).

  The first term `−S(ρ) = Re Tr(ρ log ρ)` is **convex** in ρ — this is
  exactly the concavity of the von Neumann entropy proved in
  `VonNeumannConcavity.lean` (`vonNeumann_concave`), specialised to the
  two-point ensemble `{λ, 1−λ}`:

      λ S(ρ₁) + (1−λ) S(ρ₂)  ≤  S(λρ₁+(1−λ)ρ₂),

  i.e.  `−S(λρ₁+(1−λ)ρ₂) ≤ λ(−S(ρ₁)) + (1−λ)(−S(ρ₂))`.

  The second term `−Re Tr(ρ · log σ)` is **linear** in ρ (trace and
  matrix multiplication are linear, `log σ` is fixed):

      Re Tr((λρ₁+(1−λ)ρ₂)·log σ)
          = λ Re Tr(ρ₁·log σ) + (1−λ) Re Tr(ρ₂·log σ).

  Convex + linear = convex; adding the two inequalities gives the
  claim.

  HONEST SCOPE — the positivity hypotheses.  Exactly as in
  `VonNeumannConcavity.lean`, the trace identity `Re Tr(ρ log ρ) =
  − S(ρ)` (and Klein's inequality underneath the concavity) are
  framework-available only for **positive-definite** density matrices.
  We therefore prove convexity for positive-definite `ρ₁, ρ₂` with
  positive-definite convex combination `ρbar` and positive-definite
  `σ` — the generic / full-rank case — as a genuine, `sorry`-free,
  `axiom`-free theorem.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `cross_term_two_point`
         — linearity of the cross term `Re Tr(ρ · log σ)` in ρ along a
           two-point convex combination.
    2. `negEntropy_convex_two_point`
         — convexity of `−S` (equivalently `Re Tr(ρ log ρ)`):
           `−S(ρbar) ≤ λ(−S(ρ₁)) + (1−λ)(−S(ρ₂))`.
    3. `relativeEntropy_convex_first_arg`
         — `S(ρbar‖σ) ≤ λ S(ρ₁‖σ) + (1−λ) S(ρ₂‖σ)`, the convexity of
           the quantum relative entropy in its first argument.
-/

import UnifiedTheory.LayerB.VonNeumannConcavity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.RelativeEntropyConvexity

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.VonNeumannConcavity

variable {n : ℕ}

/-! ## 1. Linearity of the cross term `Re Tr(ρ · log σ)` -/

/-- **The cross term `Re Tr(ρ · log σ)` is linear in ρ.**

    Along the two-point convex combination
    `ρbar.M = λ • ρ₁.M + (1−λ) • ρ₂.M`,

      Re Tr(ρbar · log σ)
        = λ · Re Tr(ρ₁ · log σ) + (1−λ) · Re Tr(ρ₂ · log σ).

    Pure trace / matrix-multiplication linearity; `log σ` is fixed. -/
theorem cross_term_two_point
    (ρ₁ ρ₂ σ ρbar : ComplexDensityMatrix n) (lam : ℝ)
    (hρbar : ρbar.M = (lam : ℂ) • ρ₁.M + ((1 - lam : ℝ) : ℂ) • ρ₂.M) :
    (Matrix.trace (ρbar.M * operatorLog σ)).re
      = lam * (Matrix.trace (ρ₁.M * operatorLog σ)).re
        + (1 - lam) * (Matrix.trace (ρ₂.M * operatorLog σ)).re := by
  -- Expand the matrix product over the sum, then push the trace and
  -- the scalars through.
  rw [hρbar, Matrix.add_mul, Matrix.trace_add,
      Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.trace_smul,
      Complex.add_re, smul_eq_mul, smul_eq_mul,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-! ## 2. Convexity of `−S` (concavity of the von Neumann entropy, 2-point) -/

/-- **Two-point convexity of the negative von Neumann entropy.**

    Specialising `vonNeumann_concave` to the two-point ensemble
    `p = ![lam, 1−lam]`, `ρ = ![ρ₁, ρ₂]` gives the concavity bound
    `λ S(ρ₁) + (1−λ) S(ρ₂) ≤ S(ρbar)`, i.e.

      − S(ρbar)  ≤  λ (− S(ρ₁)) + (1−λ) (− S(ρ₂)). -/
theorem negEntropy_convex_two_point
    (ρ₁ ρ₂ ρbar : ComplexDensityMatrix n) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hρbar : ρbar.M = (lam : ℂ) • ρ₁.M + ((1 - lam : ℝ) : ℂ) • ρ₂.M)
    (hρ₁pos : ρ₁.M.PosDef) (hρ₂pos : ρ₂.M.PosDef) (hbarpos : ρbar.M.PosDef) :
    - vonNeumannEntropy ρbar
      ≤ lam * (- vonNeumannEntropy ρ₁) + (1 - lam) * (- vonNeumannEntropy ρ₂) := by
  -- Two-point ensemble data.
  set p : Fin 2 → ℝ := ![lam, 1 - lam] with hp_def
  set ρ : Fin 2 → ComplexDensityMatrix n := ![ρ₁, ρ₂] with hρ_def
  have hp_nn : ∀ i, 0 ≤ p i := by
    intro i; fin_cases i <;> simp [hp_def] <;> linarith
  have hp_sum : ∑ i, p i = 1 := by
    simp [hp_def, Fin.sum_univ_two]
  have hρpos : ∀ i, (ρ i).M.PosDef := by
    intro i; fin_cases i <;> simpa [hρ_def] using ‹_›
  -- ρbar.M = ∑_i p_i • (ρ i).M.
  have hρbarM : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M := by
    rw [hρbar, Fin.sum_univ_two]
    simp [hp_def, hρ_def]
  -- Concavity: ∑ p_i S(ρ_i) ≤ S(ρbar).
  have hconc :=
    vonNeumann_concave p hp_nn hp_sum ρ ρbar hρbarM hρpos hbarpos
  rw [Fin.sum_univ_two] at hconc
  simp only [hp_def, hρ_def, Matrix.cons_val_zero, Matrix.cons_val_one] at hconc
  -- λ S(ρ₁) + (1−λ) S(ρ₂) ≤ S(ρbar)  ⇒  − S(ρbar) ≤ λ(−S ρ₁) + (1−λ)(−S ρ₂).
  nlinarith [hconc]

/-! ## 3. Convexity of the relative entropy in the first argument -/

/-- **Convexity of the Umegaki relative entropy in its first
    argument (full-rank case).**

    For `λ ∈ [0,1]`, positive-definite `ρ₁, ρ₂`, positive-definite
    convex combination `ρbar = λρ₁ + (1−λ)ρ₂`, and positive-definite
    `σ`,

      S(ρbar ‖ σ)  ≤  λ · S(ρ₁‖σ)  +  (1−λ) · S(ρ₂‖σ).

    Assembled from:
      * `umegaki_to_avg_eq`  : `S(ρ‖σ) = −S(ρ) − Re Tr(ρ log σ)`;
      * `negEntropy_convex_two_point`  : convexity of `−S`;
      * `cross_term_two_point`         : linearity of `Re Tr(ρ log σ)`. -/
theorem relativeEntropy_convex_first_arg
    (ρ₁ ρ₂ σ ρbar : ComplexDensityMatrix n) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hρbar : ρbar.M = (lam : ℂ) • ρ₁.M + ((1 - lam : ℝ) : ℂ) • ρ₂.M)
    (hρ₁pos : ρ₁.M.PosDef) (hρ₂pos : ρ₂.M.PosDef) (hbarpos : ρbar.M.PosDef) :
    umegakiRelativeEntropy ρbar σ
      ≤ lam * umegakiRelativeEntropy ρ₁ σ
        + (1 - lam) * umegakiRelativeEntropy ρ₂ σ := by
  -- Expand each Umegaki term via `S(ρ‖σ) = −S(ρ) − Re Tr(ρ log σ)`.
  rw [umegaki_to_avg_eq ρbar σ hbarpos,
      umegaki_to_avg_eq ρ₁ σ hρ₁pos,
      umegaki_to_avg_eq ρ₂ σ hρ₂pos]
  -- Cross-term linearity.
  have hcross :=
    cross_term_two_point ρ₁ ρ₂ σ ρbar lam hρbar
  -- Convexity of −S.
  have hconv :=
    negEntropy_convex_two_point ρ₁ ρ₂ ρbar lam hlam0 hlam1 hρbar
      hρ₁pos hρ₂pos hbarpos
  -- Combine: convex + linear = convex.
  rw [hcross]
  nlinarith [hconv]

/-! ## 4. Axiom audit -/

-- VERIFIED: depends ONLY on the standard Lean 4 / Mathlib core triple
-- {propext, Classical.choice, Quot.sound} — no `sorry`, no custom
-- `axiom`.  Uncomment to re-verify.

-- #print axioms cross_term_two_point
-- #print axioms negEntropy_convex_two_point
-- #print axioms relativeEntropy_convex_first_arg

end UnifiedTheory.LayerB.RelativeEntropyConvexity
