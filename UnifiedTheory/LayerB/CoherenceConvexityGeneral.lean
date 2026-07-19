/-
  LayerB/CoherenceConvexityGeneral.lean
  ─────────────────────────────────────

  **Generality lift of two relative-entropy corollaries off their
  positive-definite-on-ρ restriction, riding the newly-general Klein
  inequality and the newly-general von Neumann concavity.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  (a)  **Relative entropy of coherence `C(ρ) ≥ 0` for GENERAL ρ.**

  `CoherenceNonneg.coherence_eq_umegaki` proves the headline identity
  `C(ρ) = umegakiRelativeEntropy ρ (dephasedDM ρ)` but carries a
  `ρ.M.PosDef` hypothesis — used ONLY to invoke
  `trace_mul_operatorLog_self_re` (`Re Tr(ρ log ρ) = −S(ρ)`).  That
  trace identity is in fact **hypothesis-free**:
  `HolevoUmegakiDischarge.re_trace_mul_operatorLog ρ`.  Re-deriving the
  identity with that PosDef-free lemma gives

      `coherence_eq_umegaki_general (ρ) : C(ρ) = S(ρ ‖ Δρ)`   (NO ρ-PosDef)

  and then the UNCONDITIONAL general Klein
  `umegakiRelativeEntropy_nonneg_general_unconditional` (which needs only
  the σ-slot `Δρ` positive-definite) gives

      `coherence_nonneg_general (ρ) (Δρ PosDef) : 0 ≤ C(ρ)`.

  Only requirement on ρ: its DEPHASING `Δρ` is positive-definite, i.e.
  the diagonal of ρ is strictly positive.  This covers PURE states with
  full-support diagonal — ρ itself rank-1, no PosDef on ρ at all.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  (b)  **Convexity of relative entropy in the first argument for
       GENERAL component states.**

  `RelativeEntropyConvexity.relativeEntropy_convex_first_arg` needs
  `ρ₁, ρ₂` (and ρbar) positive-definite, inherited from the
  two-point `vonNeumann_concave` it calls.  Swapping in the general
  two-point concavity `VonNeumannConcavityGeneral.vonNeumann_concave_general`
  (which needs ONLY the average ρbar PosDef) removes the per-component
  PosDef.  The cross term `Re Tr(ρ log σ)` is linear in ρ with NO
  positivity, so:

      `relativeEntropy_convex_first_arg_general`
        (ρ₁ ρ₂ ANY, ρbar PosDef, σ PosDef) :
          S(ρbar ‖ σ) ≤ λ S(ρ₁‖σ) + (1−λ) S(ρ₂‖σ).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE / WHAT DOES *NOT* LIFT.

    · Coherence FAITHFULNESS (`C(ρ) = 0 ⟺ ρ incoherent`) still needs
      ρ PosDef: its (⇒) direction routes through the STRICT Klein
      equality case `umegakiRelativeEntropy_eq_zero_imp`, whose
      framework form requires both slots positive-definite.  NOT lifted
      here — see `CoherenceNonneg.coherence_eq_zero_iff`.

    · Convexity (b) still requires the convex-combination average ρbar
      positive-definite (general Klein / general concavity put ρbar in
      the σ-slot) and σ positive-definite (it is the fixed reference).
      These are GENUINELY needed; only the per-component ρᵢ-PosDef is
      removed.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `coherence_eq_umegaki_general`          — identity, NO ρ-PosDef.
    2. `coherence_nonneg_general`              — C(ρ) ≥ 0, only Δρ PosDef.
    3. `coherence_nonneg_of_posDef_diag`       — restated via diagonal-pos.
    4. `relativeEntropy_convex_first_arg_general`
                                               — convexity, only ρbar, σ PosDef.

  ## Build target
      `lake build UnifiedTheory.LayerB.CoherenceConvexityGeneral`
-/

import UnifiedTheory.LayerB.CoherenceNonneg
import UnifiedTheory.LayerB.VonNeumannConcavityGeneral
import UnifiedTheory.LayerB.RelativeEntropyConvexity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CoherenceConvexityGeneral

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.CoherenceResource
open UnifiedTheory.LayerB.HolevoUmegakiDischarge
open UnifiedTheory.LayerB.OperatorEntropyContinuous
open UnifiedTheory.LayerB.VonNeumannConcavityGeneral
open UnifiedTheory.LayerB.RelativeEntropyConvexity
open UnifiedTheory.LayerB.CoherenceNonneg

variable {n : ℕ}

/-! ## (a).1  The coherence/relative-entropy identity WITHOUT ρ-PosDef. -/

/-- **Relative-entropy form of the coherence — NO `ρ.M.PosDef`.**

    `C(ρ) = S(Δρ) − S(ρ) = umegakiRelativeEntropy ρ (dephasedDM ρ)` for
    an ARBITRARY density matrix ρ.

    Identical content to `CoherenceNonneg.coherence_eq_umegaki`, but the
    self-trace term `Re Tr(ρ log ρ) = −S(ρ)` is discharged by the
    HYPOTHESIS-FREE `re_trace_mul_operatorLog` instead of the
    PosDef-gated `trace_mul_operatorLog_self_re`.  The dephased-trace
    collapse (`trace_mul_operatorLog_dephased_re`) and the
    Shannon-entropy identity for the diagonal were already PosDef-free,
    so the whole identity holds with no positivity on ρ. -/
theorem coherence_eq_umegaki_general (ρ : ComplexDensityMatrix n) :
    coherence ρ = umegakiRelativeEntropy ρ (dephasedDM ρ) := by
  -- Unfold the umegaki definition into the two traces.
  unfold umegakiRelativeEntropy
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  -- Term 1: Tr(ρ · log ρ).re = −S(ρ)   (PosDef-FREE).
  rw [re_trace_mul_operatorLog ρ]
  -- Term 2: Tr(ρ · log Δρ).re = ∑ dᵢ log dᵢ = −S(Δρ)   (already PosDef-free).
  rw [trace_mul_operatorLog_dephased_re ρ]
  -- S(Δρ) = shannonEntropy (diagProbVector ρ) = −∑ dᵢ log dᵢ.
  unfold coherence
  have hS : vonNeumannEntropy (dephasedDM ρ)
      = - ∑ i, (diagProbVector ρ).p i
                * Real.log ((diagProbVector ρ).p i) := by
    unfold dephasedDM
    rw [UnifiedTheory.LayerB.HolevoDiagonalDischarge.DiagonalEnsemble.vonNeumannEntropy_diagonal_eq_shannon]
    rfl
  rw [hS]
  ring

/-! ## (a).2  Non-negativity of coherence for GENERAL states. -/

/-- **Non-negativity of the relative entropy of coherence `C(ρ) ≥ 0`
    for a GENERAL density matrix ρ** — only the dephasing `Δρ` need be
    positive-definite (positive diagonal).

    No positivity on ρ itself: ρ may be PURE (rank 1) as long as every
    diagonal entry is strictly positive (full-support pure state).  The
    PosDef-free identity `coherence_eq_umegaki_general` rewrites
    `C(ρ) = S(ρ‖Δρ)`, and the UNCONDITIONAL general Klein inequality
    `umegakiRelativeEntropy_nonneg_general_unconditional` — needing only
    the σ-slot `Δρ` positive-definite — closes it.

    This strictly generalises `CoherenceNonneg.coherence_nonneg_of_posDef`:
    if ρ is PosDef then `dephasedDM_posDef` supplies `hΔ` and `n > 0`
    automatically, recovering the old statement. -/
theorem coherence_nonneg_general (ρ : ComplexDensityMatrix n)
    (hn : 0 < n) (hΔ : (dephasedDM ρ).M.PosDef) :
    0 ≤ coherence ρ := by
  rw [coherence_eq_umegaki_general ρ]
  exact umegakiRelativeEntropy_nonneg_general_unconditional ρ (dephasedDM ρ) hn hΔ

/-- **Non-negativity of coherence, phrased via the strictly-positive
    diagonal of ρ.**  `0 < (ρ.M i i).re` for every `i` is exactly the
    positive-diagonal condition that makes `Δρ` PosDef (a diagonal
    matrix is PosDef iff its diagonal is positive). -/
theorem coherence_nonneg_of_posDef_diag (ρ : ComplexDensityMatrix n)
    (hn : 0 < n) (hdiag : ∀ i, (0 : ℝ) < (diagProbVector ρ).p i) :
    0 ≤ coherence ρ := by
  apply coherence_nonneg_general ρ hn
  -- `(dephasedDM ρ).M = diagonal (fun i => ((diagProbVector ρ).p i : ℂ))`.
  have hM : (dephasedDM ρ).M
      = Matrix.diagonal (fun i => (((diagProbVector ρ).p i : ℝ) : ℂ)) := rfl
  rw [hM, Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hdiag i

/-! ## (b)  Convexity of relative entropy in the first argument,
            GENERAL component states. -/

/-- **Two-point convexity of `−S` (concavity of von Neumann entropy)
    for GENERAL component states.**

    The PosDef-on-each-component analogue of
    `RelativeEntropyConvexity.negEntropy_convex_two_point`, but routed
    through `vonNeumann_concave_general`, so `ρ₁, ρ₂` carry NO
    positivity — only the convex combination `ρbar` is required PosDef
    (and `n > 0`):

      `−S(ρbar) ≤ λ(−S ρ₁) + (1−λ)(−S ρ₂)`. -/
theorem negEntropy_convex_two_point_general
    (ρ₁ ρ₂ ρbar : ComplexDensityMatrix n) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hρbar : ρbar.M = (lam : ℂ) • ρ₁.M + ((1 - lam : ℝ) : ℂ) • ρ₂.M)
    (hn : 0 < n) (hbarpos : ρbar.M.PosDef) :
    - vonNeumannEntropy ρbar
      ≤ lam * (- vonNeumannEntropy ρ₁) + (1 - lam) * (- vonNeumannEntropy ρ₂) := by
  -- Two-point ensemble data.
  set p : Fin 2 → ℝ := ![lam, 1 - lam] with hp_def
  set ρ : Fin 2 → ComplexDensityMatrix n := ![ρ₁, ρ₂] with hρ_def
  have hp_nn : ∀ i, 0 ≤ p i := by
    intro i; fin_cases i <;> simp [hp_def] <;> linarith
  have hp_sum : ∑ i, p i = 1 := by
    simp [hp_def, Fin.sum_univ_two]
  -- ρbar.M = ∑_i p_i • (ρ i).M.
  have hρbarM : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M := by
    rw [hρbar, Fin.sum_univ_two]
    simp [hp_def, hρ_def]
  -- General concavity: ∑ p_i S(ρ_i) ≤ S(ρbar)  (NO per-component PosDef).
  have hconc :=
    vonNeumann_concave_general p hp_nn hp_sum ρ ρbar hρbarM hn hbarpos
  rw [Fin.sum_univ_two] at hconc
  simp only [hp_def, hρ_def, Matrix.cons_val_zero, Matrix.cons_val_one] at hconc
  nlinarith [hconc]

/-- **Convexity of the Umegaki relative entropy in its first argument —
    GENERAL component states.**

    For `λ ∈ [0,1]`, ARBITRARY density matrices `ρ₁, ρ₂`,
    convex combination `ρbar = λρ₁ + (1−λ)ρ₂` positive-definite, and
    positive-definite reference `σ`,

      `S(ρbar ‖ σ) ≤ λ · S(ρ₁‖σ) + (1−λ) · S(ρ₂‖σ)`.

    The component states `ρ₁, ρ₂` may be PURE (rank-deficient).
    Assembled from:
      * `umegaki_to_avg_eq_general`  : `S(ρ‖σ) = −S(ρ) − Re Tr(ρ log σ)`,
        PosDef-FREE in ρ (only needs the trace identity);
      * `negEntropy_convex_two_point_general` : convexity of `−S` (only ρbar PosDef);
      * `cross_term_two_point`                : linearity of `Re Tr(ρ log σ)` (PosDef-free).

    HONEST SCOPE: ρbar PosDef and σ PosDef remain genuinely required;
    only the PER-COMPONENT PosDef of `relativeEntropy_convex_first_arg`
    is removed. -/
theorem relativeEntropy_convex_first_arg_general
    (ρ₁ ρ₂ σ ρbar : ComplexDensityMatrix n) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hρbar : ρbar.M = (lam : ℂ) • ρ₁.M + ((1 - lam : ℝ) : ℂ) • ρ₂.M)
    (hn : 0 < n) (hbarpos : ρbar.M.PosDef) :
    umegakiRelativeEntropy ρbar σ
      ≤ lam * umegakiRelativeEntropy ρ₁ σ
        + (1 - lam) * umegakiRelativeEntropy ρ₂ σ := by
  -- Expand each Umegaki term via `S(ρ‖σ) = −S(ρ) − Re Tr(ρ log σ)`  (PosDef-FREE).
  rw [umegaki_to_avg_eq_general ρbar σ,
      umegaki_to_avg_eq_general ρ₁ σ,
      umegaki_to_avg_eq_general ρ₂ σ]
  -- Cross-term linearity (PosDef-free).
  have hcross :=
    cross_term_two_point ρ₁ ρ₂ σ ρbar lam hρbar
  -- Convexity of −S (general; only ρbar PosDef).
  have hconv :=
    negEntropy_convex_two_point_general ρ₁ ρ₂ ρbar lam hlam0 hlam1 hρbar hn hbarpos
  rw [hcross]
  nlinarith [hconv]

/-! ## Axiom audit. -/

#print axioms coherence_eq_umegaki_general
#print axioms coherence_nonneg_general
#print axioms coherence_nonneg_of_posDef_diag
#print axioms relativeEntropy_convex_first_arg_general

end UnifiedTheory.LayerB.CoherenceConvexityGeneral
