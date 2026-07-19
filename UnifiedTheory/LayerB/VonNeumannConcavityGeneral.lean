/-
  LayerB/VonNeumannConcavityGeneral.lean
  ──────────────────────────────────────

  **Generality lift of von Neumann concavity and Holevo χ ≥ 0 to
  GENERAL component states (pure allowed), with only the AVERAGE
  required full-rank.**

  The companion file `VonNeumannConcavity.lean` proves concavity and
  `χ ≥ 0` for ensembles whose component states `ρ_i` AND average `ρ̄`
  are all positive-definite (the full-rank locus).  The per-component
  Klein step there used `umegakiRelativeEntropy_nonneg`, which needs
  BOTH arguments positive-definite.

  The newly-unconditional general Klein inequality

      `umegakiRelativeEntropy_nonneg_general_unconditional
         (ρ σ : ComplexDensityMatrix n) (hn : 0 < n) (hσ : σ.M.PosDef) :
         0 ≤ umegakiRelativeEntropy ρ σ`

  needs only the σ-slot (here ρ̄) positive-definite; the ρ-slot (here
  each component `ρ_i`) may be ANY density matrix — in particular
  rank-1 PURE states.  This lifts concavity to

      ∑_i p_i · S(ρ_i)  ≤  S(ρ̄),     ρ̄ = ∑_i p_i ρ_i,

  for arbitrary component states `ρ_i` as long as the average ρ̄ is
  full-rank — exactly the Holevo-χ-for-pure-states setting.

  **The χ-identity is PosDef-FREE.**  The trace-linearity calculation

      ∑_i p_i · S(ρ_i ‖ ρ̄)  =  S(ρ̄)  −  ∑_i p_i · S(ρ_i)

  rests only on `Re Tr(ρ · log ρ) = − S(ρ)`, which is available WITHOUT
  any positivity hypothesis as
  `HolevoUmegakiDischarge.re_trace_mul_operatorLog`
  (it routes through `vonNeumannEntropy_eq_neg_re_trace_xlogx`, the
  eigenvalue/`x log x` identity that holds for every Hermitian density
  matrix).  We therefore re-derive the χ-identity here with NO PosDef
  on any state, then use general Klein termwise.

  HONEST REMAINING HYPOTHESIS.
    The average ρ̄ = ∑ p_i ρ_i must be positive-definite (full rank).
    This is GENUINELY needed: general Klein puts ρ̄ in the σ-slot, and
    `S(ρ ‖ σ)` with rank-deficient σ is `+∞`/ill-defined where
    `supp ρ ⊄ supp σ` — the inequality has no finite content there.
    What is REMOVED is the positive-definiteness of each individual
    component `ρ_i`: those may now be pure (rank 1) or otherwise
    rank-deficient.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `weighted_umegaki_eq_holevoChi_general`
         — the χ-identity, PosDef-FREE.
    2. `vonNeumann_concave_general`
         — concavity with NO PosDef on the components, only ρ̄ PosDef.
    3. `vonNeumannConcavity_of_posDef_average`
         — gate-shape concavity for the `mkEnsemble` average, only
           the average required PosDef.
    4. `holevoChi_nonneg_general`
         — `0 ≤ χ` for general ensembles with full-rank average.
    5. `holevoChi_nonneg_pure` (corollary)
         — `0 ≤ χ` for ensembles of arbitrary (PURE-allowed) states
           with full-rank average: the standard Holevo-bound setting.
-/

import UnifiedTheory.LayerB.VonNeumannConcavity
import UnifiedTheory.LayerB.OperatorEntropyContinuous

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.VonNeumannConcavityGeneral

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.HolevoUmegakiDischarge
open UnifiedTheory.LayerB.HolevoBoundQuantum
open UnifiedTheory.LayerB.HolevoBound
open UnifiedTheory.LayerB.OperatorEntropyContinuous

variable {n : ℕ}

/-! ## 1. The χ-identity, PosDef-FREE -/

/-- **Per-component Umegaki expansion — PosDef-FREE.**

    For ANY density matrices ρ, σ (no positivity),
    `S(ρ ‖ σ) = − S(ρ) − Re Tr(ρ · log σ)`.

    The only analytic ingredient is `re_trace_mul_operatorLog`
    (`Re Tr(ρ log ρ) = − S(ρ)`), which is hypothesis-free. -/
theorem umegaki_to_avg_eq_general
    (ρ σ : ComplexDensityMatrix n) :
    umegakiRelativeEntropy ρ σ
      = - vonNeumannEntropy ρ
          - (Matrix.trace (ρ.M * operatorLog σ)).re := by
  unfold umegakiRelativeEntropy
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
      re_trace_mul_operatorLog ρ]

/-- The cross term is linear in the first argument — PosDef-FREE:
    `∑_i p_i · Re Tr(ρ_i · log ρ̄) = Re Tr( (∑_i p_i ρ_i) · log ρ̄ )`. -/
theorem sum_cross_term_eq_general
    {N : ℕ} (p : Fin N → ℝ)
    (ρ : Fin N → ComplexDensityMatrix n)
    (ρbar : ComplexDensityMatrix n)
    (hρbar : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M) :
    ∑ i, p i * (Matrix.trace ((ρ i).M * operatorLog ρbar)).re
      = (Matrix.trace (ρbar.M * operatorLog ρbar)).re := by
  have hstep : ∀ i, p i * (Matrix.trace ((ρ i).M * operatorLog ρbar)).re
                = (((p i : ℂ)) • Matrix.trace ((ρ i).M * operatorLog ρbar)).re := by
    intro i
    rw [smul_eq_mul, Complex.re_ofReal_mul]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [← Complex.re_sum]
  congr 1
  rw [hρbar, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- **The Holevo χ identity — PosDef-FREE.**

    For ANY ensemble of density matrices with average ρ̄ = ∑ p_i ρ_i
    (no positivity on any state),

      ∑_i p_i · S(ρ_i ‖ ρ̄)  =  S(ρ̄)  −  ∑_i p_i · S(ρ_i).

    Pure trace-linearity plus the hypothesis-free identity
    `Re Tr(ρ log ρ) = − S(ρ)`. -/
theorem weighted_umegaki_eq_holevoChi_general
    {N : ℕ} (p : Fin N → ℝ)
    (ρ : Fin N → ComplexDensityMatrix n)
    (ρbar : ComplexDensityMatrix n)
    (hρbar : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M) :
    ∑ i, p i * umegakiRelativeEntropy (ρ i) ρbar
      = vonNeumannEntropy ρbar - ∑ i, p i * vonNeumannEntropy (ρ i) := by
  have hterm : ∀ i, p i * umegakiRelativeEntropy (ρ i) ρbar
      = p i * (- vonNeumannEntropy (ρ i))
        - p i * (Matrix.trace ((ρ i).M * operatorLog ρbar)).re := by
    intro i
    rw [umegaki_to_avg_eq_general (ρ i) ρbar]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_sub_distrib]
  rw [sum_cross_term_eq_general p ρ ρbar hρbar]
  rw [re_trace_mul_operatorLog ρbar]
  rw [show (∑ i, p i * (- vonNeumannEntropy (ρ i)))
        = - ∑ i, p i * vonNeumannEntropy (ρ i) from by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring]
  ring

/-! ## 2. Concavity for general states with full-rank average -/

/-- **Concavity of the von Neumann entropy — GENERAL component states.**

    For ANY ensemble `{p_i, ρ_i}` of density matrices (each ρ_i an
    arbitrary density matrix — PURE allowed, no positive-definiteness)
    whose average ρ̄ = ∑ p_i ρ_i is positive-definite,

      ∑_i p_i · S(ρ_i)  ≤  S(ρ̄).

    Each `S(ρ_i ‖ ρ̄) ≥ 0` by the UNCONDITIONAL general Klein
    inequality `umegakiRelativeEntropy_nonneg_general_unconditional`
    (ρ_i in the general slot, ρ̄ in the PosDef σ-slot), so the weighted
    sum is non-negative; the PosDef-free χ-identity converts that into
    the concavity bound.

    HONEST SCOPE: only the AVERAGE ρ̄ is required positive-definite.
    The individual-component PosDef hypothesis of `vonNeumann_concave`
    is GONE. -/
theorem vonNeumann_concave_general
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (_hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (ρbar : ComplexDensityMatrix n)
    (hρbar : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M)
    (hn : 0 < n) (hbarpos : ρbar.M.PosDef) :
    ∑ i, p i * vonNeumannEntropy (ρ i) ≤ vonNeumannEntropy ρbar := by
  -- The weighted relative entropy is non-negative (general Klein, termwise).
  have hnn : 0 ≤ ∑ i, p i * umegakiRelativeEntropy (ρ i) ρbar := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hp_nn i)
      (umegakiRelativeEntropy_nonneg_general_unconditional (ρ i) ρbar hn hbarpos)
  -- Convert via the PosDef-free χ-identity.
  have hid := weighted_umegaki_eq_holevoChi_general p ρ ρbar hρbar
  rw [hid] at hnn
  linarith

/-! ## 3. Gate-shape concavity (mkEnsemble average) -/

/-- **Concavity in the `mkEnsemble`/`ensembleAverageQuantum` shape with
    only the AVERAGE required PosDef.**

    This is the body of `HolevoBound.VonNeumannConcavity n`, specialised
    to the ρ̄ produced by `mkEnsemble`, supplied with `hn` and the single
    genuinely-required hypothesis that the average is positive-definite.
    No positivity on the component states. -/
theorem vonNeumannConcavity_of_posDef_average
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (hn : 0 < n)
    (hbarpos :
      (ensembleAverageQuantum
        (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)).M.PosDef) :
    ∑ i, p i * vonNeumannEntropy (ρ i)
      ≤ vonNeumannEntropy
          (ensembleAverageQuantum (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)) := by
  set ρbar := ensembleAverageQuantum (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)
    with hρbar_def
  have hρbarM : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M := by
    rw [hρbar_def, ensembleAverageQuantum_M]
    rfl
  exact vonNeumann_concave_general p hp_nn hp_sum ρ ρbar hρbarM hn hbarpos

/-! ## 4. Holevo χ ≥ 0 for general ensembles with full-rank average -/

/-- **`0 ≤ χ` — Holevo non-negativity for GENERAL ensembles.**

    For ANY ensemble of density matrices with positive-definite
    average, the Holevo χ-quantity is non-negative.  Routes the general
    concavity bound through the entropy-difference form of χ.  No
    positivity on the component states; only the full-rank average. -/
theorem holevoChi_nonneg_general
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (hn : 0 < n)
    (hbarpos :
      (ensembleAverageQuantum
        (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)).M.PosDef) :
    0 ≤ HolevoBound.holevoChi p hp_nn hp_sum ρ := by
  rw [HolevoBound.holevoChi_eq_entropy_difference]
  have h := vonNeumannConcavity_of_posDef_average p hp_nn hp_sum ρ hn hbarpos
  linarith

/-! ## 5. Pure-state corollary — the standard Holevo setting -/

/-- **`0 ≤ χ` for an ensemble of PURE (or otherwise rank-deficient)
    states with full-rank average — the standard Holevo-bound setting.**

    This is a direct restatement of `holevoChi_nonneg_general`: the
    component states `ρ i` carry NO positivity hypothesis whatsoever, so
    in particular they may be pure (rank-1) projectors `|ψ_i⟩⟨ψ_i|`.
    The ONLY surviving requirement is that the ensemble average
    `ρ̄ = ∑ p_i ρ_i` is positive-definite (full rank), which is the
    physically generic situation for a pure-state ensemble that spans
    the Hilbert space. -/
theorem holevoChi_nonneg_pure
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (hn : 0 < n)
    (hbarpos :
      (ensembleAverageQuantum
        (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)).M.PosDef) :
    0 ≤ HolevoBound.holevoChi p hp_nn hp_sum ρ :=
  holevoChi_nonneg_general p hp_nn hp_sum ρ hn hbarpos

/-! ## 6. Axiom audit -/

-- VERIFIED (2026-06-03): all five theorems below depend ONLY on the
-- standard Lean 4 / Mathlib core triple {propext, Classical.choice,
-- Quot.sound} — no `sorry`, no custom `axiom`.  Uncomment to re-verify.

-- #print axioms weighted_umegaki_eq_holevoChi_general
-- #print axioms vonNeumann_concave_general
-- #print axioms vonNeumannConcavity_of_posDef_average
-- #print axioms holevoChi_nonneg_general
-- #print axioms holevoChi_nonneg_pure

end UnifiedTheory.LayerB.VonNeumannConcavityGeneral
