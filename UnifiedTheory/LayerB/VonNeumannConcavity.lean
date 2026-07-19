/-
  LayerB/VonNeumannConcavity.lean
  ────────────────────────────────

  **Concavity of the von Neumann entropy, and the discharge of the
  Holevo `VonNeumannConcavity` gate.**

  Given a finite ensemble `{p_i, ρ_i}` of `n`-dimensional density
  matrices with average `ρ̄ = ∑_i p_i ρ_i`, the von Neumann entropy
  is concave:

      S(ρ̄)  ≥  ∑_i p_i · S(ρ_i),

  equivalently the Holevo χ-quantity `χ = S(ρ̄) − ∑_i p_i S(ρ_i) ≥ 0`.

  **Route — the Klein / Umegaki identity.**  With `ρ̄ = ∑_i p_i ρ_i`,

      S(ρ̄) − ∑_i p_i S(ρ_i)  =  ∑_i p_i · S(ρ_i ‖ ρ̄),

  and each `S(ρ_i ‖ ρ̄) ≥ 0` by Klein's inequality
  (`umegakiRelativeEntropy_nonneg`).  The identity is the
  trace-linearity calculation

      ∑_i p_i · S(ρ_i ‖ ρ̄)
        = ∑_i p_i [ Re Tr(ρ_i log ρ_i) − Re Tr(ρ_i log ρ̄) ]
        = ∑_i p_i Re Tr(ρ_i log ρ_i)  −  Re Tr( (∑_i p_i ρ_i) log ρ̄ )
        = − ∑_i p_i S(ρ_i)            −  Re Tr( ρ̄ log ρ̄ )
        = − ∑_i p_i S(ρ_i)            +  S(ρ̄).

  The two scalar identities `Re Tr(ρ log ρ) = − S(ρ)` are the
  product-trace spectral identity `re_trace_mul_cfc_log_eq_sum`
  (which is established for **positive-definite** ρ in
  `KleinInequality.lean`); trace-linearity in the first argument is
  unconditional.

  HONEST SCOPE — the positivity hypotheses.
    Klein's inequality and the product-form trace identity
    `Re Tr(ρ · log ρ) = ∑ λ log λ` are framework-available only for
    *positive-definite* density matrices (rank-deficient states sit on
    the boundary of the PSD cone; the inequality extends there by
    continuity, but that limiting argument is not wired through this
    framework).  We therefore prove concavity for ensembles of
    positive-definite states with positive-definite average — the
    generic / full-rank case — as a genuine, `sorry`-free theorem, and
    expose it in exactly the `VonNeumannConcavity`-gate shape (item 5
    of `HolevoBound.lean`) so that `holevoChi_nonneg_of_concave` and
    `holevo_bound` become real theorems on the full-rank locus.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `re_trace_mul_operatorLog_self`
         — `Re Tr(ρ · log ρ) = − S(ρ)` for PosDef ρ.
    2. `umegaki_to_avg_eq`
         — per-component expansion
           `S(ρ_i ‖ ρ̄) = − S(ρ_i) − Re Tr(ρ_i · log ρ̄)`.
    3. `weighted_umegaki_eq_holevoChi`
         — the χ identity
           `∑ p_i S(ρ_i ‖ ρ̄) = S(ρ̄) − ∑ p_i S(ρ_i)`.
    4. `vonNeumann_concave`
         — `∑ p_i S(ρ_i) ≤ S(ρ̄)` (concavity), full-rank case.
    5. `vonNeumannConcavity_of_posDef`
         — discharge of the exact `VonNeumannConcavity n` gate shape
           under the positivity hypotheses.
    6. `holevoChi_nonneg`
         — `0 ≤ χ` as a REAL theorem on the full-rank locus, routed
           through `HolevoBound.holevoChi_nonneg_of_concave`.
-/

import UnifiedTheory.LayerB.HolevoBound
import UnifiedTheory.LayerB.KleinInequalityFull

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.VonNeumannConcavity

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.KleinInequality
open UnifiedTheory.LayerB.KleinInequalityFull
open UnifiedTheory.LayerB.HolevoBoundQuantum
open UnifiedTheory.LayerB.HolevoBound

variable {n : ℕ}

/-! ## 1. The scalar identity `Re Tr(ρ · log ρ) = − S(ρ)` -/

/-- **`Re Tr(ρ · log ρ) = − S(ρ)`** for a positive-definite density
    matrix.  Combines the product-form spectral trace identity
    `re_trace_mul_cfc_log_eq_sum` with the eigenvalue definition of
    `vonNeumannEntropy`.  The two `IsHermitian` instances
    (`hpos.isHermitian` from `PosDef`, and `ρ.hHerm`) carry the same
    matrix, hence the same eigenvalues by proof irrelevance. -/
theorem re_trace_mul_operatorLog_self
    (ρ : ComplexDensityMatrix n) (hpos : ρ.M.PosDef) :
    (Matrix.trace (ρ.M * operatorLog ρ)).re = - vonNeumannEntropy ρ := by
  -- `operatorLog ρ = cfcρ Real.log ρ = cfc Real.log ρ.M`.
  unfold operatorLog cfcρ
  -- Product-trace spectral identity (PosDef).
  rw [re_trace_mul_cfc_log_eq_sum ρ.M hpos]
  -- `vonNeumannEntropy ρ = − ∑ (ρ.hHerm.eigenvalues i) log(...)`.
  unfold vonNeumannEntropy
  -- The two `IsHermitian` proofs of `ρ.M` (`hpos.isHermitian` and `ρ.hHerm`)
  -- carry the same matrix, so their eigenvalue functions are defeq.
  rw [neg_neg]

/-! ## 2. Per-component Umegaki expansion -/

/-- **Per-component Umegaki expansion.**  For positive-definite ρ,
    `S(ρ ‖ σ) = − S(ρ) − Re Tr(ρ · log σ)`.  Splits the Umegaki
    relative entropy `Re Tr(ρ (log ρ − log σ))` into the two trace
    terms and rewrites the first via
    `re_trace_mul_operatorLog_self`. -/
theorem umegaki_to_avg_eq
    (ρ σ : ComplexDensityMatrix n) (hρpos : ρ.M.PosDef) :
    umegakiRelativeEntropy ρ σ
      = - vonNeumannEntropy ρ
          - (Matrix.trace (ρ.M * operatorLog σ)).re := by
  unfold umegakiRelativeEntropy
  -- ρ.M * (log ρ − log σ) = ρ.M * log ρ − ρ.M * log σ.
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
      re_trace_mul_operatorLog_self ρ hρpos]

/-! ## 3. Trace linearity of the cross term -/

/-- The cross term is linear in the first argument:
    `∑_i p_i · Re Tr(ρ_i · log ρ̄) = Re Tr( (∑_i p_i ρ_i) · log ρ̄ )`,
    and `∑_i p_i ρ_i = ρ̄.M`. -/
theorem sum_cross_term_eq
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (ρbar : ComplexDensityMatrix n)
    (hρbar : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M) :
    ∑ i, p i * (Matrix.trace ((ρ i).M * operatorLog ρbar)).re
      = (Matrix.trace (ρbar.M * operatorLog ρbar)).re := by
  -- Move the real scalar `p i` inside the real part.
  have hstep : ∀ i, p i * (Matrix.trace ((ρ i).M * operatorLog ρbar)).re
                = (((p i : ℂ)) • Matrix.trace ((ρ i).M * operatorLog ρbar)).re := by
    intro i
    rw [smul_eq_mul, Complex.re_ofReal_mul]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  -- Pull the sum inside `Re`.
  rw [← Complex.re_sum]
  congr 1
  -- ∑ i, (p i) • Tr((ρ i).M * log ρ̄) = Tr( (∑ i p i • (ρ i).M) * log ρ̄ ).
  rw [hρbar, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-! ## 4. The χ-identity: `∑ p_i S(ρ_i ‖ ρ̄) = S(ρ̄) − ∑ p_i S(ρ_i)` -/

/-- **The Holevo χ identity.**  For an ensemble of positive-definite
    states with positive-definite average ρ̄,

      ∑_i p_i · S(ρ_i ‖ ρ̄)  =  S(ρ̄)  −  ∑_i p_i · S(ρ_i).

    This is the trace-linearity calculation in the file header.  The
    only analytic ingredients are the two `Re Tr(ρ log ρ) = − S(ρ)`
    identities (PosDef); everything else is finite-sum algebra. -/
theorem weighted_umegaki_eq_holevoChi
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (ρbar : ComplexDensityMatrix n)
    (hρbar : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M)
    (hρpos : ∀ i, (ρ i).M.PosDef) (hbarpos : ρbar.M.PosDef) :
    ∑ i, p i * umegakiRelativeEntropy (ρ i) ρbar
      = vonNeumannEntropy ρbar - ∑ i, p i * vonNeumannEntropy (ρ i) := by
  -- Expand each Umegaki term.
  have hterm : ∀ i, p i * umegakiRelativeEntropy (ρ i) ρbar
      = p i * (- vonNeumannEntropy (ρ i))
        - p i * (Matrix.trace ((ρ i).M * operatorLog ρbar)).re := by
    intro i
    rw [umegaki_to_avg_eq (ρ i) ρbar (hρpos i)]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_sub_distrib]
  -- The cross-term sum collapses to `Re Tr(ρ̄ log ρ̄) = − S(ρ̄)`.
  rw [sum_cross_term_eq p hp_nn hp_sum ρ ρbar hρbar]
  rw [re_trace_mul_operatorLog_self ρbar hbarpos]
  -- `∑ p_i (− S(ρ_i)) = − ∑ p_i S(ρ_i)`.
  rw [show (∑ i, p i * (- vonNeumannEntropy (ρ i)))
        = - ∑ i, p i * vonNeumannEntropy (ρ i) from by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring]
  ring

/-! ## 5. Concavity of the von Neumann entropy -/

/-- **Concavity of the von Neumann entropy (full-rank case).**

    For an ensemble of positive-definite states with positive-definite
    average ρ̄ = ∑ p_i ρ_i,

      ∑_i p_i · S(ρ_i)  ≤  S(ρ̄).

    Each `S(ρ_i ‖ ρ̄) ≥ 0` by Klein's inequality
    (`umegakiRelativeEntropy_nonneg`), so the weighted sum
    `∑ p_i S(ρ_i ‖ ρ̄) ≥ 0`; the χ-identity converts that into the
    concavity inequality. -/
theorem vonNeumann_concave
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (ρbar : ComplexDensityMatrix n)
    (hρbar : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M)
    (hρpos : ∀ i, (ρ i).M.PosDef) (hbarpos : ρbar.M.PosDef) :
    ∑ i, p i * vonNeumannEntropy (ρ i) ≤ vonNeumannEntropy ρbar := by
  -- The weighted relative entropy is non-negative (Klein, termwise).
  have hnn : 0 ≤ ∑ i, p i * umegakiRelativeEntropy (ρ i) ρbar := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hp_nn i)
      (umegakiRelativeEntropy_nonneg (ρ i) ρbar (hρpos i) hbarpos)
  -- Convert via the χ-identity.
  have hid := weighted_umegaki_eq_holevoChi p hp_nn hp_sum ρ ρbar hρbar hρpos hbarpos
  rw [hid] at hnn
  linarith

/-! ## 6. Discharging the `VonNeumannConcavity` gate -/

/-- **The `VonNeumannConcavity`-gate shape, discharged under
    positivity.**  This is exactly the body of
    `HolevoBound.VonNeumannConcavity n` (item 5 of `HolevoBound.lean`),
    specialised to the ρ̄ produced by `mkEnsemble` and supplied with
    the framework-required positivity hypotheses on the component
    states and the average.

    With `hbarpos` instantiated, this is the genuine concavity bound
    `∑ p_i S(ρ_i) ≤ S(ρ̄)`. -/
theorem vonNeumannConcavity_of_posDef
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (hρpos : ∀ i, (ρ i).M.PosDef)
    (hbarpos :
      (ensembleAverageQuantum
        (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)).M.PosDef) :
    ∑ i, p i * vonNeumannEntropy (ρ i)
      ≤ vonNeumannEntropy
          (ensembleAverageQuantum (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)) := by
  set ρbar := ensembleAverageQuantum (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)
    with hρbar_def
  -- The matrix of ρ̄ is the convex combination `∑ p_i ρ_i`.
  have hρbarM : ρbar.M = ∑ i, ((p i : ℂ)) • (ρ i).M := by
    rw [hρbar_def, ensembleAverageQuantum_M]
    rfl
  exact vonNeumann_concave p hp_nn hp_sum ρ ρbar hρbarM hρpos hbarpos

/-! ## 7. Holevo χ ≥ 0 as a real theorem (full-rank locus) -/

/-- **`0 ≤ χ` — Holevo non-negativity as a REAL theorem.**

    On the full-rank locus (component states and average all
    positive-definite), the Holevo χ-quantity is non-negative.  This
    routes the genuine concavity bound `vonNeumann_concave` through
    the entropy-difference form of χ — it is `holevoChi ≥ 0` with no
    remaining concavity hypothesis. -/
theorem holevoChi_nonneg
    {N : ℕ} (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (hρpos : ∀ i, (ρ i).M.PosDef)
    (hbarpos :
      (ensembleAverageQuantum
        (HolevoBound.mkEnsemble p hp_nn hp_sum ρ)).M.PosDef) :
    0 ≤ HolevoBound.holevoChi p hp_nn hp_sum ρ := by
  rw [HolevoBound.holevoChi_eq_entropy_difference]
  have h := vonNeumannConcavity_of_posDef p hp_nn hp_sum ρ hρpos hbarpos
  -- `holevoChi = S(ρ̄) − ∑ p_i S(ρ_i) ≥ 0`.
  linarith

/-! ## 8. Axiom audit -/

-- VERIFIED: every theorem below depends ONLY on the standard Lean 4 /
-- Mathlib core triple {propext, Classical.choice, Quot.sound} —
-- no `sorry`, no custom `axiom`.  Uncomment to re-verify.

-- #print axioms re_trace_mul_operatorLog_self
-- #print axioms weighted_umegaki_eq_holevoChi
-- #print axioms vonNeumann_concave
-- #print axioms vonNeumannConcavity_of_posDef
-- #print axioms holevoChi_nonneg

end UnifiedTheory.LayerB.VonNeumannConcavity
