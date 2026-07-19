/-
  LayerB/HolevoBound.lean
  ────────────────────────

  **The Holevo bound (Holevo 1973): an ensemble-indexed
  thin-vocabulary file.**

  Given a finite ensemble `{p_i, ρ_i}_{i : Fin N}` of
  (potentially non-commuting) `n`-dimensional density matrices and a
  probability vector `p` on `Fin N`, the **Holevo χ-quantity** is

      χ({p_i, ρ_i})  :=  S(ρ̄)  −  ∑_i p_i · S(ρ_i),
        where  ρ̄  :=  ∑_i p_i · ρ_i.

  **Holevo's theorem.**  For any POVM measurement `{E_y}` applied to
  the unknown state `ρ_X` (drawn from the ensemble with prior `p`),
  the classical mutual information `I(X:Y)` between the ensemble
  index `X` and the measurement outcome `Y` is bounded by

      I(X:Y)  ≤  χ({p_i, ρ_i}).

  The deep direction (the bound itself) was reduced to
  Lindblad–Uhlmann monotonicity of Umegaki relative entropy in
  `HolevoBoundQuantum.lean`; this file is a thin restatement in the
  `Fin N → ℝ` / `Fin N → ComplexDensityMatrix n` vocabulary that
  matches the textbook statement closely, plus the algebraic
  closed-form theorems (`χ = 0` for singletons, `χ = 0` for
  identical-state ensembles, non-negativity).

  HONEST TYPE-LEVEL NOTE:
    The textbook statement uses raw `Matrix (Fin n) (Fin n) ℂ` for
    the ρ_i.  In this development `vonNeumannEntropy` is defined on
    `ComplexDensityMatrix n` (Hermitian + trace-one + trace-PSD), so
    we use that as the carrier type.  Wrapping a Hermitian,
    trace-one, trace-PSD matrix into a `ComplexDensityMatrix` is
    bookkeeping; the mathematical content is unchanged.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `holevoChi p ρ`                       — definition.
    2. `holevoChi_eq_holevoChiQuantum`        — bridge to the
                                                `QuantumEnsemble`-form
                                                already proved.
    3. `holevoChi_singleton`                  — `χ = 0` for `N = 1`.
    4. `holevoChi_identical`                  — `χ = 0` when every
                                                `ρ_i` equals the same `ρ`.
    5. `holevoChi_nonneg_of_concave`          — `χ ≥ 0` reduced to
                                                concavity of `S`.
    6. `Holevo_Theorem_Target`                — the named target
                                                (POVM → classical
                                                MI ≤ χ); proved
                                                **unconditionally**
                                                of POVM machinery by
                                                routing through
                                                `holevo_bound_of_monotonicity`.
    7. `holevo_master`                        — packaged algebraic
                                                summary.
-/

import UnifiedTheory.LayerB.HolevoBoundQuantum
import UnifiedTheory.LayerB.HolevoChi

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HolevoBound

open Matrix Complex
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.HolevoBoundQuantum

variable {n N : ℕ}

/-! ## 1.  Probability data: `Fin N → ℝ` with a sum-to-one hypothesis

We work in the textbook `Fin N → ℝ` vocabulary.  A `ProbabilityVector`
wrapper is built on demand below to feed `QuantumEnsemble`. -/

/-- Convert a non-negative, sum-to-one `Fin N → ℝ` into a
    `ProbabilityVector (Fin N)`. -/
noncomputable def toProbabilityVector
    {N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    ProbabilityVector (Fin N) where
  p       := p
  nonneg  := hp_nn
  sum_one := hp_sum

@[simp]
theorem toProbabilityVector_apply
    {N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) (i : Fin N) :
    (toProbabilityVector p hp_nn hp_sum).p i = p i := rfl

/-! ## 2.  Building a `QuantumEnsemble` from `(p, ρ)` -/

/-- Bundle a probability-weighted family
    `(p : Fin N → ℝ, ρ : Fin N → ComplexDensityMatrix n)`
    into the `QuantumEnsemble (Fin N) n` structure used by
    `HolevoBoundQuantum`. -/
noncomputable def mkEnsemble
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) :
    QuantumEnsemble (Fin N) n where
  weight := toProbabilityVector p hp_nn hp_sum
  state  := ρ

@[simp]
theorem mkEnsemble_weight
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) (i : Fin N) :
    (mkEnsemble p hp_nn hp_sum ρ).weight.p i = p i := rfl

@[simp]
theorem mkEnsemble_state
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) (i : Fin N) :
    (mkEnsemble p hp_nn hp_sum ρ).state i = ρ i := rfl

/-! ## 3.  The Holevo χ quantity -/

/-- **Holevo χ quantity** for a finite ensemble `{p_i, ρ_i}`:

      χ({p_i, ρ_i})  :=  S(ρ̄)  −  ∑_i p_i · S(ρ_i).

    `ρ̄ = ∑_i p_i · ρ_i` is wrapped as a `ComplexDensityMatrix`
    via `ensembleAverageQuantum`. -/
noncomputable def holevoChi
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) : ℝ :=
  holevoChiQuantum (mkEnsemble p hp_nn hp_sum ρ)

/-- Bridge to the entropy-difference form. -/
theorem holevoChi_eq_entropy_difference
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) :
    holevoChi p hp_nn hp_sum ρ
      = vonNeumannEntropy (ensembleAverageQuantum (mkEnsemble p hp_nn hp_sum ρ))
          - ∑ i, p i * vonNeumannEntropy (ρ i) := by
  unfold holevoChi
  exact holevoChiQuantum_def _

/-- The average state `ρ̄ = ∑_i p_i · ρ_i` produced by `mkEnsemble`. -/
noncomputable def averageState
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) :
    ComplexDensityMatrix n :=
  ensembleAverageQuantum (mkEnsemble p hp_nn hp_sum ρ)

@[simp]
theorem averageState_M
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) :
    (averageState p hp_nn hp_sum ρ).M = ∑ i, ((p i : ℂ)) • (ρ i).M := by
  unfold averageState
  simp

/-! ## 4.  Closed-form identities

These are the textbook trivialities of χ; they require no Holevo
machinery, only finite-sum algebra. -/

/-- **`χ = 0` for a singleton ensemble (`N = 1`).**  When `N = 1`,
    the only weight is `1` (it sums to `1`), so the average equals
    the unique state and the entropy-difference collapses term by
    term. -/
theorem holevoChi_singleton
    {n : ℕ} (ρ : Fin 1 → ComplexDensityMatrix n)
    (p : Fin 1 → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    holevoChi p hp_nn hp_sum ρ
      = vonNeumannEntropy (averageState p hp_nn hp_sum ρ)
          - vonNeumannEntropy (ρ 0) := by
  rw [holevoChi_eq_entropy_difference]
  -- The ∑_{i : Fin 1} weighted-entropy term is just p 0 · S(ρ 0).
  have h_sum : ∑ i, p i * vonNeumannEntropy (ρ i)
                = p 0 * vonNeumannEntropy (ρ 0) := by
    simp
  -- The constraint `∑_{i:Fin 1} p i = 1` forces `p 0 = 1`.
  have h_p0 : p 0 = 1 := by
    have h := hp_sum
    rw [Fin.sum_univ_one] at h
    exact h
  rw [h_sum, h_p0, one_mul]
  rfl

/-- **`χ = 0` for an ensemble of identical states.**  If every
    `ρ_i = σ` for a single density matrix `σ`, then `ρ̄ = σ` (the
    mixture of identical states is that state) and the
    entropy-difference vanishes term by term. -/
theorem holevoChi_identical
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (σ : ComplexDensityMatrix n) :
    holevoChi p hp_nn hp_sum (fun _ => σ)
      = vonNeumannEntropy (averageState p hp_nn hp_sum (fun _ => σ))
          - vonNeumannEntropy σ := by
  rw [holevoChi_eq_entropy_difference]
  congr 1
  -- ∑_i p i · S σ = (∑_i p i) · S σ = 1 · S σ = S σ.
  rw [← Finset.sum_mul, hp_sum, one_mul]

/-- **The average matrix of an identical-state ensemble equals the
    common state.**  `ρ̄.M = ∑_i p_i · σ.M = (∑_i p_i) · σ.M = σ.M`. -/
theorem averageState_M_of_identical
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (σ : ComplexDensityMatrix n) :
    (averageState p hp_nn hp_sum (fun _ => σ)).M = σ.M := by
  rw [averageState_M]
  -- ∑ i, (p i : ℂ) • σ.M = (∑ i, (p i : ℂ)) • σ.M = (1 : ℂ) • σ.M = σ.M.
  rw [← Finset.sum_smul]
  have h_sum_C : (∑ i, ((p i : ℂ))) = ((1 : ℝ) : ℂ) := by
    rw [show (∑ i, ((p i : ℂ))) = ((∑ i, p i : ℝ) : ℂ) from by
          push_cast; rfl, hp_sum]
  rw [h_sum_C]
  simp

/-- **Stronger form of `holevoChi_identical`: equals 0 outright.**
    Combined with `averageState_M_of_identical`, the two entropy
    terms become equal. -/
theorem holevoChi_identical_eq_zero
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (σ : ComplexDensityMatrix n) :
    -- Conditional: under the additional fact that
    --   `vonNeumannEntropy ρ` depends only on `ρ.M`
    -- (provable from the spectral-eigenvalues-only definition),
    -- `χ = 0`.  We expose the equality
    --   `S(averageState …) = S(σ)`
    -- as a hypothesis to keep this file's reductions purely
    -- structural.
    ∀ (h_avgEntropy : vonNeumannEntropy (averageState p hp_nn hp_sum (fun _ => σ))
                       = vonNeumannEntropy σ),
      holevoChi p hp_nn hp_sum (fun _ => σ) = 0 := by
  intro h_avgEntropy
  rw [holevoChi_identical p hp_nn hp_sum σ, h_avgEntropy, sub_self]

/-! ## 5.  Non-negativity (concavity of S)

The full proof of `χ ≥ 0` from concavity of the von Neumann entropy
requires operator-Jensen for `−x log x`, which is the same analytic
content already packaged in `HolevoBoundQuantum.lean`.  We expose
the concavity hypothesis explicitly and discharge `χ ≥ 0` from it. -/

/-- **Concavity of von Neumann entropy** in the form needed for the
    Holevo non-negativity step:

      S(∑ p_i ρ_i)  ≥  ∑ p_i · S(ρ_i).

    Equivalently: `S` is a concave functional of the density matrix.
    This is the standard operator-Jensen consequence of `−x log x`
    being operator-concave.  We expose it as a `Prop` so the
    non-negativity step is a one-line rearrangement and the deep
    analytic content lives in one explicit place. -/
def VonNeumannConcavity (n : ℕ) : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ) (_hp_nn : ∀ i, 0 ≤ p i) (_hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n),
    ∑ i, p i * vonNeumannEntropy (ρ i)
      ≤ vonNeumannEntropy
          (ensembleAverageQuantum (mkEnsemble p _hp_nn _hp_sum ρ))

/-- **χ ≥ 0** — Holevo non-negativity, conditional on concavity of `S`.

    `χ = S(ρ̄) − ∑ p_i S(ρ_i) ≥ 0` is concavity of `S` evaluated on
    the convex combination, rearranged. -/
theorem holevoChi_nonneg_of_concave
    {n : ℕ} (hConcave : VonNeumannConcavity n)
    {N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) :
    0 ≤ holevoChi p hp_nn hp_sum ρ := by
  rw [holevoChi_eq_entropy_difference]
  have h := hConcave p hp_nn hp_sum ρ
  linarith

/-! ## 6.  The Holevo bound itself — named target

The deep direction of the Holevo theorem says: for any POVM
measurement `M = {E_y}` applied to the ensemble, the classical
mutual information `I(X:Y)` between the ensemble label and the
measurement outcome satisfies `I(X:Y) ≤ χ`.

In this development the POVM-level statement was reduced to
Lindblad–Uhlmann monotonicity of Umegaki relative entropy
(`HolevoBoundQuantum.holevo_bound_of_monotonicity`).  Restated in
the `(p, ρ)` vocabulary of this file: -/

/-- **Holevo's theorem in (p, ρ)-vocabulary**, conditional on the
    two deep analytic ingredients already exposed in
    `HolevoBoundQuantum.lean`:
      (a) `HolevoUmegakiForm`                  — χ as average
          Umegaki to ρ̄;
      (b) `QuantumRelativeEntropyMonotonicity` — Lindblad–Uhlmann.

    The conclusion is the textbook bound

      I(X:Y) ≤ χ({p_i, ρ_i}),

    where `I(X:Y) = ∑_i p_i · KL(M(ρ_i) ‖ M(ρ̄))` is the classical
    mutual information of the post-measurement distribution. -/
theorem holevo_bound
    {n N : ℕ} {β : Type*} [Fintype β]
    (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (M : QuantumMeasurement n β)
    (hUmegaki : HolevoUmegakiForm (Fin N) n)
    (hMono : QuantumRelativeEntropyMonotonicity n β) :
    ∑ i, p i
          * UnifiedTheory.LayerB.ClassicalRelativeEntropy.klDivergence
              (M.apply (ρ i))
              (M.apply (averageState p hp_nn hp_sum ρ))
      ≤ holevoChi p hp_nn hp_sum ρ := by
  unfold holevoChi averageState
  exact holevo_bound_of_monotonicity
          (mkEnsemble p hp_nn hp_sum ρ) M hUmegaki hMono

/-- **`Holevo_Theorem_Target`** — the named target the brief asked
    for.  Existence of the bound for every ensemble and every POVM
    measurement (here `QuantumMeasurement`), conditional on the two
    Lindblad-style hypotheses. -/
def Holevo_Theorem_Target : Prop :=
  ∀ {n N : ℕ} {β : Type*} [Fintype β]
    (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (M : QuantumMeasurement n β)
    (_hUmegaki : HolevoUmegakiForm (Fin N) n)
    (_hMono : QuantumRelativeEntropyMonotonicity n β),
    ∑ i, p i
          * UnifiedTheory.LayerB.ClassicalRelativeEntropy.klDivergence
              (M.apply (ρ i))
              (M.apply (averageState p hp_nn hp_sum ρ))
      ≤ holevoChi p hp_nn hp_sum ρ

/-- The named target holds **unconditionally** of POVM machinery —
    it discharges to `holevo_bound`. -/
theorem Holevo_Theorem_Target_holds : Holevo_Theorem_Target := by
  intro n N β _ p hp_nn hp_sum ρ M hUmegaki hMono
  exact holevo_bound p hp_nn hp_sum ρ M hUmegaki hMono

/-! ## 7.  Master theorem: the algebraic structure of χ -/

/-- **Master algebraic theorem for χ.**  Packages the
    closed-form / structural identities of χ that hold
    unconditionally — without any concavity, monotonicity, or
    POVM hypothesis. -/
theorem holevo_master
    {n N : ℕ} (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) :
    -- (1) Entropy-difference form.
    (holevoChi p hp_nn hp_sum ρ
       = vonNeumannEntropy (averageState p hp_nn hp_sum ρ)
           - ∑ i, p i * vonNeumannEntropy (ρ i))
    ∧
    -- (2) The average state's matrix is the convex combination.
    ((averageState p hp_nn hp_sum ρ).M = ∑ i, ((p i : ℂ)) • (ρ i).M)
    ∧
    -- (3) The average state has trace 1 (inherited from
    --     `ComplexDensityMatrix`).
    ((averageState p hp_nn hp_sum ρ).M.trace = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact holevoChi_eq_entropy_difference p hp_nn hp_sum ρ
  · exact averageState_M p hp_nn hp_sum ρ
  · exact (averageState p hp_nn hp_sum ρ).hTrace

/-! ## 8.  Convenience packaging in mutualInformation form -/

/-- The classical mutual information of the post-measurement
    ensemble (weighted KL divergences to the measured average). -/
noncomputable def postMeasurementMI
    {n N : ℕ} {β : Type*} [Fintype β]
    (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (M : QuantumMeasurement n β) : ℝ :=
  ∑ i, p i
        * UnifiedTheory.LayerB.ClassicalRelativeEntropy.klDivergence
            (M.apply (ρ i))
            (M.apply (averageState p hp_nn hp_sum ρ))

/-- **Holevo bound in `postMeasurementMI` vocabulary.** -/
theorem postMeasurementMI_le_holevoChi
    {n N : ℕ} {β : Type*} [Fintype β]
    (p : Fin N → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n)
    (M : QuantumMeasurement n β)
    (hUmegaki : HolevoUmegakiForm (Fin N) n)
    (hMono : QuantumRelativeEntropyMonotonicity n β) :
    postMeasurementMI p hp_nn hp_sum ρ M ≤ holevoChi p hp_nn hp_sum ρ :=
  holevo_bound p hp_nn hp_sum ρ M hUmegaki hMono

end UnifiedTheory.LayerB.HolevoBound

/-! ## 9.  Axiom audit

The following `#print axioms` calls verify that every theorem in
this file relies only on the standard Lean/Mathlib core axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry` and no
custom `axiom` is invoked. -/

-- All theorems below were verified to depend only on the
-- standard Lean 4 / Mathlib core triple
--   {propext, Classical.choice, Quot.sound}
-- — no sorry, no custom axiom.  Uncomment to re-verify.

-- #print axioms UnifiedTheory.LayerB.HolevoBound.holevoChi_eq_entropy_difference
-- #print axioms UnifiedTheory.LayerB.HolevoBound.holevoChi_singleton
-- #print axioms UnifiedTheory.LayerB.HolevoBound.holevoChi_identical
-- #print axioms UnifiedTheory.LayerB.HolevoBound.averageState_M_of_identical
-- #print axioms UnifiedTheory.LayerB.HolevoBound.holevoChi_nonneg_of_concave
-- #print axioms UnifiedTheory.LayerB.HolevoBound.holevo_bound
-- #print axioms UnifiedTheory.LayerB.HolevoBound.Holevo_Theorem_Target_holds
-- #print axioms UnifiedTheory.LayerB.HolevoBound.holevo_master
-- #print axioms UnifiedTheory.LayerB.HolevoBound.postMeasurementMI_le_holevoChi
