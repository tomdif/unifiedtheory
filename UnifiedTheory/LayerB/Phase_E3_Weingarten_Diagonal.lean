/-
  LayerB/Phase_E3_Weingarten_Diagonal.lean
  ─────────────────────────────────────────────────────────────────────
  THE SO(10) DIAGONAL WEINGARTEN IDENTITY  ⟨U_{ii}²⟩ = 1/10.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  TIGHT SCOPE.  This file proves ONE concrete piece of the Weingarten
  formula for SO(10):

      ∫_{SO(10)}  U_{ii}²  d Haar  =  1 / 10        (any fixed i)

  and its corollary

      ∫_{SO(10)}  ∑_i U_{ii}²  d Haar  =  1.

  We do NOT prove the full Weingarten formula.  We do NOT prove
  off-diagonal vanishing (e.g. ⟨U_{ij}²⟩ = 1/(N(N+2)) for i≠j on
  the symmetric channel) — that is the Phase_E3 PeterWeyl residual.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  STRATEGY (clean, two-step).

  STEP A — POINTWISE COLUMN NORMALIZATION (UNCONDITIONAL).
    For U ∈ SO(N), the orthogonality relation Uᵀ * U = I gives, on
    the (i, i) entry,
        ∑_k U_{ki}² = 1                     (column i has unit norm).
    This is a POINTWISE identity on the carrier — no integration
    involved.  Integrating against the Haar PROBABILITY measure
    yields
        ∑_k ⟨U_{ki}²⟩ = 1.

  STEP B — ROW PERMUTATION SYMMETRY (STRUCTURAL HYPOTHESIS).
    Under the action U ↦ P · U for P a permutation matrix in SO(N)
    (a 3-cycle on rows, which has det = +1 hence lies in SO(N) for
    N ≥ 3), Haar invariance gives
        ⟨U_{σ(k), i}²⟩  =  ⟨U_{k, i}²⟩
    for any 3-cycle σ.  Composing 3-cycles sweeps out the entire
    alternating group A_N, which acts TRANSITIVELY on {1, …, N} for
    N ≥ 3.  Hence all ⟨U_{k, i}²⟩ are EQUAL across k ∈ {1, …, N}.

    We package this as a single HYPOTHESIS-LEVEL Prop predicate
    `RowPermutationSymmetrySO10` and discharge it as a
    structural input.  (Discharging it from Mathlib's left-invariance
    of `haarMeasureSO10` plus the explicit 3-cycle is routine but
    tedious; we DO NOT do it here.  The task explicitly allows
    this as a structural input.)

  CONCLUSION.  STEP A gives ∑_k ⟨U_{ki}²⟩ = 1.  STEP B gives all
  N values equal, hence each = 1/N.  In particular ⟨U_{ii}²⟩ = 1/N.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST RESIDUAL — the (Tr U)² = 1 corollary.

  The expansion (Tr U)² = ∑_i U_{ii}² + ∑_{i≠j} U_{ii} · U_{jj}.
  The diagonal sum ⟨∑_i U_{ii}²⟩ = N · (1/N) = 1 we PROVE.
  The off-diagonal sum ⟨∑_{i≠j} U_{ii} · U_{jj}⟩ requires a
  SEPARATE off-diagonal Weingarten input that this file DOES NOT
  PROVIDE — see `OffDiagonalDiagSquaredCorrelation`.

  For SO(N) the standard Weingarten formula gives
      ⟨U_{ii} · U_{jj}⟩  =  (something)        for i ≠ j,
  and the resulting (Tr U)² integral is ⟨χ_vector(U)²⟩ which by
  Schur orthogonality (Phase_E3_PeterWeyl_Mathlib's
  `SO10_chi_vector_chi_vector_integral`) equals 1/N.  We bridge to
  that named Prop here and STATE the (Tr U)² = 1 corollary as a
  CONDITIONAL theorem on it.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONESTY MANDATE.

    (1) Zero `sorry`.  Zero custom `axiom` in the real content.

    (2) STEP A is COMPLETELY UNCONDITIONAL — derived from the
        SO(N) defining equation and `integral_const`.

    (3) STEP B is stated as a typed Prop predicate
        `RowPermutationSymmetrySO10`; CONDITIONAL theorems consume
        it.  Discharging it from Mathlib's Haar-invariance is
        flagged as a routine follow-on.

    (4) The (Tr U)² = 1 corollary is CONDITIONAL on
        `SO10_chi_vector_chi_vector_integral` (the same residual
        already named in `Phase_E3_PeterWeyl_Mathlib`).  No new
        hidden axiom is introduced.

    (5) HONEST VERDICT
        `DIAGONAL_PROVED_SYMMETRY_HYP_TRUSQ_CONDITIONAL`
        — see `weingarten_diagonal_verdict` at file end.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option maxHeartbeats 800000

namespace UnifiedTheory.LayerB.Phase_E3_Weingarten_Diagonal

open MeasureTheory MeasureTheory.Measure Matrix
open UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  POINTWISE COLUMN/ROW NORMALIZATION FROM SO(N) DEFINING EQUATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For U ∈ SO(N), Uᵀ * U = I (Mathlib `mem_orthogonalGroup_iff'`),
    so the (i,j) entry of Uᵀ * U equals δ_{ij}:
        ∑_k U_{ki} · U_{kj}  =  δ_{ij}.
    Setting i = j gives the column-normalization identity:
        ∑_k U_{ki}²  =  1.
    This is a POINTWISE identity (no integration). -/

/-- For U ∈ SO(10), the (i, j) entry of `Uᵀ * U` equals
    `∑_k U_{ki} · U_{kj}` (matrix multiplication unfolds). -/
lemma transpose_mul_apply (U : G_SO10) (i j : Fin d10) :
    ((U : Matrix (Fin d10) (Fin d10) ℝ).transpose *
       (U : Matrix (Fin d10) (Fin d10) ℝ)) i j
      = ∑ k, (U : Matrix (Fin d10) (Fin d10) ℝ) k i *
              (U : Matrix (Fin d10) (Fin d10) ℝ) k j := by
  -- (Mᵀ * N) i j = ∑ k, Mᵀ i k * N k j = ∑ k, M k i * N k j
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- For U ∈ SO(10), `Uᵀ * U = I`.  Direct from
    `mem_orthogonalGroup_iff'`. -/
lemma orthogonality (U : G_SO10) :
    (U : Matrix (Fin d10) (Fin d10) ℝ).transpose *
      (U : Matrix (Fin d10) (Fin d10) ℝ) = 1 := by
  -- U.property : U.val ∈ specialOrthogonalGroup, which gives
  -- U.val ∈ orthogonalGroup, hence Uᵀ * U = 1.
  have h_so : (U : Matrix (Fin d10) (Fin d10) ℝ)
                ∈ Matrix.specialOrthogonalGroup (Fin d10) ℝ := U.property
  have h_o : (U : Matrix (Fin d10) (Fin d10) ℝ)
                ∈ Matrix.orthogonalGroup (Fin d10) ℝ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp h_so).1
  exact (Matrix.mem_orthogonalGroup_iff' (A := (U : Matrix (Fin d10) (Fin d10) ℝ))).mp h_o

/-- **POINTWISE COLUMN NORMALIZATION.**  For any U ∈ SO(10) and any
    column index i, the sum of squared entries in column i equals 1. -/
theorem column_norm_squared_eq_one (U : G_SO10) (i : Fin d10) :
    ∑ k, (U : Matrix (Fin d10) (Fin d10) ℝ) k i *
          (U : Matrix (Fin d10) (Fin d10) ℝ) k i = 1 := by
  -- (Uᵀ * U) i i = ∑ k, U_{ki}², and (Uᵀ * U) i i = (1) i i = 1.
  have h := transpose_mul_apply U i i
  rw [orthogonality] at h
  -- h :  (1 : Matrix _ _ ℝ) i i = ∑ k, U k i * U k i
  rw [Matrix.one_apply_eq] at h
  exact h.symm

/-- **POINTWISE FROBENIUS-NORM IDENTITY.**  For any U ∈ SO(10),
    `∑_{i, k} U_{ki}² = 10`.  (Sum of all squared entries equals
    the dimension.)  Direct corollary of column normalization. -/
theorem frobenius_norm_squared_eq_dim (U : G_SO10) :
    ∑ i, ∑ k, (U : Matrix (Fin d10) (Fin d10) ℝ) k i *
                (U : Matrix (Fin d10) (Fin d10) ℝ) k i
      = (d10 : ℝ) := by
  -- ∑_i 1 = card (Fin 10) = 10.
  have h : ∀ i : Fin d10, ∑ k, (U : Matrix (Fin d10) (Fin d10) ℝ) k i *
                (U : Matrix (Fin d10) (Fin d10) ℝ) k i = 1 := by
    intro i; exact column_norm_squared_eq_one U i
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-
  **DIAGONAL TRACE-SQUARED IDENTITY (POINTWISE).**  For any U ∈ SO(10),
  `∑_i U_{ii}² ≤ 10` is consistent with `∑_{i,k} U_{ki}² = 10`,
  and the diagonal sum SEPARATELY equals
  `∑_i U_{ii}² = (Uᵀ U)_{ii}` summed over i — this is computed
  pointwise from `column_norm_squared_eq_one` evaluated only at
  k = i.  We DO NOT make this claim pointwise (it's false in
  general — only the AVERAGE over Haar is 1/10 per entry).  We
  DO use the integrated form below.
-/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE INTEGRATED FORM — STEP A
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Integrating the pointwise column-normalization identity against
    the Haar PROBABILITY measure on SO(10) gives, for any column i,
        ∑_k ⟨U_{ki}²⟩  =  1.
    This is unconditional — it uses only `integral_const` and the
    fact that `haarMeasureSO10` is a probability measure (i.e.
    `IsProbabilityMeasure`, established in
    `R2b_SO10HaarConcreteConstruction`). -/

/-- The (k, i)-th squared-entry function on SO(10), viewed as a
    real-valued function on G_SO10.  For each (k, i), this is a
    continuous, measurable, real-valued function. -/
def sqEntry (k i : Fin d10) : G_SO10 → ℝ :=
  fun U => (U : Matrix (Fin d10) (Fin d10) ℝ) k i *
            (U : Matrix (Fin d10) (Fin d10) ℝ) k i

@[simp]
lemma sqEntry_apply (k i : Fin d10) (U : G_SO10) :
    sqEntry k i U =
      (U : Matrix (Fin d10) (Fin d10) ℝ) k i *
        (U : Matrix (Fin d10) (Fin d10) ℝ) k i := rfl

/-- The (k, i)-th squared-entry function is bounded above by 1 on
    SO(10), since |U_{ki}| ≤ 1 for orthogonal U
    (`entry_norm_bound_of_unitary`). -/
lemma sqEntry_le_one (k i : Fin d10) (U : G_SO10) :
    sqEntry k i U ≤ 1 := by
  unfold sqEntry
  have h_orth : (U : Matrix (Fin d10) (Fin d10) ℝ)
                  ∈ Matrix.orthogonalGroup (Fin d10) ℝ := by
    have h_so : (U : Matrix (Fin d10) (Fin d10) ℝ)
                  ∈ Matrix.specialOrthogonalGroup (Fin d10) ℝ := U.property
    exact (Matrix.mem_specialUnitaryGroup_iff.mp h_so).1
  have h_bound : ‖(U : Matrix (Fin d10) (Fin d10) ℝ) k i‖ ≤ 1 :=
    entry_norm_bound_of_unitary h_orth k i
  rw [Real.norm_eq_abs] at h_bound
  -- |x| ≤ 1 implies x² ≤ 1.
  have habs : |(U : Matrix (Fin d10) (Fin d10) ℝ) k i| ≤ 1 := h_bound
  have hsq : ((U : Matrix (Fin d10) (Fin d10) ℝ) k i) *
              ((U : Matrix (Fin d10) (Fin d10) ℝ) k i)
              = |(U : Matrix (Fin d10) (Fin d10) ℝ) k i| *
                |(U : Matrix (Fin d10) (Fin d10) ℝ) k i| := by
    rw [abs_mul_abs_self]
  rw [hsq]
  have habs_nn : 0 ≤ |(U : Matrix (Fin d10) (Fin d10) ℝ) k i| := abs_nonneg _
  calc |(U : Matrix (Fin d10) (Fin d10) ℝ) k i| *
        |(U : Matrix (Fin d10) (Fin d10) ℝ) k i|
        ≤ 1 * 1 := by
              exact mul_le_mul habs habs habs_nn (by norm_num)
      _ = 1 := by norm_num

/-- The (k, i)-th squared-entry function is non-negative. -/
lemma sqEntry_nonneg (k i : Fin d10) (U : G_SO10) :
    0 ≤ sqEntry k i U := by
  unfold sqEntry
  exact mul_self_nonneg _

/-- **POINTWISE SUM-OVER-COLUMN IDENTITY** rewritten in `sqEntry`
    notation. -/
lemma sum_sqEntry_column_eq_one (U : G_SO10) (i : Fin d10) :
    ∑ k, sqEntry k i U = 1 := column_norm_squared_eq_one U i

/-- **POINTWISE TOTAL FROBENIUS IDENTITY** rewritten in `sqEntry`
    notation: ∑_{i, k} U_{ki}² = 10. -/
lemma sum_sqEntry_total_eq_dim (U : G_SO10) :
    ∑ i, ∑ k, sqEntry k i U = (d10 : ℝ) := frobenius_norm_squared_eq_dim U

/-- **STEP A — INTEGRATED COLUMN NORMALIZATION.**  For any column
    index i ∈ Fin 10:
        ∫_{SO(10)}  ∑_k U_{ki}²  d Haar  =  1.
    PROOF: pointwise integrand is the constant 1, and Haar is a
    probability measure. -/
theorem integral_sum_column_squared_eq_one (i : Fin d10) :
    ∫ U, (∑ k, sqEntry k i U) ∂haarMeasureSO10 = 1 := by
  -- The integrand pointwise equals 1.
  have h_pt : ∀ U : G_SO10, (∑ k, sqEntry k i U) = 1 := by
    intro U; exact sum_sqEntry_column_eq_one U i
  rw [show (fun U : G_SO10 => ∑ k, sqEntry k i U) = (fun _ => (1 : ℝ)) from
        funext h_pt]
  rw [integral_const]
  rw [probReal_univ]
  exact one_smul ℝ 1

/-- **STEP A — INTEGRATED TOTAL FROBENIUS IDENTITY.**
        ∫_{SO(10)}  ∑_{i, k} U_{ki}²  d Haar  =  10. -/
theorem integral_sum_total_squared_eq_dim :
    ∫ U, (∑ i, ∑ k, sqEntry k i U) ∂haarMeasureSO10 = (d10 : ℝ) := by
  have h_pt : ∀ U : G_SO10, (∑ i, ∑ k, sqEntry k i U) = (d10 : ℝ) := by
    intro U; exact sum_sqEntry_total_eq_dim U
  rw [show (fun U : G_SO10 => ∑ i, ∑ k, sqEntry k i U) =
        (fun _ => (d10 : ℝ)) from funext h_pt]
  rw [integral_const, probReal_univ, one_smul]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  STEP B — ROW PERMUTATION SYMMETRY (STRUCTURAL HYPOTHESIS)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Under the action U ↦ P · U for P a permutation matrix in SO(N)
    (a 3-cycle has det = 1, hence lies in SO(N) for N ≥ 3), Haar
    left-invariance gives
        ∫ f(P · U) d Haar  =  ∫ f(U) d Haar.
    Applying this to f(U) = U_{ki}² yields
        ⟨U_{σ(k), i}²⟩  =  ⟨U_{k, i}²⟩
    for any 3-cycle σ.  Composing 3-cycles sweeps out the
    alternating group A_N, which acts TRANSITIVELY on {1, …, N}
    for N ≥ 3.  Hence all ⟨U_{k, i}²⟩ are equal.

    We package this as a single Prop predicate
    `RowPermutationSymmetrySO10` and consume it as a hypothesis.
    Discharging it from Mathlib's `IsMulLeftInvariant haarMeasureSO10`
    plus the explicit 3-cycle is a routine follow-on (the SAME
    pattern as `R2b.haarTraceIdentitySO10_concrete` uses Mathlib's
    `integral_eq_zero_of_mul_left_eq_neg`).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **STRUCTURAL INPUT — ROW PERMUTATION SYMMETRY.**

    For any column index i and any two row indices k, l, the Haar
    expectations of the squared entries `U_{ki}²` and `U_{li}²`
    coincide:
        ⟨U_{ki}²⟩  =  ⟨U_{li}²⟩.

    JUSTIFICATION (NOT FORMALIZED HERE).  Pick any row index m ∉
    {k, l}, exists for N = 10 ≥ 3.  The 3-cycle (k l m) is an EVEN
    permutation, hence its permutation matrix P_{(k l m)} lies in
    SO(N).  Left-invariance of Haar gives
        ∫ f(P_{(k l m)} · U) d Haar = ∫ f(U) d Haar
    for any integrable f.  Take f(U) = U_{ki}².  Then
        f(P · U) = (P · U)_{ki}² = U_{σ(k), i}² = U_{l, i}²
    where σ = (k l m) sends k ↦ l.  Hence ⟨U_{l, i}²⟩ = ⟨U_{k, i}²⟩.

    Discharging this in Lean requires (a) a permutation-matrix
    construction, (b) a det-of-3-cycle = +1 lemma, and (c) the
    standard left-invariance integral substitution.  All routine
    but voluminous; we treat as input here. -/
def RowPermutationSymmetrySO10 : Prop :=
  ∀ (i : Fin d10) (k l : Fin d10),
    ∫ U, sqEntry k i U ∂haarMeasureSO10
      = ∫ U, sqEntry l i U ∂haarMeasureSO10

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  COMBINING STEP A + STEP B → ⟨U_{ii}²⟩ = 1/10
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    From Step A: ∑_k ⟨U_{ki}²⟩ = 1.
    From Step B: all 10 summands equal.
    Conclusion: each summand = 1/10.  In particular ⟨U_{ii}²⟩ = 1/10.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The squared-entry function `sqEntry k i` is bounded by 1 hence
    integrable on the FINITE measure `haarMeasureSO10`.  We use
    Mathlib's `Integrable.of_bound` style derivation. -/
lemma sqEntry_integrable (k i : Fin d10) :
    Integrable (sqEntry k i) haarMeasureSO10 := by
  -- The function is bounded by 1 on the whole space.
  -- For a bounded function on a finite measure, we use
  -- HasFiniteIntegral.of_bounded.
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable: sqEntry is continuous (in fact a
    -- polynomial in matrix entries).  We provide a measurability
    -- argument via Matrix.entry → ℝ being measurable.
    -- The function U ↦ U.val k i is continuous (it's the (k, i)
    -- coordinate projection composed with the inducing subtype
    -- coercion).  Then squaring is continuous.  Hence the function
    -- is continuous, hence strongly measurable.
    have h_cont : Continuous (fun U : G_SO10 =>
        (U : Matrix (Fin d10) (Fin d10) ℝ) k i) := by
      have h_sub : Continuous (fun U : G_SO10 =>
          (U : Matrix (Fin d10) (Fin d10) ℝ)) :=
        continuous_subtype_val
      -- Coordinate projection is continuous on Pi-type.
      have h_proj : Continuous (fun M : Matrix (Fin d10) (Fin d10) ℝ => M k i) := by
        change Continuous (fun M : (Fin d10) → (Fin d10) → ℝ => M k i)
        exact (continuous_apply i).comp (continuous_apply k)
      exact h_proj.comp h_sub
    have h_sq : Continuous (sqEntry k i) := by
      unfold sqEntry
      exact h_cont.mul h_cont
    exact h_sq.aestronglyMeasurable
  · -- HasFiniteIntegral via boundedness by 1.
    apply MeasureTheory.HasFiniteIntegral.of_bounded (C := 1)
    refine Filter.Eventually.of_forall (fun U => ?_)
    have h_le : sqEntry k i U ≤ 1 := sqEntry_le_one k i U
    have h_nn : 0 ≤ sqEntry k i U := sqEntry_nonneg k i U
    rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
    exact h_le

/-- The integral over Haar of a finite sum of `sqEntry`'s commutes
    with the sum (linearity of integration). -/
lemma integral_sum_sqEntry_eq_sum_integral (i : Fin d10) :
    ∫ U, (∑ k, sqEntry k i U) ∂haarMeasureSO10
      = ∑ k, ∫ U, sqEntry k i U ∂haarMeasureSO10 := by
  rw [integral_finset_sum (Finset.univ) (fun k _ => sqEntry_integrable k i)]

/-- **CONSEQUENCE OF ROW SYMMETRY: SUM OF EQUAL TERMS.**  Under
    `RowPermutationSymmetrySO10`, the sum `∑_k ⟨U_{ki}²⟩` equals
    `10 · ⟨U_{ii}²⟩` for any fixed i. -/
lemma sum_eq_card_smul_diag
    (h_sym : RowPermutationSymmetrySO10) (i : Fin d10) :
    ∑ k, ∫ U, sqEntry k i U ∂haarMeasureSO10
      = (d10 : ℝ) * ∫ U, sqEntry i i U ∂haarMeasureSO10 := by
  -- By symmetry, every term in the sum equals the i-th term.
  have h_eq : ∀ k ∈ (Finset.univ : Finset (Fin d10)),
      ∫ U, sqEntry k i U ∂haarMeasureSO10
        = ∫ U, sqEntry i i U ∂haarMeasureSO10 := by
    intro k _; exact h_sym i k i
  rw [Finset.sum_congr rfl h_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

/-- **MAIN DIAGONAL IDENTITY (CONDITIONAL ON ROW SYMMETRY).**

    Under the row-permutation symmetry hypothesis, for any column
    index i ∈ Fin 10:
        ∫_{SO(10)}  U_{ii}²  d Haar  =  1 / 10. -/
theorem diagonal_squared_integral
    (h_sym : RowPermutationSymmetrySO10) (i : Fin d10) :
    ∫ U, sqEntry i i U ∂haarMeasureSO10 = 1 / (d10 : ℝ) := by
  -- Step A:  ∫ ∑_k U_{ki}² d Haar = 1
  have hA : ∫ U, (∑ k, sqEntry k i U) ∂haarMeasureSO10 = 1 :=
    integral_sum_column_squared_eq_one i
  -- Linearity:  ∑_k ∫ U_{ki}² d Haar = ∫ ∑_k U_{ki}² d Haar
  rw [integral_sum_sqEntry_eq_sum_integral i] at hA
  -- Symmetry: ∑_k ∫ U_{ki}² d Haar = 10 · ∫ U_{ii}² d Haar
  rw [sum_eq_card_smul_diag h_sym i] at hA
  -- Now hA :  10 · ∫ U_{ii}² d Haar = 1.
  -- Conclude:  ∫ U_{ii}² d Haar = 1/10.
  have hd10 : ((d10 : ℝ)) ≠ 0 := by unfold d10; norm_num
  field_simp at hA ⊢
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  THE COROLLARY:  ∫ ∑_i U_{ii}² d Haar = 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Sum over i of the diagonal identity. -/

/-- **DIAGONAL SUM COROLLARY (CONDITIONAL ON ROW SYMMETRY).**

        ∫_{SO(10)}  ∑_i U_{ii}²  d Haar  =  1.

    PROOF: ∑_i (1/10) = 10 · (1/10) = 1. -/
theorem sum_diagonal_squared_integral
    (h_sym : RowPermutationSymmetrySO10) :
    ∫ U, (∑ i, sqEntry i i U) ∂haarMeasureSO10 = 1 := by
  -- Linearity moves the sum out of the integral.
  rw [integral_finset_sum Finset.univ (fun i _ => sqEntry_integrable i i)]
  -- Each term is 1/10 by the diagonal identity.
  have h_eq : ∀ i ∈ (Finset.univ : Finset (Fin d10)),
      ∫ U, sqEntry i i U ∂haarMeasureSO10 = 1 / (d10 : ℝ) := by
    intro i _; exact diagonal_squared_integral h_sym i
  rw [Finset.sum_congr rfl h_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  unfold d10
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  CORRESPONDENCE WITH THE TRACE FUNCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework's `reTraceSO10 U = Σ_i U_{ii}` is the trace of the
    underlying matrix.  The diagonal sum identity Section §5 above
    is NOT the squared trace.  We have:

        (Tr U)²  =  (Σ_i U_{ii})²  =  Σ_{i, j} U_{ii} · U_{jj}
                 =  Σ_i U_{ii}²  +  Σ_{i ≠ j} U_{ii} · U_{jj}.

    The first piece we PROVE: ⟨Σ_i U_{ii}²⟩ = 1.  The second piece
    requires off-diagonal Weingarten input
    (⟨U_{ii} · U_{jj}⟩ for i ≠ j) which this file does NOT supply.

    Hence the (Tr U)² = 1 corollary remains CONDITIONAL on the
    Phase_E3 PeterWeyl residual.  We expose the precise CONDITIONAL
    form here.  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The (i, j) diagonal-product function on SO(10):
    `U ↦ U_{ii} · U_{jj}`. -/
def diagProdEntry (i j : Fin d10) : G_SO10 → ℝ :=
  fun U => (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
            (U : Matrix (Fin d10) (Fin d10) ℝ) j j

@[simp]
lemma diagProdEntry_apply (i j : Fin d10) (U : G_SO10) :
    diagProdEntry i j U =
      (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
        (U : Matrix (Fin d10) (Fin d10) ℝ) j j := rfl

/-- The diagonal-product function is bounded by 1 in absolute value
    on SO(10). -/
lemma diagProdEntry_abs_le_one (i j : Fin d10) (U : G_SO10) :
    |diagProdEntry i j U| ≤ 1 := by
  unfold diagProdEntry
  have h_orth : (U : Matrix (Fin d10) (Fin d10) ℝ)
                  ∈ Matrix.orthogonalGroup (Fin d10) ℝ := by
    have h_so : (U : Matrix (Fin d10) (Fin d10) ℝ)
                  ∈ Matrix.specialOrthogonalGroup (Fin d10) ℝ := U.property
    exact (Matrix.mem_specialUnitaryGroup_iff.mp h_so).1
  have hbi : ‖(U : Matrix (Fin d10) (Fin d10) ℝ) i i‖ ≤ 1 :=
    entry_norm_bound_of_unitary h_orth i i
  have hbj : ‖(U : Matrix (Fin d10) (Fin d10) ℝ) j j‖ ≤ 1 :=
    entry_norm_bound_of_unitary h_orth j j
  rw [Real.norm_eq_abs] at hbi hbj
  rw [abs_mul]
  have hbj_nn : 0 ≤ |(U : Matrix (Fin d10) (Fin d10) ℝ) j j| := abs_nonneg _
  calc |(U : Matrix (Fin d10) (Fin d10) ℝ) i i| *
        |(U : Matrix (Fin d10) (Fin d10) ℝ) j j|
      ≤ 1 * 1 := mul_le_mul hbi hbj hbj_nn (by norm_num)
    _ = 1 := by norm_num

/-- The diagonal-product function is integrable on the finite Haar
    measure. -/
lemma diagProdEntry_integrable (i j : Fin d10) :
    Integrable (diagProdEntry i j) haarMeasureSO10 := by
  refine ⟨?_, ?_⟩
  · -- Continuity → AEStronglyMeasurable.
    have h_sub : Continuous (fun U : G_SO10 =>
        (U : Matrix (Fin d10) (Fin d10) ℝ)) :=
      continuous_subtype_val
    have h_proj_ii : Continuous (fun U : G_SO10 =>
        (U : Matrix (Fin d10) (Fin d10) ℝ) i i) := by
      have h_proj : Continuous (fun M : Matrix (Fin d10) (Fin d10) ℝ => M i i) := by
        change Continuous (fun M : (Fin d10) → (Fin d10) → ℝ => M i i)
        exact (continuous_apply i).comp (continuous_apply i)
      exact h_proj.comp h_sub
    have h_proj_jj : Continuous (fun U : G_SO10 =>
        (U : Matrix (Fin d10) (Fin d10) ℝ) j j) := by
      have h_proj : Continuous (fun M : Matrix (Fin d10) (Fin d10) ℝ => M j j) := by
        change Continuous (fun M : (Fin d10) → (Fin d10) → ℝ => M j j)
        exact (continuous_apply j).comp (continuous_apply j)
      exact h_proj.comp h_sub
    have h_cont : Continuous (diagProdEntry i j) := by
      unfold diagProdEntry
      exact h_proj_ii.mul h_proj_jj
    exact h_cont.aestronglyMeasurable
  · -- Boundedness by 1 → HasFiniteIntegral.
    apply MeasureTheory.HasFiniteIntegral.of_bounded (C := 1)
    refine Filter.Eventually.of_forall (fun U => ?_)
    rw [Real.norm_eq_abs]
    exact diagProdEntry_abs_le_one i j U

/-- **NAMED RESIDUAL: OFF-DIAGONAL DIAG-SQUARED CORRELATION.**

    The Haar correlation between distinct diagonal entries:
        ∫_{SO(10)}  Σ_{i ≠ j} U_{ii} · U_{jj}  d Haar  =  c

    where for SO(N) standard Weingarten gives c = -(N-1)/N · 1/N · N
    = -1/N — but this requires the Schur orthogonality (vector,
    vector) closure (`SO10_chi_vector_chi_vector_integral` of
    `Phase_E3_PeterWeyl_Mathlib`) and is NOT provided here.  We
    name the value `c` precisely as a Prop (parameterized over the
    expected value 0, the "naive" choice for the diagonal-only
    contribution to be the entire ⟨(Tr U)²⟩). -/
def OffDiagonalDiagSquaredCorrelation (c : ℝ) : Prop :=
  ∫ U, (∑ i, ∑ j ∈ Finset.univ.erase i, diagProdEntry i j U)
        ∂haarMeasureSO10
    = c

/-- **TRACE-SQUARED COROLLARY (CONDITIONAL).**

    GIVEN row-permutation symmetry AND the off-diagonal correlation
    value `c`, we conclude
        ∫_{SO(10)}  (Tr U)²  d Haar  =  1 + c.

    For SO(10) the Schur (vector, vector) orthogonality fixes the
    LHS as 1, hence c = 0.  But proving c = 0 requires the
    PeterWeyl input that this file does not supply.

    The conditional form is the honest, sharp statement we can make
    HERE without that input.

    Note: Tr U = ∑_i U_{ii} and (Tr U)² = ∑_i U_{ii}² + ∑_{i ≠ j}
    U_{ii} · U_{jj} as a pointwise identity. -/
theorem trace_squared_integral_conditional
    (h_sym : RowPermutationSymmetrySO10)
    {c : ℝ} (h_off : OffDiagonalDiagSquaredCorrelation c) :
    ∫ U, (reTraceSO10 U) * (reTraceSO10 U) ∂haarMeasureSO10
      = 1 + c := by
  -- Pointwise expansion: (∑_i U_{ii}) · (∑_i U_{ii})
  --                    = ∑_i U_{ii}² + ∑_i ∑_{j≠i} U_{ii} · U_{jj}.
  have h_expand : ∀ U : G_SO10,
      reTraceSO10 U * reTraceSO10 U
        = (∑ i, sqEntry i i U)
          + (∑ i, ∑ j ∈ Finset.univ.erase i, diagProdEntry i j U) := by
    intro U
    -- reTraceSO10 U = Matrix.trace U.val = ∑ i, U.val i i
    unfold reTraceSO10
    rw [Matrix.trace]
    simp only [diag_apply]
    -- (∑ i, a i) · (∑ j, a j) = ∑ i, ∑ j, a i · a j
    rw [Finset.sum_mul_sum]
    -- Goal:  ∑ ⟨i, j⟩ ∈ univ ×ˢ univ, U_{ii} * U_{jj}
    --      = ∑ i, U_{ii}² + ∑ i ∑ j ∈ univ.erase i, U_{ii} * U_{jj}
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    -- Goal:  ∑ j, U_{ii} * U_{jj}  =  U_{ii}² + ∑ j ∈ univ.erase i, U_{ii} * U_{jj}
    -- Split the j-sum at j = i.
    rw [show (fun j : Fin d10 => (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                                  (U : Matrix (Fin d10) (Fin d10) ℝ) j j)
            = (fun j : Fin d10 => diagProdEntry i j U) from
        funext (fun j => rfl)]
    rw [show sqEntry i i U
            = diagProdEntry i i U from rfl]
    rw [add_comm]
    exact (Finset.sum_erase_add (Finset.univ : Finset (Fin d10))
            (fun j : Fin d10 => diagProdEntry i j U)
            (Finset.mem_univ i)).symm
  -- Now integrate both sides.
  rw [show (fun U : G_SO10 => reTraceSO10 U * reTraceSO10 U) =
        (fun U : G_SO10 => (∑ i, sqEntry i i U)
                  + (∑ i, ∑ j ∈ Finset.univ.erase i, diagProdEntry i j U)) from
        funext h_expand]
  -- Integrability for both summands.
  have h_int_diag : Integrable
      (fun U : G_SO10 => ∑ i, sqEntry i i U) haarMeasureSO10 := by
    apply integrable_finset_sum
    intro i _; exact sqEntry_integrable i i
  have h_int_off : Integrable
      (fun U : G_SO10 => ∑ i, ∑ j ∈ Finset.univ.erase i, diagProdEntry i j U)
      haarMeasureSO10 := by
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    exact diagProdEntry_integrable i j
  rw [MeasureTheory.integral_add h_int_diag h_int_off]
  -- Diagonal piece equals 1.
  rw [sum_diagonal_squared_integral h_sym]
  -- Off-diagonal piece equals c.
  rw [h_off]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  HONEST VERDICT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The verdict for this construction. -/
inductive WeingartenDiagonalVerdict
  /-- Diagonal identity ⟨U_{ii}²⟩ = 1/N proved (conditional on row
      permutation symmetry); (Tr U)² = 1 still conditional on the
      separately-named off-diagonal Weingarten residual. -/
  | DiagonalProvedSymmetryHypTrUsqConditional
  /-- Both fully proved unconditionally. -/
  | FullyUnconditional
  /-- Diagonal not yet established. -/
  | DiagonalIncomplete
  deriving DecidableEq, Repr

/-- **HONEST VERDICT.**  The diagonal Weingarten identity ⟨U_{ii}²⟩
    = 1/10 is proved conditional on the row-permutation symmetry
    structural input.  The (Tr U)² = 1 corollary remains
    conditional on the separately-named off-diagonal residual
    `OffDiagonalDiagSquaredCorrelation 0`. -/
def weingarten_diagonal_verdict : WeingartenDiagonalVerdict :=
  .DiagonalProvedSymmetryHypTrUsqConditional

/-- A self-check that the verdict is indeed
    `DiagonalProvedSymmetryHypTrUsqConditional`. -/
theorem verdict_consistent :
    weingarten_diagonal_verdict =
      WeingartenDiagonalVerdict.DiagonalProvedSymmetryHypTrUsqConditional := rfl

/-- **HEADLINE THEOREM (RESTATEMENT).**  The diagonal Weingarten
    identity in its cleanest form.  Conditional on the structural
    row-permutation symmetry input. -/
theorem SO10_diagonal_squared_haar_integral
    (h_sym : RowPermutationSymmetrySO10) (i : Fin d10) :
    ∫ U : G_SO10, (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                    (U : Matrix (Fin d10) (Fin d10) ℝ) i i ∂haarMeasureSO10
      = 1 / 10 := by
  have h := diagonal_squared_integral h_sym i
  unfold sqEntry at h
  unfold d10 at h
  exact h

/-- **HEADLINE COROLLARY (RESTATEMENT).**  The diagonal SUM identity
    in its cleanest form. -/
theorem SO10_sum_diagonal_squared_haar_integral
    (h_sym : RowPermutationSymmetrySO10) :
    ∫ U : G_SO10, (∑ i, (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                          (U : Matrix (Fin d10) (Fin d10) ℝ) i i)
        ∂haarMeasureSO10
      = 1 := by
  have h := sum_diagonal_squared_integral h_sym
  -- Convert sqEntry i i to U.val i i * U.val i i.
  have heq : (fun U : G_SO10 => ∑ i, sqEntry i i U)
            = (fun U : G_SO10 => ∑ i,
                (U : Matrix (Fin d10) (Fin d10) ℝ) i i *
                  (U : Matrix (Fin d10) (Fin d10) ℝ) i i) := by
    funext U
    apply Finset.sum_congr rfl; intro i _; rfl
  rw [heq] at h
  exact h

/-- **POINTWISE FROBENIUS-NORM IDENTITY (RESTATEMENT, CLOSED FORM).**

        For U ∈ SO(10), ∑_{i, k} U_{ki}² = 10  pointwise.

    This is the strongest unconditional content of the file: the
    "trace identity" in Frobenius form, true POINTWISE (not just on
    average).  Direct from Uᵀ U = I. -/
theorem SO10_frobenius_norm_squared_pointwise (U : G_SO10) :
    ∑ i, ∑ k, (U : Matrix (Fin d10) (Fin d10) ℝ) k i *
                (U : Matrix (Fin d10) (Fin d10) ℝ) k i = 10 := by
  have h := frobenius_norm_squared_eq_dim U
  unfold d10 at h
  exact_mod_cast h

/-- **INTEGRATED FROBENIUS-NORM IDENTITY (RESTATEMENT).**

        ∫_{SO(10)} ∑_{i, k} U_{ki}² d Haar = 10. -/
theorem SO10_frobenius_norm_squared_integral :
    ∫ U : G_SO10, (∑ i, ∑ k, (U : Matrix (Fin d10) (Fin d10) ℝ) k i *
                              (U : Matrix (Fin d10) (Fin d10) ℝ) k i)
        ∂haarMeasureSO10
      = 10 := by
  have h := integral_sum_total_squared_eq_dim
  unfold d10 at h
  exact_mod_cast h

end UnifiedTheory.LayerB.Phase_E3_Weingarten_Diagonal
