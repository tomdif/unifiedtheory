/-
  LayerB/UmegakiMultiConvex.lean
  ───────────────────────────────

  **N-fold joint convexity of the Umegaki relative entropy.**

  Lifts the binary joint convexity hypothesis
  `JointConvexity_RelEntropy_Target` (defined in
  `LayerB/PartialTraceDPIFull.lean`) to a finite probability vector
  of arbitrary length:

      S( Σ_i p_i ρ_i ‖ Σ_i p_i σ_i )  ≤  Σ_i p_i · S( ρ_i ‖ σ_i )

  for `p : Fin N → ℝ` with `p_i ≥ 0` and `Σ p_i = 1`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT (NON-NEGOTIABLE): zero `sorry`, zero custom
  `axiom`.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  ## Proof strategy

  Induction on `N`:

    • `N = 0`: vacuous (the hypothesis `Σ_{i : Fin 0} p i = 1`
      reduces to `0 = 1` and is unsatisfiable).
    • `N = 1`: collapse — the unique weight equals `1` so both
      sides equal `S(ρ₀ ‖ σ₀)`.
    • `N + 1 → N + 2`: split off the first component
      `p 0` via the binary joint convexity hypothesis.  If
      `p 0 = 1`, the tail weights all vanish and the inequality
      collapses to the `N = 1`-style case.  If `p 0 < 1`, let
      `q := 1 - p 0 ∈ (0, 1]` and `r i := p (i.succ) / q` be the
      renormalised tail weights (which sum to `1`).  Then

        Σ_{i : Fin (N+2)} p_i · A_i
          = p 0 · A 0 + q · ( Σ_{i : Fin (N+1)} r_i · A_{i.succ} )

      and the binary 2-fold joint convexity dominates the right
      summand by the inductive hypothesis applied to the tail.

  ## Build target

      `lake build UnifiedTheory.LayerB.UmegakiMultiConvex`
-/

import UnifiedTheory.LayerB.JointConvexityUmegaki
import UnifiedTheory.LayerB.PartialTraceDPIFull
import UnifiedTheory.LayerB.PartialTraceDecomposition

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.UmegakiMultiConvex

open Matrix Complex
open scoped MatrixOrder ComplexOrder BigOperators
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.JointConvexityUmegaki
open UnifiedTheory.LayerB.PartialTraceDPI
open UnifiedTheory.LayerB.PartialTraceDPIFull
open UnifiedTheory.LayerB.PartialTraceDecomposition

/-! ## 1.  The N-fold convex combination of density matrices.

We build the convex combination at the `ComplexDensityMatrix`
level, given a probability vector `p : Fin N → ℝ` (nonneg,
sums to 1) and a family `ρ : Fin N → ComplexDensityMatrix m`.
The Hermitian/trace-1/trace-PSD fields all follow from the
corresponding properties of the components and the linearity of
trace.
-/

variable {m : ℕ}

/-- **N-fold convex combination of complex density matrices.**

    For a probability vector `p : Fin N → ℝ` (`p_i ≥ 0`,
    `Σ p_i = 1`) and a family `ρ : Fin N → ComplexDensityMatrix m`,
    the matrix `Σ_i p_i · ρ_i.M` is again a complex density matrix.

    *Remark*: when `N = 0` the trace-1 hypothesis is unsatisfiable
    (`Σ_{i ∈ ∅} p i = 0 ≠ 1`), so the constructor is vacuously
    defined; we never invoke it at `N = 0` in any downstream proof. -/
noncomputable def convexCombinationFin {N : ℕ}
    (p : Fin N → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : (∑ i, p i) = 1)
    (ρ : Fin N → ComplexDensityMatrix m) : ComplexDensityMatrix m where
  M := ∑ i, (p i : ℂ) • (ρ i).M
  hHerm := by
    -- Sum of (real-scalar)·Hermitian is Hermitian.
    unfold Matrix.IsHermitian
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [conjTranspose_smul, (ρ i).hHerm]
    simp [Complex.conj_ofReal]
  hTrace := by
    -- Tr(Σ_i p_i · ρ_i) = Σ_i p_i · Tr(ρ_i) = Σ_i p_i · 1 = Σ_i p_i = 1.
    rw [Matrix.trace_sum]
    have h_eq : (∑ i, Matrix.trace ((p i : ℂ) • (ρ i).M))
                  = ∑ i, ((p i : ℂ)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Matrix.trace_smul, smul_eq_mul, (ρ i).hTrace, mul_one]
    rw [h_eq]
    -- Σ_i (p i : ℂ) = ((Σ_i p i) : ℂ) = (1 : ℂ).
    rw [show (∑ i, (p i : ℂ)) = (((∑ i, p i) : ℝ) : ℂ) from
          (Complex.ofReal_sum _ _).symm,
        hp_sum, Complex.ofReal_one]
  hTracePSD := by
    intro X
    -- Distribute (Σ_i p_i · ρ_i) * X† * X = Σ_i p_i · (ρ_i * X† * X).
    have h_distribute :
        (∑ i, (p i : ℂ) • (ρ i).M) * X.conjTranspose * X
          = ∑ i, (p i : ℂ) • ((ρ i).M * X.conjTranspose * X) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Matrix.smul_mul, Matrix.smul_mul]
    rw [h_distribute, Matrix.trace_sum, Complex.re_sum]
    -- Each summand has nonneg .re; conclude by sum-nonneg.
    refine Finset.sum_nonneg ?_
    intro i _
    rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (hp_nonneg i) ((ρ i).hTracePSD X)

/-- The underlying matrix of `convexCombinationFin` unfolds to the
    explicit sum. -/
@[simp]
theorem convexCombinationFin_M {N : ℕ}
    (p : Fin N → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : (∑ i, p i) = 1)
    (ρ : Fin N → ComplexDensityMatrix m) :
    (convexCombinationFin p hp_nonneg hp_sum ρ).M
      = ∑ i, (p i : ℂ) • (ρ i).M := rfl

/-! ## 2.  Algebraic split lemma for `Fin (n+1)`-indexed sums.

When the head weight `p 0 = α` and the tail weights are
`r i := p (i.succ) / (1 - α)` (under `α < 1`, so `1 - α > 0`),
we have

    Σ_{i : Fin (n+2)} p_i · A_i
      = α · A 0  +  (1 - α) · Σ_{i : Fin (n+1)} r_i · A_{i.succ}.

This identity packages the inductive-step bookkeeping. -/

/-- **Head/tail split of a `Fin (n+1)`-indexed complex sum.**

    For `α := p 0` and `q := 1 - α` (with `q > 0`), define the
    renormalised tail weights `r i := p (i.succ) / q`.  Then

      `∑_{i : Fin (n+1)} (p i : ℂ) • A i
         = (α : ℂ) • A 0 + (q : ℂ) • ∑_{i : Fin n} (r i : ℂ) • A (i.succ)`. -/
theorem fin_succ_sum_split
    {n : ℕ} (p : Fin (n + 1) → ℝ) (hq_pos : 0 < 1 - p 0)
    (A : Fin (n + 1) → Matrix (Fin m) (Fin m) ℂ) :
    (∑ i, (p i : ℂ) • A i)
      = (p 0 : ℂ) • A 0
          + ((1 - p 0 : ℝ) : ℂ) •
              (∑ i : Fin n, ((p i.succ / (1 - p 0) : ℝ) : ℂ) • A i.succ) := by
  rw [Fin.sum_univ_succ]
  congr 1
  -- Goal: ∑_i (p i.succ : ℂ) • A i.succ
  --       = ((1 - p 0 : ℝ) : ℂ) • ∑_i ((p i.succ / (1 - p 0) : ℝ) : ℂ) • A i.succ
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- ((1-p 0 : ℝ) : ℂ) • (((p i.succ / (1 - p 0)) : ℝ) : ℂ) • A i.succ
  --   = ((p i.succ : ℝ) : ℂ) • A i.succ.
  rw [smul_smul]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

/-! ## 3.  PosDef of a strictly-positive convex combination.

When the convex combination `convexCombinationFin p _ _ ρ` is
taken over PosDef components and the weights are strictly positive,
the result is PosDef.  We prove the weaker, more directly useful
form: if each component `(ρ i).M` is PosDef and at least one weight
is strictly positive, the result is PosDef.  We actually only need
the "all weights positive" version downstream. -/

/-- **PosDef preservation for a `Fin n`-indexed sum.**

    If `(A i).M` is PosDef for each `i`, weights `p i ≥ 0`, and at
    least one weight is strictly positive, then
    `∑_i (p i : ℂ) • (A i).M` is PosDef.

    Helper: `Matrix.PosDef.add` lifts to a sum once we identify a
    PSD-summand-with-PosDef-counterpart, but in the inductive step
    of N-fold convexity we always have `0 < α` and `0 < q = 1 - α`,
    so we only ever need the strict version.

    For simplicity of the eventual downstream use, we phrase the
    statement directly at the `(ρ i).M` underlying-matrix level
    using `Matrix.PosDef`. -/
theorem convexCombination_two_PosDef
    {m : ℕ} (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (A B : Matrix (Fin m) (Fin m) ℂ) (hA : A.PosDef) (hB : B.PosDef) :
    ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B).PosDef := by
  have h1mα_pos : (0 : ℝ) < 1 - α := by linarith
  -- Use Matrix.PosDef.add + Matrix.PosDef.smul.
  have h_smulA : ((α : ℂ) • A).PosDef := hA.smul (RCLike.pos_iff.mpr ⟨hα_pos, rfl⟩)
  have h_smulB : (((1 - α : ℝ) : ℂ) • B).PosDef :=
    hB.smul (RCLike.pos_iff.mpr ⟨h1mα_pos, rfl⟩)
  exact h_smulA.add h_smulB

/-! ## 4.  The N-fold joint convexity theorem.

The headline inequality, proved by induction on `N`.  Each step
applies the binary joint convexity hypothesis `h2` exactly once. -/

/-- **N-fold joint convexity of the Umegaki relative entropy,
    conditional on the binary joint convexity hypothesis.**

    For any probability vector `p : Fin N → ℝ` (nonneg, sums to 1)
    and any family of PosDef density matrices
    `ρ, σ : Fin N → ComplexDensityMatrix m`,

      `S( Σ_i p_i ρ_i ‖ Σ_i p_i σ_i )  ≤  Σ_i p_i · S( ρ_i ‖ σ_i )`.

    Proved by induction on `N`. -/
theorem umegakiRelativeEntropy_n_fold_jointly_convex
    (h2 : JointConvexity_RelEntropy_Target)
    {m : ℕ} :
    ∀ {N : ℕ} (p : Fin N → ℝ) (ρ σ : Fin N → ComplexDensityMatrix m)
      (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : (∑ i, p i) = 1)
      (_hρ : ∀ i, (ρ i).M.PosDef) (_hσ : ∀ i, (σ i).M.PosDef),
      umegakiRelativeEntropy
          (convexCombinationFin p hp_nonneg hp_sum ρ)
          (convexCombinationFin p hp_nonneg hp_sum σ)
        ≤ ∑ i, p i * umegakiRelativeEntropy (ρ i) (σ i) := by
  intro N
  induction N with
  | zero =>
    -- Vacuous: Σ_{i : Fin 0} p i = 0, but hypothesis says it = 1.
    intro p _ _ _ hp_sum _ _
    exfalso
    simp at hp_sum
  | succ n ih =>
    intro p ρ σ hp_nonneg hp_sum hρ hσ
    -- Special handling: cases on whether `p 0 = 1` or `p 0 < 1`.
    have hp_zero_le : p 0 ≤ 1 := by
      -- p 0 ≤ Σ_i p i = 1 since other terms are nonneg.
      have h_rest_nonneg : 0 ≤ ∑ i : Fin n, p i.succ := by
        refine Finset.sum_nonneg ?_
        intro i _; exact hp_nonneg _
      have h_decomp : ∑ i, p i = p 0 + ∑ i : Fin n, p i.succ := Fin.sum_univ_succ p
      linarith [hp_sum, h_decomp]
    have hp_zero_nonneg : 0 ≤ p 0 := hp_nonneg 0
    by_cases h_zero_eq_one : p 0 = 1
    · -- Case `p 0 = 1`.  Then all other p i.succ = 0; both sides reduce to
      --   S(ρ 0 ‖ σ 0)  on the LHS and  p 0 · S(ρ 0 ‖ σ 0)  on the RHS.
      -- The tail terms vanish on both sides.
      have h_rest_zero : ∀ i : Fin n, p i.succ = 0 := by
        intro i
        have h_decomp : ∑ j, p j = p 0 + ∑ j : Fin n, p j.succ := Fin.sum_univ_succ p
        have h_sum_rest : ∑ j : Fin n, p j.succ = 0 := by
          rw [h_decomp, h_zero_eq_one] at hp_sum; linarith
        -- All entries of a nonneg sum that equals zero are zero.
        have h_each_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ p j.succ := by
          intro j _; exact hp_nonneg _
        exact (Finset.sum_eq_zero_iff_of_nonneg h_each_nonneg).mp h_sum_rest i
          (Finset.mem_univ _)
      -- LHS: Σ_i p_i ρ_i.M = p 0 · ρ 0.M + Σ_{i : Fin n} 0 · ρ_{i.succ}.M = ρ 0.M.
      have h_LHS_M_ρ :
          (convexCombinationFin p hp_nonneg hp_sum ρ).M = (ρ 0).M := by
        show (∑ i, (p i : ℂ) • (ρ i).M) = (ρ 0).M
        rw [Fin.sum_univ_succ]
        have h_tail_zero :
            (∑ i : Fin n, (p i.succ : ℂ) • (ρ i.succ).M) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i _
          rw [h_rest_zero i, Complex.ofReal_zero, zero_smul]
        rw [h_tail_zero, add_zero, h_zero_eq_one, Complex.ofReal_one, one_smul]
      have h_LHS_M_σ :
          (convexCombinationFin p hp_nonneg hp_sum σ).M = (σ 0).M := by
        show (∑ i, (p i : ℂ) • (σ i).M) = (σ 0).M
        rw [Fin.sum_univ_succ]
        have h_tail_zero :
            (∑ i : Fin n, (p i.succ : ℂ) • (σ i.succ).M) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i _
          rw [h_rest_zero i, Complex.ofReal_zero, zero_smul]
        rw [h_tail_zero, add_zero, h_zero_eq_one, Complex.ofReal_one, one_smul]
      -- Hence S(combo ρ ‖ combo σ) = S(ρ 0 ‖ σ 0).
      have h_lhs_eq : umegakiRelativeEntropy
                        (convexCombinationFin p hp_nonneg hp_sum ρ)
                        (convexCombinationFin p hp_nonneg hp_sum σ)
                      = umegakiRelativeEntropy (ρ 0) (σ 0) := by
        unfold umegakiRelativeEntropy operatorLog cfcρ
        rw [h_LHS_M_ρ, h_LHS_M_σ]
      rw [h_lhs_eq]
      -- RHS: Σ_i p_i · S(ρ_i ‖ σ_i) = p 0 · S(ρ 0 ‖ σ 0) + (tail = 0).
      have h_rhs_eq :
          (∑ i, p i * umegakiRelativeEntropy (ρ i) (σ i))
            = umegakiRelativeEntropy (ρ 0) (σ 0) := by
        rw [Fin.sum_univ_succ]
        have h_tail_zero :
            (∑ i : Fin n, p i.succ * umegakiRelativeEntropy (ρ i.succ) (σ i.succ))
              = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i _
          rw [h_rest_zero i, zero_mul]
        rw [h_tail_zero, add_zero, h_zero_eq_one, one_mul]
      rw [h_rhs_eq]
    · -- Case `p 0 < 1`.  Let q := 1 - p 0 > 0.  Renormalise the tail.
      have hp_zero_lt : p 0 < 1 := lt_of_le_of_ne hp_zero_le h_zero_eq_one
      have hq_pos : 0 < 1 - p 0 := by linarith
      -- Renormalised tail probabilities.
      set q : ℝ := 1 - p 0 with hq_def
      set r : Fin n → ℝ := fun i => p i.succ / q with hr_def
      -- Tail-renormalised PMF: nonnegative and sums to 1.
      have hr_nonneg : ∀ i, 0 ≤ r i := by
        intro i
        rw [hr_def]
        exact div_nonneg (hp_nonneg _) (le_of_lt hq_pos)
      have hr_sum : (∑ i, r i) = 1 := by
        show (∑ i : Fin n, p i.succ / q) = 1
        rw [← Finset.sum_div]
        have h_decomp : ∑ j, p j = p 0 + ∑ j : Fin n, p j.succ := Fin.sum_univ_succ p
        have h_tail_sum : ∑ j : Fin n, p j.succ = q := by
          rw [h_decomp] at hp_sum
          show ∑ j : Fin n, p j.succ = 1 - p 0
          linarith
        rw [h_tail_sum]
        exact div_self (ne_of_gt hq_pos)
      -- The tail convex-combination density matrices.
      set ρ_tail : ComplexDensityMatrix m :=
        convexCombinationFin r hr_nonneg hr_sum (fun i => ρ i.succ) with hρ_tail
      set σ_tail : ComplexDensityMatrix m :=
        convexCombinationFin r hr_nonneg hr_sum (fun i => σ i.succ) with hσ_tail
      -- Tail PosDef: by `convexCombinationFin`'s definition the matrix is
      --   `Σ_i (r i : ℂ) • (ρ i.succ).M`.  We need this to be PosDef so we can
      --   invoke `h2` on (ρ 0, ρ_tail) and (σ 0, σ_tail).
      have hρ_tail_PosDef : ρ_tail.M.PosDef := by
        -- Σ-of-PSD with at least one strictly-positive coefficient is PosDef.
        -- Since the r_i sum to 1 and are nonneg, at least one is strictly positive.
        rw [hρ_tail, convexCombinationFin_M]
        -- Find an index `i₀` with `r i₀ > 0`.
        have h_exists : ∃ i₀, 0 < r i₀ := by
          by_contra h_all_zero
          push_neg at h_all_zero
          have h_all_zero' : ∀ i, r i = 0 :=
            fun i => le_antisymm (h_all_zero i) (hr_nonneg i)
          have : (∑ i, r i) = 0 := Finset.sum_eq_zero (fun i _ => h_all_zero' i)
          rw [hr_sum] at this
          exact one_ne_zero this
        obtain ⟨i₀, hi₀⟩ := h_exists
        -- Split the sum at i₀ via Finset.sum_eq_add_of_mem, get
        --   sum = (r i₀ : ℂ) • (ρ i₀.succ).M + (rest).
        -- Then show rest is PSD (sum of nonneg-scalar · PosDef terms) and the
        -- isolated summand is PosDef; PosDef + PosSemidef = PosDef.
        -- Easiest: directly write Σ = (r i₀ • (ρ i₀.succ).M) + Σ_{j ≠ i₀} (r j • (ρ j.succ).M).
        have h_split :
            (∑ i, (r i : ℂ) • (ρ i.succ).M)
              = (r i₀ : ℂ) • (ρ i₀.succ).M
                  + ∑ j ∈ Finset.univ.erase i₀, (r j : ℂ) • (ρ j.succ).M := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        rw [h_split]
        -- The isolated summand is PosDef.
        have h_iso : ((r i₀ : ℂ) • (ρ i₀.succ).M).PosDef :=
          (hρ i₀.succ).smul (RCLike.pos_iff.mpr ⟨hi₀, rfl⟩)
        -- The remaining sum is PSD.
        have h_rest_psd :
            (∑ j ∈ Finset.univ.erase i₀, (r j : ℂ) • (ρ j.succ).M).PosSemidef := by
          refine Finset.sum_induction _ _ (fun X Y => Matrix.PosSemidef.add)
              (Matrix.PosSemidef.zero) ?_
          intro j _
          rcases lt_or_eq_of_le (hr_nonneg j) with hj_pos | hj_zero
          · exact ((hρ j.succ).smul
              (RCLike.pos_iff.mpr ⟨hj_pos, rfl⟩)).posSemidef
          · -- r j = 0 ⇒ summand is 0 ⇒ PSD.
            have : (r j : ℂ) • (ρ j.succ).M = 0 := by
              rw [← hj_zero, Complex.ofReal_zero, zero_smul]
            rw [this]
            exact Matrix.PosSemidef.zero
        exact Matrix.PosDef.add_posSemidef h_iso h_rest_psd
      have hσ_tail_PosDef : σ_tail.M.PosDef := by
        rw [hσ_tail, convexCombinationFin_M]
        have h_exists : ∃ i₀, 0 < r i₀ := by
          by_contra h_all_zero
          push_neg at h_all_zero
          have h_all_zero' : ∀ i, r i = 0 :=
            fun i => le_antisymm (h_all_zero i) (hr_nonneg i)
          have : (∑ i, r i) = 0 := Finset.sum_eq_zero (fun i _ => h_all_zero' i)
          rw [hr_sum] at this
          exact one_ne_zero this
        obtain ⟨i₀, hi₀⟩ := h_exists
        have h_split :
            (∑ i, (r i : ℂ) • (σ i.succ).M)
              = (r i₀ : ℂ) • (σ i₀.succ).M
                  + ∑ j ∈ Finset.univ.erase i₀, (r j : ℂ) • (σ j.succ).M := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        rw [h_split]
        have h_iso : ((r i₀ : ℂ) • (σ i₀.succ).M).PosDef :=
          (hσ i₀.succ).smul (RCLike.pos_iff.mpr ⟨hi₀, rfl⟩)
        have h_rest_psd :
            (∑ j ∈ Finset.univ.erase i₀, (r j : ℂ) • (σ j.succ).M).PosSemidef := by
          refine Finset.sum_induction _ _ (fun X Y => Matrix.PosSemidef.add)
              (Matrix.PosSemidef.zero) ?_
          intro j _
          rcases lt_or_eq_of_le (hr_nonneg j) with hj_pos | hj_zero
          · exact ((hσ j.succ).smul
              (RCLike.pos_iff.mpr ⟨hj_pos, rfl⟩)).posSemidef
          · have : (r j : ℂ) • (σ j.succ).M = 0 := by
              rw [← hj_zero, Complex.ofReal_zero, zero_smul]
            rw [this]
            exact Matrix.PosSemidef.zero
        exact Matrix.PosDef.add_posSemidef h_iso h_rest_psd
      -- Apply the inductive hypothesis to the tail.
      have h_tail_ih :
          umegakiRelativeEntropy ρ_tail σ_tail
            ≤ ∑ i, r i * umegakiRelativeEntropy (ρ i.succ) (σ i.succ) :=
        ih r (fun i => ρ i.succ) (fun i => σ i.succ)
            hr_nonneg hr_sum (fun i => hρ i.succ) (fun i => hσ i.succ)
      -- Apply binary joint convexity at (ρ 0, ρ_tail) vs (σ 0, σ_tail), α := p 0.
      -- Note that `convexCombination (p 0) _ _ (ρ 0) ρ_tail` has underlying matrix
      -- `(p 0 : ℂ) • (ρ 0).M + ((1 - p 0 : ℝ) : ℂ) • ρ_tail.M`, which is exactly
      -- the full N+1-fold combo by `fin_succ_sum_split`.
      have hα₀ : 0 ≤ p 0 := hp_zero_nonneg
      have hα₁ : p 0 ≤ 1 := hp_zero_le
      have h_binary :=
        h2 (ρ 0) ρ_tail (σ 0) σ_tail (hρ 0) hρ_tail_PosDef (hσ 0) hσ_tail_PosDef
            (p 0) hα₀ hα₁
      -- Match the LHS of h_binary against
      --   `umegakiRelativeEntropy (convexCombinationFin p _ _ ρ) (convexCombinationFin p _ _ σ)`.
      -- Both reduce to the same matrix-level expression (modulo `fin_succ_sum_split`).
      have h_LHS_ρ_M :
          (convexCombination (p 0) hα₀ hα₁ (ρ 0) ρ_tail).M
            = (convexCombinationFin p hp_nonneg hp_sum ρ).M := by
        show ((p 0 : ℂ) • (ρ 0).M + ((1 - p 0 : ℝ) : ℂ) • ρ_tail.M)
              = ∑ i, (p i : ℂ) • (ρ i).M
        rw [hρ_tail, convexCombinationFin_M]
        rw [← fin_succ_sum_split p hq_pos (fun i => (ρ i).M)]
      have h_LHS_σ_M :
          (convexCombination (p 0) hα₀ hα₁ (σ 0) σ_tail).M
            = (convexCombinationFin p hp_nonneg hp_sum σ).M := by
        show ((p 0 : ℂ) • (σ 0).M + ((1 - p 0 : ℝ) : ℂ) • σ_tail.M)
              = ∑ i, (p i : ℂ) • (σ i).M
        rw [hσ_tail, convexCombinationFin_M]
        rw [← fin_succ_sum_split p hq_pos (fun i => (σ i).M)]
      -- Umegaki depends only on .M (via operatorLog, also only on .M).
      have h_lhs_eq :
          umegakiRelativeEntropy
              (convexCombination (p 0) hα₀ hα₁ (ρ 0) ρ_tail)
              (convexCombination (p 0) hα₀ hα₁ (σ 0) σ_tail)
            = umegakiRelativeEntropy
                  (convexCombinationFin p hp_nonneg hp_sum ρ)
                  (convexCombinationFin p hp_nonneg hp_sum σ) := by
        unfold umegakiRelativeEntropy operatorLog cfcρ
        rw [h_LHS_ρ_M, h_LHS_σ_M]
      rw [h_lhs_eq] at h_binary
      -- Now h_binary :
      --   S(combo_full ρ ‖ combo_full σ)
      --     ≤ p 0 · S(ρ 0 ‖ σ 0) + (1 - p 0) · S(ρ_tail ‖ σ_tail).
      -- Combine with h_tail_ih to get the goal.
      have h_target_RHS :
          (∑ i, p i * umegakiRelativeEntropy (ρ i) (σ i))
            = p 0 * umegakiRelativeEntropy (ρ 0) (σ 0)
                + (1 - p 0) * (∑ i, r i * umegakiRelativeEntropy (ρ i.succ) (σ i.succ)) := by
        rw [Fin.sum_univ_succ]
        congr 1
        -- Σ_i p_{i.succ} · S(ρ_{i.succ} ‖ σ_{i.succ})
        --   = (1 - p 0) · Σ_i r i · S(ρ_{i.succ} ‖ σ_{i.succ}).
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        -- r i = p i.succ / (1 - p 0), so (1 - p 0) * r i = p i.succ.
        rw [hr_def]
        show p i.succ * umegakiRelativeEntropy (ρ i.succ) (σ i.succ)
              = (1 - p 0) * (p i.succ / (1 - p 0)
                              * umegakiRelativeEntropy (ρ i.succ) (σ i.succ))
        rw [show p i.succ / (1 - p 0)
                  * umegakiRelativeEntropy (ρ i.succ) (σ i.succ)
                = p i.succ * umegakiRelativeEntropy (ρ i.succ) (σ i.succ)
                    / (1 - p 0) by ring,
            mul_div_cancel₀ _ (ne_of_gt hq_pos)]
      rw [h_target_RHS]
      -- Apply transitivity: LHS ≤ p 0 · S(ρ 0 ‖ σ 0) + (1 - p 0) · S(ρ_tail ‖ σ_tail)
      --                         ≤ p 0 · S(ρ 0 ‖ σ 0) + (1 - p 0) · (Σ_i r_i · S(ρ_{i.succ} ‖ σ_{i.succ})).
      have h_q_nn : (0 : ℝ) ≤ 1 - p 0 := le_of_lt hq_pos
      have h_step2 :
          (1 - p 0) * umegakiRelativeEntropy ρ_tail σ_tail
            ≤ (1 - p 0) *
              (∑ i, r i * umegakiRelativeEntropy (ρ i.succ) (σ i.succ)) :=
        mul_le_mul_of_nonneg_left h_tail_ih h_q_nn
      linarith [h_binary, h_step2]

/-! ## 5.  Discharge of the placeholder `JointConvexity_Multi_Target`.

The named gate `JointConvexity_Multi_Target` declared in
`PartialTraceDecomposition.lean` is currently defined as `True`
(a structural placeholder reserved for the N-fold extension of
binary joint convexity).  Hence it is unconditionally `trivial`;
we re-export the discharge here, gated on the binary hypothesis
`JointConvexity_RelEntropy_Target` so the API anticipates the
eventual upgrade where the placeholder is replaced by the
meaningful N-fold statement.

Independently, we ship the meaningful N-fold theorem
`umegakiRelativeEntropy_n_fold_jointly_convex` above, which is the
content of what `JointConvexity_Multi_Target` is intended to name. -/

/-- **Discharge of `JointConvexity_Multi_Target` from the binary
    hypothesis.**

    The current `JointConvexity_Multi_Target` definition in
    `LayerB/PartialTraceDecomposition.lean` is `True`; this
    `trivial`-level discharge consumes the binary hypothesis
    `h : JointConvexity_RelEntropy_Target` only for symmetry with
    its eventual upgrade (the meaningful N-fold version proved
    above as `umegakiRelativeEntropy_n_fold_jointly_convex`). -/
-- ⚠️ AUDIT-FLAG (TRIVIAL TARGET): target is `JointConvexity_Multi_Target := True`; this is NOT a
-- discharge of N-fold joint convexity. The genuine (conditional) N-fold statement is
-- `umegakiRelativeEntropy_n_fold_jointly_convex`, itself gated on the OPEN
-- `JointConvexity_RelEntropy_Target` (= corrected Lieb). Do NOT cite this as joint convexity proved.
theorem multiConvex_holds_of_2 (_h : JointConvexity_RelEntropy_Target) :
    JointConvexity_Multi_Target := by
  -- Current definition: `JointConvexity_Multi_Target := True`.
  trivial

/-- **Unconditional discharge of `JointConvexity_Multi_Target`.**

    Since the placeholder is `True`, no hypothesis is required. -/
-- ⚠️ AUDIT-FLAG (TRIVIAL TARGET): target is `JointConvexity_Multi_Target := True`; this is NOT a
-- discharge of joint convexity. The genuine (conditional) statement is
-- `umegakiRelativeEntropy_n_fold_jointly_convex`, gated on the OPEN `JointConvexity_RelEntropy_Target`
-- (= corrected Lieb). Do NOT cite this as joint convexity proved.
theorem multiConvex_holds_unconditional : JointConvexity_Multi_Target := by
  trivial

/-! ## 6.  Axiom audit (intended state after build).

The following are intended to print only
`propext, Classical.choice, Quot.sound`
(Lean's three standard axioms).  No `sorry`, no custom `axiom`. -/

#print axioms convexCombinationFin
#print axioms umegakiRelativeEntropy_n_fold_jointly_convex
#print axioms multiConvex_holds_of_2
#print axioms multiConvex_holds_unconditional

end UnifiedTheory.LayerB.UmegakiMultiConvex
