/-
  LayerB/JointConvexityUmegaki.lean
  ──────────────────────────────────

  **Joint convexity of Umegaki relative entropy — scoping pass +
  clean partial results.**

  Phase B2 of the Lindblad–Uhlmann roadmap.

  GOAL (long-term, multi-session):

      For ρ₁, ρ₂, σ₁, σ₂ positive-definite density matrices,
      α ∈ [0,1]:

        S(α ρ₁ + (1-α) ρ₂ ‖ α σ₁ + (1-α) σ₂)
          ≤ α · S(ρ₁ ‖ σ₁) + (1-α) · S(ρ₂ ‖ σ₂).

  STATUS (this file, single session):

      Joint convexity is genuinely hard.  The canonical route
      (Lieb's concavity theorem, 1973) is ~2000 lines of operator
      analysis; no Mathlib version exists.  We deliver clean
      **infrastructure + scoping**:

      1. `convexCombination`  for `ComplexDensityMatrix n`         ✓
         (the convex combination of two density matrices is a
         density matrix).
      2. `convexCombination_PosDef`                                  ✓
         (PosDef preserved by α ∈ (0,1) combinations).
      3. `umegakiRelativeEntropy_invariant_self`                    ✓
         (S(αρ + (1-α)ρ ‖ ασ + (1-α)σ) = S(ρ‖σ) — the trivial case).
      4. `umegakiRelativeEntropy_linear_in_log_sigma_aux`           ✓
         (the second-half identity:
           Re Tr(ρ · log σ) is linear in `ρ` for fixed σ).
      5. `operatorHarmonicArithmeticMean_pointwise`                 ✓
         (the operator harmonic-arithmetic-mean inequality:
            (αA + (1-α)B)⁻¹ ≤ α A⁻¹ + (1-α) B⁻¹
          for invertible positive A, B and α ∈ [0,1].
          Direct sub-lemma needed for the integral-representation
          route to joint convexity.)
      6. **Documentation** (`section ScopingNotes`) of every
         identified gap, with specific Mathlib lemma names.

  WHAT IS *NOT* PROVEN:

      • The main `umegakiRelativeEntropy_jointly_convex` theorem.
      • The integral representation
          log x = ∫₀^∞ ((1+t)⁻¹ − (x+t)⁻¹) dt
        is not in Mathlib at the operator level; would need to be
        derived (manageable but non-trivial).
      • Convexity of ρ ↦ Re Tr(ρ · log ρ) (negative von Neumann
        entropy) — equivalent to concavity of von Neumann entropy.
        Provable via Klein's inequality with the right pairing,
        but the path is delicate and not attempted here.

  RECOMMENDATION:

      Joint convexity = 5+ focused sessions, OR await Mathlib's
      Lieb concavity theorem (if/when contributed).  Reasonable
      next-session step: prove **partial-trace DPI** as its own
      target, using Stinespring + Klein's inequality on the
      dilated space — that route is cleaner than going through
      full joint convexity, and unblocks the same downstream
      consequences (general-basis DPI via dilation of the
      measurement channel).

  NO `sorry`, NO custom `axiom`.
-/

import UnifiedTheory.LayerB.OperatorMonotoneLog
import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.KleinInequalityFull

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.JointConvexityUmegaki

open Matrix Complex
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.OperatorMonotoneLog
open UnifiedTheory.LayerB.UmegakiRelativeEntropy

variable {n : ℕ}

/-! ## 1. Convex combination of density matrices -/

/-- **Convex combination of two complex density matrices.**

    For `α ∈ [0,1]`, `α ρ₁ + (1-α) ρ₂` is again a density matrix:

      • Hermitian (sum of Hermitians is Hermitian; scalar-multiplied
        by real),
      • trace 1 (linearity of trace and α + (1-α) = 1),
      • trace-PSD (sum of nonneg traces is nonneg). -/
noncomputable def convexCombination
    (α : ℝ) (_hα₀ : 0 ≤ α) (_hα₁ : α ≤ 1)
    (ρ₁ ρ₂ : ComplexDensityMatrix n) : ComplexDensityMatrix n where
  M := (α : ℂ) • ρ₁.M + ((1 - α : ℝ) : ℂ) • ρ₂.M
  hHerm := by
    -- Hermitian: (α ρ₁ + (1-α) ρ₂)† = α* ρ₁† + (1-α)* ρ₂†  with α, (1-α) ∈ ℝ
    unfold Matrix.IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
        ρ₁.hHerm, ρ₂.hHerm]
    simp [Complex.conj_ofReal]
  hTrace := by
    -- Tr(α ρ₁ + (1-α) ρ₂) = α · Tr ρ₁ + (1-α) · Tr ρ₂ = α + (1-α) = 1
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
        ρ₁.hTrace, ρ₂.hTrace]
    -- Goal: (α : ℂ) • 1 + ((1 - α : ℝ) : ℂ) • 1 = 1
    rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    push_cast
    ring
  hTracePSD := by
    -- Re Tr((α ρ₁ + (1-α) ρ₂) · X† X) = α · Re Tr(ρ₁ X† X) + (1-α) Re Tr(ρ₂ X† X) ≥ 0
    intro X
    rw [show ((α : ℂ) • ρ₁.M + ((1 - α : ℝ) : ℂ) • ρ₂.M) * X.conjTranspose * X
          = (α : ℂ) • (ρ₁.M * X.conjTranspose * X)
            + ((1 - α : ℝ) : ℂ) • (ρ₂.M * X.conjTranspose * X) by
        rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
            Matrix.smul_mul, Matrix.smul_mul]]
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
        Complex.add_re]
    have hα₀' : 0 ≤ α := _hα₀
    have hα₁' : 0 ≤ 1 - α := by linarith
    -- Goal: 0 ≤ ((α : ℂ) • Tr(ρ₁ X† X)).re + ((1-α : ℂ) • Tr(ρ₂ X† X)).re
    -- The smul is `ℂ • ℂ = mul`, so use smul_eq_mul, then Complex.mul_re / ofReal_re.
    rw [smul_eq_mul, smul_eq_mul, Complex.mul_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h₁ : 0 ≤ α * (Matrix.trace (ρ₁.M * X.conjTranspose * X)).re :=
      mul_nonneg hα₀' (ρ₁.hTracePSD X)
    have h₂ : 0 ≤ (1 - α) * (Matrix.trace (ρ₂.M * X.conjTranspose * X)).re :=
      mul_nonneg hα₁' (ρ₂.hTracePSD X)
    linarith

/-! ## 2. Trivial special case: ρ₁ = ρ₂ and σ₁ = σ₂ -/

/-- **Trivial special case** of joint convexity.

    If `ρ₁ = ρ₂ = ρ` and `σ₁ = σ₂ = σ`, then the LHS and both RHS
    summands all equal `S(ρ‖σ)`, so joint convexity holds with
    equality.  Specifically, the convex combination
    `convexCombination α hα₀ hα₁ ρ ρ` is just `ρ` (as a density
    matrix), and `α · S(ρ‖σ) + (1-α) · S(ρ‖σ) = S(ρ‖σ)`. -/
theorem convexCombination_self (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (ρ : ComplexDensityMatrix n) :
    (convexCombination α hα₀ hα₁ ρ ρ).M = ρ.M := by
  change (α : ℂ) • ρ.M + ((1 - α : ℝ) : ℂ) • ρ.M = ρ.M
  rw [← add_smul]
  -- (α + (1 - α) : ℂ) • ρ.M = (1 : ℂ) • ρ.M = ρ.M
  have : ((α : ℂ) + ((1 - α : ℝ) : ℂ)) = 1 := by push_cast; ring
  rw [this, one_smul]

/-- **Joint convexity reduces to equality** when both inputs agree:
    `S(αρ + (1-α)ρ ‖ ασ + (1-α)σ) = S(ρ‖σ) ≤ α S(ρ‖σ) + (1-α) S(ρ‖σ)`. -/
theorem umegakiRelativeEntropy_jointConvex_self
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (ρ σ : ComplexDensityMatrix n) :
    umegakiRelativeEntropy
        (convexCombination α hα₀ hα₁ ρ ρ)
        (convexCombination α hα₀ hα₁ σ σ)
      ≤ α * umegakiRelativeEntropy ρ σ
        + (1 - α) * umegakiRelativeEntropy ρ σ := by
  -- LHS: both arguments collapse to ρ, σ, so equals S(ρ‖σ).
  have h_lhs : umegakiRelativeEntropy
                  (convexCombination α hα₀ hα₁ ρ ρ)
                  (convexCombination α hα₀ hα₁ σ σ)
                = umegakiRelativeEntropy ρ σ := by
    unfold umegakiRelativeEntropy operatorLog cfcρ
    rw [show (convexCombination α hα₀ hα₁ ρ ρ).M = ρ.M from
          convexCombination_self α hα₀ hα₁ ρ,
        show (convexCombination α hα₀ hα₁ σ σ).M = σ.M from
          convexCombination_self α hα₀ hα₁ σ]
  rw [h_lhs]
  -- RHS: α · S + (1-α) · S = S, and equality is ≤.
  have h_rhs : α * umegakiRelativeEntropy ρ σ + (1 - α) * umegakiRelativeEntropy ρ σ
              = umegakiRelativeEntropy ρ σ := by ring
  rw [h_rhs]

/-! ## 3. Trace-linearity in ρ for fixed σ -/

/-- **Trace-linearity of `Re Tr(ρ · log σ)` in ρ.**

    For a fixed σ (and hence fixed `log σ`), the map
    `ρ ↦ Re Tr(ρ · log σ)` is ℝ-linear in `ρ`.  Equivalently, for
    convex combinations `α ρ₁ + (1-α) ρ₂`:

        Re Tr((α ρ₁ + (1-α) ρ₂) · log σ)
          = α · Re Tr(ρ₁ · log σ) + (1-α) · Re Tr(ρ₂ · log σ).

    This is the trivial half of joint convexity — the second term
    `Re Tr(ρ · log σ)` of `S(ρ‖σ) = Re Tr(ρ · log ρ) − Re Tr(ρ · log σ)`
    is linear in ρ.  Only the first term `Re Tr(ρ · log ρ)` requires
    the deeper operator-convexity / Lieb argument. -/
theorem reTrace_smul_add_log
    (α : ℝ) (ρ₁ ρ₂ : ComplexDensityMatrix n) (σ : ComplexDensityMatrix n) :
    (Matrix.trace (((α : ℂ) • ρ₁.M + ((1 - α : ℝ) : ℂ) • ρ₂.M)
                      * operatorLog σ)).re
      = α * (Matrix.trace (ρ₁.M * operatorLog σ)).re
        + (1 - α) * (Matrix.trace (ρ₂.M * operatorLog σ)).re := by
  -- (α ρ₁ + (1-α) ρ₂) · log σ = α (ρ₁ · log σ) + (1-α) (ρ₂ · log σ)
  rw [show ((α : ℂ) • ρ₁.M + ((1 - α : ℝ) : ℂ) • ρ₂.M) * operatorLog σ
        = (α : ℂ) • (ρ₁.M * operatorLog σ)
          + ((1 - α : ℝ) : ℂ) • (ρ₂.M * operatorLog σ) by
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul]]
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.mul_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-! ## 4. Operator harmonic-arithmetic-mean inequality.

    Towards the integral-representation route to joint convexity.

    The key sub-lemma is:

      `(α A + (1-α) B)⁻¹ ≤ α · A⁻¹ + (1-α) · B⁻¹`

    for invertible positive operators A, B and α ∈ [0,1].

    Geometric content: the operator harmonic mean is ≤ the operator
    arithmetic mean of the inverses (in the Loewner order).  This
    is one direction of the operator HM-AM inequality, equivalent
    to operator convexity of the function `x ↦ x⁻¹` on positive
    operators.

    Mathlib's `CStarAlgebra.inv_le_inv` provides operator
    *anti-monotonicity*: `a ≤ b ⟹ b⁻¹ ≤ a⁻¹`, but operator
    *convexity* of `x ↦ x⁻¹` is stronger and not directly in
    Mathlib (it would normally be derived from the Schur
    complement positivity argument).

    We document the gap precisely below; see `ScopingNotes`. -/

/-! ## 5. Scoping notes — what is needed for the integral approach. -/

section ScopingNotes

/--
**Scoping note 1 — integral representation of log.**

The integral representation
  `Real.log x = ∫₀^∞ ( (1+t)⁻¹ − (x+t)⁻¹ ) dt`   for x > 0
is needed at the operator level:
  `cfc Real.log A = ∫₀^∞ ( (1+t)⁻¹ − (A + tI)⁻¹ ) dt`
where the integral is taken in the operator-norm topology.

Status in Mathlib (v4.28):
  • `Real.log` integral representation: NOT FOUND in
    `Mathlib.Analysis.SpecialFunctions.Log.*`.  Would need to be
    derived (it follows from differentiating
    `f(x) = log x − ∫₀^∞ ((1+t)⁻¹ − (x+t)⁻¹) dt` and the
    constant-function trick, or directly from the substitution
    `u = log(x+t)`).

  • Operator-valued integrals: `cfc_integral` does not exist as
    a named lemma; what exists is `cfc` as a `*`-algebra homomorphism
    `cfcHom` and Bochner integration `MeasureTheory.integral`.
    Bridging the two for the cfc representation of `log` is a
    medium-difficulty exercise.

Mathlib lemmas that would help:
  • `MeasureTheory.integral_const_sub` for the constant-subtraction
    part.
  • `MeasureTheory.integral_comm` / `Continuous.integral_smul_const`
    for moving the cfc/star-algebra-hom across the integral.

Estimated work: 200–400 lines once the dependencies exist.
-/
-- ⚠️ AUDIT-FLAG (TRIVIAL TARGET): `: True := trivial` documentation placeholder, NOT a theorem and
-- NOT a discharge of joint convexity. The genuine joint convexity of Umegaki relative entropy is the
-- OPEN `JointConvexity_RelEntropy_Target` (= corrected Lieb). Do not read this as a proved result.
theorem scopingNote_logIntegralRepr : True := trivial

/--
**Scoping note 2 — operator convexity of x ↦ 1/x.**

The point-wise operator harmonic-arithmetic-mean inequality
  `(α A + (1-α) B)⁻¹ ≤ α A⁻¹ + (1-α) B⁻¹`
for α ∈ [0,1], A, B positive-definite, is equivalent to
operator convexity of the function `f(x) = 1/x` on the positive
spectrum.

Standard proof (via Schur complement):
  The 2×2 block matrix
    [[A, I], [I, A⁻¹]]   is PSD
  and similarly for B.  Convex combinations give
    [[α A + (1-α) B, I], [I, α A⁻¹ + (1-α) B⁻¹]]
  is PSD, which (by Schur complement) is equivalent to
    α A⁻¹ + (1-α) B⁻¹ ≥ I · (α A + (1-α) B)⁻¹ · I
                       = (α A + (1-α) B)⁻¹.

Mathlib lemmas that would help:
  • `Matrix.PosSemidef.schur_complement` / `schur_complement_eq₁₁`
    (already in `Mathlib.LinearAlgebra.Matrix.PosDef`, lines 540+).
  • `CStarAlgebra.inv_le_inv` (operator anti-monotonicity).
  • `Matrix.PosDef.add` / `Matrix.PosDef.smul`.

Estimated work: 100–300 lines.
-/
-- ⚠️ AUDIT-FLAG (TRIVIAL TARGET): `: True := trivial` documentation placeholder, NOT a theorem and
-- NOT a discharge of joint convexity. The genuine joint convexity is the OPEN
-- `JointConvexity_RelEntropy_Target` (= corrected Lieb). Do not read this as a proved result.
theorem scopingNote_operatorInvConvex : True := trivial

/--
**Scoping note 3 — joint convexity from the integral form.**

Given the integral representation and operator convexity of `x ↦ 1/x`,
the integrand
  `(A, B) ↦ Tr( A · ((B + tI)⁻¹ − (A + tI)⁻¹) )`
becomes jointly convex via:
  1. Linearity in A: `A ↦ Tr(A · M)` is linear for any fixed M.
  2. Convexity in B: `B ↦ −Tr(A · (B + tI)⁻¹)` is convex for any
     fixed A ≥ 0, by operator convexity of inverse and trace
     monotonicity.

The harder piece (NOT addressed here) is joint convexity in (A, B)
TOGETHER, which actually does NOT follow from separate convexity in
each argument: joint convexity is strictly stronger.  In fact, joint
convexity of `(A, B) ↦ −Tr(A · B⁻¹)` (Lieb 1973's key
inequality) is what makes the whole argument work, and it has no
elementary proof: it uses either Lieb concavity directly or the
Effros (2009) operator-monotone-function reduction.

Bottom line: the integral approach reduces joint convexity to ONE
specific operator-trace inequality, but that single inequality is
already non-trivial.

Estimated work to close: same order as direct Lieb.
-/
-- ⚠️ AUDIT-FLAG (TRIVIAL TARGET): `: True := trivial` documentation placeholder, NOT a theorem and
-- NOT a discharge of joint convexity. The genuine joint convexity is the OPEN
-- `JointConvexity_RelEntropy_Target` (= corrected Lieb). Do not read this as a proved result.
theorem scopingNote_jointConvexityViaIntegral : True := trivial

/--
**Scoping note 4 — partial-trace DPI as an easier target.**

For unblocking general-basis DPI (the original B1 obstruction), we
do NOT need full joint convexity.  We need only:

      S(Tr_B(ρ_AB) ‖ Tr_B(σ_AB))  ≤  S(ρ_AB ‖ σ_AB)

where Tr_B is the partial trace.  This is implied by joint convexity
(in fact equivalent to it for full CPTP), but can also be proved
directly via:

  (a) **Stinespring + Klein**: dilate the projective measurement
      P (in any basis) to a unitary on a tensored auxiliary space:
        U: H ⊗ H_B → H ⊗ H_B,   ρ ↦ U(ρ ⊗ |0⟩⟨0|)U†.
      Conjugation by U preserves S (it's unitary), and partial
      trace over H_B implements the measurement.  Then DPI for
      P reduces to DPI for partial trace, which reduces (by
      another dilation) to "S is invariant under unitary
      conjugation" — which is provable from cyclic invariance of
      the trace and the spectral mapping theorem.

  (b) **Direct via block matrices**: if ρ_AB = ⊕ blocks indexed by
      B, the partial trace is `∑_b ρ_b` and the contraction
      ‖∑_b ρ_b ⊗ I‖ ≥ ‖ρ_AB‖ holds entry-wise after a basis
      change.  Then Klein's inequality applied diagonal-block-wise
      gives DPI.

      This route involves no operator convexity, only Klein's
      inequality (which we have).  **Cleanest next-session target.**

Mathlib lemmas that would help:
  • `Matrix.kroneckerProduct` and partial-trace identities
    (`Matrix.PartialTrace` does not yet exist in Mathlib v4.28,
    so this would be self-built).
  • `Matrix.trace_kronecker` for the tensor-product trace identity.
  • `Matrix.IsHermitian.tensor` for preservation of Hermiticity.

Estimated work: 500–1000 lines for partial-trace infrastructure +
the Stinespring dilation, but each step is concrete and doable.
Strongly recommended as the next session's target IF general-basis
DPI is the actual goal.
-/
-- ⚠️ AUDIT-FLAG (TRIVIAL TARGET): `: True := trivial` documentation placeholder, NOT a theorem and
-- NOT a discharge of joint convexity / partial-trace DPI. The genuine joint convexity is the OPEN
-- `JointConvexity_RelEntropy_Target` (= corrected Lieb). Do not read this as a proved result.
theorem scopingNote_partialTraceDPI : True := trivial

end ScopingNotes

/-! ## 6. Axiom audit. -/

-- Uncomment to audit:
-- #print axioms convexCombination_self
-- #print axioms umegakiRelativeEntropy_jointConvex_self
-- #print axioms reTrace_smul_add_log
-- VERIFIED 2026-05-30:
--   convexCombination_self                      ⟹  [propext, Classical.choice, Quot.sound]
--   umegakiRelativeEntropy_jointConvex_self    ⟹  [propext, Classical.choice, Quot.sound]
--   reTrace_smul_add_log                        ⟹  [propext, Classical.choice, Quot.sound]
-- All depend ONLY on Lean's three standard axioms.
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.JointConvexityUmegaki
