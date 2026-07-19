/-
  LayerB/RobertsonSchrodinger.lean
  ─────────────────────────────────

  The Robertson uncertainty bound for finite-dimensional complex
  Hermitian observables:

      Var_ρ(A) · Var_ρ(B)  ≥  (1/4) · ‖⟨[A, B]⟩_ρ‖²

  where  ⟨X⟩_ρ := Re(Tr(ρ X))  and  Var_ρ(A) := ⟨A²⟩_ρ − ⟨A⟩_ρ².

  This is the "commutator-only" Robertson bound.  The full
  Robertson–Schrödinger inequality additionally bounds by the
  anticommutator/covariance term; that strengthening is left for a
  follow-up file.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. For any complex-Hermitian trace-PSD trace-1 ρ and any pair of
       complex-Hermitian observables A, B in dim n:
            Var_ρ(A) · Var_ρ(B) ≥ (1/4) · ‖⟨[A,B]⟩_ρ‖²
    2. Var_ρ(A) ≥ 0 for any Hermitian A.
    3. ⟨[A,B]⟩_ρ is purely imaginary when A, B, ρ are Hermitian.
    4. Standalone real-algebra core:
            ∀ x, 0 ≤ a x² + b x + c   ∧   0 ≤ a   ⟹   b² ≤ 4 a c .

  SCOPE:
    – Finite-dimensional n × n complex matrices.
    – Does NOT claim canonical [x, p] = iℏ; that would require an
      unbounded-operator framework not in scope.
    – Conservative: commutator term only, no anticommutator
      (Robertson, not full Robertson–Schrödinger).
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.RobertsonSchrodinger

open Matrix Complex

/-! ## 1. Real-algebra core: nonnegative quadratic ⟹ discriminant ≤ 0 -/

/-- **Discriminant lemma.**  If a real quadratic `a x² + b x + c` is
    nonnegative for every real x and `a ≥ 0`, then `b² ≤ 4 a c`.

    This is the algebraic engine of every Cauchy–Schwarz / uncertainty
    argument.  Self-contained (no PSD, no inner products). -/
theorem discrim_le_of_quad_nonneg
    {a b c : ℝ} (ha : 0 ≤ a)
    (h : ∀ x : ℝ, 0 ≤ a * x^2 + b * x + c) :
    b^2 ≤ 4 * a * c := by
  by_cases ha0 : a = 0
  · -- Degenerate case a = 0: linear `b x + c ≥ 0` for all x ⟹ b = 0.
    subst ha0
    have hlin : ∀ x : ℝ, 0 ≤ b * x + c := by
      intro x
      have := h x
      simpa using this
    have hb : b = 0 := by
      by_contra hb_ne
      rcases lt_or_gt_of_ne hb_ne with hb_neg | hb_pos
      · -- b < 0: pick x = (c+1)/(-b), giving b·x + c = -(c+1) + c = -1 < 0
        have h_pos : 0 < -b := by linarith
        have h_pick := hlin ((c + 1) / (-b))
        have h_eq : b * ((c + 1) / (-b)) + c = - (c + 1) + c := by
          field_simp
        rw [h_eq] at h_pick
        linarith
      · -- b > 0: pick x = -(c+1)/b
        have h_pick := hlin (-(c + 1) / b)
        have h_eq : b * (-(c + 1) / b) + c = -(c + 1) + c := by
          field_simp
        rw [h_eq] at h_pick
        linarith
    rw [hb]
    norm_num
  · -- Main case a > 0: minimum is at x = -b/(2a), value c - b²/(4a).
    have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h_min := h (-b / (2 * a))
    have h_eq : a * (-b / (2 * a))^2 + b * (-b / (2 * a)) + c
        = c - b^2 / (4 * a) := by
      field_simp
      ring
    rw [h_eq] at h_min
    have h4a_pos : 0 < 4 * a := by linarith
    have h1 : b^2 / (4 * a) ≤ c := by linarith
    calc b^2
        = b^2 / (4 * a) * (4 * a) := by field_simp
      _ ≤ c * (4 * a) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt h4a_pos)
      _ = 4 * a * c := by ring

/-! ## 2. The complex density-matrix structure -/

/-- A complex finite-dimensional density matrix: Hermitian, trace 1,
    and trace-PSD (Re(Tr(M · X† · X)) ≥ 0 for all X).
    The trace-PSD field is what the Robertson proof actually needs;
    it follows from `Matrix.PosSemidef` but we make it a field directly
    so the theorem is self-contained. -/
structure ComplexDensityMatrix (n : ℕ) where
  /-- The matrix. -/
  M : Matrix (Fin n) (Fin n) ℂ
  /-- Hermiticity. -/
  hHerm : M.IsHermitian
  /-- Trace 1. -/
  hTrace : M.trace = 1
  /-- Trace-PSD via conjugate-transpose: Re(Tr(M · X† · X)) ≥ 0. -/
  hTracePSD : ∀ X : Matrix (Fin n) (Fin n) ℂ,
                0 ≤ (Matrix.trace (M * X.conjTranspose * X)).re

namespace ComplexDensityMatrix

variable {n : ℕ}

/-- Expectation value ⟨A⟩_ρ := Re(Tr(ρ · A)).  For Hermitian A this
    is the standard real-valued expectation. -/
noncomputable def expectation (ρ : ComplexDensityMatrix n)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (ρ.M * A)).re

/-- Variance Var_ρ(A) := ⟨A²⟩_ρ − ⟨A⟩_ρ². -/
noncomputable def variance (ρ : ComplexDensityMatrix n)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  expectation ρ (A * A) - (expectation ρ A)^2

/-- The commutator of two matrices. -/
def commutator (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

/-! ## 3. Linearity of expectation -/

theorem expectation_add (ρ : ComplexDensityMatrix n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    expectation ρ (A + B) = expectation ρ A + expectation ρ B := by
  unfold expectation
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem expectation_sub (ρ : ComplexDensityMatrix n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    expectation ρ (A - B) = expectation ρ A - expectation ρ B := by
  unfold expectation
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

theorem expectation_smul_real (ρ : ComplexDensityMatrix n)
    (c : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    expectation ρ ((c : ℂ) • A) = c * expectation ρ A := by
  unfold expectation
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp

theorem expectation_one (ρ : ComplexDensityMatrix n) :
    expectation ρ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold expectation
  rw [Matrix.mul_one, ρ.hTrace]
  simp

/-! ## 4. Hermitian and imaginary-trace properties -/

/-- For a real scalar α, `A − α·I` is Hermitian whenever A is. -/
theorem centered_isHermitian {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (α : ℝ) :
    (A - (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_sub, hA, conjTranspose_smul, Matrix.conjTranspose_one]
  congr 1
  simp [Complex.conj_ofReal]

/-- The trace of a Hermitian matrix is real (its imaginary part is zero). -/
theorem trace_isHermitian_im_zero {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : (Matrix.trace H).im = 0 := by
  -- Tr H = Tr H† = star (Tr H), so 2·Im(Tr H) = 0.
  have h_real : Matrix.trace H = star (Matrix.trace H) := by
    rw [← Matrix.trace_conjTranspose, hH]
  have h_im := congrArg Complex.im h_real
  rw [Complex.star_def, Complex.conj_im] at h_im
  linarith

/-- The commutator of two Hermitian matrices is anti-Hermitian. -/
theorem commutator_hermitian_antiHerm
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (commutator A B).conjTranspose = -(commutator A B) := by
  unfold commutator
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
  rw [hA, hB]
  -- Goal: B*A - A*B = -(A*B - B*A)
  rw [neg_sub]

/-- Centering the operands does not change the commutator:
    `[A − αI, B − βI] = [A, B]` for any scalars α, β. -/
theorem commutator_centered (A B : Matrix (Fin n) (Fin n) ℂ) (α β : ℂ) :
    commutator (A - α • (1 : Matrix (Fin n) (Fin n) ℂ))
               (B - β • (1 : Matrix (Fin n) (Fin n) ℂ))
      = commutator A B := by
  unfold commutator
  -- (A - αI)(B - βI) = AB - αB - βA + αβI;  same for swap.
  -- Differences cancel the αβI and the linear-in-α, linear-in-β
  -- (αB and βA) terms.
  -- simp's normal form: `Matrix.mul_smul` fires before `Matrix.smul_mul`,
  -- so `(α•1) * (β•1)` ↦ `β • α • 1` and symmetrically
  --     `(β•1) * (α•1)` ↦ `α • β • 1`.
  -- We state the intermediate targets to match.
  have h1 : (A - α • (1 : Matrix (Fin n) (Fin n) ℂ))
              * (B - β • (1 : Matrix (Fin n) (Fin n) ℂ))
          = A * B - α • B - β • A
              + β • α • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    abel
  have h2 : (B - β • (1 : Matrix (Fin n) (Fin n) ℂ))
              * (A - α • (1 : Matrix (Fin n) (Fin n) ℂ))
          = B * A - β • A - α • B
              + α • β • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [h1, h2]
  -- Goal: (A*B - α•B - β•A + β•α•1) - (B*A - β•A - α•B + α•β•1) = A*B - B*A
  -- Identify β•α•1 = α•β•1 by smul_comm; then everything cancels via abel.
  rw [show (β : ℂ) • α • (1 : Matrix (Fin n) (Fin n) ℂ) = α • β • 1
      from smul_comm β α 1]
  abel

/-- For Hermitian ρ, A, B:  `Re(Tr(ρ · [A, B])) = 0`,
    i.e., the commutator expectation is purely imaginary. -/
theorem trace_rho_commutator_re_zero
    (ρ : ComplexDensityMatrix n)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (ρ.M * commutator A B)).re = 0 := by
  -- z := Tr(ρ [A,B]).  Show z = -star z, hence Re z = 0.
  set z := Matrix.trace (ρ.M * commutator A B) with hz_def
  have h_neg_z : z = -star z := by
    rw [hz_def, ← Matrix.trace_conjTranspose]
    rw [conjTranspose_mul, ρ.hHerm]
    rw [commutator_hermitian_antiHerm hA hB]
    -- Goal: (ρ.M * commutator A B).trace
    --     = -((-commutator A B * ρ.M).trace)
    rw [Matrix.neg_mul, Matrix.trace_neg, neg_neg]
    -- Goal: (ρ.M * commutator A B).trace = (commutator A B * ρ.M).trace
    exact Matrix.trace_mul_comm _ _
  -- z = -star z ⟹ Re z = -Re z ⟹ Re z = 0
  have h_re := congrArg Complex.re h_neg_z
  rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h_re
  linarith

/-! ## 5. Variance as centered expectation -/

/-- The variance equals the expectation of the centered observable squared:
    `Var_ρ(A) = ⟨(A − ⟨A⟩I)²⟩_ρ`. -/
theorem variance_eq_centered_sq (ρ : ComplexDensityMatrix n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    variance ρ A
      = expectation ρ ((A - (expectation ρ A : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
                       * (A - (expectation ρ A : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) := by
  set α : ℝ := expectation ρ A with hα_def
  -- Expand (A - αI)(A - αI) = A·A - α•A - α•A + α•α•I
  have expand :
      (A - (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
        * (A - (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
      = A * A - (α : ℂ) • A - (α : ℂ) • A
          + (α : ℂ) • (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [expand]
  -- Apply linearity of expectation (use simp only so all instances fire)
  simp only [expectation_add, expectation_sub, expectation_smul_real,
             expectation_one]
  -- After simp: ⟨A²⟩ - α·⟨A⟩ - α·⟨A⟩ + α·(α·1) = variance ρ A.
  -- variance ρ A = ⟨A²⟩ - (⟨A⟩)² = ⟨A²⟩ - α² by α-definition.
  unfold variance
  -- Goal: variance side = centered-expansion side.  Substitute ⟨A⟩ → α and ring.
  have h_α : expectation ρ A = α := rfl
  rw [h_α]
  ring

/-! ## 6. Variance non-negativity -/

/-- `Var_ρ(A) ≥ 0` for any Hermitian observable A. -/
theorem variance_nonneg (ρ : ComplexDensityMatrix n)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    0 ≤ variance ρ A := by
  set α : ℝ := expectation ρ A with hα_def
  set A' : Matrix (Fin n) (Fin n) ℂ :=
    A - (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hA'_def
  have hA'_herm : A'.IsHermitian := centered_isHermitian hA α
  have h_psd := ρ.hTracePSD A'
  -- ρ.hTracePSD A' : 0 ≤ Re(Tr(ρ.M * A'.conjTranspose * A'))
  -- A' Hermitian so A'.conjTranspose = A'
  rw [hA'_herm] at h_psd
  -- 0 ≤ Re(Tr(ρ.M * A' * A')) = Re(Tr(ρ.M * (A' * A'))) (assoc)
  rw [Matrix.mul_assoc] at h_psd
  -- Identify with expectation
  have h_eq : expectation ρ (A' * A') = (Matrix.trace (ρ.M * (A' * A'))).re := rfl
  -- variance ρ A = expectation ρ (A' * A')
  rw [variance_eq_centered_sq]
  change 0 ≤ expectation ρ
              ((A - (expectation ρ A : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
                * (A - (expectation ρ A : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)))
  exact h_psd

/-! ## 7. The Robertson uncertainty bound -/

/-- **Robertson uncertainty bound (commutator form).**

    For Hermitian observables A, B and a complex Hermitian, trace-PSD,
    trace-1 density matrix ρ in finite dimension n:

        Var_ρ(A) · Var_ρ(B)  ≥  (1/4) · ‖Tr(ρ · [A, B])‖²

    where `[A, B] = AB − BA` is the commutator and `‖·‖² = Complex.normSq`.

    Conservative scope:
      • commutator term only (not the full Robertson–Schrödinger
        inequality with the anticommutator/covariance term);
      • finite-dimensional matrices (no canonical [x, p] = iℏ claim);
      • no infinite-dimensional or unbounded-operator content. -/
theorem robertson_uncertainty
    (ρ : ComplexDensityMatrix n)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    variance ρ A * variance ρ B
      ≥ (1 / 4) * Complex.normSq (Matrix.trace (ρ.M * commutator A B)) := by
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- Setup: centered observables and the commutator-expectation z.
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  set α : ℝ := expectation ρ A with hα_def
  set β : ℝ := expectation ρ B with hβ_def
  set A' : Matrix (Fin n) (Fin n) ℂ :=
    A - (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hA'_def
  set B' : Matrix (Fin n) (Fin n) ℂ :=
    B - (β : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hB'_def
  have hA'_herm : A'.IsHermitian := centered_isHermitian hA α
  have hB'_herm : B'.IsHermitian := centered_isHermitian hB β
  have h_comm_eq : commutator A' B' = commutator A B :=
    commutator_centered A B (α : ℂ) (β : ℂ)
  set z : ℂ := Matrix.trace (ρ.M * commutator A B) with hz_def
  have hz_re : z.re = 0 := trace_rho_commutator_re_zero ρ hA hB
  have h_normSq : Complex.normSq z = (z.im)^2 := by
    rw [Complex.normSq_apply, hz_re]; ring
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- The quadratic-in-λ inequality from M(λ) := A' + (iλ)•B'.
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  have h_quad : ∀ lam : ℝ,
      0 ≤ variance ρ B * lam^2 + (-z.im) * lam + variance ρ A := by
    intro lam
    set M : Matrix (Fin n) (Fin n) ℂ :=
      A' + (Complex.I * (lam : ℂ)) • B' with hM_def
    -- M† = A' − (iλ)•B'  (conj(iλ) = -iλ; A', B' Hermitian)
    have hM_conj : M.conjTranspose
        = A' - (Complex.I * (lam : ℂ)) • B' := by
      rw [hM_def, conjTranspose_add, conjTranspose_smul, hA'_herm, hB'_herm]
      have h_star : star (Complex.I * (lam : ℂ)) = -(Complex.I * (lam : ℂ)) := by
        rw [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      rw [h_star, neg_smul]
      abel
    -- M† * M = A'² + (λ²:ℂ)•(B'·B') + (iλ)•[A',B']
    have hMM : M.conjTranspose * M
        = A' * A' + ((lam^2 : ℝ) : ℂ) • (B' * B')
                  + (Complex.I * (lam : ℂ)) • commutator A' B' := by
      rw [hM_conj, hM_def]
      rw [sub_mul, mul_add, mul_add]
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      -- (A'·A' + (Iλ)•(A'·B')) - ((Iλ)•(B'·A') + (Iλ)•((Iλ)•(B'·B')))
      -- Combine the smul tower (Iλ)•(Iλ)•(B'·B') = (Iλ)²•(B'·B') = -(λ²)•(B'·B')
      have h_double : (Complex.I * (lam : ℂ)) • (Complex.I * (lam : ℂ)) • (B' * B')
          = -(((lam^2 : ℝ) : ℂ) • (B' * B')) := by
        have h_sq : (Complex.I * (lam : ℂ)) * (Complex.I * (lam : ℂ))
            = -((lam^2 : ℝ) : ℂ) := by
          push_cast
          ring_nf
          rw [Complex.I_sq]
          ring
        calc (Complex.I * (lam : ℂ)) • (Complex.I * (lam : ℂ)) • (B' * B')
            = ((Complex.I * (lam : ℂ)) * (Complex.I * (lam : ℂ))) • (B' * B') := by
                rw [smul_smul]
          _ = (-((lam^2 : ℝ) : ℂ)) • (B' * B') := by rw [h_sq]
          _ = -(((lam^2 : ℝ) : ℂ) • (B' * B')) := by rw [neg_smul]
      rw [h_double]
      -- Now: A'·A' + (Iλ)•(A'·B') - ((Iλ)•(B'·A') - (λ²)•(B'·B'))
      --    = A'·A' + (Iλ)•(A'·B') - (Iλ)•(B'·A') + (λ²)•(B'·B')
      -- Want: A'·A' + (λ²)•(B'·B') + (Iλ)•[A'·B' - B'·A']
      -- commutator A' B' = A'·B' - B'·A'
      unfold commutator
      rw [smul_sub]
      abel
    -- Substitute commutator equality
    rw [h_comm_eq] at hMM
    -- Apply hTracePSD with M
    have h_psd := ρ.hTracePSD M
    rw [Matrix.mul_assoc] at h_psd
    rw [hMM] at h_psd
    -- h_psd : 0 ≤ Re(Tr(ρ.M * (A'·A' + (λ²:ℂ)•(B'·B') + (iλ)•[A,B])))
    -- Distribute trace and Re
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
        Complex.add_re, Complex.add_re] at h_psd
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
        Matrix.trace_smul] at h_psd
    -- Convert ℂ-on-ℂ smul to multiplication, then apply Complex.mul_re
    rw [smul_eq_mul, smul_eq_mul, Complex.mul_re, Complex.mul_re] at h_psd
    -- Identify (lam^2 : ℂ).re = lam^2, (lam^2 : ℂ).im = 0, (Iλ).re = 0, (Iλ).im = lam
    have h_lam2_re : (((lam^2 : ℝ) : ℂ)).re = lam^2 := Complex.ofReal_re _
    have h_lam2_im : (((lam^2 : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _
    have h_Ilam_re : (Complex.I * (lam : ℂ)).re = 0 := by simp
    have h_Ilam_im : (Complex.I * (lam : ℂ)).im = lam := by simp
    rw [h_lam2_re, h_lam2_im, h_Ilam_re, h_Ilam_im] at h_psd
    -- Identify ⟨A'·A'⟩ and ⟨B'·B'⟩ with variances
    have h_var_A_eq : (Matrix.trace (ρ.M * (A' * A'))).re = variance ρ A := by
      change expectation ρ (A' * A') = variance ρ A
      rw [variance_eq_centered_sq ρ A]
    have h_var_B_eq : (Matrix.trace (ρ.M * (B' * B'))).re = variance ρ B := by
      change expectation ρ (B' * B') = variance ρ B
      rw [variance_eq_centered_sq ρ B]
    -- z = Tr(ρ · commutator A B)
    have hz_eq : (Matrix.trace (ρ.M * commutator A B)) = z := rfl
    rw [hz_eq, h_var_A_eq, h_var_B_eq, hz_re] at h_psd
    -- h_psd : 0 ≤ variance ρ A + (lam^2 · variance ρ B - 0 · 0) + (0 · 0 - lam · z.im)
    -- Simplify
    linarith
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- Apply discriminant lemma; convert to the target inequality.
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  have h_var_B_nn : 0 ≤ variance ρ B := variance_nonneg ρ hB
  have h_discrim := discrim_le_of_quad_nonneg h_var_B_nn h_quad
  -- h_discrim : (-z.im)^2 ≤ 4 * variance ρ B * variance ρ A
  rw [h_normSq]
  -- Goal: variance ρ A * variance ρ B ≥ 1/4 * z.im^2
  nlinarith [h_discrim, sq_nonneg z.im]

end ComplexDensityMatrix

end UnifiedTheory.LayerB.RobertsonSchrodinger
