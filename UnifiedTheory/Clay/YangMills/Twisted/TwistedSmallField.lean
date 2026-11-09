/- A nonperturbative coercivity estimate around the flat twisted field, with explicit
constants. A divergence-free perturbation with every link rotation at most `1/(20 N)`
has twisted action at least `‖Ω‖²/N²`. Existence of such a gauge for a given field
near the flat orbit is not proved here, and no measure is involved. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedActionJet
import UnifiedTheory.Clay.YangMills.Twisted.TwistedStability
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Angle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField
noncomputable section
open PeriodicLattice4 TwistedRectangle TwistedFlat CommutingShifts TwistedHessian TwistedActionJet
open WilsonSingleLinkStaples (Q character)
open scoped Quaternion

/-! ### Exponentials of imaginary quaternions -/

theorem exp_imag (Y : ℍ[ℝ]) (hY : Y.re = 0) :
    NormedSpace.exp Y = ((Real.cos ‖Y‖ : ℝ) : ℍ[ℝ]) + (Real.sin ‖Y‖ / ‖Y‖) • Y :=
  Quaternion.exp_of_re_eq_zero Y hY

theorem norm_exp_imag (Y : ℍ[ℝ]) (hY : Y.re = 0) : ‖NormedSpace.exp Y‖ = 1 := by
  rw [Quaternion.norm_exp, hY]
  simp

theorem exp_re_eq (Y : ℍ[ℝ]) (hY : Y.re = 0) : (NormedSpace.exp Y).re = Real.cos ‖Y‖ := by
  rw [exp_imag Y hY]
  simp [hY]

/-- First-order bound. -/
theorem norm_exp_sub_one (Y : ℍ[ℝ]) (hY : Y.re = 0) : ‖NormedSpace.exp Y - 1‖ ≤ ‖Y‖ := by
  have h : ‖NormedSpace.exp Y - 1‖ ^ 2 = 2 - 2 * Real.cos ‖Y‖ := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self]
    have hn : Quaternion.normSq (NormedSpace.exp Y) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, norm_exp_imag Y hY, one_mul]
    rw [Quaternion.normSq_def'] at hn ⊢
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one, exp_re_eq Y hY]
      at hn ⊢
    linear_combination hn
  have hc := Real.one_sub_sq_div_two_le_cos (x := ‖Y‖)
  exact abs_le_of_sq_le_sq' (by rw [h]; linarith only [hc]) (norm_nonneg Y) |>.2

/-- Second-order bound, for rotations at most one. -/
theorem norm_exp_sub_one_sub (Y : ℍ[ℝ]) (hY : Y.re = 0) (h1 : ‖Y‖ ≤ 1) :
    ‖NormedSpace.exp Y - 1 - Y‖ ≤ ‖Y‖ ^ 2 := by
  set r := ‖Y‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg Y
  have hc := Real.one_sub_sq_div_two_le_cos (x := r)
  have hc1 := Real.cos_le_one r
  rcases hr0.eq_or_lt with h0 | hpos
  · have hY0 : Y = 0 := norm_eq_zero.mp (by rw [← hr, ← h0])
    simp [hY0]
    positivity
  have hs1 : r - r ^ 3 / 4 < Real.sin r := Real.sin_gt_sub_cube hpos h1
  have hs2 : Real.sin r ≤ r := Real.sin_le hr0
  have hdecomp : NormedSpace.exp Y - 1 - Y =
      ((Real.cos r - 1 : ℝ) : ℍ[ℝ]) + (Real.sin r / r - 1) • Y := by
    rw [exp_imag Y hY, sub_smul, one_smul]
    push_cast
    abel
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [Quaternion.norm_coe, norm_smul, ← hr, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (by linarith only [hc1] : Real.cos r - 1 ≤ 0)]
  have hq : Real.sin r / r - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hpos]
    exact hs2
  rw [abs_of_nonpos hq]
  have e : -(Real.sin r / r - 1) * r = r - Real.sin r := by
    field_simp
    ring
  rw [e]
  have h3 : r ^ 3 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
  linarith only [hc, hs1, h3, sq_nonneg r]

/-! ### The plaquette expansion -/

/-- The four-exponential product differs from `1 + ΣY` by at most `(Σ‖Y‖)²`. -/
theorem product_expansion (A B C D : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0)
    (hD : D.re = 0) (h1A : ‖A‖ ≤ 1) (h1B : ‖B‖ ≤ 1) (h1C : ‖C‖ ≤ 1) (h1D : ‖D‖ ≤ 1) :
    ‖NormedSpace.exp A * NormedSpace.exp B * (NormedSpace.exp C * NormedSpace.exp D) - 1 -
        (A + B + C + D)‖ ≤ (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2 := by
  set E₁ := NormedSpace.exp A
  set E₂ := NormedSpace.exp B
  set E₃ := NormedSpace.exp C
  set E₄ := NormedSpace.exp D
  have n₁ : ‖E₁‖ = 1 := norm_exp_imag A hA
  have n₂ : ‖E₂‖ = 1 := norm_exp_imag B hB
  have n₃ : ‖E₃‖ = 1 := norm_exp_imag C hC
  have a₁ : ‖E₁ - 1‖ ≤ ‖A‖ := norm_exp_sub_one A hA
  have a₂ : ‖E₂ - 1‖ ≤ ‖B‖ := norm_exp_sub_one B hB
  have a₃ : ‖E₃ - 1‖ ≤ ‖C‖ := norm_exp_sub_one C hC
  have a₄ : ‖E₄ - 1‖ ≤ ‖D‖ := norm_exp_sub_one D hD
  have b₁ : ‖E₁ - 1 - A‖ ≤ ‖A‖ ^ 2 := norm_exp_sub_one_sub A hA h1A
  have b₂ : ‖E₂ - 1 - B‖ ≤ ‖B‖ ^ 2 := norm_exp_sub_one_sub B hB h1B
  have b₃ : ‖E₃ - 1 - C‖ ≤ ‖C‖ ^ 2 := norm_exp_sub_one_sub C hC h1C
  have b₄ : ‖E₄ - 1 - D‖ ≤ ‖D‖ ^ 2 := norm_exp_sub_one_sub D hD h1D
  -- partial products stay close to one
  have p₂ : ‖E₁ * E₂ - 1‖ ≤ ‖A‖ + ‖B‖ := by
    have e : E₁ * E₂ - 1 = E₁ * (E₂ - 1) + (E₁ - 1) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, n₁, one_mul]
    linarith only [a₁, a₂]
  have p₃ : ‖E₁ * E₂ * E₃ - 1‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
    have e : E₁ * E₂ * E₃ - 1 = E₁ * E₂ * (E₃ - 1) + (E₁ * E₂ - 1) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, n₁, n₂, one_mul, one_mul]
    linarith only [a₃, p₂]
  have hdec : E₁ * E₂ * (E₃ * E₄) - 1 - (A + B + C + D) =
      (E₁ - 1 - A) + (E₂ - 1 - B) + (E₃ - 1 - C) + (E₄ - 1 - D) +
        (E₁ - 1) * (E₂ - 1) + (E₁ * E₂ - 1) * (E₃ - 1) + (E₁ * E₂ * E₃ - 1) * (E₄ - 1) := by
    noncomm_ring
  rw [hdec]
  have t₁ : ‖(E₁ - 1) * (E₂ - 1)‖ ≤ ‖A‖ * ‖B‖ := by
    rw [norm_mul]
    exact mul_le_mul a₁ a₂ (norm_nonneg _) (norm_nonneg _)
  have t₂ : ‖(E₁ * E₂ - 1) * (E₃ - 1)‖ ≤ (‖A‖ + ‖B‖) * ‖C‖ := by
    rw [norm_mul]
    exact mul_le_mul p₂ a₃ (norm_nonneg _) (by positivity)
  have t₃ : ‖(E₁ * E₂ * E₃ - 1) * (E₄ - 1)‖ ≤ (‖A‖ + ‖B‖ + ‖C‖) * ‖D‖ := by
    rw [norm_mul]
    exact mul_le_mul p₃ a₄ (norm_nonneg _) (by positivity)
  have hsum := norm_add_le ((E₁ - 1 - A) + (E₂ - 1 - B) + (E₃ - 1 - C) + (E₄ - 1 - D) +
        (E₁ - 1) * (E₂ - 1) + (E₁ * E₂ - 1) * (E₃ - 1)) ((E₁ * E₂ * E₃ - 1) * (E₄ - 1))
  have h5 := norm_add_le ((E₁ - 1 - A) + (E₂ - 1 - B) + (E₃ - 1 - C) + (E₄ - 1 - D) +
        (E₁ - 1) * (E₂ - 1)) ((E₁ * E₂ - 1) * (E₃ - 1))
  have h4 := norm_add_le ((E₁ - 1 - A) + (E₂ - 1 - B) + (E₃ - 1 - C) + (E₄ - 1 - D))
    ((E₁ - 1) * (E₂ - 1))
  have h3 := norm_add_le ((E₁ - 1 - A) + (E₂ - 1 - B) + (E₃ - 1 - C)) (E₄ - 1 - D)
  have h2 := norm_add_le ((E₁ - 1 - A) + (E₂ - 1 - B)) (E₃ - 1 - C)
  have h1 := norm_add_le (E₁ - 1 - A) (E₂ - 1 - B)
  have hexp : (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2 +
      ‖A‖ * ‖B‖ + (‖A‖ + ‖B‖) * ‖C‖ + (‖A‖ + ‖B‖ + ‖C‖) * ‖D‖ +
      (‖A‖ * ‖B‖ + (‖A‖ + ‖B‖) * ‖C‖ + (‖A‖ + ‖B‖ + ‖C‖) * ‖D‖) := by ring
  have hpos : 0 ≤ ‖A‖ * ‖B‖ + (‖A‖ + ‖B‖) * ‖C‖ + (‖A‖ + ‖B‖ + ‖C‖) * ‖D‖ := by positivity
  linarith only [hsum, h5, h4, h3, h2, h1, b₁, b₂, b₃, b₄, t₁, t₂, t₃, hexp, hpos]

/-! ### The field-theory estimate -/

open TwistedReflection PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge

variable (n : ℕ) [NeZero n]

theorem imag_re {N : ℕ} [NeZero N] (Ω : Fin 3 → Fin 4 → Section N) (μ : Fin 4) (x : Vertex N) :
    (imag Ω μ x).re = 0 := by
  simp [imag, Fin.sum_univ_three, basis]

theorem imag_normSq {N : ℕ} [NeZero N] (Ω : Fin 3 → Fin 4 → Section N) (μ : Fin 4) (x : Vertex N) :
    ‖imag Ω μ x‖ ^ 2 = ∑ a, Ω a μ x ^ 2 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp [imag, Fin.sum_univ_three, basis]

/-- Conjugation by a unit quaternion preserves norms. -/
theorem norm_conj (u : Q) (X : ℍ[ℝ]) :
    ‖(u : ℍ[ℝ]) * X * ((u⁻¹ : Q) : ℍ[ℝ])‖ = ‖X‖ := by
  rw [norm_mul, norm_mul, TwistedStability.norm_coe, TwistedStability.norm_coe, one_mul,
    mul_one]

theorem basis_coord_norm (c : Fin 3 → ℝ) : ‖∑ a, c a • basis a‖ ^ 2 = ∑ a, c a ^ 2 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp [Fin.sum_univ_three, basis]

theorem basis_sum_re (c : Fin 3 → ℝ) : (∑ a, c a • basis a).re = 0 := by
  simp [Fin.sum_univ_three, basis]

/-- A real inequality: a lower bound `u ≥ a - b` gives `u² ≥ a²/2 - b²`. -/
theorem sq_lower (u a b : ℝ) (ha : 0 ≤ a) (h : a - b ≤ u) :
    a ^ 2 / 2 - b ^ 2 ≤ u ^ 2 := by
  by_cases hab : a ≤ b
  · have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
    nlinarith [sq_nonneg u, sq_nonneg a]
  · push_neg at hab
    have h1 : (a - b) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by linarith) h 2
    nlinarith [sq_nonneg (a - 2 * b)]

/-- Single-plaquette estimate at `t = 1`. -/
theorem term_lower (Ω : Fin 3 → Fin 4 → Section (2 * n)) (r : ℝ) (hr1 : r ≤ 1)
    (hr : ∀ μ x, ‖imag Ω μ x‖ ≤ r) (p : PlaquetteIndex (2 * n)) :
    ‖plaquetteLie Ω p.2.1.1 p.2.1.2 p.1‖ ^ 2 / 2 - 64 * r ^ 2 *
        (‖imag Ω p.2.1.1 p.1‖ ^ 2 + ‖imag Ω p.2.1.2 (step (2 * n) p.1 p.2.1.1)‖ ^ 2 +
          ‖imag Ω p.2.1.1 (step (2 * n) p.1 p.2.1.2)‖ ^ 2 + ‖imag Ω p.2.1.2 p.1‖ ^ 2) ≤
      term n Q (spatialTwist n) character 2 (pertConfig n Ω 1) p := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
  simp only
  rw [term_pert]
  simp only
  set A := lieA n Ω μ ν x with hAd
  set B := lieB n Ω μ ν x with hBd
  set C := lieC n Ω μ ν x with hCd
  set D := lieD n Ω μ ν x with hDd
  have nA : ‖A‖ = ‖imag Ω μ x‖ := rfl
  have nB : ‖B‖ = ‖imag Ω ν (step (2 * n) x μ)‖ := norm_conj _ _
  have nC : ‖C‖ = ‖imag Ω μ (step (2 * n) x ν)‖ := by
    rw [hCd, lieC, norm_neg, norm_conj]
  have nD : ‖D‖ = ‖imag Ω ν x‖ := by
    rw [hDd, lieD, norm_neg]
  have rA : A.re = 0 := imag_re Ω μ x
  have rB : B.re = 0 := by
    rw [hBd, lieB, conj_imag]
    exact basis_sum_re _
  have rC : C.re = 0 := by
    rw [hCd, lieC, conj_imag, Quaternion.re_neg, basis_sum_re, neg_zero]
  have rD : D.re = 0 := by
    rw [hDd, lieD, Quaternion.re_neg, imag_re, neg_zero]
  have hAr : ‖A‖ ≤ r := by rw [nA]; exact hr _ _
  have hBr : ‖B‖ ≤ r := by rw [nB]; exact hr _ _
  have hCr : ‖C‖ ≤ r := by rw [nC]; exact hr _ _
  have hDr : ‖D‖ ≤ r := by rw [nD]; exact hr _ _
  have hexp := product_expansion A B C D rA rB rC rD (hAr.trans hr1) (hBr.trans hr1)
    (hCr.trans hr1) (hDr.trans hr1)
  have hG : G A B C D 1 = NormedSpace.exp A * NormedSpace.exp B *
      (NormedSpace.exp C * NormedSpace.exp D) := by
    simp only [G, one_smul]
  rw [← hG] at hexp
  set g := G A B C D 1 with hg
  have ng : ‖g‖ = 1 := by
    rw [hG, norm_mul, norm_mul, norm_mul, norm_exp_imag A rA, norm_exp_imag B rB,
      norm_exp_imag C rC, norm_exp_imag D rD]
    norm_num
  have hterm : 2 - 2 * g.re = ‖g - 1‖ ^ 2 := by
    have h1 : Quaternion.normSq g = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, ng, one_mul]
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self]
    rw [Quaternion.normSq_def'] at h1 ⊢
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
    linear_combination -h1
  rw [hterm]
  have hZ : plaquetteLie Ω μ ν x = A + B + C + D := rfl
  rw [hZ, ← nA, ← nB, ← nC, ← nD]
  set Z := A + B + C + D
  set T := ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ with hT
  have hgap : ‖Z‖ - T ^ 2 ≤ ‖g - 1‖ := by
    have e : Z = (g - 1) - (g - 1 - Z) := by abel
    have := norm_sub_le (g - 1) (g - 1 - Z)
    rw [← e] at this
    linarith only [this, hexp]
  have hbase := sq_lower ‖g - 1‖ ‖Z‖ (T ^ 2) (norm_nonneg _) hgap
  have hT0 : 0 ≤ T := by positivity
  have hT4 : T ≤ 4 * r := by linarith only [hAr, hBr, hCr, hDr, hT]
  have hTsq : T ^ 2 ≤ 16 * r ^ 2 := by
    have := pow_le_pow_left₀ hT0 hT4 2
    nlinarith only [this]
  have hCS : T ^ 2 ≤ 4 * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2) := by
    rw [hT]
    nlinarith only [sq_nonneg (‖A‖ - ‖B‖), sq_nonneg (‖A‖ - ‖C‖), sq_nonneg (‖A‖ - ‖D‖),
      sq_nonneg (‖B‖ - ‖C‖), sq_nonneg (‖B‖ - ‖D‖), sq_nonneg (‖C‖ - ‖D‖)]
  have hT44 : (T ^ 2) ^ 2 ≤ 64 * r ^ 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2) := by
    have h3 : (T ^ 2) * (T ^ 2) ≤ (16 * r ^ 2) *
        (4 * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2)) :=
      mul_le_mul hTsq hCS (by positivity) (by positivity)
    nlinarith only [h3]
  linarith only [hbase, hT44]

/-- Summing a translated nonnegative density returns the original sum. -/
theorem sum_step {N : ℕ} [NeZero N] (f : Vertex N → ℝ) (μ : Fin 4) :
    ∑ x, f (step N x μ) = ∑ y, f y :=
  Equiv.sum_comp (stepEquiv (N := N) μ) f

/-- Each link lies in six plaquettes. -/
theorem link_count (Ω : Fin 3 → Fin 4 → Section (2 * n)) :
    ∑ p : PlaquetteIndex (2 * n),
        (‖imag Ω p.2.1.1 p.1‖ ^ 2 + ‖imag Ω p.2.1.2 (step (2 * n) p.1 p.2.1.1)‖ ^ 2 +
          ‖imag Ω p.2.1.1 (step (2 * n) p.1 p.2.1.2)‖ ^ 2 + ‖imag Ω p.2.1.2 p.1‖ ^ 2) =
      6 * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 := by
  let M : Fin 4 → ℝ := fun μ => ∑ x, ‖imag Ω μ x‖ ^ 2
  have hM : M = fun μ => ∑ x, ‖imag Ω μ x‖ ^ 2 := rfl
  have hpl (μ ν : Fin 4) : ∑ x, (‖imag Ω μ x‖ ^ 2 + ‖imag Ω ν (step (2 * n) x μ)‖ ^ 2 +
      ‖imag Ω μ (step (2 * n) x ν)‖ ^ 2 + ‖imag Ω ν x‖ ^ 2) = 2 * M μ + 2 * M ν := by
    simp only [Finset.sum_add_distrib]
    rw [sum_step (fun y => ‖imag Ω ν y‖ ^ 2) μ, sum_step (fun y => ‖imag Ω μ y‖ ^ 2) ν]
    simp only [hM]
    ring
  have hL : ∑ p : PlaquetteIndex (2 * n),
      (‖imag Ω p.2.1.1 p.1‖ ^ 2 + ‖imag Ω p.2.1.2 (step (2 * n) p.1 p.2.1.1)‖ ^ 2 +
        ‖imag Ω p.2.1.1 (step (2 * n) p.1 p.2.1.2)‖ ^ 2 + ‖imag Ω p.2.1.2 p.1‖ ^ 2) =
      ∑ d : Plane, (2 * M d.1.1 + 2 * M d.1.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact hpl d.1.1 d.1.2
  have hP : ∑ d : Plane, (2 * M d.1.1 + 2 * M d.1.2) =
      ∑ μ, ∑ ν, if μ < ν then 2 * M μ + 2 * M ν else 0 :=
    plane_sum (fun μ ν => 2 * M μ + 2 * M ν)
  rw [hL, hP]
  have hR : ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 = ∑ μ, M μ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [hM, imag_normSq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [hR]
  simp (decide := true) only [Fin.sum_univ_four, if_true, if_false]
  ring

/-- The curl energy in plaquette form. -/
theorem lie_sum (Ω : Fin 3 → Fin 4 → Section (2 * n)) :
    ∑ p : PlaquetteIndex (2 * n), ‖plaquetteLie Ω p.2.1.1 p.2.1.2 p.1‖ ^ 2 =
      ∑ a, curlEnergy (shifts a) (Ω a) := by
  simp only [plaquetteLie_eq, basis_coord_norm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hn (c : Section (2 * n)) : ‖c‖ ^ 2 = ∑ x, c x ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  unfold curlEnergy
  rw [← plane_sum (fun μ ν => ‖curl (shifts a) (Ω a) μ ν‖ ^ 2), Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [hn]

/-- **Nonperturbative small-field bound.** For every link rotation at most `r ≤ 1`. -/
theorem action_lower (Ω : Fin 3 → Fin 4 → Section (2 * n)) (r : ℝ) (hr1 : r ≤ 1)
    (hr : ∀ μ x, ‖imag Ω μ x‖ ≤ r) :
    (∑ a, curlEnergy (shifts a) (Ω a)) / 2 - 384 * r ^ 2 * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 ≤
      action n Q (spatialTwist n) character 1 2 (pertConfig n Ω 1) := by
  unfold action
  rw [one_mul]
  have h := Finset.sum_le_sum (s := Finset.univ) fun p _ => term_lower n Ω r hr1 hr p
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, lie_sum, link_count] at h
  linarith only [h]

theorem lam_lower (N : ℕ) [NeZero N] : 4 / (N : ℝ) ^ 2 ≤ lam N := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hx0 : 0 ≤ Real.pi / (2 * N) := by positivity
  have hx1 : Real.pi / (2 * N) ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith only [hN]
  have hs := Real.mul_le_sin hx0 hx1
  have e : 2 / Real.pi * (Real.pi / (2 * N)) = 1 / (N : ℝ) := by
    have := Real.pi_pos.ne'
    field_simp
  rw [e] at hs
  have hsq : (1 / (N : ℝ)) ^ 2 ≤ Real.sin (Real.pi / (2 * N)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hs 2
  unfold lam
  have e2 : 4 / (N : ℝ) ^ 2 = 4 * (1 / (N : ℝ)) ^ 2 := by ring
  rw [e2]
  linarith only [hsq]

/-- **Coercivity without a gauge condition.** The divergence appears with an explicit sign. -/
theorem action_coercive (Ω : Fin 3 → Fin 4 → Section (2 * n)) (r : ℝ) (hr1 : r ≤ 1)
    (hr : ∀ μ x, ‖imag Ω μ x‖ ≤ r) :
    (lam (2 * n) / 2 - 384 * r ^ 2) * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 -
        (∑ a, ‖div (shifts a) (Ω a)‖ ^ 2) / 2 ≤
      action n Q (spatialTwist n) character 1 2 (pertConfig n Ω 1) := by
  have h := action_lower n Ω r hr1 hr
  have hc := Finset.sum_le_sum (s := Finset.univ) fun a _ => colour_bound a (Ω a)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hc
  linarith only [h, hc]

/-- **Small-field coercivity in Coulomb form.** Divergence-free, with every rotation at most
`1/(20 N)`, the action is at least `‖Ω‖²/N²`. -/
theorem action_coercive_coulomb (Ω : Fin 3 → Fin 4 → Section (2 * n))
    (hdiv : ∀ a, div (shifts a) (Ω a) = 0)
    (hr : ∀ μ x, ‖imag Ω μ x‖ ≤ 1 / (20 * ((2 * n : ℕ) : ℝ))) :
    (∑ a, ∑ μ, ‖Ω a μ‖ ^ 2) / ((2 * n : ℕ) : ℝ) ^ 2 ≤
      action n Q (spatialTwist n) character 1 2 (pertConfig n Ω 1) := by
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hNd
  have hN : (1 : ℝ) ≤ N := by
    rw [hNd]
    exact_mod_cast NeZero.pos (2 * n)
  have hNpos : 0 < N := by linarith only [hN]
  set r := 1 / (20 * N) with hrd
  have hr1 : r ≤ 1 := by
    rw [hrd, div_le_one (by positivity)]
    linarith only [hN]
  have hc := action_coercive n Ω r hr1 hr
  simp only [hdiv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, zero_div, sub_zero] at hc
  refine le_trans ?_ hc
  have hl := lam_lower (2 * n)
  rw [← hNd] at hl
  have hr2 : 384 * r ^ 2 = 96 / 100 / N ^ 2 := by
    rw [hrd]
    field_simp
    ring
  have hcoef : 1 / N ^ 2 ≤ lam (2 * n) / 2 - 384 * r ^ 2 := by
    rw [hr2]
    have e1 : 4 / N ^ 2 / 2 = 2 / N ^ 2 := by ring
    have e2 : 2 / N ^ 2 - 96 / 100 / N ^ 2 = (104 / 100) / N ^ 2 := by ring
    have e3 : 1 / N ^ 2 ≤ (104 / 100) / N ^ 2 :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith only [hl, e1, e2, e3]
  have hS : 0 ≤ ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hcoef hS
  have e4 : (∑ a, ∑ μ, ‖Ω a μ‖ ^ 2) / N ^ 2 = 1 / N ^ 2 * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 := by ring
  rw [e4]
  exact this

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField
