/- Two-sided comparison of the actual twisted action with its Gaussian part, around the flat field.
For a divergence-free perturbation with every rotation at most `r` and `10 N r ≤ 1`,
`(1 - 20 N r) C ≤ S ≤ (1 + 30 N r) C`, where `C` is the curl energy. This is a pointwise statement
about the action. No Laplace estimate for the measure follows from it directly. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianCompare
noncomputable section
open PeriodicLattice4 TwistedFlat CommutingShifts TwistedHessian TwistedActionJet TwistedSmallField
open WilsonSingleLinkStaples (Q character)
open scoped Quaternion
open TwistedReflection

variable (n : ℕ) [NeZero n]

theorem sq_lower_delta (u a b δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : a - b ≤ u) : (1 - δ) * a ^ 2 - b ^ 2 / δ ≤ u ^ 2 := by
  have hd : (1 - δ) * a ^ 2 - b ^ 2 / δ ≤ (a - b) ^ 2 := by
    have e : (a - b) ^ 2 - ((1 - δ) * a ^ 2 - b ^ 2 / δ) = (δ * a - b) ^ 2 / δ + b ^ 2 := by
      field_simp
      ring
    have hpos : 0 ≤ (δ * a - b) ^ 2 / δ + b ^ 2 := by positivity
    linarith only [e, hpos]
  by_cases hab : b ≤ a
  · exact hd.trans (pow_le_pow_left₀ (by linarith only [hab]) h 2)
  · push_neg at hab
    have h1 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab.le 2
    have h2 : b ^ 2 ≤ b ^ 2 / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith only [hδ1, sq_nonneg b]
    have h3 : (1 - δ) * a ^ 2 ≤ a ^ 2 := by nlinarith only [hδ, sq_nonneg a]
    linarith only [h1, h2, h3, sq_nonneg u]

theorem sq_upper_delta (u a b δ : ℝ) (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : u ≤ a + b) : u ^ 2 ≤ (1 + δ) * a ^ 2 + 2 * b ^ 2 / δ := by
  have h1 : u ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hu h 2
  have e : (1 + δ) * a ^ 2 + 2 * b ^ 2 / δ - (a + b) ^ 2 =
      (δ * a - b) ^ 2 / δ + b ^ 2 * (1 / δ - 1) := by
    field_simp
    ring
  have hq : 0 ≤ 1 / δ - 1 := by
    rw [sub_nonneg, le_div_iff₀ hδ]
    linarith only [hδ1]
  have hpos : 0 ≤ (δ * a - b) ^ 2 / δ + b ^ 2 * (1 / δ - 1) := by positivity
  linarith only [h1, e, hpos]

/-- Single-plaquette two-sided estimate. -/
theorem term_two_sided (Ω : Fin 3 → Fin 4 → Section (2 * n)) (r δ : ℝ) (hr1 : r ≤ 1) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hr : ∀ μ x, ‖imag Ω μ x‖ ≤ r) (p : PlaquetteIndex (2 * n)) :
    (1 - δ) * ‖plaquetteLie Ω p.2.1.1 p.2.1.2 p.1‖ ^ 2 - 64 * r ^ 2 / δ *
        (‖imag Ω p.2.1.1 p.1‖ ^ 2 + ‖imag Ω p.2.1.2 (step (2 * n) p.1 p.2.1.1)‖ ^ 2 +
          ‖imag Ω p.2.1.1 (step (2 * n) p.1 p.2.1.2)‖ ^ 2 + ‖imag Ω p.2.1.2 p.1‖ ^ 2) ≤
      term n Q (spatialTwist n) character 2 (pertConfig n Ω 1) p ∧
    term n Q (spatialTwist n) character 2 (pertConfig n Ω 1) p ≤
      (1 + δ) * ‖plaquetteLie Ω p.2.1.1 p.2.1.2 p.1‖ ^ 2 + 128 * r ^ 2 / δ *
        (‖imag Ω p.2.1.1 p.1‖ ^ 2 + ‖imag Ω p.2.1.2 (step (2 * n) p.1 p.2.1.1)‖ ^ 2 +
          ‖imag Ω p.2.1.1 (step (2 * n) p.1 p.2.1.2)‖ ^ 2 + ‖imag Ω p.2.1.2 p.1‖ ^ 2) := by
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
  have hgap2 : ‖g - 1‖ ≤ ‖Z‖ + T ^ 2 := by
    have e : g - 1 = (g - 1 - Z) + Z := by abel
    have := norm_add_le (g - 1 - Z) Z
    rw [← e] at this
    linarith only [this, hexp]
  have hT0 : 0 ≤ T := by positivity
  have hTsq0 : 0 ≤ T ^ 2 := sq_nonneg T
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
      mul_le_mul hTsq hCS hTsq0 (by positivity)
    nlinarith only [h3]
  have hl := sq_lower_delta ‖g - 1‖ ‖Z‖ (T ^ 2) δ (norm_nonneg _) hTsq0 hδ hδ1 hgap
  have hu := sq_upper_delta ‖g - 1‖ ‖Z‖ (T ^ 2) δ (norm_nonneg _) (norm_nonneg _) hTsq0 hδ hδ1 hgap2
  have hdiv : (T ^ 2) ^ 2 / δ ≤ 64 * r ^ 2 / δ * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2) := by
    have e : 64 * r ^ 2 / δ * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2) =
        (64 * r ^ 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2)) / δ := by ring
    rw [e]
    exact div_le_div_of_nonneg_right hT44 hδ.le
  have e2 : 128 * r ^ 2 / δ * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2) =
      2 * (64 * r ^ 2 / δ * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2)) := by ring
  have e3 : 2 * (T ^ 2) ^ 2 / δ = 2 * ((T ^ 2) ^ 2 / δ) := by ring
  constructor
  · linarith only [hl, hdiv]
  · linarith only [hu, hdiv, e2, e3]

/-- Global two-sided estimate, with the curl energy `C` and norm `W`. -/
theorem action_two_sided (Ω : Fin 3 → Fin 4 → Section (2 * n)) (r δ : ℝ) (hr1 : r ≤ 1) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hr : ∀ μ x, ‖imag Ω μ x‖ ≤ r) :
    (1 - δ) * (∑ a, curlEnergy (shifts a) (Ω a)) - 384 * r ^ 2 / δ * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 ≤
      action n Q (spatialTwist n) character 1 2 (pertConfig n Ω 1) ∧
    action n Q (spatialTwist n) character 1 2 (pertConfig n Ω 1) ≤
      (1 + δ) * (∑ a, curlEnergy (shifts a) (Ω a)) + 768 * r ^ 2 / δ * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 := by
  unfold action
  rw [one_mul]
  have hl := Finset.sum_le_sum (s := Finset.univ) fun p _ =>
    (term_two_sided n Ω r δ hr1 hδ hδ1 hr p).1
  have hu := Finset.sum_le_sum (s := Finset.univ) fun p _ =>
    (term_two_sided n Ω r δ hr1 hδ hδ1 hr p).2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, lie_sum, link_count] at hl
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, lie_sum, link_count] at hu
  have e1 : 64 * r ^ 2 / δ * (6 * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2) = 384 * r ^ 2 / δ * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 := by
    ring
  have e2 : 128 * r ^ 2 / δ * (6 * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2) = 768 * r ^ 2 / δ * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 := by
    ring
  rw [e1] at hl
  rw [e2] at hu
  exact ⟨hl, hu⟩

/-- **Gaussian comparison in Coulomb form.** If `div Ω = 0` and `10 N r ≤ 1`, with rotations at most
`r`, the action equals the curl energy up to relative error `30 N r`. -/
theorem gaussian_comparison (Ω : Fin 3 → Fin 4 → Section (2 * n))
    (hdiv : ∀ a, div (shifts a) (Ω a) = 0) (r : ℝ) (hr0 : 0 < r)
    (hNr : 10 * ((2 * n : ℕ) : ℝ) * r ≤ 1) (hr : ∀ μ x, ‖imag Ω μ x‖ ≤ r) :
    (1 - 20 * ((2 * n : ℕ) : ℝ) * r) * (∑ a, curlEnergy (shifts a) (Ω a)) ≤
      action n Q (spatialTwist n) character 1 2 (pertConfig n Ω 1) ∧
    action n Q (spatialTwist n) character 1 2 (pertConfig n Ω 1) ≤
      (1 + 30 * ((2 * n : ℕ) : ℝ) * r) * (∑ a, curlEnergy (shifts a) (Ω a)) := by
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hNd
  have hN : (1 : ℝ) ≤ N := by
    rw [hNd]
    exact_mod_cast NeZero.pos (2 * n)
  have hNpos : 0 < N := by linarith only [hN]
  have hr1 : r ≤ 1 := by nlinarith only [hN, hNr, hr0]
  set δ := 10 * N * r with hδd
  have hδ : 0 < δ := by positivity
  set C := ∑ a, curlEnergy (shifts a) (Ω a) with hC
  set W := ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  -- `W ≤ N² C / 4`, from coercivity on the divergence-free part
  have hcoer : 4 * W ≤ N ^ 2 * C := by
    have hc := Finset.sum_le_sum (s := Finset.univ) fun a _ => colour_bound a (Ω a)
    simp only [hdiv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero] at hc
    rw [← Finset.mul_sum] at hc
    have hl := lam_lower (2 * n)
    rw [← hNd] at hl
    have h1 : 4 / N ^ 2 * W ≤ C := (mul_le_mul_of_nonneg_right hl hW0).trans hc
    have hN2 : 0 < N ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h1 hN2.le
    have e : N ^ 2 * (4 / N ^ 2 * W) = 4 * W := by field_simp
    rwa [e] at this
  have hC0 : 0 ≤ C := by
    have hN2 : 0 < N ^ 2 := by positivity
    by_contra hneg
    push_neg at hneg
    nlinarith only [hcoer, hW0, mul_neg_of_pos_of_neg hN2 hneg]
  have hlin : r ^ 2 / δ * W ≤ N * r / 40 * C := by
    have hsimp : r ^ 2 / δ = r / (10 * N) := by
      rw [hδd]
      field_simp
    rw [hsimp]
    have h2 : r / (10 * N) * W = r / (40 * N) * (4 * W) := by
      field_simp
      ring
    rw [h2]
    have hq : 0 ≤ r / (40 * N) := by positivity
    have := mul_le_mul_of_nonneg_left hcoer hq
    have e3 : r / (40 * N) * (N ^ 2 * C) = N * r / 40 * C := by
      field_simp
    rwa [e3] at this
  obtain ⟨hl, hu⟩ := action_two_sided n Ω r δ hr1 hδ hNr hr
  have e1 : 384 * r ^ 2 / δ * W = 384 * (r ^ 2 / δ * W) := by ring
  have e2 : 768 * r ^ 2 / δ * W = 768 * (r ^ 2 / δ * W) := by ring
  rw [e1] at hl
  rw [e2] at hu
  have hNrC : 0 ≤ N * r * C := by positivity
  constructor
  · have e : (1 - 20 * N * r) * C = C - 20 * (N * r * C) := by ring
    have e' : (1 - δ) * C = C - 10 * (N * r * C) := by rw [hδd]; ring
    have e'' : N * r / 40 * C = (N * r * C) / 40 := by ring
    rw [e]
    rw [e'] at hl
    rw [e''] at hlin
    linarith only [hl, hlin, hNrC]
  · have e : (1 + 30 * N * r) * C = C + 30 * (N * r * C) := by ring
    have e' : (1 + δ) * C = C + 10 * (N * r * C) := by rw [hδd]; ring
    have e'' : N * r / 40 * C = (N * r * C) / 40 := by ring
    rw [e]
    rw [e'] at hu
    rw [e''] at hlin
    linarith only [hu, hlin, hNrC]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianCompare
