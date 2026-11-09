import Mathlib.Analysis.Normed.Algebra.QuaternionExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A value-level lower bound for one plaquette

For imaginary quaternions `A B C D` (the transported link increments of a plaquette around a flat background) with
`s = ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ ≤ 1/2`,

  `((‖A + B + C + D‖ - 5 s²)₊)² / 2 ≤ 1 - Re (exp A * exp B * exp C * exp D)`.

The left side involves only the linear curl `A + B + C + D` and a quartic error `s⁴`, with constants independent of the
lattice. This is the per-plaquette step of the scale-invariant coercivity argument (`COERCIVITY_SCALE_INVARIANT.md`,
part (i)): summed over plaquettes, the error is `Σ_p s_p⁴ ≲ ‖a‖₄⁴`, which a Sobolev inequality controls by the
square of the energy, with no `n`-dependent sup norm.
-/

open NormedSpace
open scoped Quaternion

namespace TwistedPlaquetteValue

/-- The exponential of an imaginary quaternion is within `‖η‖²` of `1 + η` when `‖η‖ ≤ 1`. -/
theorem exp_sub_one_sub_le (η : ℍ[ℝ]) (hη : η.re = 0) (h1 : ‖η‖ ≤ 1) :
    ‖exp η - 1 - η‖ ≤ ‖η‖ ^ 2 := by
  by_cases hη0 : η = 0
  · subst hη0; simp
  have hpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
  rw [Quaternion.exp_of_re_eq_zero η hη]
  set t := ‖η‖ with ht
  have ht0 : 0 ≤ t := hpos.le
  have e : (↑(Real.cos t) + (Real.sin t / t) • η - 1 - η : ℍ[ℝ]) =
      ↑(Real.cos t - 1) + (Real.sin t / t - 1) • η := by
    rw [sub_smul, one_smul, Quaternion.coe_sub, Quaternion.coe_one]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Quaternion.norm_coe, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← ht]
  have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have hc2 : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
  have hs1 : Real.sin t ≤ t := Real.sin_le ht0
  have hs2 : t - t ^ 3 / 4 < Real.sin t := Real.sin_gt_sub_cube hpos h1
  have hq : Real.sin t / t - 1 = (Real.sin t - t) / t := by field_simp
  rw [hq, abs_div, abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  nlinarith only [hc2, hs2, h1, ht0]

/-- Unit quaternions: `1 - Re q = ‖q - 1‖² / 2`. -/
theorem one_sub_re (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : 1 - q.re = ‖q - 1‖ ^ 2 / 2 := by
  have h2 : Quaternion.normSq q = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hq, one_mul]
  rw [show ‖q - 1‖ ^ 2 = Quaternion.normSq (q - 1) by rw [Quaternion.normSq_eq_norm_mul_self, sq]]
  rw [Quaternion.normSq_def'] at h2 ⊢
  simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
  nlinarith only [h2]

/-- The expansion of a four-fold product with no first-order terms. -/
theorem prod_four_expand (a b c d : ℍ[ℝ]) :
    (1 + a) * (1 + b) * (1 + c) * (1 + d) - 1 - (a + b + c + d) =
      a * b + a * c + a * d + b * c + b * d + c * d +
        (a * b * c + a * b * d + a * c * d + b * c * d) + a * b * c * d := by
  noncomm_ring

theorem prod_four_le (a b c d : ℍ[ℝ]) (hs : ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ ≤ 1) :
    ‖(1 + a) * (1 + b) * (1 + c) * (1 + d) - 1 - (a + b + c + d)‖ ≤
      (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) ^ 2 := by
  rw [prod_four_expand]
  set u := ‖a‖; set v := ‖b‖; set w := ‖c‖; set x := ‖d‖
  have hu : 0 ≤ u := norm_nonneg _
  have hv : 0 ≤ v := norm_nonneg _
  have hw : 0 ≤ w := norm_nonneg _
  have hx : 0 ≤ x := norm_nonneg _
  have m2 (p q : ℍ[ℝ]) : ‖p * q‖ = ‖p‖ * ‖q‖ := norm_mul p q
  have m3 (p q r : ℍ[ℝ]) : ‖p * q * r‖ = ‖p‖ * ‖q‖ * ‖r‖ := by rw [norm_mul, norm_mul]
  have m4 (p q r t : ℍ[ℝ]) : ‖p * q * r * t‖ = ‖p‖ * ‖q‖ * ‖r‖ * ‖t‖ := by
    rw [norm_mul, norm_mul, norm_mul]
  have T : ‖a * b + a * c + a * d + b * c + b * d + c * d +
        (a * b * c + a * b * d + a * c * d + b * c * d) + a * b * c * d‖ ≤
      (u * v + u * w + u * x + v * w + v * x + w * x) +
        (u * v * w + u * v * x + u * w * x + v * w * x) + u * v * w * x := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (le_of_eq (m2 _ _)) (le_of_eq (m2 _ _))))
        (le_of_eq (m2 _ _)))) (le_of_eq (m2 _ _)))) (le_of_eq (m2 _ _)))) (le_of_eq (m2 _ _)))
    · refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (le_of_eq (m3 _ _ _)) (le_of_eq (m3 _ _ _))))
        (le_of_eq (m3 _ _ _)))) (le_of_eq (m3 _ _ _)))
    · exact le_of_eq (m4 _ _ _ _)
  refine T.trans ?_
  set s := u + v + w + x with hs'
  have e2 : 2 * (u * v + u * w + u * x + v * w + v * x + w * x) ≤ s ^ 2 := by
    rw [hs']; nlinarith only [sq_nonneg u, sq_nonneg v, sq_nonneg w, sq_nonneg x]
  have e3 : 3 * (u * v * w + u * v * x + u * w * x + v * w * x) ≤
      s * (u * v + u * w + u * x + v * w + v * x + w * x) := by
    rw [hs']
    nlinarith only [mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hw,
      mul_nonneg (mul_nonneg hu hu) hx, mul_nonneg (mul_nonneg hv hv) hu,
      mul_nonneg (mul_nonneg hv hv) hw, mul_nonneg (mul_nonneg hv hv) hx,
      mul_nonneg (mul_nonneg hw hw) hu, mul_nonneg (mul_nonneg hw hw) hv,
      mul_nonneg (mul_nonneg hw hw) hx, mul_nonneg (mul_nonneg hx hx) hu,
      mul_nonneg (mul_nonneg hx hx) hv, mul_nonneg (mul_nonneg hx hx) hw]
  have e4 : 4 * (u * v * w * x) ≤ s * (u * v * w + u * v * x + u * w * x + v * w * x) := by
    rw [hs']
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hw,
      mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hx, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hx,
      mul_nonneg (mul_nonneg (mul_nonneg hv hv) hu) hw, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hu) hx,
      mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hx, mul_nonneg (mul_nonneg (mul_nonneg hw hw) hu) hv,
      mul_nonneg (mul_nonneg (mul_nonneg hw hw) hu) hx, mul_nonneg (mul_nonneg (mul_nonneg hw hw) hv) hx,
      mul_nonneg (mul_nonneg (mul_nonneg hx hx) hu) hv, mul_nonneg (mul_nonneg (mul_nonneg hx hx) hu) hw,
      mul_nonneg (mul_nonneg (mul_nonneg hx hx) hv) hw]
  have hs0 : 0 ≤ s := by positivity
  have hE2 : 0 ≤ u * v + u * w + u * x + v * w + v * x + w * x := by positivity
  have hE3 : 0 ≤ u * v * w + u * v * x + u * w * x + v * w * x := by positivity
  nlinarith only [e2, e3, e4, hs, hs0, hE2, hE3, mul_le_mul_of_nonneg_right hs hE2,
    mul_le_mul_of_nonneg_right hs hE3]

/-- The four-exponential product is within `5 s²` of `1 + (A + B + C + D)` when `s ≤ 1/2`. -/
theorem exp_four_le (A B C D : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0) (hD : D.re = 0)
    (hs : ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ ≤ 1 / 2) :
    ‖exp A * exp B * exp C * exp D - 1 - (A + B + C + D)‖ ≤ 5 * (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2 := by
  have hA0 := norm_nonneg A; have hB0 := norm_nonneg B
  have hC0 := norm_nonneg C; have hD0 := norm_nonneg D
  have rA := exp_sub_one_sub_le A hA (by linarith)
  have rB := exp_sub_one_sub_le B hB (by linarith)
  have rC := exp_sub_one_sub_le C hC (by linarith)
  have rD := exp_sub_one_sub_le D hD (by linarith)
  have nrm (E X : ℍ[ℝ]) (h : ‖E - 1 - X‖ ≤ ‖X‖ ^ 2) : ‖E - 1‖ ≤ ‖X‖ + ‖X‖ ^ 2 := by
    have e : E - 1 = (E - 1 - X) + X := by abel
    rw [e]; exact (norm_add_le _ _).trans (by linarith)
  have na := nrm _ _ rA; have nb := nrm _ _ rB; have nc := nrm _ _ rC; have nd := nrm _ _ rD
  set s := ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ with hsdef
  have hsq : ‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2 ≤ s ^ 2 := by
    rw [hsdef]; nlinarith only [hA0, hB0, hC0, hD0]
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hss : s ^ 2 ≤ s := by nlinarith only [hs, hs0]
  have hσ : ‖exp A - 1‖ + ‖exp B - 1‖ + ‖exp C - 1‖ + ‖exp D - 1‖ ≤ 2 * s := by
    linarith only [na, nb, nc, nd, hsq, hss, hsdef]
  have P := prod_four_le (exp A - 1) (exp B - 1) (exp C - 1) (exp D - 1) (by linarith)
  simp only [add_sub_cancel] at P
  have split : exp A * exp B * exp C * exp D - 1 - (A + B + C + D) =
      (exp A * exp B * exp C * exp D - 1 - ((exp A - 1) + (exp B - 1) + (exp C - 1) + (exp D - 1))) +
        ((exp A - 1 - A) + (exp B - 1 - B) + (exp C - 1 - C) + (exp D - 1 - D)) := by abel
  rw [split]
  refine (norm_add_le _ _).trans ?_
  have R : ‖(exp A - 1 - A) + (exp B - 1 - B) + (exp C - 1 - C) + (exp D - 1 - D)‖ ≤ s ^ 2 := by
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      (norm_add_le _ _) le_rfl)) le_rfl)).trans ?_
    linarith only [rA, rB, rC, rD, hsq]
  have hσ0 : 0 ≤ ‖exp A - 1‖ + ‖exp B - 1‖ + ‖exp C - 1‖ + ‖exp D - 1‖ := by positivity
  have P' := pow_le_pow_left₀ hσ0 hσ 2
  nlinarith only [P, P', R]

/-- **Plaquette value bound.** For imaginary `A B C D` with `s = ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ ≤ 1/2`,
`(max 0 (‖A + B + C + D‖ - 5 s²))² / 2 ≤ 1 - Re (exp A * exp B * exp C * exp D)`. -/
theorem plaquette_value_lower (A B C D : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0)
    (hD : D.re = 0) (hs : ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ ≤ 1 / 2) :
    (max 0 (‖A + B + C + D‖ - 5 * (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2)) ^ 2 / 2 ≤
      1 - (exp A * exp B * exp C * exp D).re := by
  have hu : ‖exp A * exp B * exp C * exp D‖ = 1 := by
    simp only [norm_mul, Quaternion.norm_exp, hA, hB, hC, hD, norm_one, mul_one,
      NormedSpace.exp_zero]
  rw [one_sub_re _ hu]
  have K := exp_four_le A B C D hA hB hC hD hs
  set q := exp A * exp B * exp C * exp D
  set c := A + B + C + D
  have tri : ‖c‖ - 5 * (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2 ≤ ‖q - 1‖ := by
    have : c = (q - 1) - (q - 1 - c) := by abel
    have h := norm_sub_le (q - 1) (q - 1 - c)
    rw [← this] at h
    linarith
  have h0 : 0 ≤ ‖q - 1‖ := norm_nonneg _
  have hm : max 0 (‖c‖ - 5 * (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2) ≤ ‖q - 1‖ := max_le h0 tri
  have hm0 : 0 ≤ max 0 (‖c‖ - 5 * (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2) := le_max_left _ _
  have := pow_le_pow_left₀ hm0 hm 2
  linarith

/-- `(x - y)₊² ≥ (1 - δ) x² - y² / δ` for `x, y ≥ 0` and `0 < δ ≤ 1`. -/
theorem pos_part_sq (x y δ : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) * x ^ 2 - y ^ 2 / δ ≤ (max 0 (x - y)) ^ 2 := by
  have key : (1 - δ) * x ^ 2 - y ^ 2 / δ ≤ (x - y) ^ 2 := by
    have e : (x - y) ^ 2 - ((1 - δ) * x ^ 2 - y ^ 2 / δ) = (δ * x - y) ^ 2 / δ + y ^ 2 := by
      field_simp; ring
    have : 0 ≤ (δ * x - y) ^ 2 / δ := by positivity
    nlinarith only [e, this, sq_nonneg y]
  rcases le_total (x - y) 0 with h | h
  · rw [max_eq_left h]
    have : (1 - δ) * x ^ 2 ≤ y ^ 2 / δ := by
      have hxy : x ≤ y := by linarith
      have h1 : (1 - δ) * x ^ 2 ≤ x ^ 2 := by nlinarith only [hδ, sq_nonneg x]
      have h2 : x ^ 2 ≤ y ^ 2 := by nlinarith only [hx, hxy]
      have h3 : y ^ 2 ≤ y ^ 2 / δ := by
        rw [le_div_iff₀ hδ]; nlinarith only [hδ1, sq_nonneg y]
      linarith
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    linarith
  · rw [max_eq_right h]; exact key

/-- **Summed plaquette bound.** For any finite family of plaquettes with imaginary increments `A p, B p, C p, D p`,
each with `s p = ‖A p‖ + ‖B p‖ + ‖C p‖ + ‖D p‖ ≤ 1/2`, and `0 < δ ≤ 1`:

  `(1 - δ)/2 · Σ ‖A p + B p + C p + D p‖² - 25/(2δ) · Σ s p⁴ ≤ Σ (1 - Re (exp A p · exp B p · exp C p · exp D p))`.

On a lattice with `U = exp(a) V` around a flat twisted vacuum, the first sum is the energy `‖d_V a‖²`, and the second is
at most `384 ‖a‖₄⁴`: `s⁴ ≤ 4³ Σ ‖·‖⁴`, and each link lies in 6 plaquettes. No sup norm at scale `n` enters. -/
theorem sum_value_lower {ι : Type*} (P : Finset ι) (A B C D : ι → ℍ[ℝ])
    (hA : ∀ p, (A p).re = 0) (hB : ∀ p, (B p).re = 0) (hC : ∀ p, (C p).re = 0) (hD : ∀ p, (D p).re = 0)
    (hs : ∀ p ∈ P, ‖A p‖ + ‖B p‖ + ‖C p‖ + ‖D p‖ ≤ 1 / 2) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) / 2 * ∑ p ∈ P, ‖A p + B p + C p + D p‖ ^ 2 -
        25 / (2 * δ) * ∑ p ∈ P, (‖A p‖ + ‖B p‖ + ‖C p‖ + ‖D p‖) ^ 4 ≤
      ∑ p ∈ P, (1 - (exp (A p) * exp (B p) * exp (C p) * exp (D p)).re) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have L := plaquette_value_lower (A p) (B p) (C p) (D p) (hA p) (hB p) (hC p) (hD p) (hs p hp)
  set sp := ‖A p‖ + ‖B p‖ + ‖C p‖ + ‖D p‖
  have hsp : 0 ≤ sp := by positivity
  have Q := pos_part_sq ‖A p + B p + C p + D p‖ (5 * sp ^ 2) δ (norm_nonneg _) (by positivity) hδ hδ1
  have e : (5 * sp ^ 2) ^ 2 / δ = 25 * sp ^ 4 / δ := by ring
  rw [e] at Q
  have e2 : 25 / (2 * δ) * sp ^ 4 = (25 * sp ^ 4 / δ) / 2 := by field_simp
  rw [e2]
  linarith

end TwistedPlaquetteValue
