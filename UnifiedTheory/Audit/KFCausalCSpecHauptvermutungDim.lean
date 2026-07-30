/-
  Audit/KFCausalCSpecHauptvermutungDim.lean
  — THE QUANTITATIVE HAUPTVERMUTUNG IN EVERY DIMENSION

  The 4D chain generalizes: the only dimension-dependent link was the
  counting dictionary `V = C_d·τ^d`, and its error propagation needs exactly
  one new fact — fractional roots never amplify relative error:

  1.  `rpow_error_le`:  |u^α − 1| ≤ |u − 1| for u ≥ 0, 0 < α ≤ 1.
  2.  `count_estimator_error_dim`:  in dimension d, a count in the
      ε-window gives  |(n/(ρC_d))^{k/d} − τ^k| ≤ ε·τ^k  for every k ≤ d —
      in particular the squared-interval estimator (k = 2) that polarization
      consumes.
  3.  `quantitative_hauptvermutung_dim`:  the d-dimensional metric-component
      reconstruction: three counts determine `B(aᵢ−a₀, aⱼ−a₀)` through
      `½((n_io/(ρC_d))^{2/d} + (n_jo/(ρC_d))^{2/d} − (n_ij/(ρC_d))^{2/d})`
      with error ≤ (3/2)·ε·S.  The polarization constant 3/2 and the
      Chebyshev–Poisson window are dimension-free; only C_d changes.

  Combined with `am_gm_tradeoff` (dimension-free), the resolution-limit
  structure extends to every d — the input to the d-dimensional clock-limit
  (Salecker–Wigner) identity, whose exponents ℓ_p^{(d−2)/(d−1)}·T^{1/(d−1)}
  match the causal-set closure exponents in every dimension.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecQuantitativeHauptvermutung

set_option autoImplicit false

open Real

namespace UnifiedTheory.Audit.KFCausalCSpecHauptvermutungDim

open UnifiedTheory.Audit.KFCausalCSpecQuantitativeHauptvermutung

/-- **Fractional roots never amplify relative error**:
`|u^α − 1| ≤ |u − 1|` for `u ≥ 0`, `0 < α ≤ 1`. -/
theorem rpow_error_le (u α : ℝ) (hu : 0 ≤ u) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    |u ^ α - 1| ≤ |u - 1| := by
  rcases eq_or_lt_of_le hu with hu0 | hupos
  · rw [← hu0, Real.zero_rpow hα0.ne']
  · rcases le_or_gt 1 u with h1 | h1
    · have ha : 1 ≤ u ^ α := Real.one_le_rpow h1 hα0.le
      have hb : u ^ α ≤ u := by
        calc u ^ α ≤ u ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1 hα1
          _ = u := Real.rpow_one u
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · have ha : u ≤ u ^ α := by
        calc u = u ^ (1:ℝ) := (Real.rpow_one u).symm
          _ ≤ u ^ α := Real.rpow_le_rpow_of_exponent_ge hupos h1.le hα1
      have hb : u ^ α ≤ 1 := by
        calc u ^ α ≤ u ^ (0:ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hupos h1.le hα0.le
          _ = 1 := Real.rpow_zero u
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith

/-- **The d-dimensional counting dictionary with error.**  `V = C_d·τ^d`;
a count in the ε-window estimates any power `τ^k` (k ≤ d) with relative
error ε via the fractional-root estimator. -/
theorem count_estimator_error_dim (d k : ℕ) (hk : 0 < k) (hkd : k ≤ d)
    (Cd rho tau n ε : ℝ)
    (hCd : 0 < Cd) (hρ : 0 < rho) (hτ : 0 < tau) (hn : 0 ≤ n)
    (hconc : |n / (rho * (Cd * tau^d)) - 1| ≤ ε) :
    |(n / (rho * Cd)) ^ ((k:ℝ)/(d:ℝ)) - tau^k| ≤ ε * tau^k := by
  have hd : 0 < d := lt_of_lt_of_le hk hkd
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  set u := n / (rho * (Cd * tau^d)) with hudef
  have hu0 : 0 ≤ u := by
    rw [hudef]
    positivity
  have harg : n / (rho * Cd) = tau^d * u := by
    rw [hudef]
    first
    | (field_simp; ring)
    | field_simp
  have hτd : (0:ℝ) < tau^d := pow_pos hτ d
  have hsplit : (tau^d * u) ^ ((k:ℝ)/(d:ℝ))
      = tau^k * u ^ ((k:ℝ)/(d:ℝ)) := by
    rw [Real.mul_rpow hτd.le hu0, ← Real.rpow_natCast tau d,
      ← Real.rpow_mul hτ.le,
      show (d:ℝ) * ((k:ℝ)/(d:ℝ)) = (k:ℝ) from by field_simp,
      Real.rpow_natCast]
  have hα0 : 0 < (k:ℝ)/(d:ℝ) := by positivity
  have hα1 : (k:ℝ)/(d:ℝ) ≤ 1 := by
    rw [div_le_one hdR]
    exact_mod_cast hkd
  calc |(n / (rho * Cd)) ^ ((k:ℝ)/(d:ℝ)) - tau^k|
      = tau^k * |u ^ ((k:ℝ)/(d:ℝ)) - 1| := by
        rw [harg, hsplit,
          show tau^k * u ^ ((k:ℝ)/(d:ℝ)) - tau^k
            = tau^k * (u ^ ((k:ℝ)/(d:ℝ)) - 1) from by ring,
          abs_mul, abs_of_pos (pow_pos hτ k)]
    _ ≤ tau^k * |u - 1| :=
        mul_le_mul_of_nonneg_left
          (rpow_error_le u ((k:ℝ)/(d:ℝ)) hu0 hα0 hα1) (pow_pos hτ k).le
    _ ≤ tau^k * ε := mul_le_mul_of_nonneg_left hconc (pow_pos hτ k).le
    _ = ε * tau^k := by ring

/-- **THE QUANTITATIVE HAUPTVERMUTUNG IN DIMENSION d.**  Three interval
counts determine the metric component through the explicit d-dimensional
estimator, with the dimension-free polarization constant 3/2:

    |½((n_io/(ρC_d))^{2/d} + (n_jo/(ρC_d))^{2/d} − (n_ij/(ρC_d))^{2/d})
      − B(aᵢ−a₀, aⱼ−a₀)|  ≤  (3/2)·ε·S. -/
theorem quantitative_hauptvermutung_dim {V : Type*} [AddCommGroup V]
    [Module ℝ V] (d : ℕ) (hd : 2 ≤ d)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (ai aj ao : V) (Cd rho ε S : ℝ)
    (t_io t_jo t_ij n_io n_jo n_ij : ℝ)
    (hCd : 0 < Cd) (hρ : 0 < rho) (hε : 0 ≤ ε)
    (ht_io : sigma2 B ai ao = t_io^2) (ht_jo : sigma2 B aj ao = t_jo^2)
    (ht_ij : sigma2 B ai aj = t_ij^2)
    (hpos_io : 0 < t_io) (hpos_jo : 0 < t_jo) (hpos_ij : 0 < t_ij)
    (hS_io : t_io^2 ≤ S) (hS_jo : t_jo^2 ≤ S) (hS_ij : t_ij^2 ≤ S)
    (hn_io : 0 ≤ n_io) (hn_jo : 0 ≤ n_jo) (hn_ij : 0 ≤ n_ij)
    (hconc_io : |n_io / (rho * (Cd * t_io^d)) - 1| ≤ ε)
    (hconc_jo : |n_jo / (rho * (Cd * t_jo^d)) - 1| ≤ ε)
    (hconc_ij : |n_ij / (rho * (Cd * t_ij^d)) - 1| ≤ ε) :
    |((n_io / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ))
        + (n_jo / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ))
        - (n_ij / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ))) / 2
      - B (ai - ao) (aj - ao)| ≤ 3/2 * (ε * S) := by
  have h2d : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
  have e_io := count_estimator_error_dim d 2 (by norm_num) hd Cd rho t_io
    n_io ε hCd hρ hpos_io hn_io hconc_io
  have e_jo := count_estimator_error_dim d 2 (by norm_num) hd Cd rho t_jo
    n_jo ε hCd hρ hpos_jo hn_jo hconc_jo
  have e_ij := count_estimator_error_dim d 2 (by norm_num) hd Cd rho t_ij
    n_ij ε hCd hρ hpos_ij hn_ij hconc_ij
  rw [h2d] at e_io e_jo e_ij
  apply gram_reconstruction_lipschitz B hsymm ai aj ao _ _ _ (ε * S)
  · rw [ht_io]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hS_io hε)
    have : t_io^2 = t_io^(2:ℕ) := by norm_num
    calc |(n_io / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ)) - t_io^2|
        = |(n_io / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ)) - t_io^(2:ℕ)| := by rw [← this]
      _ ≤ ε * t_io^(2:ℕ) := e_io
      _ = ε * t_io^2 := by norm_num
  · rw [ht_jo]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hS_jo hε)
    have : t_jo^2 = t_jo^(2:ℕ) := by norm_num
    calc |(n_jo / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ)) - t_jo^2|
        = |(n_jo / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ)) - t_jo^(2:ℕ)| := by rw [← this]
      _ ≤ ε * t_jo^(2:ℕ) := e_jo
      _ = ε * t_jo^2 := by norm_num
  · rw [ht_ij]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hS_ij hε)
    have : t_ij^2 = t_ij^(2:ℕ) := by norm_num
    calc |(n_ij / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ)) - t_ij^2|
        = |(n_ij / (rho * Cd)) ^ ((2:ℝ)/(d:ℝ)) - t_ij^(2:ℕ)| := by rw [← this]
      _ ≤ ε * t_ij^(2:ℕ) := e_ij
      _ = ε * t_ij^2 := by norm_num

#print axioms rpow_error_le
#print axioms count_estimator_error_dim
#print axioms quantitative_hauptvermutung_dim

end UnifiedTheory.Audit.KFCausalCSpecHauptvermutungDim
