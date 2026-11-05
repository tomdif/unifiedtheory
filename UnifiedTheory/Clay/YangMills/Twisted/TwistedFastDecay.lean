/- The contraction half of the neutral window from decay of correlations. `slow_lower_corr`
(TwistedSlowObservable) turns one slow correlator into the second clause of `NeutralWindow`. This file
gives the first clause from the opposite kind of input: if every neutral vector `f` orthogonal to the
vacuum has a correlator `⟨f, T²ᵏ f⟩` that decays like `C_f (ρ ‖T‖)²ᵏ`, with a prefactor `C_f` that may
depend on `f` arbitrarily, then `T` contracts the neutral complement by `ρ`. The prefactor drops out
because for a self-adjoint `T` the sequence `‖Tᵏ f‖` is log-convex:
`‖Tᵐ f‖² = ⟨f, T²ᵐ f⟩ ≤ ‖f‖ ‖T²ᵐ f‖`, so `‖f‖ ‖T f‖^N ≤ ‖f‖^N ‖T^N f‖` for `N = 2ʲ`, and a
geometric bound on the right forces `‖T f‖ ≤ ρ ‖T‖ ‖f‖` as `N → ∞`. No spectral theorem is used.
This is the step a decay-of-correlations argument (for example Helffer–Sjöstrand from a convexity bound,
with `f`-dependent constants) must pass through to reach `NeutralWindow`. Nothing here proves decay
for the Yang–Mills measure. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay
noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `‖Tᵐ f‖² = Re ⟨f, T²ᵐ f⟩` for self-adjoint `T`. -/
theorem norm_pow_sq (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (m : ℕ) (f : E) :
    ‖(T ^ m) f‖ ^ 2 = (inner ℂ f ((T ^ (2 * m)) f)).re := by
  have h : inner ℂ ((T ^ m) f) ((T ^ m) f) = inner ℂ f ((T ^ (2 * m)) f) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, (hT.pow m).adjoint_eq,
      ← ContinuousLinearMap.mul_apply, ← pow_add, two_mul]
  rw [← h, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Log-convexity step.** `‖Tᵐ f‖² ≤ ‖f‖ ‖T²ᵐ f‖`. -/
theorem norm_pow_sq_le (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (m : ℕ) (f : E) :
    ‖(T ^ m) f‖ ^ 2 ≤ ‖f‖ * ‖(T ^ (2 * m)) f‖ := by
  rw [norm_pow_sq T hT]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

/-- `‖f‖ ‖T f‖^N ≤ ‖f‖^N ‖T^N f‖` for `N = 2ʲ`. -/
theorem norm_pow_two_pow (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (f : E) (j : ℕ) :
    ‖f‖ * ‖T f‖ ^ (2 ^ j) ≤ ‖f‖ ^ (2 ^ j) * ‖(T ^ (2 ^ j)) f‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    set N := 2 ^ j with hN
    have hN2 : 2 ^ (j + 1) = 2 * N := by rw [hN, pow_succ, mul_comm]
    rw [hN2]
    by_cases h0 : ‖f‖ = 0
    · rw [h0]
      have : (0 : ℝ) ^ (2 * N) = 0 := zero_pow (by positivity)
      rw [this]
      simp
    have hf : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hsq : (‖f‖ * ‖T f‖ ^ N) ^ 2 ≤ (‖f‖ ^ N * ‖(T ^ N) f‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) ih 2
    have hstep := norm_pow_sq_le T hT N f
    have key : ‖f‖ * (‖f‖ * ‖T f‖ ^ (2 * N)) ≤ ‖f‖ * (‖f‖ ^ (2 * N) * ‖(T ^ (2 * N)) f‖) := by
      calc ‖f‖ * (‖f‖ * ‖T f‖ ^ (2 * N)) = (‖f‖ * ‖T f‖ ^ N) ^ 2 := by ring
        _ ≤ (‖f‖ ^ N * ‖(T ^ N) f‖) ^ 2 := hsq
        _ = ‖f‖ ^ (2 * N) * ‖(T ^ N) f‖ ^ 2 := by ring
        _ ≤ ‖f‖ ^ (2 * N) * (‖f‖ * ‖(T ^ (2 * N)) f‖) := by gcongr
        _ = ‖f‖ * (‖f‖ ^ (2 * N) * ‖(T ^ (2 * N)) f‖) := by ring
    exact le_of_mul_le_mul_left key hf

/-- **Decay with any prefactor gives a one-step contraction.** If `‖Tᵏ f‖ ≤ C rᵏ` for all `k`, then
`‖T f‖ ≤ r ‖f‖`. -/
theorem contraction_of_decay (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (f : E) (r : ℝ) (hr : 0 ≤ r)
    (C : ℝ) (hdec : ∀ k : ℕ, ‖(T ^ k) f‖ ≤ C * r ^ k) : ‖T f‖ ≤ r * ‖f‖ := by
  rcases hr.lt_or_eq with hr | hr
  swap
  · subst hr
    have h1 := hdec 1
    simp only [pow_one, mul_zero] at h1
    simpa using h1
  by_cases h0 : ‖f‖ = 0
  · have hf : f = 0 := norm_eq_zero.mp h0
    simp [hf]
  have hf : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  by_contra hcon
  push_neg at hcon
  set x := ‖T f‖ / (r * ‖f‖) with hx
  have hrf : 0 < r * ‖f‖ := mul_pos hr hf
  have hx1 : 1 < x := by rw [hx, lt_div_iff₀ hrf]; linarith
  -- (x^N) ‖f‖ ≤ C for N = 2^j
  have hbound (j : ℕ) : x ^ (2 ^ j) * ‖f‖ ≤ C := by
    have h1 := norm_pow_two_pow T hT f j
    have h2 := hdec (2 ^ j)
    have h3 : ‖f‖ * ‖T f‖ ^ (2 ^ j) ≤ ‖f‖ ^ (2 ^ j) * (C * r ^ (2 ^ j)) :=
      h1.trans (by gcongr)
    have hTf : ‖T f‖ = x * (r * ‖f‖) := by rw [hx]; field_simp
    rw [hTf, mul_pow, mul_pow] at h3
    have hpos : 0 < ‖f‖ ^ (2 ^ j) * r ^ (2 ^ j) := by positivity
    have : (x ^ (2 ^ j) * ‖f‖) * (‖f‖ ^ (2 ^ j) * r ^ (2 ^ j)) ≤
        C * (‖f‖ ^ (2 ^ j) * r ^ (2 ^ j)) := by
      nlinarith only [h3]
    exact le_of_mul_le_mul_right this hpos
  -- Bernoulli: x^N ≥ 1 + N (x - 1) grows without bound
  obtain ⟨j, hj⟩ := exists_nat_gt (C / (‖f‖ * (x - 1)))
  have hbern : 1 + ((2 ^ j : ℕ) : ℝ) * (x - 1) ≤ x ^ (2 ^ j) := by
    have := one_add_mul_le_pow (a := x - 1) (by linarith) (2 ^ j)
    simpa using this
  have hj2 : (j : ℝ) < ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self
  have hpos : 0 < ‖f‖ * (x - 1) := mul_pos hf (by linarith)
  have hC : C < ((2 ^ j : ℕ) : ℝ) * (‖f‖ * (x - 1)) := by
    rw [div_lt_iff₀ hpos] at hj
    nlinarith only [hj, hj2, hpos]
  have := hbound j
  nlinarith only [this, hbern, hC, hf]

/-- **Correlator form.** If `Re ⟨f, T²ᵏ f⟩ ≤ C r²ᵏ` for all `k`, then `‖T f‖ ≤ r ‖f‖`. -/
theorem contraction_of_corr (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (f : E) (r : ℝ) (hr : 0 ≤ r)
    (C : ℝ) (hcorr : ∀ k : ℕ, (inner ℂ f ((T ^ (2 * k)) f)).re ≤ C * r ^ (2 * k)) :
    ‖T f‖ ≤ r * ‖f‖ := by
  have hC : 0 ≤ C := by
    have h0 := hcorr 0
    rw [← norm_pow_sq T hT] at h0
    simpa using (sq_nonneg _).trans h0
  refine contraction_of_decay T hT f r hr (Real.sqrt C) fun k => ?_
  have h := hcorr k
  rw [← norm_pow_sq T hT] at h
  have h' : ‖(T ^ k) f‖ ^ 2 ≤ (Real.sqrt C * r ^ k) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC, ← pow_mul, mul_comm k 2]
    exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'

end General

open TwistedTransfer WilsonSlabOperator

variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "T" => TwistedTransfer.transfer n β

/-- **Decay of neutral correlations gives the contraction clause of `NeutralWindow`.** If every
neutral `f` orthogonal to `Ω` has `Re ⟨f, T²ᵏ f⟩ ≤ C_f (ρ ‖T‖)²ᵏ` for all `k`, with any prefactor
`C_f`, then `‖T f‖ ≤ ρ ‖T‖ ‖f‖` on the whole neutral complement. With `F = g η` the hypothesis is
exponential decay `C(t) ≤ C_g e^{-m t}` of every neutral connected Euclidean correlator at a rate
`m = −log ρ` that does not depend on the observable. -/
theorem fast_upper_corr (Ω : Hilbert n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdec : ∀ f : Hilbert n, Neutral n f → inner ℂ Ω f = 0 →
      ∃ C : ℝ, ∀ k : ℕ, (inner ℂ f ((T ^ (2 * k)) f)).re ≤ C * (ρ * ‖T‖) ^ (2 * k)) :
    ∀ f : Hilbert n, Neutral n f → inner ℂ Ω f = 0 → ‖T f‖ ≤ ρ * ‖T‖ * ‖f‖ := by
  intro f hfn hfo
  obtain ⟨C, hC⟩ := hdec f hfn hfo
  exact contraction_of_corr T (TwistedTransfer.transfer_selfAdjoint n β) f (ρ * ‖T‖)
    (mul_nonneg hρ (norm_nonneg _)) C hC

/-- **The neutral window from correlators alone.** Given a normalized neutral top eigenvector `Ω`,
`NeutralWindow n β ρ₁ ρ₂` follows from two statements about Euclidean correlators:
* every neutral connected correlator decays at least like `C_f (ρ₁ ‖T‖)²ᵏ` (any prefactor), and
* one neutral connected correlator survives to some lag `2k`, `⟨F, T²ᵏ F⟩ ≥ (ρ₂ ‖T‖)²ᵏ ‖F‖²`. -/
theorem window_of_correlators (Ω : Hilbert n) (hΩn : ‖Ω‖ = 1) (hΩ : T Ω = ‖T‖ • Ω)
    (hΩN : Neutral n Ω) (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 < ρ₂) (hT : 0 < ‖T‖)
    (hdec : ∀ f : Hilbert n, Neutral n f → inner ℂ Ω f = 0 →
      ∃ C : ℝ, ∀ k : ℕ, (inner ℂ f ((T ^ (2 * k)) f)).re ≤ C * (ρ₁ * ‖T‖) ^ (2 * k))
    (k : ℕ) (hk : 0 < k) (F : Hilbert n) (hFn : Neutral n F) (hFo : inner ℂ Ω F = 0)
    (hF0 : F ≠ 0)
    (hcorr : (ρ₂ * ‖T‖) ^ (2 * k) * ‖F‖ ^ 2 ≤ (inner ℂ F ((T ^ (2 * k)) F)).re) :
    NeutralWindow n β ρ₁ ρ₂ :=
  ⟨Ω, hΩn, hΩ, hΩN, fast_upper_corr n β Ω ρ₁ hρ₁ hdec,
    TwistedSlowObservable.slow_lower_corr n β k hk Ω F hΩ hFn hFo hF0 ρ₂ hρ₂ hT hcorr⟩

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedFastDecay
