/- At each finite cutoff the twisted transfer operator has a positive gap on the whole complement of
the vacuum. The proof is compactness and simplicity, so `ρ` depends on `n` and `β` with no control.
This makes the gap half of `NeutralWindow` true at every cutoff, so Target A is a statement about
uniformity in `n`, not about existence of a gap. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFiniteGap
noncomputable section
open WilsonSlabOperator TwistedTransfer TwistedVacuum
open scoped InnerProductSpace

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A rank-one operator is compact. -/
theorem rankOne_compact (Ω : H) :
    IsCompactOperator ((innerSL ℂ Ω).smulRight Ω : H →L[ℂ] H) := by
  let line : ℂ → H := fun c => c • Ω
  have hline : Continuous line := continuous_id.smul continuous_const
  refine ⟨line '' Metric.closedBall 0 ‖Ω‖, (isCompact_closedBall _ _).image hline, ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) one_pos) fun f hf => ?_
  refine ⟨inner ℂ Ω f, ?_, rfl⟩
  have hf1 : ‖f‖ < 1 := by simpa using hf
  rw [mem_closedBall_zero_iff]
  refine (norm_inner_le_norm Ω f).trans ?_
  nlinarith only [norm_nonneg Ω, hf1]

/-- **The abstract gap.** A positive compact operator with a simple top eigenvector has norm strictly
below the top on the orthogonal complement. -/
theorem gap_of_simple (A : H →L[ℂ] H) (hpos : A.IsPositive) (hc : IsCompactOperator A) (Ω : H)
    (hΩ : ‖Ω‖ = 1) (htop : A Ω = ‖A‖ • Ω) (hlam : 0 < ‖A‖)
    (hsimple : ∀ v, A v = ‖A‖ • v → ∃ c : ℂ, v = c • Ω) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ f, inner ℂ Ω f = 0 → ‖A f‖ ≤ ρ * ‖A‖ * ‖f‖ := by
  set lam := ‖A‖ with hlamd
  have hsym : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y) := hpos.isSymmetric
  have hself : inner ℂ Ω Ω = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hΩA (f : H) : inner ℂ Ω (A f) = lam * inner ℂ Ω f := by
    rw [← hsym, htop, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left]
    simp
  let R : H →L[ℂ] H := (innerSL ℂ Ω).smulRight Ω
  have hR (f : H) : R f = inner ℂ Ω f • Ω := rfl
  let S : H →L[ℂ] H := A - (lam : ℂ) • R
  have hS (f : H) : S f = A f - (lam : ℂ) • (inner ℂ Ω f • Ω) := rfl
  have hSc : IsCompactOperator S :=
    hc.sub ((rankOne_compact Ω).smul (lam : ℂ))
  have hSorth (f : H) (hf : inner ℂ Ω f = 0) : S f = A f := by
    rw [hS, hf]
    simp
  have hSsplit (f : H) : S f = A (f - inner ℂ Ω f • Ω) := by
    rw [hS, map_sub, map_smul, htop, smul_comm]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hSsym : (S : H →ₗ[ℂ] H).IsSymmetric := by
    intro x y
    change inner ℂ (S x) y = inner ℂ x (S y)
    rw [hS, hS, inner_sub_left, inner_sub_right, hsym, inner_smul_left, inner_smul_left,
      inner_smul_right, inner_smul_right]
    simp only [Complex.conj_ofReal, inner_conj_symm]
    ring
  have hSpos : S.IsPositive := by
    refine ⟨hSsym, fun f => ?_⟩
    set a := inner ℂ Ω f with ha
    set g := f - a • Ω with hg
    have hfg : f = g + a • Ω := by rw [hg]; abel
    have hΩg : inner ℂ Ω g = 0 := by
      rw [hg, inner_sub_right, inner_smul_right, hself, mul_one, sub_self]
    have hSf : S f = A g := hSsplit f
    have hΩAg : inner ℂ Ω (A g) = 0 := by rw [hΩA, hΩg, mul_zero]
    have hform : inner ℂ f (S f) = inner ℂ g (A g) := by
      rw [hSf]
      conv_lhs => rw [hfg]
      rw [inner_add_left, inner_smul_left, hΩAg, mul_zero, add_zero]
    have hA := hpos.2 g
    have hq : ContinuousLinearMap.reApplyInnerSelf S f = ContinuousLinearMap.reApplyInnerSelf A g := by
      simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
      rw [← inner_conj_symm, RCLike.conj_re, hform, ← inner_conj_symm, RCLike.conj_re]
    rw [hq]
    exact hA
  by_cases hS0 : S = 0
  · refine ⟨0, le_rfl, one_pos, fun f hf => ?_⟩
    rw [← hSorth f hf, hS0]
    simp
  have htopS := PositiveKernelGroundState.positive_compact_top_eigenvector S hSpos hSc hS0
  obtain ⟨hSpos', v, hv, hSv⟩ := htopS
  have hΩv : inner ℂ Ω v = 0 := by
    have h1 : inner ℂ Ω (S v) = (‖S‖ : ℂ) * inner ℂ Ω v := by
      rw [hSv, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
      rfl
    have h2 : inner ℂ Ω (S v) = 0 := by
      rw [hS, inner_sub_right, hΩA, inner_smul_right, inner_smul_right, hself, mul_one, sub_self]
    rw [h2] at h1
    have hne : ((‖S‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hSpos'.ne'
    exact (mul_eq_zero.mp h1.symm).resolve_left hne
  have hAv : A v = ‖S‖ • v := by rw [← hSorth v hΩv, hSv]
  have hle : ‖S‖ ≤ lam := by
    have h1 := A.le_opNorm v
    rw [hAv, norm_smul, hv, mul_one, mul_one, Real.norm_eq_abs, abs_of_pos hSpos'] at h1
    exact h1
  have hlt : ‖S‖ < lam := by
    refine lt_of_le_of_ne hle fun heq => ?_
    rw [heq] at hAv
    obtain ⟨c, hc'⟩ := hsimple v hAv
    have hc0 : c = 0 := by
      have := hΩv
      rw [hc', inner_smul_right, hself, mul_one] at this
      exact this
    rw [hc0, zero_smul] at hc'
    rw [hc', norm_zero] at hv
    exact zero_ne_one hv
  refine ⟨‖S‖ / lam, by positivity, (div_lt_one hlam).mpr hlt, fun f hf => ?_⟩
  rw [← hSorth f hf, div_mul_cancel₀ _ hlam.ne']
  exact S.le_opNorm f

end Abstract

variable (n : ℕ) [NeZero n] (β : ℝ)

/-- **The finite-cutoff gap of the twisted operator.** The vacuum is neutral, and there is `ρ < 1`
contracting its entire orthogonal complement. `ρ` is not uniform in `n` or `β`. -/
theorem finite_gap (hβ : 0 ≤ β) :
    ∃ Ω : Hilbert n, ‖Ω‖ = 1 ∧ TwistedTransfer.transfer n β Ω = ‖TwistedTransfer.transfer n β‖ • Ω ∧
      Neutral n Ω ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ f, inner ℂ Ω f = 0 →
        ‖TwistedTransfer.transfer n β f‖ ≤ ρ * ‖TwistedTransfer.transfer n β‖ * ‖f‖ := by
  obtain ⟨Ω, h1, h2, h3, h4⟩ := neutral_vacuum n β hβ
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  exact ⟨Ω, h1, h2, h3, gap_of_simple _ (transfer_positive n β hβ) (transfer_compact n β) Ω h1 h2
    hlam h4⟩

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedFiniteGap
