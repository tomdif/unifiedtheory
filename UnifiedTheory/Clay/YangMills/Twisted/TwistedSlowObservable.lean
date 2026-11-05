/- The other half of the neutral window from one slow observable. `TwistedPoincare` turns a neutral
Poincaré inequality into the contraction half of `NeutralWindow`. Here a single neutral observable `g`
with small Dirichlet form gives the remaining half: a neutral vector orthogonal to the vacuum that `T`
shrinks by at most `ρ`. Read through the stationary chain of consecutive time slices (law `η²`),
the hypothesis is `E[(g(u₁) − g(u₀))²] ≤ 2 (1 − ρ) E[g²]`: a slow observable. Together the two
halves make `NeutralWindow` a two-sided Poincaré statement about the Euclidean measure alone. Neither
side is proved for any trajectory. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator TwistedTransfer TwistedFluxSector TwistedPoincare
open WilsonPositiveGroundState (complexify)

variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "μ'" => WilsonSlabOperator.measure n
local notation "T" => TwistedTransfer.transfer n β

/-- The embedding of a flip-invariant continuous function is neutral. -/
theorem neutral_embed (f : C(Slice n, ℝ)) (hf : ∀ i c u, f (TwistedTransfer.flip n i c u) = f u) :
    Neutral n (ContinuousMap.toLp 2 (μ') ℂ (complexify f)) := by
  intro i c
  have hmp := flip_measurePreserving n i c
  apply Lp.ext
  have h1 : (flipOp n i c (ContinuousMap.toLp 2 (μ') ℂ (complexify f)) : Slice n → ℂ) =ᵐ[μ']
      ((ContinuousMap.toLp 2 (μ') ℂ (complexify f) : Hilbert n) ∘ TwistedTransfer.flip n i c) :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') (complexify f)
  have h3 := hmp.quasiMeasurePreserving.ae_eq_comp h2
  have hinv : ((complexify f : Slice n → ℂ) ∘ TwistedTransfer.flip n i c) =ᵐ[μ']
      (complexify f : Slice n → ℂ) := by
    refine Filter.Eventually.of_forall fun u => ?_
    change ((f (TwistedTransfer.flip n i c u) : ℝ) : ℂ) = ((f u : ℝ) : ℂ)
    rw [hf]
  exact h1.trans (h3.trans (hinv.trans h2.symm))

variable (hβ : 0 ≤ β)

include hβ

/-- **A slow neutral observable bounds the neutral level from below.** If `g` is flip invariant, has
mean zero and positive variance under `η²`, and its Dirichlet form is at most `2 (1 − ρ) ‖T‖ E[g²]`,
then the neutral vector `g η` is orthogonal to the vacuum and shrinks by at most `ρ`. -/
theorem slow_lower (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u)
    (g : C(Slice n, ℝ)) (hg : ∀ i c u, g (TwistedTransfer.flip n i c u) = g u)
    (hmean : ∫ u, g u * η u ^ 2 ∂μ' = 0) (hX : 0 < ∫ u, g u ^ 2 * η u ^ 2 ∂μ') (ρ : ℝ)
    (hslow : dirichlet n β η g ≤ 2 * (1 - ρ) * ‖T‖ * ∫ u, g u ^ 2 * η u ^ 2 ∂μ') :
    ∃ f : Hilbert n, Neutral n f ∧
      inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 ∧ f ≠ 0 ∧
      ρ * ‖T‖ * ‖f‖ ≤ ‖T f‖ := by
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  have hflipη := top_flip n β η hη heig hlam
  let f : C(Slice n, ℝ) := g * η
  have hfv (u : Slice n) : f u = g u * η u := rfl
  set F := ContinuousMap.toLp 2 (μ') ℂ (complexify f) with hF
  set X := ∫ u, g u ^ 2 * η u ^ 2 ∂μ' with hXd
  set lam := ‖T‖ with hlamd
  have hFsq : ‖F‖ ^ 2 = X := by
    rw [hF, WilsonPositiveGroundState.real_embedding_norm_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hfv]
    ring
  have hFpos : 0 < ‖F‖ := by
    by_contra hneg
    have h0 : ‖F‖ = 0 := le_antisymm (not_lt.mp hneg) (norm_nonneg _)
    rw [h0] at hFsq
    norm_num at hFsq
    linarith only [hFsq, hX]
  refine ⟨F, neutral_embed n f fun i c u => by rw [hfv, hfv, hg, hflipη], ?_,
    norm_pos_iff.mp hFpos, ?_⟩
  · rw [hF, inner_embed]
    have hzero : ∫ u, η u * f u ∂μ' = 0 := by
      rw [← hmean]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [hfv]
      ring
    rw [hzero]
    simp
  · set Q := ∫ u, (g u * η u) * (∫ v, twistedKernel n β (u, v) * (g v * η v) ∂μ') ∂μ' with hQ
    have hid := ground_state_identity n β η g heig
    have hinner : inner ℂ F (T F) = (Q : ℂ) := by
      rw [hF, transfer_embed, inner_embed]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [sm_apply]
      rfl
    have hbound : Q ≤ ‖F‖ * ‖T F‖ := by
      have h1 := norm_inner_le_norm (𝕜 := ℂ) F (T F)
      rw [hinner, Complex.norm_real, Real.norm_eq_abs] at h1
      exact (le_abs_self _).trans h1
    have hkey : ρ * lam * X ≤ Q := by
      rw [← hlamd, ← hXd, ← hQ] at hid
      rw [hid] at hslow
      nlinarith only [hslow]
    have hfin : ρ * lam * ‖F‖ * ‖F‖ ≤ ‖T F‖ * ‖F‖ := by
      have := hkey.trans hbound
      rw [← hFsq] at this
      nlinarith only [this]
    exact le_of_mul_le_mul_right hfin hFpos

/-- **The neutral window as a two-sided Poincaré statement.** A neutral Poincaré inequality with
constant `n / c` and one slow neutral observable, with Dirichlet form at most
`2 (1 − e^{−C/n}) ‖T‖ E[g²]`, give `NeutralWindow` with ratios `e^{−c/n}` and `e^{−C/n}`. These two
inequalities over all `n ≥ 2` and `β ≥ b log n + β₀` imply `TargetAGap b`. -/
theorem window_of_two_sided (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (hnormL : ‖ContinuousMap.toLp 2 (μ') ℂ (complexify η)‖ = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u)
    (c C : ℝ) (hc : 0 < c) (hcn : c ≤ n) (hP : NeutralPoincare n β η (n / c))
    (g : C(Slice n, ℝ)) (hg : ∀ i c u, g (TwistedTransfer.flip n i c u) = g u)
    (hmean : ∫ u, g u * η u ^ 2 ∂μ' = 0) (hX : 0 < ∫ u, g u ^ 2 * η u ^ 2 ∂μ')
    (hslow : dirichlet n β η g ≤
      2 * (1 - Real.exp (-C / n)) * ‖T‖ * ∫ u, g u ^ 2 * η u ^ 2 ∂μ') :
    NeutralWindow n β (Real.exp (-c / n)) (Real.exp (-C / n)) := by
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  have hflipη := top_flip n β η hη heig hlam
  set Ω := ContinuousMap.toLp 2 (μ') ℂ (complexify η) with hΩ
  have hTΩ : T Ω = ‖T‖ • Ω := by
    rw [hΩ, transfer_embed]
    have hs : sm n β η = ‖T‖ • η := by
      ext u
      rw [sm_apply, heig]
      rfl
    rw [hs, WilsonPositiveGroundState.complexify_smul, map_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  obtain ⟨f, hfN, hfo, hf0, hfr⟩ :=
    slow_lower n β hβ η hη heig g hg hmean hX (Real.exp (-C / n)) hslow
  exact ⟨Ω, hnormL, hTΩ, neutral_embed n η fun i c u => hflipη i c u,
    exp_of_poincare n β hβ η hη heig c hc hcn hP, f, hfN, hfo, hf0, hfr⟩

omit hβ in
/-- Powers of the transfer operator preserve neutrality. -/
theorem neutral_pow (k : ℕ) (F : Hilbert n) (hF : Neutral n F) : Neutral n ((T ^ k) F) := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    intro i c
    rw [pow_succ', ContinuousLinearMap.mul_apply, ← transfer_flipOp, ih i c]

omit hβ in
/-- Powers of the transfer operator preserve orthogonality to the top eigenvector. -/
theorem orth_pow (k : ℕ) (Ω F : Hilbert n) (hΩ : T Ω = ‖T‖ • Ω) (hF : inner ℂ Ω F = 0) :
    inner ℂ Ω ((T ^ k) F) = 0 := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
      (TwistedTransfer.transfer_selfAdjoint n β).adjoint_eq, hΩ,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, ih, mul_zero]

omit hβ in
/-- `⟨Tᵏ F, Tᵏ G⟩ = ⟨F, T²ᵏ G⟩`. -/
theorem inner_pow_pow (k : ℕ) (F G : Hilbert n) :
    inner ℂ ((T ^ k) F) ((T ^ k) G) = inner ℂ F ((T ^ (2 * k)) G) := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ((TwistedTransfer.transfer_selfAdjoint n β).pow k).adjoint_eq,
    ← ContinuousLinearMap.mul_apply, ← pow_add, two_mul]

omit hβ in
/-- **A slow correlator at some lag bounds the neutral level from below.** If a neutral vector `F`
orthogonal to the vacuum has `ρ ‖T‖ ⟨F, T²ᵏ F⟩ ≤ ⟨F, T²ᵏ⁺¹ F⟩` with `Tᵏ F ≠ 0`, then `Tᵏ F` is a
neutral complement vector that `T` shrinks by at most `ρ`. Read through the Euclidean measure, with
`F = g η`, this asks the time correlator `C(t)` of `g` to satisfy `C(2k+1) ≥ ρ ‖T‖ C(2k)` at one
lag:
the fast part of `g` may decay at any rate, only the decay at lag `2k` matters. -/
theorem slow_lower_lag (k : ℕ) (Ω F : Hilbert n) (hΩ : T Ω = ‖T‖ • Ω) (hFn : Neutral n F)
    (hFo : inner ℂ Ω F = 0) (hne : (T ^ k) F ≠ 0) (ρ : ℝ)
    (hslow : ρ * ‖T‖ * (inner ℂ F ((T ^ (2 * k)) F)).re ≤ (inner ℂ F ((T ^ (2 * k + 1)) F)).re) :
    ∃ f : Hilbert n, Neutral n f ∧ inner ℂ Ω f = 0 ∧ f ≠ 0 ∧ ρ * ‖T‖ * ‖f‖ ≤ ‖T f‖ := by
  set f := (T ^ k) F with hf
  refine ⟨f, neutral_pow n β k F hFn, orth_pow n β k Ω F hΩ hFo, hne, ?_⟩
  have h2 : (inner ℂ F ((T ^ (2 * k)) F)).re = ‖f‖ ^ 2 := by
    rw [← inner_pow_pow, ← hf, inner_self_eq_norm_sq_to_K]
    norm_cast
  have h3 : inner ℂ F ((T ^ (2 * k + 1)) F) = inner ℂ f (T f) := by
    have hTf : T f = (T ^ k) (T F) := by
      rw [hf, ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← pow_succ',
        ← pow_succ]
    rw [hTf, hf, inner_pow_pow, ← ContinuousLinearMap.mul_apply, ← pow_succ]
  have hcs : (inner ℂ f (T f)).re ≤ ‖f‖ * ‖T f‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm f (T f))
  have hpos : 0 < ‖f‖ := norm_pos_iff.mpr hne
  rw [h2, h3] at hslow
  have : ρ * ‖T‖ * ‖f‖ * ‖f‖ ≤ ‖T f‖ * ‖f‖ := by nlinarith only [hslow, hcs]
  exact le_of_mul_le_mul_right this hpos

omit hβ in
/-- **A correlator that survives to lag `2k` bounds the neutral level from below.** If a neutral
vector `F ≠ 0` orthogonal to the vacuum keeps `⟨F, T²ᵏ F⟩ ≥ (ρ ‖T‖)²ᵏ ‖F‖²`, then some `Tʲ F` is a
neutral complement vector that `T` shrinks by at most `ρ`. With `F = g η` and `C(t)` the connected
Euclidean correlator of `g`, the hypothesis is `C(2k) ≥ ρ²ᵏ C(0)`: at `2k ≈ n` and `C(2k) ≥ δ C(0)`
this gives `ρ = δ^{1/(2k)} ≈ e^{-log(1/δ)/n}`, an O(1) statement with no small parameter. -/
theorem slow_lower_corr (k : ℕ) (hk : 0 < k) (Ω F : Hilbert n) (hΩ : T Ω = ‖T‖ • Ω)
    (hFn : Neutral n F) (hFo : inner ℂ Ω F = 0) (hF0 : F ≠ 0) (ρ : ℝ) (hρ : 0 < ρ)
    (hT : 0 < ‖T‖)
    (hcorr : (ρ * ‖T‖) ^ (2 * k) * ‖F‖ ^ 2 ≤ (inner ℂ F ((T ^ (2 * k)) F)).re) :
    ∃ f : Hilbert n, Neutral n f ∧ inner ℂ Ω f = 0 ∧ f ≠ 0 ∧ ρ * ‖T‖ * ‖f‖ ≤ ‖T f‖ := by
  by_contra hno
  push_neg at hno
  have hstep (j : ℕ) (hj : (T ^ j) F ≠ 0) : ‖(T ^ (j + 1)) F‖ < ρ * ‖T‖ * ‖(T ^ j) F‖ := by
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact hno _ (neutral_pow n β j F hFn) (orth_pow n β j Ω F hΩ hFo) hj
  have hr : 0 < ρ * ‖T‖ := mul_pos hρ hT
  have hdecay : ∀ j, 1 ≤ j → ‖(T ^ j) F‖ < (ρ * ‖T‖) ^ j * ‖F‖ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simpa using hstep 0 (by simpa using hF0)
    | succ j hj ih =>
      by_cases h0 : (T ^ j) F = 0
      · have : (T ^ (j + 1)) F = 0 := by
          rw [pow_succ', ContinuousLinearMap.mul_apply, h0, map_zero]
        rw [this, norm_zero]
        exact mul_pos (pow_pos hr _) (norm_pos_iff.mpr hF0)
      · calc ‖(T ^ (j + 1)) F‖ < ρ * ‖T‖ * ‖(T ^ j) F‖ := hstep j h0
          _ ≤ ρ * ‖T‖ * ((ρ * ‖T‖) ^ j * ‖F‖) := by gcongr
          _ = (ρ * ‖T‖) ^ (j + 1) * ‖F‖ := by ring
  have hk' := hdecay k hk
  have hsq : (inner ℂ F ((T ^ (2 * k)) F)).re = ‖(T ^ k) F‖ ^ 2 := by
    rw [← inner_pow_pow, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hsq] at hcorr
  have h1 : ‖(T ^ k) F‖ ^ 2 < ((ρ * ‖T‖) ^ k * ‖F‖) ^ 2 :=
    pow_lt_pow_left₀ hk' (norm_nonneg _) two_ne_zero
  have h2 : ((ρ * ‖T‖) ^ k * ‖F‖) ^ 2 = (ρ * ‖T‖) ^ (2 * k) * ‖F‖ ^ 2 := by ring
  linarith

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedSlowObservable
