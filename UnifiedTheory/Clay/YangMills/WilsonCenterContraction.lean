/- Matching seam-response upper and lower bounds give actual one-step
contraction of the center-odd sector. Its explicit rate tends to one when
coupling times seam area diverges; no uniform physical mass gap follows. -/
import UnifiedTheory.Clay.YangMills.WilsonCenterLikelihood
import UnifiedTheory.Clay.YangMills.WilsonDissipationIteration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCenterContraction
noncomputable section
open MeasureTheory Filter WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist
open WilsonPhysicalVariance WilsonCenterCoercivity WilsonCenterLikelihood
open scoped Topology

variable (n : ℕ)

def rate (β : ℝ) : ℝ := (scale n β - 1)^2 / (scale n β + 1)^2

theorem rate_nonneg (β : ℝ) : 0 ≤ rate n β := div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem rate_lt_one (β : ℝ) : rate n β < 1 := by
  have hp := scale_pos n β
  apply (div_lt_one (sq_pos_of_pos (by linarith : 0 < scale n β + 1))).mpr
  nlinarith

theorem coefficient_identity (β : ℝ) :
    (4 + WilsonCenterLikelihood.coefficient n β) * rate n β =
      WilsonCenterLikelihood.coefficient n β := by
  unfold WilsonCenterLikelihood.coefficient rate
  have hp := scale_pos n β
  field_simp [hp.ne', (by linarith : scale n β + 1 ≠ 0)]
  ring

/-- This quantifies the proved rate, not an upper bound on the actual spectral gap. -/
theorem rate_margin (β : ℝ) : 1 - rate n β = 4 * scale n β / (scale n β + 1)^2 := by
  unfold rate
  have hp := scale_pos n β
  field_simp [(by linarith : scale n β + 1 ≠ 0)]
  ring

theorem rate_margin_upper (β : ℝ) : 1 - rate n β ≤ 4 / scale n β := by
  rw [rate_margin]
  have hp := scale_pos n β
  apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < scale n β + 1)) hp).mpr
  nlinarith

theorem rate_margin_lower (β : ℝ) (hβ : 0 ≤ β) : (scale n β)⁻¹ ≤ 1 - rate n β := by
  rw [rate_margin, ← one_div]
  have hp := scale_pos n β
  have h1 := scale_ge_one n β hβ
  apply (div_le_div_iff₀ hp (sq_pos_of_pos (by linarith : 0 < scale n β + 1))).mpr
  nlinarith

omit n in
/-- The available rate deteriorates along every trajectory with divergent coupling times area. -/
theorem rate_tendsto {ι : Type*} {l : Filter ι} (N : ι → ℕ) (β : ι → ℝ)
    (hcost : Tendsto (fun k => 4 * β k * (N k : ℝ) ^ 2) l atTop) :
    Tendsto (fun k => rate (N k) (β k)) l (𝓝 1) := by
  have hs : Tendsto (fun k => (scale (N k) (β k))⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp hcost)
  have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub hs).div (tendsto_const_nhds.add hs)
    (by norm_num : (1 : ℝ) + 0 ≠ 0)).pow 2
  have he (k : ι) : rate (N k) (β k) =
      ((1 - (scale (N k) (β k))⁻¹) / (1 + (scale (N k) (β k))⁻¹))^2 := by
    unfold rate
    have hp := scale_pos (N k) (β k)
    field_simp [hp.ne', (by linarith : scale (N k) (β k) + 1 ≠ 0)]
  simp only [Pi.div_apply] at hh
  simpa only [← he, sub_zero, add_zero, div_one, one_pow] using hh

variable [NeZero n]

theorem step_odd (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, f (twist n i u) = -f u) :
    ∀ u, step n β hβ f (twist n i u) = -step n β hβ f u := by
  have he : oddPart n i f = f := by
    ext u
    simp only [oddPart, ContinuousMap.smul_apply, ContinuousMap.sub_apply, pull_apply, hf,
      smul_eq_mul]
    ring
  have hp := (step_parts n i β hβ f).2
  rw [he] at hp
  intro u
  have hh := odd_parity n i (step n β hβ f) u
  rw [← hp] at hh
  exact hh

/-- The earlier lower bound and the new upper bound use exactly the same response energy. -/
theorem odd_contraction (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, f (twist n i u) = -f u) :
    variance n β hβ (step n β hβ f) ≤ rate n β * variance n β hβ f := by
  have hu := WilsonCenterLikelihood.response_le_loss n i β hβ f
  have hl := odd_coercivity n i β hβ (step n β hβ f) (step_odd n i β hβ f hf)
  rw [loss] at hu
  have hh : (4 + WilsonCenterLikelihood.coefficient n β) *
      variance n β hβ (step n β hβ f) ≤
        WilsonCenterLikelihood.coefficient n β * variance n β hβ f := by
    nlinarith only [hu, hl]
  apply (mul_le_mul_iff_right₀
    (show 0 < 4 + WilsonCenterLikelihood.coefficient n β from by
      have hc := WilsonCenterLikelihood.coefficient_nonneg n β
      linarith)).mp
  calc
    _ ≤ WilsonCenterLikelihood.coefficient n β * variance n β hβ f := by
      simpa only [mul_comm] using hh
    _ = _ := by rw [← mul_assoc, coefficient_identity]

/-- Explicit identification with the original full physical transition. -/
theorem physical_odd_contraction (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (f : C(Slice n, ℝ)) (hinv : ∀ h u, f (gaugeSlice h u) = f u)
    (hf : ∀ u, f (twist n i u) = -f u) :
    (∫ u, (∫ v, WilsonGroundLocalComparison.transition n β hβ u v * f v
      ∂WilsonSlabOperator.measure n)^2 ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤
        rate n β * variance n β hβ f := by
  have hh := odd_contraction n i β hβ f hf
  rw [variance_formula, odd_mean n i β hβ _ (step_odd n i β hβ f hf)] at hh
  simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero, step_full n β hβ f hinv] using hh

theorem flow_odd (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, f (twist n i u) = -f u) (k : ℕ) :
    ∀ u, WilsonDissipationIteration.flow n β hβ f k (twist n i u) =
      -WilsonDissipationIteration.flow n β hβ f k u := by
  induction k with
  | zero => exact hf
  | succ k ih => exact step_odd n i β hβ _ ih

/-- Iteration uses the actual original transfer clock. -/
theorem odd_iterate (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, f (twist n i u) = -f u) (k : ℕ) :
    variance n β hβ (WilsonDissipationIteration.flow n β hβ f k) ≤
      (rate n β)^k * variance n β hβ f := by
  induction k with
  | zero => simp only [WilsonDissipationIteration.flow, pow_zero, one_mul, le_refl]
  | succ k ih =>
    apply (odd_contraction n i β hβ _ (flow_odd n i β hβ f hf k)).trans
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left ih (rate_nonneg n β)

/-- No arbitrary-source variance is lost: the center-even contribution is retained. -/
theorem partial_contraction (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    variance n β hβ (step n β hβ f) ≤ variance n β hβ (evenPart n i f) +
      rate n β * variance n β hβ (oddPart n i f) := by
  rw [variance_split n i β hβ (step n β hβ f),
    ← (step_parts n i β hβ f).1, ← (step_parts n i β hβ f).2]
  exact add_le_add (variance_step_le n β hβ _) (odd_contraction n i β hβ _ (odd_parity n i f))

/-- A nonzero eigenfunction in this sector obeys the explicit finite-cutoff bound. -/
theorem odd_eigenvalue (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, f (twist n i u) = -f u) (hv : 0 < variance n β hβ f)
    (σ : ℝ) (heigen : step n β hβ f = σ • f) : σ^2 ≤ rate n β := by
  have hh := odd_contraction n i β hβ f hf
  rw [heigen] at hh
  have hs : variance n β hβ (σ • f) = σ^2 * variance n β hβ f :=
    ProbabilityTheory.variance_smul σ f (WilsonGroundHeatBath.groundLaw n β hβ)
  rw [hs] at hh
  exact (mul_le_mul_iff_left₀ hv).mp hh

end
end UnifiedTheory.Clay.YangMills.WilsonCenterContraction
