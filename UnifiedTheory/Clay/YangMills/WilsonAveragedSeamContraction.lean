/- An unconditional improved center-odd contraction rate at finite cutoff.
The rate is the attained maximum of the original transfer applied to the
physical row profile. Its cutoff-uniform physical scaling remains open. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundRowAveraging
import UnifiedTheory.Clay.YangMills.WilsonSeamRateProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonAveragedSeamContraction
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonSeamRateProfile
open WilsonGroundRowAveraging CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def averaged (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) : C(Slice n, ℝ) :=
  step n β hβ (profile n i β)

/-- The averaging uses the original full physical transfer with its original clock. -/
theorem averaged_full (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    averaged n i β hβ u = ∫ v, WilsonGroundLocalComparison.transition n β hβ u v *
      profile n i β v ∂WilsonSlabOperator.measure n :=
  step_full n β hβ _ (fun h v => profile_gauge n i β v h) u

theorem averaged_nonneg (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    0 ≤ averaged n i β hβ u := step_nonneg n β hβ _ (profile_nonneg n i β) u

theorem averaged_le_global (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    averaged n i β hβ u ≤ WilsonCenterContraction.rate n β :=
  step_le_const n β hβ _ _ (profile_le_global n i β) u

/-- Strict positivity propagates the identity-region improvement to every input. -/
theorem averaged_lt_global (hn : 4 ≤ n) (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (hβpos : 0 < β) (u : Slice n) :
    averaged n i β hβ u < WilsonCenterContraction.rate n β :=
  step_lt_const n β hβ _ _ (profile_le_global n i β) 1
    (profile_identity_lt n hn i β hβpos) u

theorem exists_maximizer (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ u : Slice n, ∀ v : Slice n, averaged n i β hβ v ≤ averaged n i β hβ u := by
  obtain ⟨u, _, hu⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (Slice n)).Nonempty)
    (averaged n i β hβ).continuous.continuousOn
  exact ⟨u, fun v => hu (Set.mem_univ v)⟩

def maximizer (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) : Slice n :=
  (exists_maximizer n i β hβ).choose

def rate (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) : ℝ :=
  averaged n i β hβ (maximizer n i β hβ)

theorem averaged_le_rate (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    averaged n i β hβ u ≤ rate n i β hβ := (exists_maximizer n i β hβ).choose_spec u

theorem rate_nonneg (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) : 0 ≤ rate n i β hβ :=
  averaged_nonneg n i β hβ _

theorem rate_le_global (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    rate n i β hβ ≤ WilsonCenterContraction.rate n β := averaged_le_global n i β hβ _

theorem rate_lt_one (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) : rate n i β hβ < 1 :=
  (rate_le_global n i β hβ).trans_lt (WilsonCenterContraction.rate_lt_one n β)

/-- A strict improvement is proved without an additional source-weighted estimate. -/
theorem rate_lt_global (hn : 4 ≤ n) (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (hβpos : 0 < β) :
    rate n i β hβ < WilsonCenterContraction.rate n β := averaged_lt_global n hn i β hβ hβpos _

/-- The margin is an actual physical row integral with no remaining arbitrary-source weight. -/
theorem row_margin (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    1 - averaged n i β hβ u = ∫ v, WilsonGroundLocalComparison.transition n β hβ u v *
      (4 / (4 + WilsonPhysicalSeamResponse.weight n i β v)) ∂WilsonSlabOperator.measure n := by
  simp_rw [← profile_complement, mul_sub, mul_one]
  rw [integral_sub
    (continuous_integrable (WilsonSlabOperator.measure n) _
      (WilsonPhysicalScore.transition_continuous n β hβ u))
    (continuous_integrable (WilsonSlabOperator.measure n)
      (fun v => WilsonGroundLocalComparison.transition n β hβ u v * profile n i β v)
      ((WilsonPhysicalScore.transition_continuous n β hβ u).mul (profile n i β).continuous)),
    WilsonGroundLocalComparison.transition_mass, ← averaged_full]

theorem rate_margin_le_row (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    1 - rate n i β hβ ≤ ∫ v, WilsonGroundLocalComparison.transition n β hβ u v *
      (4 / (4 + WilsonPhysicalSeamResponse.weight n i β v)) ∂WilsonSlabOperator.measure n := by
  rw [← row_margin]
  linarith only [averaged_le_rate n i β hβ u]

/-- The lower row margin is attained, giving a concrete target for physical-scale estimates. -/
theorem rate_margin_at_maximum (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    1 - rate n i β hβ = ∫ v,
      WilsonGroundLocalComparison.transition n β hβ (maximizer n i β hβ) v *
        (4 / (4 + WilsonPhysicalSeamResponse.weight n i β v)) ∂WilsonSlabOperator.measure n :=
  row_margin n i β hβ _

/-- Reversibility moves the row profile onto the source through the actual transfer. -/
theorem odd_source_bound (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hf : ∀ u, f (twist n i u) = -f u) :
    variance n β hβ (step n β hβ f) ≤
      ∫ u, (f u)^2 * averaged n i β hβ u ∂groundLaw n β hβ := by
  letI := groundLaw_probability n β hβ
  have hh := integral_mono
    (continuous_integrable (groundLaw n β hβ) _ ((step n β hβ f).continuous.pow 2))
    (continuous_integrable (groundLaw n β hβ) _
      ((profile n i β).continuous.mul (step n β hβ (f^2)).continuous))
    (odd_square n i β hβ f hinv hf)
  simp only [Pi.mul_apply] at hh
  rw [pairing n β hβ (profile n i β) (f^2)] at hh
  rw [variance_formula, WilsonCenterCoercivity.odd_mean n i β hβ _
    (WilsonCenterContraction.step_odd n i β hβ f hf)]
  simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero, ContinuousMap.pow_apply] using hh

theorem odd_contraction (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hf : ∀ u, f (twist n i u) = -f u) :
    variance n β hβ (step n β hβ f) ≤ rate n i β hβ * variance n β hβ f := by
  letI := groundLaw_probability n β hβ
  have hh := integral_mono
    (continuous_integrable (groundLaw n β hβ) _
      ((f.continuous.pow 2).mul (averaged n i β hβ).continuous))
    ((continuous_integrable (groundLaw n β hβ) _ (f.continuous.pow 2)).mul_const
      (rate n i β hβ))
    (fun u => mul_le_mul_of_nonneg_left (averaged_le_rate n i β hβ u) (sq_nonneg (f u)))
  rw [integral_mul_const] at hh
  have hu := (odd_source_bound n i β hβ f hinv hf).trans hh
  rw [variance_formula n β hβ f, WilsonCenterCoercivity.odd_mean n i β hβ f hf]
  simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_comm] using hu

/-- The center-even variance remains explicitly present for arbitrary physical sources. -/
theorem partial_contraction (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    variance n β hβ (step n β hβ f) ≤
      variance n β hβ (WilsonCenterCoercivity.evenPart n i f) +
        rate n i β hβ * variance n β hβ (WilsonCenterCoercivity.oddPart n i f) := by
  rw [WilsonCenterCoercivity.variance_split n i β hβ (step n β hβ f),
    ← (WilsonCenterCoercivity.step_parts n i β hβ f).1,
    ← (WilsonCenterCoercivity.step_parts n i β hβ f).2]
  exact add_le_add (variance_step_le n β hβ _)
    (odd_contraction n i β hβ _
      (fun h u => (WilsonCenterCoercivity.parts_gauge n i f hinv h u).2)
      (WilsonCenterCoercivity.odd_parity n i f))

theorem odd_iterate (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hf : ∀ u, f (twist n i u) = -f u) (k : ℕ) :
    variance n β hβ (WilsonDissipationIteration.flow n β hβ f k) ≤
      (rate n i β hβ)^k * variance n β hβ f := by
  induction k with
  | zero => simp only [WilsonDissipationIteration.flow, pow_zero, one_mul, le_refl]
  | succ k ih =>
    apply (odd_contraction n i β hβ _ (WilsonDissipationIteration.flow_gauge n β hβ f hinv k)
      (WilsonCenterContraction.flow_odd n i β hβ f hf k)).trans
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left ih (rate_nonneg n i β hβ)

theorem odd_eigenvalue (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hf : ∀ u, f (twist n i u) = -f u)
    (hv : 0 < variance n β hβ f) (σ : ℝ) (heigen : step n β hβ f = σ • f) :
    σ^2 ≤ rate n i β hβ := by
  have hh := odd_contraction n i β hβ f hinv hf
  rw [heigen] at hh
  have hs : variance n β hβ (σ • f) = σ^2 * variance n β hβ f :=
    ProbabilityTheory.variance_smul σ f (groundLaw n β hβ)
  rw [hs] at hh
  exact (mul_le_mul_iff_left₀ hv).mp hh

end
end UnifiedTheory.Clay.YangMills.WilsonAveragedSeamContraction
