/- Physical odd-sector contraction from the actual row overlap. The exact
row coefficient is averaged through the original transfer, without imposing
the earlier exponential likelihood profile as its definition. -/
import UnifiedTheory.Clay.YangMills.WilsonContrastMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonOverlapContraction
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonContrastMoment
open WilsonGroundRowAveraging CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def averaged (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) : C(Slice n, ℝ) :=
  step n β hβ (moment n i β hβ)

theorem averaged_full (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    averaged n i β hβ u = ∫ v, WilsonGroundLocalComparison.transition n β hβ u v *
      moment n i β hβ v ∂WilsonSlabOperator.measure n :=
  step_full n β hβ _ (fun h v => moment_gauge n i β hβ v h) u

theorem averaged_le_previous (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    averaged n i β hβ u ≤ WilsonAveragedSeamContraction.averaged n i β hβ u := by
  letI := WilsonTemporalInfluence.rowLaw_probability n β hβ u
  exact integral_mono
    (continuous_integrable (WilsonTemporalInfluence.rowLaw n β hβ u) _
      (moment n i β hβ).continuous)
    (continuous_integrable (WilsonTemporalInfluence.rowLaw n β hβ u) _
      (WilsonSeamRateProfile.profile n i β).continuous)
    (moment_le_profile n i β hβ)

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
  step_nonneg n β hβ _ (moment_nonneg n i β hβ) _

theorem rate_le_previous (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    rate n i β hβ ≤ WilsonAveragedSeamContraction.rate n i β hβ :=
  (averaged_le_previous n i β hβ _).trans
    (WilsonAveragedSeamContraction.averaged_le_rate n i β hβ _)

theorem rate_lt_one (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) : rate n i β hβ < 1 :=
  (rate_le_previous n i β hβ).trans_lt (WilsonAveragedSeamContraction.rate_lt_one n i β hβ)

theorem row_margin (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    1 - averaged n i β hβ u = ∫ v, WilsonGroundLocalComparison.transition n β hβ u v *
      (1 - moment n i β hβ v) ∂WilsonSlabOperator.measure n := by
  simp_rw [mul_sub, mul_one]
  rw [integral_sub
    (continuous_integrable (WilsonSlabOperator.measure n) _
      (WilsonPhysicalScore.transition_continuous n β hβ u))
    (continuous_integrable (WilsonSlabOperator.measure n)
      (fun v => WilsonGroundLocalComparison.transition n β hβ u v * moment n i β hβ v)
      ((WilsonPhysicalScore.transition_continuous n β hβ u).mul (moment n i β hβ).continuous)),
    WilsonGroundLocalComparison.transition_mass, ← averaged_full]

theorem rate_margin_le_row (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    1 - rate n i β hβ ≤ ∫ v, WilsonGroundLocalComparison.transition n β hβ u v *
      (1 - moment n i β hβ v) ∂WilsonSlabOperator.measure n := by
  rw [← row_margin]
  linarith only [averaged_le_rate n i β hβ u]

/-- The certified margin is the attained least averaged harmonic overlap of the original rows. -/
theorem rate_margin_overlap (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    1 - rate n i β hβ = ∫ v,
      WilsonGroundLocalComparison.transition n β hβ (maximizer n i β hβ) v *
        (∫ w, 2 * WilsonGroundLocalComparison.transition n β hβ v w *
          WilsonGroundLocalComparison.transition n β hβ (twist n i v) w /
          (WilsonGroundLocalComparison.transition n β hβ v w +
            WilsonGroundLocalComparison.transition n β hβ (twist n i v) w)
          ∂WilsonSlabOperator.measure n) ∂WilsonSlabOperator.measure n := by
  simp_rw [← overlap_identity]
  exact row_margin n i β hβ _

/-- The harmonic-kernel expression retains the temporal Haar integral and original ground. -/
theorem rate_margin_kernel (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    1 - rate n i β hβ = ∫ v,
      WilsonGroundLocalComparison.transition n β hβ (maximizer n i β hβ) v *
        (∫ w, harmonicKernel n i β (v,w) * WilsonGroundLocalComparison.ground n β hβ w /
          (‖transfer n β‖ * WilsonGroundLocalComparison.ground n β hβ v)
          ∂WilsonSlabOperator.measure n) ∂WilsonSlabOperator.measure n := by
  simp_rw [← overlap_kernel]
  exact row_margin n i β hβ _

theorem odd_source_bound (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hf : ∀ u, f (twist n i u) = -f u) :
    variance n β hβ (step n β hβ f) ≤
      ∫ u, (f u)^2 * averaged n i β hβ u ∂groundLaw n β hβ := by
  letI := groundLaw_probability n β hβ
  have hh := integral_mono
    (continuous_integrable (groundLaw n β hβ) _ ((step n β hβ f).continuous.pow 2))
    (continuous_integrable (groundLaw n β hβ) _
      ((moment n i β hβ).continuous.mul (step n β hβ (f^2)).continuous))
    (WilsonContrastMoment.odd_square n i β hβ f hinv hf)
  simp only [Pi.mul_apply] at hh
  rw [pairing n β hβ (moment n i β hβ) (f^2)] at hh
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

end
end UnifiedTheory.Clay.YangMills.WilsonOverlapContraction
