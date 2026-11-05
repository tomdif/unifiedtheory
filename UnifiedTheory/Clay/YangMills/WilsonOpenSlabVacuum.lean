/- Quantitative vacuum limit for the midpoint of the actually constructed
finite open Wilson chain. The cutoff and coupling are fixed; the explicit
rate and prefactor are not uniform in physical scaling. -/
import UnifiedTheory.Clay.YangMills.WilsonOpenSlab
import UnifiedTheory.Clay.YangMills.WilsonVacuumConvergence
import UnifiedTheory.Clay.YangMills.SquaredDensityConvergence
import UnifiedTheory.Clay.YangMills.GibbsConstantShift
import UnifiedTheory.Clay.YangMills.WilsonGroundHeatBath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonOpenSlabVacuum
noncomputable section
open MeasureTheory Filter WilsonSlabOperator WilsonTimeSlab WilsonOpenSlab
open WilsonPositiveGroundState WilsonVacuumConvergence WilsonSlabContraction
open TransferEnergySurvival SquaredDensityConvergence
open scoped Topology

/-- Real normalization commutes exactly with every transfer iterate. -/
theorem iterate_real_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (r : ℝ) (k : ℕ) (w : H) :
    iterate (r • T) k w = r ^ k • iterate T k w := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [iterate_succ, ContinuousLinearMap.smul_apply, ih,
      map_real_smul T T.continuous, smul_smul, pow_succ, mul_comm]

variable (n : ℕ) [NeZero n]

def scaledMessage (β : ℝ) (k : ℕ) : C(Slice n, ℝ) :=
  (‖transfer n β‖⁻¹) ^ k • message n β k

theorem scaledMessage_embedding (β : ℝ) (k : ℕ) :
    ContinuousMap.toLp 2 (measure n) ℂ (complexify (scaledMessage n β k)) =
      iterate (normalized n β) k (boundary n) := by
  rw [scaledMessage, complexify_smul, map_smul, message_embedding,
    normalized, iterate_real_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem scaledMessage_norm_pos (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) :
    0 < amplitudeNorm (measure n) (scaledMessage n β k) := by
  have hm : 0 < amplitudeNorm (measure n) (message n β k) := by
    have hs := squareMass_positive n β k
    rw [squareMass, ← amplitudeNorm_sq] at hs
    have hn : 0 ≤ amplitudeNorm (measure n) (message n β k) := norm_nonneg _
    nlinarith
  have hT := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  rw [scaledMessage, amplitudeNorm_smul, abs_of_pos (pow_pos (inv_pos.mpr hT) k)]
  exact mul_pos (pow_pos (inv_pos.mpr hT) k) hm

/-- The auxiliary normalization of the message cancels from the actual midpoint law. -/
theorem scaledMessage_law (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) :
    LocalGibbsComparison.weightedLaw (measure n) (fun u => (scaledMessage n β k u) ^ 2) =
      midpointLaw n β k := by
  have hT := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  simp only [scaledMessage, ContinuousMap.smul_apply, smul_eq_mul, mul_pow]
  exact GibbsConstantShift.weightedLaw_const_mul (measure n)
    (fun u => (message n β k u) ^ 2) ((message n β k).continuous.pow 2).measurable
    (((‖transfer n β‖⁻¹) ^ k) ^ 2) (by positivity)

/-- Ground-law integration is exactly integration against the unit positive profile squared. -/
theorem ground_integral (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    (∫ u, F u ∂WilsonGroundHeatBath.groundLaw n β hβ) =
      ∫ u, (WilsonGroundLocalComparison.ground n β hβ u) ^ 2 * F u ∂measure n := by
  rw [WilsonGroundHeatBath.groundLaw_eq_weightedLaw,
    LocalGibbsComparison.weighted_integral _ _
      ((WilsonGroundLocalComparison.ground n β hβ).continuous.pow 2).measurable
      (fun u => sq_nonneg (WilsonGroundLocalComparison.ground n β hβ u))
      (by rw [WilsonGroundLocalComparison.ground_square_integral]; norm_num),
    WilsonGroundLocalComparison.ground_square_integral, div_one]

theorem amplitude_error (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) :
    amplitudeNorm (measure n) (scaledMessage n β k -
      overlap n β hβ • WilsonGroundLocalComparison.ground n β hβ) ≤
      ratioCap n β ^ k * ‖boundary n - (overlap n β hβ : ℂ) • vacuum n β hβ‖ := by
  rw [amplitudeNorm_complex]
  have he : complexify (scaledMessage n β k -
      overlap n β hβ • WilsonGroundLocalComparison.ground n β hβ) =
      complexify (scaledMessage n β k) -
        (overlap n β hβ : ℂ) • complexify (WilsonGroundLocalComparison.ground n β hβ) := by
    ext u
    simp [complexify]
  rw [he, map_sub, map_smul, scaledMessage_embedding]
  exact boundary_power_error n β hβ k

/-- Quantitative midpoint convergence with the actual positive boundary overlap. -/
theorem midpoint_error (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) (F : C(Slice n, ℝ)) :
    |(∫ u, F u ∂midpointLaw n β k) -
      (∫ u, F u ∂WilsonGroundHeatBath.groundLaw n β hβ)| ≤
      (4 * ‖F‖ / overlap n β hβ) *
        (ratioCap n β ^ k * ‖boundary n - (overlap n β hβ : ℂ) • vacuum n β hβ‖) := by
  have hn : amplitudeNorm (measure n) (WilsonGroundLocalComparison.ground n β hβ) = 1 := by
    rw [amplitudeNorm_complex]
    exact vacuum_norm n β hβ
  have h := square_law_error (measure n) (scaledMessage n β k)
    (WilsonGroundLocalComparison.ground n β hβ) F (scaledMessage_norm_pos n β hβ k)
    hn (overlap n β hβ) (overlap_pos n β hβ)
  rw [scaledMessage_law n β hβ k, ← ground_integral n β hβ F] at h
  exact h.trans (mul_le_mul_of_nonneg_left (amplitude_error n β hβ k)
    (div_nonneg (by positivity) (overlap_pos n β hβ).le))

/-- The actual boundary overlap has an explicit finite-volume lower bound. -/
theorem overlap_lower (β : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))) ≤ overlap n β hβ := by
  have hg (u : Slice n) := top_eigenfunction_profile_bounds n β hβ
    (WilsonGroundLocalComparison.ground n β hβ)
    (fun v => (WilsonGroundLocalComparison.ground_pos n β hβ v).le)
    (WilsonGroundLocalComparison.ground_square_integral n β hβ)
    (WilsonGroundLocalComparison.ground_equation n β hβ) u
  have h := integral_mono
    (integrable_const (Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))))
    ((WilsonGroundLocalComparison.ground n β hβ).continuous.integrable_of_hasCompactSupport
      (μ := measure n) (HasCompactSupport.of_compactSpace _)) (fun u => (hg u).1)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

/-- Orthogonal projection cannot enlarge the unit constant boundary vector. -/
theorem boundary_residual_norm_le_one (β : ℝ) (hβ : 0 ≤ β) :
    ‖boundary n - (overlap n β hβ : ℂ) • vacuum n β hβ‖ ≤ 1 := by
  have hi : inner ℂ (boundary n) (vacuum n β hβ) = (overlap n β hβ : ℂ) := by
    rw [← inner_conj_symm, overlap_inner, Complex.conj_ofReal]
  have h := norm_sub_sq (𝕜 := ℂ) (boundary n)
    ((overlap n β hβ : ℂ) • vacuum n β hβ)
  rw [boundary_norm, inner_smul_right, hi, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (overlap_pos n β hβ), vacuum_norm, mul_one] at h
  simp only [← Complex.ofReal_mul, one_pow] at h
  change ‖boundary n - (overlap n β hβ : ℂ) • vacuum n β hβ‖ ^ 2 =
    1 - 2 * (overlap n β hβ * overlap n β hβ) + overlap n β hβ ^ 2 at h
  nlinarith [sq_nonneg (overlap n β hβ),
    norm_nonneg (boundary n - (overlap n β hβ : ℂ) • vacuum n β hβ)]

/-- A completely explicit finite-cutoff error, whose constants display the volume loss. -/
theorem midpoint_error_explicit (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) (F : C(Slice n, ℝ)) :
    |(∫ u, F u ∂midpointLaw n β k) -
      (∫ u, F u ∂WilsonGroundHeatBath.groundLaw n β hβ)| ≤
      4 * ‖F‖ * Real.exp (24 * β * (Fintype.card (SpatialVertex n) : ℝ)) * ratioCap n β ^ k := by
  have hq : 0 ≤ ratioCap n β ^ k := pow_nonneg (ratioCap_nonneg n β hβ) k
  have hc : 0 ≤ 4 * ‖F‖ / overlap n β hβ :=
    div_nonneg (by positivity) (overlap_pos n β hβ).le
  calc
    _ ≤ (4 * ‖F‖ / overlap n β hβ) *
        (ratioCap n β ^ k * ‖boundary n - (overlap n β hβ : ℂ) • vacuum n β hβ‖) :=
      midpoint_error n β hβ k F
    _ ≤ (4 * ‖F‖ / overlap n β hβ) * ratioCap n β ^ k := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (boundary_residual_norm_le_one n β hβ) hq) hc
    _ ≤ (4 * ‖F‖ / Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))) *
        ratioCap n β ^ k :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
        (Real.exp_pos _) (overlap_lower n β hβ)) hq
    _ = _ := by rw [Real.exp_neg, div_inv_eq_mul]

/-- The explicit estimate for the midpoint observable on the actual finite open chain. -/
theorem open_midpoint_error (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) (F : C(Slice n, ℝ)) :
    |(∫ z, F z.1 ∂openLaw n β k) -
      (∫ u, F u ∂WilsonGroundHeatBath.groundLaw n β hβ)| ≤
      4 * ‖F‖ * Real.exp (24 * β * (Fintype.card (SpatialVertex n) : ℝ)) * ratioCap n β ^ k := by
  rw [midpoint_integral n β k F F.continuous]
  exact midpoint_error_explicit n β hβ k F

/-- At each fixed cutoff, midpoint expectations converge to the constructed Wilson ground law. -/
theorem midpoint_tendsto (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    Tendsto (fun k => ∫ u, F u ∂midpointLaw n β k) atTop
      (𝓝 (∫ u, F u ∂WilsonGroundHeatBath.groundLaw n β hβ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => by simpa only [Real.norm_eq_abs] using midpoint_error_explicit n β hβ k F)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (ratioCap_nonneg n β hβ)
      (ratioCap_lt_one n β)).const_mul
        (4 * ‖F‖ * Real.exp (24 * β * (Fintype.card (SpatialVertex n) : ℝ)))

/-- The vacuum limit belongs to the explicitly constructed original open-chain midpoint. -/
theorem open_midpoint_tendsto (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    Tendsto (fun k => ∫ z, F z.1 ∂openLaw n β k) atTop
      (𝓝 (∫ u, F u ∂WilsonGroundHeatBath.groundLaw n β hβ)) := by
  have he : (fun k => ∫ z, F z.1 ∂openLaw n β k) =
      (fun k => ∫ u, F u ∂midpointLaw n β k) :=
    funext (fun k => midpoint_integral n β k F F.continuous)
  rw [he]
  exact midpoint_tendsto n β hβ F

end
end UnifiedTheory.Clay.YangMills.WilsonOpenSlabVacuum
