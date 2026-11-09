/- Actual row-entropy quadratic-form bounds for interior-dependent source
weights. Their finite-difference energy pays for the ground correction. -/
import UnifiedTheory.Clay.YangMills.WilsonExteriorResponse
import UnifiedTheory.Clay.YangMills.CompactRotationIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonWeightedEntropy
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonGroundHeatBath WilsonStationaryEntropy CompactDensityEntropy

variable (n : ℕ) [NeZero n]
local instance haar_left : (WilsonSlabOperator.measure n).IsMulLeftInvariant := by
  unfold WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar
  infer_instance

def mass (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) : ℝ :=
  ∫ U, (F U)^2 ∂groundLaw n β hβ

def sourceEnergy (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) : ℝ :=
  ∫ U, (F (q*U)-F U)^2 ∂groundLaw n β hβ

def amplitudeEnergy (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) : ℝ :=
  CompactRotationIdentity.amplitudeEnergy (WilsonSlabOperator.measure n) (ground n β hβ) F q

theorem amplitudeEnergy_nonneg (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) :
    0 ≤ amplitudeEnergy n β hβ q F :=
  CompactRotationIdentity.amplitudeEnergy_nonneg _ _ _ _

theorem sourceEnergy_eq (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) :
    sourceEnergy n β hβ q F =
      CompactRotationIdentity.sourceEnergy (WilsonSlabOperator.measure n) (ground n β hβ) F q := by
  rw [sourceEnergy, groundLaw, GroundStateDirichlet.stationary_integral
    (WilsonSlabOperator.measure n) (ground n β hβ) (ground n β hβ).continuous]
  rfl

/-- The weight may depend on every link, including the rotated coordinates. -/
theorem ground_pair_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) :
    (∫ U, (F U)^2*(WilsonJointEntropy.logGain n β hβ q U +
      WilsonJointEntropy.logGain n β hβ q⁻¹ U) ∂groundLaw n β hβ) +
      amplitudeEnergy n β hβ q F ≤
        (sourceEnergy n β hβ q F+sourceEnergy n β hβ q⁻¹ F)/2 := by
  have h := CompactRotationIdentity.weighted_log_le_energy
    (WilsonSlabOperator.measure n) (ground n β hβ) F (ground_pos n β hβ) q
  rw [sourceEnergy_eq, sourceEnergy_eq]
  have he : (∫ U, (F U)^2*(WilsonJointEntropy.logGain n β hβ q U +
      WilsonJointEntropy.logGain n β hβ q⁻¹ U) ∂groundLaw n β hβ) =
      ∫ U, (ground n β hβ U)^2*(F U)^2*
        (Real.log (ground n β hβ (q*U))+Real.log (ground n β hβ (q⁻¹*U)) -
          2*Real.log (ground n β hβ U)) ∂WilsonSlabOperator.measure n := by
    rw [groundLaw, GroundStateDirichlet.stationary_integral
      (WilsonSlabOperator.measure n) (ground n β hβ) (ground n β hβ).continuous]
    apply integral_congr_ae
    filter_upwards with U
    unfold WilsonJointEntropy.logGain
    ring
  rw [he]
  exact h

def weightedEntropy (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) : ℝ :=
  ∫ U, (F U)^2*rowEntropy n β hβ U (q*U) ∂groundLaw n β hβ

theorem weightedEntropy_nonneg (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) :
    0 ≤ weightedEntropy n β hβ q F :=
  integral_nonneg (fun U => mul_nonneg (sq_nonneg _) (rowEntropy_nonneg n β hβ U _))

/-- The source-energy price is explicit; the nonnegative amplitude term is retained. -/
theorem paired_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) :
    weightedEntropy n β hβ q F + weightedEntropy n β hβ q⁻¹ F +
      amplitudeEnergy n β hβ q F ≤
      18*β*WilsonJointRotation.cost n q*mass n β hβ F +
        (sourceEnergy n β hβ q F+sourceEnergy n β hβ q⁻¹ F)/2 := by
  letI := groundLaw_probability n β hβ
  have hE (r : Slice n) : Continuous (fun U => (F U)^2*rowEntropy n β hβ U (r*U)) :=
    (F.continuous.pow 2).mul ((rowEntropy_continuous n β hβ).comp
      (f := fun U : Slice n => (U,r*U))
      (continuous_id.prodMk (continuous_const.mul continuous_id)))
  have hp := continuous_integrable (groundLaw n β hβ) _ (hE q)
  have hm := continuous_integrable (groundLaw n β hβ) _ (hE q⁻¹)
  have hM := continuous_integrable (groundLaw n β hβ) _ (F.continuous.pow 2)
  have hG := continuous_integrable (groundLaw n β hβ)
    (fun U => (F U)^2*(WilsonJointEntropy.logGain n β hβ q U+
      WilsonJointEntropy.logGain n β hβ q⁻¹ U))
    ((F.continuous.pow 2).mul ((WilsonJointEntropy.logGain_continuous n β hβ q).add
      (WilsonJointEntropy.logGain_continuous n β hβ q⁻¹)))
  have hK := hM.const_mul (18*β*WilsonJointRotation.cost n q)
  have h := integral_mono (hp.add hm) (hK.add hG) (fun U => by
    have hh := mul_le_mul_of_nonneg_left (WilsonJointEntropy.rowEntropy_pair_bound n β hβ q U)
      (sq_nonneg (F U))
    simp only [Pi.add_apply]
    nlinarith)
  have he := integral_add hp hm
  have hr := integral_add hK hG
  simp only [Pi.add_apply] at h he hr
  rw [he, hr, integral_const_mul] at h
  change weightedEntropy n β hβ q F+weightedEntropy n β hβ q⁻¹ F ≤
    18*β*WilsonJointRotation.cost n q*mass n β hβ F +
      (∫ U, (F U)^2*(WilsonJointEntropy.logGain n β hβ q U+
        WilsonJointEntropy.logGain n β hβ q⁻¹ U) ∂groundLaw n β hβ) at h
  linarith [ground_pair_bound n β hβ q F]

theorem bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (F : C(Slice n, ℝ)) :
    weightedEntropy n β hβ q F ≤ 18*β*WilsonJointRotation.cost n q*mass n β hβ F +
      (sourceEnergy n β hβ q F+sourceEnergy n β hβ q⁻¹ F)/2 := by
  linarith [paired_bound n β hβ q F, weightedEntropy_nonneg n β hβ q⁻¹ F,
    amplitudeEnergy_nonneg n β hβ q F]

end
end UnifiedTheory.Clay.YangMills.WilsonWeightedEntropy
