/- The middle bridge controls the actual source-weighted ground insertion.
This yields a closed variance-loss response bound with l1-times-l2 cost,
without passing through separate profile and ground-amplitude energies. -/
import UnifiedTheory.Clay.YangMills.WilsonMiddleGroundGain

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBridgeResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonMiddleBridge WilsonMiddleGroundGain WilsonVariancePair WilsonVarianceProfile
open WilsonGroundHeatBath WilsonPhysicalVariance WilsonWeightedEntropy WilsonStationaryEntropy
open WilsonPhysicalResponse WilsonAveragedResponse CompactDensityEntropy

variable (n : ℕ) [NeZero n]

theorem endpoint_continuous (β : ℝ) (hβ : 0 ≤ β) :
    Continuous (fun z : Slice n × Slice n => endpointWeight n β hβ z.1 z.2) := by
  have he : (fun z : Slice n × Slice n => endpointWeight n β hβ z.1 z.2) =
      fun z => ∫ u, pairWeight n β hβ u z.1 z.2 ∂WilsonSlabOperator.measure n :=
    funext (fun z => endpointWeight_integral n β hβ z.1 z.2)
  rw [he]
  exact GibbsMarginalTower.fiber_integral_continuous (WilsonSlabOperator.measure n) _
    ((pairWeight_continuous n β hβ).comp
      (f := fun p : (Slice n × Slice n) × Slice n => (p.2,p.1)) (by fun_prop))

/-- The endpoint source weight is retained in the actual law throughout. -/
theorem weighted_gain_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (f : C(Slice n, ℝ)) :
    (∫ u, (profile n β hβ f u)^2*pairedGain n β hβ q u ∂groundLaw n β hβ) ≤
      gainCap n β q*loss n β hβ f := by
  let μ := (WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)
  have hW : Continuous (fun z : Slice n × Slice n =>
      endpointWeight n β hβ z.1 z.2*(f z.1-f z.2)^2) :=
    (endpoint_continuous n β hβ).mul (by fun_prop)
  have hG : Continuous (fun z : Slice n × Slice n =>
      endpointWeight n β hβ z.1 z.2*(f z.1-f z.2)^2*gainMean n β hβ q z.1 z.2) := by
    have he : (fun z : Slice n × Slice n =>
        endpointWeight n β hβ z.1 z.2*(f z.1-f z.2)^2*gainMean n β hβ q z.1 z.2) =
        fun z => (f z.1-f z.2)^2*(∫ u, pairWeight n β hβ u z.1 z.2*
          pairedGain n β hβ q u ∂WilsonSlabOperator.measure n) := by
      funext z
      rw [fiber_integral]
      unfold gainMean
      ring
    rw [he]
    exact (by fun_prop : Continuous (fun z : Slice n × Slice n => (f z.1-f z.2)^2)).mul
      (GibbsMarginalTower.fiber_integral_continuous (WilsonSlabOperator.measure n) _
        (((pairWeight_continuous n β hβ).comp
          (f := fun p : (Slice n × Slice n) × Slice n => (p.2,p.1)) (by fun_prop)).mul
          ((pairedGain n β hβ q).continuous.comp continuous_snd)))
  have hi := integral_mono (continuous_integrable μ _ hG)
    (continuous_integrable μ _ (continuous_const.mul hW)) (fun z => by
      have h := mul_le_mul_of_nonneg_left (abs_le.mp (gainMean_bound n β hβ q z.1 z.2)).2
        (mul_nonneg (endpointWeight_pos n β hβ z.1 z.2).le (sq_nonneg (f z.1-f z.2)))
      simp only [Pi.mul_apply]
      nlinarith)
  simp only [Pi.mul_apply] at hi
  rw [integral_const_mul] at hi
  have hm := loss_pair n β hβ f
  have hw := weighted_profile n β hβ f (pairedGain n β hβ q)
  change _ = (∫ z, endpointWeight n β hβ z.1 z.2*(f z.1-f z.2)^2*
    gainMean n β hβ q z.1 z.2 ∂μ)/2 at hw
  change loss n β hβ f =
    (∫ z, endpointWeight n β hβ z.1 z.2*(f z.1-f z.2)^2 ∂μ)/2 at hm
  rw [hw, hm]
  linarith

/-- Direct control of the actual weighted ground insertion bypasses the profile-energy price. -/
theorem weighted_entropy_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (f : C(Slice n, ℝ)) :
    weightedEntropy n β hβ q (profile n β hβ f) ≤
      (18*β*WilsonJointRotation.cost n q+gainCap n β q)*loss n β hβ f := by
  letI := groundLaw_probability n β hβ
  let F := profile n β hβ f
  have hE (r : Slice n) : Continuous (fun u => (F u)^2*rowEntropy n β hβ u (r*u)) :=
    (F.continuous.pow 2).mul ((rowEntropy_continuous n β hβ).comp
      (f := fun u : Slice n => (u,r*u))
      (continuous_id.prodMk (continuous_const.mul continuous_id)))
  have hp := continuous_integrable (groundLaw n β hβ) _ (hE q)
  have hm := continuous_integrable (groundLaw n β hβ) _ (hE q⁻¹)
  have hM := continuous_integrable (groundLaw n β hβ) _ (F.continuous.pow 2)
  have hG := continuous_integrable (groundLaw n β hβ) _
    ((F.continuous.pow 2).mul (pairedGain n β hβ q).continuous)
  have hK := hM.const_mul (18*β*WilsonJointRotation.cost n q)
  have hi := integral_mono (hp.add hm) (hK.add hG) (fun u => by
    have h := mul_le_mul_of_nonneg_left (WilsonJointEntropy.rowEntropy_pair_bound n β hβ q u)
      (sq_nonneg (F u))
    simp only [Pi.add_apply, Pi.mul_apply, pairedGain, ContinuousMap.coe_mk]
    nlinarith)
  have he := integral_add hp hm
  have hr := integral_add hK hG
  simp only [Pi.add_apply, Pi.mul_apply] at hi he hr
  rw [he, hr, integral_const_mul] at hi
  change weightedEntropy n β hβ q F+weightedEntropy n β hβ q⁻¹ F ≤
    18*β*WilsonJointRotation.cost n q*WilsonWeightedEntropy.mass n β hβ F+
      (∫ u, (F u)^2*pairedGain n β hβ q u ∂groundLaw n β hβ) at hi
  dsimp only [F] at hi
  rw [profile_mass] at hi
  nlinarith [weighted_gain_bound n β hβ q f,
    weightedEntropy_nonneg n β hβ q⁻¹ (profile n β hβ f)]

theorem response_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (f : C(Slice n, ℝ)) :
    sourceEnergy n β hβ q (step n β hβ f) ≤
      coefficient n β q*(18*β*WilsonJointRotation.cost n q+gainCap n β q)*loss n β hβ f := by
  letI := groundLaw_probability n β hβ
  have hP := rowMean_continuous n β hβ f
  have hE : Continuous (fun u => (profile n β hβ f u)^2*rowEntropy n β hβ u (q*u)) :=
    ((profile n β hβ f).continuous.pow 2).mul ((rowEntropy_continuous n β hβ).comp
      (f := fun u : Slice n => (u,q*u))
      (continuous_id.prodMk (continuous_const.mul continuous_id)))
  have hR : Continuous (fun u => (rowMean n β hβ f (q*u)-rowMean n β hβ f u)^2) :=
    ((hP.comp (f := fun u : Slice n => q*u) (continuous_const.mul continuous_id)).sub hP).pow 2
  have hi := integral_mono (continuous_integrable (groundLaw n β hβ) _ hR)
    (continuous_integrable (groundLaw n β hβ) _ (continuous_const.mul hE)) (fun u => by
      have h := pointwise_response n β hβ q u f
      simp only [Pi.mul_apply, profile_square]
      nlinarith)
  simp only [Pi.mul_apply] at hi
  rw [integral_const_mul] at hi
  have he := mul_le_mul_of_nonneg_left (weighted_entropy_bound n β hβ q f)
    (coefficient_nonneg n β q)
  change sourceEnergy n β hβ q (step n β hβ f) ≤
    coefficient n β q*weightedEntropy n β hβ q (profile n β hβ f) at hi
  nlinarith

/-- The resulting bound uses the original full transfer on physical sources. -/
theorem physical_response_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ u, ((∫ v, transition n β hβ (q*u) v*f v ∂WilsonSlabOperator.measure n) -
      (∫ v, transition n β hβ u v*f v ∂WilsonSlabOperator.measure n))^2
      ∂groundLaw n β hβ) ≤
      coefficient n β q*(18*β*WilsonJointRotation.cost n q+gainCap n β q)*loss n β hβ f := by
  simp_rw [← step_full n β hβ f hinv]
  exact response_bound n β hβ q f

end
end UnifiedTheory.Clay.YangMills.WilsonBridgeResponse
