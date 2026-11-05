/- The entropy form is tested with the actual row standard deviation.
Its squared mass equals actual transfer variance loss. The remaining error
is its finite-difference energy, with ground-amplitude energy retained. -/
import UnifiedTheory.Clay.YangMills.CompactEntropyMoment
import UnifiedTheory.Clay.YangMills.WilsonInteriorResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonVarianceProfile
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonStationaryEntropy WilsonTemporalGauge WilsonAveragedResponse WilsonPhysicalResponse
open WilsonVarianceResponse WilsonPhysicalVariance CompactDensityEntropy WilsonRowGeometry
open WilsonWeightedEntropy WilsonTemporalInfluence WilsonGroundLocalComparison
open scoped Quaternion

variable (n : ℕ) [NeZero n]

def length (q : Slice n) : ℝ := ∑ e, WilsonJointRotation.displacement n q e

theorem rotation_cost (q u : Slice n) : inputCost n (q*u) u = length n q := by
  unfold inputCost length WilsonJointRotation.displacement
  apply Finset.sum_congr rfl
  intro e _
  change ‖(q e : ℍ)*(u e : ℍ)-(u e : ℍ)‖ = _
  calc
    _ = ‖((q e : ℍ)-1)*(u e : ℍ)‖ := by congr 1; noncomm_ring
    _ = _ := by rw [norm_mul, QuaternionSymmetricChange.unit_norm, mul_one]

def coefficient (β : ℝ) (q : Slice n) : ℝ := 2*(1+Real.exp (4*β*length n q))

theorem coefficient_nonneg (β : ℝ) (q : Slice n) : 0 ≤ coefficient n β q := by
  unfold coefficient
  positivity

def profile (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  ⟨fun u => Real.sqrt (rowVariance n β hβ f u), (rowVariance_continuous n β hβ f).sqrt⟩

theorem profile_square (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) :
    (profile n β hβ f u)^2 = rowVariance n β hβ f u :=
  Real.sq_sqrt (rowVariance_nonneg n β hβ f u)

theorem profile_mass (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    mass n β hβ (profile n β hβ f) = loss n β hβ f := by
  unfold mass
  simp_rw [profile_square]
  exact mean_rowVariance_eq_loss n β hβ f

/-- No source range occurs: the factor is the actual baseline row variance. -/
theorem pointwise_response (β : ℝ) (hβ : 0 ≤ β) (q u : Slice n) (f : C(Slice n, ℝ)) :
    (rowMean n β hβ f u-rowMean n β hβ f (q*u))^2 ≤
      coefficient n β q*rowVariance n β hβ f u*rowEntropy n β hβ u (q*u) := by
  have hr (v : Slice n) : rawTransition n β hβ (q*u) v ≤
      Real.exp (4*β*length n q)*rawTransition n β hβ u v := by
    simpa only [rotation_cost] using row_geometric n β hβ (q*u) u v
  have h := CompactEntropyMoment.response_sq_le_entropy_moment (WilsonSlabOperator.measure n)
    (rawTransition n β hβ u) (rawTransition n β hβ (q*u)) f
    (row_continuous n β hβ u) (row_continuous n β hβ (q*u)) f.continuous
    (rawTransition_pos n β hβ u) (rawTransition_pos n β hβ (q*u))
    (rawTransition_mass n β hβ u) (rawTransition_mass n β hβ (q*u))
    (Real.exp (4*β*length n q)) (rowMean n β hβ f u) (Real.exp_pos _).le hr
  have hv : (∫ v, rawTransition n β hβ u v*(f v-rowMean n β hβ f u)^2
      ∂WilsonSlabOperator.measure n) = rowVariance n β hβ f u := by
    rw [rowVariance, ProbabilityTheory.variance_eq_integral f.continuous.measurable.aemeasurable]
    exact (rowLaw_integral n β hβ u _).symm
  rw [hv, ← rowMean_eq_raw, ← rowMean_eq_raw] at h
  exact h

/-- Actual variance loss replaces squared range; the profile energy remains explicit. -/
theorem response_with_remainder (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (f : C(Slice n, ℝ)) :
    sourceEnergy n β hβ q (step n β hβ f) +
      coefficient n β q*amplitudeEnergy n β hβ q (profile n β hβ f) ≤
      coefficient n β q*(18*β*WilsonJointRotation.cost n q*loss n β hβ f +
        (sourceEnergy n β hβ q (profile n β hβ f)+
          sourceEnergy n β hβ q⁻¹ (profile n β hβ f))/2) := by
  letI := groundLaw_probability n β hβ
  have hP := rowMean_continuous n β hβ f
  have hE : Continuous (fun u => (profile n β hβ f u)^2*rowEntropy n β hβ u (q*u)) :=
    ((profile n β hβ f).continuous.pow 2).mul ((rowEntropy_continuous n β hβ).comp
      (f := fun u : Slice n => (u,q*u))
      (continuous_id.prodMk (continuous_const.mul continuous_id)))
  have hR : Continuous (fun u => (rowMean n β hβ f (q*u)-rowMean n β hβ f u)^2) :=
    ((hP.comp (f := fun u : Slice n => q*u) (continuous_const.mul continuous_id)).sub hP).pow 2
  have h := integral_mono (continuous_integrable (groundLaw n β hβ) _ hR)
    (continuous_integrable (groundLaw n β hβ) _ (continuous_const.mul hE)) (fun u => by
      have hh := pointwise_response n β hβ q u f
      simp only [Pi.mul_apply, profile_square]
      nlinarith)
  simp only [Pi.mul_apply] at h
  rw [integral_const_mul] at h
  change sourceEnergy n β hβ q (step n β hβ f) ≤
    coefficient n β q*weightedEntropy n β hβ q (profile n β hβ f) at h
  have he := mul_le_mul_of_nonneg_left
    (paired_bound n β hβ q (profile n β hβ f)) (coefficient_nonneg n β q)
  rw [profile_mass] at he
  have hn := mul_nonneg (coefficient_nonneg n β q)
    (weightedEntropy_nonneg n β hβ q⁻¹ (profile n β hβ f))
  nlinarith

/-- The same estimate applies to the original full transfer on physical sources. -/
theorem physical_response_with_remainder (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ u, ((∫ v, transition n β hβ (q*u) v*f v ∂WilsonSlabOperator.measure n) -
      (∫ v, transition n β hβ u v*f v ∂WilsonSlabOperator.measure n))^2
      ∂groundLaw n β hβ) +
      coefficient n β q*amplitudeEnergy n β hβ q (profile n β hβ f) ≤
      coefficient n β q*(18*β*WilsonJointRotation.cost n q*loss n β hβ f +
        (sourceEnergy n β hβ q (profile n β hβ f)+
          sourceEnergy n β hβ q⁻¹ (profile n β hβ f))/2) := by
  simp_rw [← step_full n β hβ f hinv]
  exact response_with_remainder n β hβ q f

/-- Small total displacement keeps this density-comparison prefactor bounded. -/
theorem coefficient_cap (β : ℝ) (q : Slice n) (s : ℝ)
    (hs : β * length n q ≤ s) : coefficient n β q ≤ 2*(1+Real.exp (4*s)) := by
  unfold coefficient
  have h := Real.exp_le_exp.mpr (show 4*β*length n q ≤ 4*s by nlinarith)
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonVarianceProfile
