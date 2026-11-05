/- A proved coarse bound on the variance-profile energy. It is paid for by
actual transfer variance loss, but its coefficient uses total displacement.
This does not supply a volume-uniform collective contraction estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonVarianceProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonVarianceProfileCost
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonTemporalInfluence WilsonAveragedResponse WilsonPhysicalVariance WilsonRowGeometry
open WilsonVarianceProfile WilsonWeightedEntropy CompactDensityEntropy WilsonPhysicalResponse

variable (n : ℕ) [NeZero n]

theorem length_nonneg (q : Slice n) : 0 ≤ length n q :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem length_inv (q : Slice n) : length n q⁻¹ = length n q := by
  calc
    _ = inputCost n (q⁻¹*q) q := (rotation_cost n q⁻¹ q).symm
    _ = inputCost n 1 q := by rw [inv_mul_cancel]
    _ = inputCost n q 1 := inputCost_symm n 1 q
    _ = _ := by simpa only [mul_one] using rotation_cost n q 1

/-- Compare variances using the optimal center in the baseline row. -/
theorem rowVariance_geometric (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (f : C(Slice n, ℝ)) :
    rowVariance n β hβ f w ≤
      Real.exp (4*β*inputCost n w u)*rowVariance n β hβ f u := by
  letI := rowLaw_probability n β hβ w
  let c := rowMean n β hβ f u
  have hc : Continuous (fun v : Slice n => (f v-c)^2) :=
    (f.continuous.sub continuous_const).pow 2
  have hh := CompactEntropyMoment.variance_le_centered_moment
    (rowLaw n β hβ w) f f.continuous c
  rw [rowLaw_integral] at hh
  have hi := integral_mono (continuous_integrable (WilsonSlabOperator.measure n) _
    ((WilsonStationaryEntropy.row_continuous n β hβ w).mul hc))
    (continuous_integrable (WilsonSlabOperator.measure n) _
      (continuous_const.mul ((WilsonStationaryEntropy.row_continuous n β hβ u).mul hc)))
    (fun v => by
      have h := mul_le_mul_of_nonneg_right
        (WilsonVarianceResponse.row_geometric n β hβ w u v) (sq_nonneg (f v-c))
      simp only [Pi.mul_apply]
      nlinarith)
  simp only [Pi.mul_apply] at hi
  rw [integral_const_mul] at hi
  have he : (∫ v, WilsonTemporalGauge.rawTransition n β hβ u v*(f v-c)^2
      ∂WilsonSlabOperator.measure n) = rowVariance n β hβ f u := by
    rw [rowVariance, ProbabilityTheory.variance_eq_integral f.continuous.measurable.aemeasurable]
    exact (rowLaw_integral n β hβ u _).symm
  rw [he] at hi
  exact hh.trans hi

def errorCoefficient (β : ℝ) (q : Slice n) : ℝ :=
  (Real.exp (2*β*length n q)-1)^2

theorem errorCoefficient_nonneg (β : ℝ) (q : Slice n) :
    0 ≤ errorCoefficient n β q := sq_nonneg _

theorem errorCoefficient_inv (β : ℝ) (q : Slice n) :
    errorCoefficient n β q⁻¹ = errorCoefficient n β q := by
  simp only [errorCoefficient, length_inv]

/-- The row standard deviation changes by at most the square-root density ratio. -/
theorem profile_difference (β : ℝ) (hβ : 0 ≤ β) (q u : Slice n)
    (f : C(Slice n, ℝ)) :
    (profile n β hβ f (q*u)-profile n β hβ f u)^2 ≤
      errorCoefficient n β q*rowVariance n β hβ f u := by
  have hp := rowVariance_geometric n β hβ u (q*u) f
  have hm := rowVariance_geometric n β hβ (q*u) u f
  rw [rotation_cost] at hp
  rw [inputCost_symm, rotation_cost] at hm
  have he : Real.exp (2*β*length n q)^2 = Real.exp (4*β*length n q) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hr : 1 ≤ Real.exp (2*β*length n q) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) (length_nonneg n q))
  have h := CompactEntropyMoment.sqrt_gap (rowVariance n β hβ f u)
    (rowVariance n β hβ f (q*u)) (Real.exp (2*β*length n q))
    (rowVariance_nonneg n β hβ f u) (rowVariance_nonneg n β hβ f (q*u)) hr
    (by simpa only [he] using hm) (by simpa only [he] using hp)
  exact h

/-- This energy error is bounded by actual variance loss, with an explicit l1 cost. -/
theorem profile_energy (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (f : C(Slice n, ℝ)) :
    sourceEnergy n β hβ q (profile n β hβ f) ≤
      errorCoefficient n β q*loss n β hβ f := by
  letI := groundLaw_probability n β hβ
  have hc := (profile n β hβ f).continuous
  have hi := integral_mono (continuous_integrable (groundLaw n β hβ) _
    (((hc.comp (f := fun u : Slice n => q*u) (continuous_const.mul continuous_id)).sub hc).pow 2))
    (continuous_integrable (groundLaw n β hβ) _
      (continuous_const.mul (rowVariance_continuous n β hβ f)))
    (fun u => profile_difference n β hβ q u f)
  simp only [Pi.mul_apply] at hi
  rw [integral_const_mul, mean_rowVariance_eq_loss] at hi
  exact hi

/-- The closed coarse estimate retains the amplitude term but loses collective l2 scaling. -/
theorem response_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (f : C(Slice n, ℝ)) :
    sourceEnergy n β hβ q (step n β hβ f) +
      coefficient n β q*amplitudeEnergy n β hβ q (profile n β hβ f) ≤
      coefficient n β q*(18*β*WilsonJointRotation.cost n q+
        errorCoefficient n β q)*loss n β hβ f := by
  have h := response_with_remainder n β hβ q f
  have hp := profile_energy n β hβ q f
  have hm := profile_energy n β hβ q⁻¹ f
  rw [errorCoefficient_inv] at hm
  have he : (sourceEnergy n β hβ q (profile n β hβ f)+
      sourceEnergy n β hβ q⁻¹ (profile n β hβ f))/2 ≤
      errorCoefficient n β q*loss n β hβ f := by linarith
  have hh := mul_le_mul_of_nonneg_left he (coefficient_nonneg n β q)
  nlinarith

/-- The coarse price contains squared total displacement, not only squared l2 displacement. -/
theorem errorCoefficient_lower (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) :
    4*β^2*(length n q)^2 ≤ errorCoefficient n β q := by
  have hx : 0 ≤ 2*β*length n q := mul_nonneg (by positivity) (length_nonneg n q)
  have he := Real.add_one_le_exp (2*β*length n q)
  have h := (sq_le_sq₀ hx (show 0 ≤ Real.exp (2*β*length n q)-1 by linarith)).mpr
    (show 2*β*length n q ≤ Real.exp (2*β*length n q)-1 by linarith)
  unfold errorCoefficient
  nlinarith

/-- Equal rotations exhibit the link-count loss in this coarse proof coefficient. -/
theorem constant_rotation_lower (β : ℝ) (hβ : 0 ≤ β) (a : Q) :
    4*β^2*(Fintype.card (SpatialVertex n × Fin 3) : ℝ)*
      WilsonJointRotation.cost n (fun _ => a) ≤ errorCoefficient n β (fun _ => a) := by
  have he : (length n (fun _ => a))^2 =
      (Fintype.card (SpatialVertex n × Fin 3) : ℝ)*
        WilsonJointRotation.cost n (fun _ => a) := by
    simp only [length, WilsonJointRotation.cost, WilsonJointRotation.displacement,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have h := errorCoefficient_lower n β hβ (fun _ => a)
  rw [he] at h
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonVarianceProfileCost
