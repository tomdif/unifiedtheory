/- A local response estimate with actual conditional variance in place of
observable range. The explicit coefficient is not a mixing assumption. -/
import UnifiedTheory.Clay.YangMills.WilsonAveragedResponse
import UnifiedTheory.Clay.YangMills.CompactLikelihoodVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonVarianceResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge
open WilsonTemporalInfluence WilsonPhysicalResponse WilsonRowGeometry
open WilsonSymmetricLinkChange WilsonAveragedResponse WilsonStationaryEntropy
open CompactLikelihoodVariance
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem rowWeight_geometric (β : ℝ) (hβ : 0 ≤ β) (u w v : Slice n) :
    rowWeight n β hβ u v ≤ Real.exp (2*β*inputCost n u w) * rowWeight n β hβ w v := by
  rw [← rowAction_weight, ← rowAction_weight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp (rowAction_difference_bound n β hβ u w v)).2
  linarith

theorem rowPartition_geometric (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) :
    rowPartition n β hβ u ≤ Real.exp (2*β*inputCost n u w) * rowPartition n β hβ w := by
  have h := integral_mono
    (CompactDensityEntropy.continuous_integrable (measure n) _ (rowWeight_continuous n β hβ u))
    ((CompactDensityEntropy.continuous_integrable (measure n) _
      (rowWeight_continuous n β hβ w)).const_mul (Real.exp (2*β*inputCost n u w)))
    (fun v => rowWeight_geometric n β hβ u w v)
  simpa only [integral_const_mul, rowPartition] using h

theorem row_geometric (β : ℝ) (hβ : 0 ≤ β) (u w v : Slice n) :
    rawTransition n β hβ u v ≤
      Real.exp (4*β*inputCost n u w) * rawTransition n β hβ w v := by
  have hw := rowWeight_geometric n β hβ u w v
  have hz := rowPartition_geometric n β hβ w u
  rw [inputCost_symm n w u] at hz
  have hp := mul_le_mul hw hz (rowPartition_pos n β hβ w).le
    (mul_nonneg (Real.exp_pos _).le (rowWeight_pos n β hβ w v).le)
  have he : Real.exp (4*β*inputCost n u w) = Real.exp (2*β*inputCost n u w)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp_rw [rawTransition_quotient]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (rowPartition_pos n β hβ u) (rowPartition_pos n β hβ w)).mpr
  rw [he]
  nlinarith

theorem shift_cost (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    inputCost n (shift n e q u) u = ‖(q : ℍ)-1‖ := by
  rw [inputCost_eq_support n {e} _ u (fun j hj =>
    shift_away n e q u j (by simpa only [Finset.mem_singleton] using hj))]
  simp only [Finset.sum_singleton, shift_at]
  change ‖(q : ℍ)*(u e : ℍ)-(u e : ℍ)‖ = _
  calc
    _ = ‖((q : ℍ)-1)*(u e : ℍ)‖ := by congr 1; noncomm_ring
    _ = _ := by rw [norm_mul, QuaternionSymmetricChange.unit_norm, mul_one]

def coefficient (β : ℝ) (q : Q) : ℝ := (Real.exp (4*β*‖(q : ℍ)-1‖)-1)^2

omit [NeZero n] in
theorem coefficient_nonneg (β : ℝ) (q : Q) : 0 ≤ coefficient β q := sq_nonneg _

def likelihood (β : ℝ) (hβ : 0 ≤ β) (u w v : Slice n) : ℝ :=
  rawTransition n β hβ w v / rawTransition n β hβ u v

theorem likelihood_continuous (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) :
    Continuous (likelihood n β hβ u w) :=
  (row_continuous n β hβ w).div (row_continuous n β hβ u)
    (fun v => (rawTransition_pos n β hβ u v).ne')

theorem likelihood_mean (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) :
    (∫ v, likelihood n β hβ u w v ∂rowLaw n β hβ u) = 1 := by
  rw [rowLaw_integral, ← rawTransition_mass n β hβ w]
  apply integral_congr_ae
  filter_upwards with v
  unfold likelihood
  field_simp [(rawTransition_pos n β hβ u v).ne']

theorem likelihood_reweight (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) (f : C(Slice n, ℝ)) :
    (∫ v, likelihood n β hβ u w v*f v ∂rowLaw n β hβ u) = rowMean n β hβ f w := by
  rw [rowLaw_integral, rowMean_eq_raw]
  apply integral_congr_ae
  filter_upwards with v
  unfold likelihood
  field_simp [(rawTransition_pos n β hβ u v).ne']

theorem likelihood_shift_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u v : Slice n) :
    |likelihood n β hβ u (shift n e q u) v-1| ≤ Real.exp (4*β*‖(q : ℍ)-1‖)-1 := by
  have ha := row_geometric n β hβ (shift n e q u) u v
  have hb := row_geometric n β hβ u (shift n e q u) v
  rw [shift_cost] at ha
  rw [inputCost_symm n u, shift_cost] at hb
  have hr : likelihood n β hβ u (shift n e q u) v ≤ Real.exp (4*β*‖(q : ℍ)-1‖) :=
    (div_le_iff₀ (rawTransition_pos n β hβ u v)).mpr ha
  have hl : 1 ≤ Real.exp (4*β*‖(q : ℍ)-1‖)*likelihood n β hβ u (shift n e q u) v := by
    have h := div_le_div_of_nonneg_right hb (rawTransition_pos n β hβ u v).le
    rw [div_self (rawTransition_pos n β hβ u v).ne', mul_div_assoc] at h
    exact h
  exact ratio_deviation _ _ (Real.one_le_exp_iff.mpr (by positivity)) hr hl

/-- Pointwise response is paid for by the actual conditional variance at the baseline input. -/
theorem response_sq_conditional_variance (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) (f : C(Slice n, ℝ)) :
    (rowMean n β hβ f (shift n e q u)-rowMean n β hβ f u)^2 ≤
      coefficient β q * ProbabilityTheory.variance f (rowLaw n β hβ u) := by
  letI := rowLaw_probability n β hβ u
  have h := response_sq_le_variance (rowLaw n β hβ u)
    (likelihood n β hβ u (shift n e q u)) f
    (likelihood_continuous n β hβ u _) f.continuous (likelihood_mean n β hβ u _)
    (Real.exp (4*β*‖(q : ℍ)-1‖)-1)
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity)))
    (likelihood_shift_bound n β hβ e q u)
  rw [likelihood_reweight] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonVarianceResponse
