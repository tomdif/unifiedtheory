/- Actual physical transfer powers have summable local mean-square response,
paid for by initial stationary variance. A collective coercivity estimate
would give contraction; that additional estimate is not asserted here. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalVariance
import UnifiedTheory.Clay.YangMills.WilsonSlabContraction
import UnifiedTheory.Clay.YangMills.ContinuousBoundaryMoments
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonDissipationIteration
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonPhysicalVariance WilsonVarianceResponse WilsonSymmetricLinkChange
open WilsonPositiveGroundState WilsonSlabContraction ContinuousBoundaryMoments
open scoped Quaternion Topology

variable (n : ℕ) [NeZero n]

def flow (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℕ → C(Slice n, ℝ)
  | 0 => f
  | k+1 => step n β hβ (flow β hβ f k)

theorem flow_gauge (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (k : ℕ) :
    ∀ h u, flow n β hβ f k (gaugeSlice h u) = flow n β hβ f k u := by
  induction k with
  | zero => exact hinv
  | succ k ih => exact step_gauge n β hβ _ ih

theorem flow_succ_full (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (k : ℕ) (u : Slice n) :
    flow n β hβ f (k+1) u =
      ∫ v, transition n β hβ u v * flow n β hβ f k v ∂measure n :=
  step_full n β hβ _ (flow_gauge n β hβ f hinv k) u

theorem weighted_step (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    step n β hβ f * ground n β hβ = (‖transfer n β‖⁻¹ : ℝ) •
      realSmoothing (measure n) (kernelMap n β) (f * ground n β hβ) := by
  ext u
  change step n β hβ f u * ground n β hβ u =
    ‖transfer n β‖⁻¹ * realSmoothing (measure n) (kernelMap n β) (f * ground n β hβ) u
  rw [step_full n β hβ f hinv, realSmoothing_integral,
    ← integral_mul_const, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  unfold transition GroundStateDirichlet.transition
  simp only [ContinuousMap.mul_apply]
  field_simp [(ground_pos n β hβ u).ne',
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1.ne']

/-- One physical step agrees with the original normalized complex Hilbert-space operator. -/
theorem step_embedding (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    embed (measure n) (step n β hβ f * ground n β hβ) =
      normalized n β (embed (measure n) (f * ground n β hβ)) := by
  rw [weighted_step n β hβ f hinv, embed_smul]
  unfold ContinuousBoundaryMoments.embed
  rw [complexify_realSmoothing]
  change ((‖transfer n β‖⁻¹ : ℝ) : ℂ) • transfer n β
    (ContinuousMap.toLp 2 (measure n) ℂ (complexify (f * ground n β hβ))) = _
  simp only [normalized, ContinuousLinearMap.smul_apply]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

/-- No auxiliary clock: these are the already constructed original physical transfer powers. -/
theorem flow_embedding (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (k : ℕ) :
    embed (measure n) (flow n β hβ f k * ground n β hβ) =
      TransferEnergySurvival.iterate (normalized n β) k
        (embed (measure n) (f * ground n β hβ)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change embed (measure n) (step n β hβ (flow n β hβ f k) * ground n β hβ) = _
    rw [step_embedding n β hβ _ (flow_gauge n β hβ f hinv k), ih]
    rfl

theorem variance_flow_le (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (k : ℕ) :
    variance n β hβ (flow n β hβ f k) ≤ variance n β hβ f := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (variance_step_le n β hβ _).trans ih

theorem loss_telescope (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (k : ℕ) :
    (∑ j ∈ Finset.range k, loss n β hβ (flow n β hβ f j)) =
      variance n β hβ f - variance n β hβ (flow n β hβ f k) := by
  induction k with
  | zero => simp [flow]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, loss]
    change _ = variance n β hβ f - variance n β hβ (step n β hβ (flow n β hβ f k))
    ring

/-- Time accumulation is paid for once, by the actual variance lost over the interval. -/
theorem response_sum_le_loss (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) (k : ℕ) :
    (∑ j ∈ Finset.range k, responseEnergy n β hβ e q (flow n β hβ f (j+1))) ≤
      coefficient β q * (variance n β hβ f-variance n β hβ (flow n β hβ f k)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range k, coefficient β q * loss n β hβ (flow n β hβ f j) :=
      Finset.sum_le_sum (fun j _ => response_le_loss n β hβ e q _)
    _ = _ := by rw [← Finset.mul_sum, loss_telescope]

theorem response_sum_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) (k : ℕ) :
    (∑ j ∈ Finset.range k, responseEnergy n β hβ e q (flow n β hβ f (j+1))) ≤
      coefficient β q * variance n β hβ f := by
  have h := response_sum_le_loss n β hβ e q f k
  nlinarith [mul_nonneg (coefficient_nonneg β q)
    (variance_nonneg n β hβ (flow n β hβ f k))]

theorem response_summable (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) :
    Summable (fun j => responseEnergy n β hβ e q (flow n β hβ f (j+1))) :=
  summable_of_sum_range_le (fun j =>
    responseEnergy_nonneg n β hβ e q (flow n β hβ f (j+1)))
    (response_sum_bound n β hβ e q f)

theorem response_tsum_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) :
    (∑' j, responseEnergy n β hβ e q (flow n β hβ f (j+1))) ≤
      coefficient β q * variance n β hβ f :=
  Real.tsum_le_of_sum_range_le (fun j =>
    responseEnergy_nonneg n β hβ e q (flow n β hβ f (j+1)))
    (response_sum_bound n β hβ e q f)

theorem response_tendsto_zero (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) :
    Filter.Tendsto (fun j => responseEnergy n β hβ e q (flow n β hβ f (j+1)))
      Filter.atTop (𝓝 0) := (response_summable n β hβ e q f).tendsto_atTop_zero

theorem response_time_average (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) (k : ℕ) :
    (∑ j ∈ Finset.range k, responseEnergy n β hβ e q (flow n β hβ f (j+1))) / k ≤
      coefficient β q * variance n β hβ f / k :=
  div_le_div_of_nonneg_right (response_sum_bound n β hβ e q f k) (Nat.cast_nonneg k)

omit [NeZero n] in
theorem coefficient_scaled (β : ℝ) (hβ : 0 ≤ β) (q : Q)
    (hscale : β * ‖(q : ℍ) - 1‖ ≤ 1) : coefficient β q ≤ (Real.exp 4-1)^2 := by
  apply (sq_le_sq₀ (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity)))
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num)))).mpr
  apply sub_le_sub_right
  exact Real.exp_le_exp.mpr (by linarith)

/-- Rotations with beta times displacement at most one have a common time-sum coefficient. -/
theorem scaled_response_sum (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (hscale : β * ‖(q : ℍ) - 1‖ ≤ 1)
    (f : C(Slice n, ℝ)) (k : ℕ) :
    (∑ j ∈ Finset.range k, responseEnergy n β hβ e q (flow n β hβ f (j+1))) ≤
      (Real.exp 4-1)^2 * variance n β hβ f :=
  (response_sum_bound n β hβ e q f k).trans (mul_le_mul_of_nonneg_right
    (coefficient_scaled β hβ q hscale) (variance_nonneg n β hβ f))

/-- Conditional payoff: the collective coercivity premise is the remaining analytic input. -/
theorem contraction_of_coercivity {ι : Type*} [Fintype ι]
    (β : ℝ) (hβ : 0 ≤ β) (edges : ι → SpatialVertex n × Fin 3) (rotations : ι → Q)
    (weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i) (f : C(Slice n, ℝ))
    (hcoerce : variance n β hβ (step n β hβ f) ≤
      ∑ i, weights i * responseEnergy n β hβ (edges i) (rotations i) (step n β hβ f)) :
    variance n β hβ (step n β hβ f) ≤
      ((∑ i, weights i * coefficient β (rotations i)) /
        (1+∑ i, weights i * coefficient β (rotations i))) * variance n β hβ f := by
  let B := ∑ i, weights i * coefficient β (rotations i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (coefficient_nonneg β _))
  have hsum : (∑ i, weights i *
      responseEnergy n β hβ (edges i) (rotations i) (step n β hβ f)) ≤ B*loss n β hβ f := by
    calc
      _ ≤ ∑ i, weights i * (coefficient β (rotations i) * loss n β hβ f) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (response_le_loss n β hβ (edges i) (rotations i) f) (hw i))
      _ = _ := by simp_rw [← mul_assoc]; rw [← Finset.sum_mul]
  have h := hcoerce.trans hsum
  change variance n β hβ (step n β hβ f) ≤ B/(1+B)*variance n β hβ f
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1+B)).mpr
  unfold loss at h
  nlinarith

/-- A physical slab may use its whole time-integrated response. The coefficient
has no additional factor equal to the number of transfer steps. The collective
observability premise is an assumption, not a claimed weak-coupling estimate. -/
theorem block_contraction_of_coercivity {ι : Type*} [Fintype ι]
    (β : ℝ) (hβ : 0 ≤ β) (edges : ι → SpatialVertex n × Fin 3) (rotations : ι → Q)
    (weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i) (f : C(Slice n, ℝ)) (k : ℕ)
    (hcoerce : variance n β hβ (flow n β hβ f k) ≤ ∑ i, weights i *
      ∑ j ∈ Finset.range k,
        responseEnergy n β hβ (edges i) (rotations i) (flow n β hβ f (j + 1))) :
    variance n β hβ (flow n β hβ f k) ≤
      ((∑ i, weights i * coefficient β (rotations i)) /
        (1+∑ i, weights i * coefficient β (rotations i))) * variance n β hβ f := by
  let B := ∑ i, weights i * coefficient β (rotations i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (coefficient_nonneg β _))
  have hsum : (∑ i, weights i * ∑ j ∈ Finset.range k,
      responseEnergy n β hβ (edges i) (rotations i) (flow n β hβ f (j+1))) ≤
      B*(variance n β hβ f-variance n β hβ (flow n β hβ f k)) := by
    calc
      _ ≤ ∑ i, weights i * (coefficient β (rotations i) *
          (variance n β hβ f-variance n β hβ (flow n β hβ f k))) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (response_sum_le_loss n β hβ (edges i) (rotations i) f k) (hw i))
      _ = _ := by simp_rw [← mul_assoc]; rw [← Finset.sum_mul]
  have h := hcoerce.trans hsum
  change variance n β hβ (flow n β hβ f k) ≤ B/(1+B)*variance n β hβ f
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1+B)).mpr
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonDissipationIteration
