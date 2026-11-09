/- Quantitative suppression near globally opposite bridge endpoints.
The actual transfer normalization and positive ground amplitudes are kept.
This concerns a particular exceptional region, not its full complement. -/
import UnifiedTheory.Clay.YangMills.WilsonAntipodalBridge
import UnifiedTheory.Clay.YangMills.WilsonJointGroundLipschitz
import UnifiedTheory.Clay.YangMills.WilsonGroundSlabEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAntipodalSuppression
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonMiddleBridge WilsonRowGeometry WilsonTemporalGauge WilsonSingleLinkStaples
open CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- A fixed cap already suffices to control normalization on the exponential
scale needed here. This is uniform in the spatial volume. -/
theorem top_lower (β : ℝ) (hβ : 0 ≤ β) (hlarge : 112 * Real.log 201 ≤ β) :
    Real.exp (-(β / 2 * (Fintype.card (SpatialVertex n × Fin 3) : ℝ))) ≤
      ‖transfer n β‖ := by
  have h := WilsonGroundSlabEnergy.top_cap_lower n β hβ 100 (by norm_num)
  have hm : UnitaryHaarNeighborhood.massLower (Fin 2) 100 =
      Real.exp (-8 * Real.log 201) := by
    rw [show -8 * Real.log (201 : ℝ) = -((8 : ℕ) * Real.log 201) by norm_num,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 201)]
    norm_num [UnitaryHaarNeighborhood.massLower]
  have ht : UnitaryHaarNeighborhood.squaredTolerance (Fin 2) 100 = 98 / 625 := by
    norm_num [UnitaryHaarNeighborhood.squaredTolerance_formula]
  rw [hm, ht, ← Real.exp_nat_mul, ← Real.exp_add] at h
  apply le_trans (Real.exp_le_exp.mpr ?_) h
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  have hs : 0 ≤ (Fintype.card (SpatialVertex n) : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_right hlarge hs
  have hb := mul_nonneg hβ hs
  nlinarith

/-- Total distance to the opposite endpoint, with no division by volume. -/
def oppositeCost (v w : Slice n) : ℝ := inputCost n (-v) w

theorem oppositeCost_nonneg (v w : Slice n) : 0 ≤ oppositeCost n v w :=
  inputCost_nonneg n (-v) w

theorem oppositeCost_symm (v w : Slice n) : oppositeCost n v w = oppositeCost n w v := by
  unfold oppositeCost inputCost
  apply Finset.sum_congr rfl
  intro e _
  change ‖-(v e : ℍ)-(w e : ℍ)‖ = ‖-(w e : ℍ)-(v e : ℍ)‖
  congr 1
  abel

theorem oppositeCost_continuous :
    Continuous (fun z : Slice n × Slice n => oppositeCost n z.1 z.2) := by
  unfold oppositeCost inputCost
  fun_prop

/-- The temporal action is still extensive throughout an opposite-endpoint tube. -/
theorem kinetic_lower (u v w : Slice n) :
    4 * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)-2 * oppositeCost n v w ≤
      kineticAction character 2 u v+kineticAction character 2 u w := by
  have h := (abs_le.mp (kinetic_difference_bound n (-v) w u)).1
  rw [WilsonSlabGauge.kineticAction_symm character character_inverse_re 2 w u,
    WilsonSlabGauge.kineticAction_symm character character_inverse_re 2 (-v) u] at h
  have he := WilsonAntipodalBridge.kinetic_antipodal n u v
  unfold oppositeCost
  linarith

theorem spatialWeight_le_one (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    spatialWeight character β 2 u ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h := (WilsonSlabBounds.potential_bounds n u).1
  change -(β / 2) * potential character 2 u ≤ 0
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) h

theorem middle_mass_upper (β : ℝ) (hβ : 0 ≤ β) (v w : Slice n) :
    mass n β v w ≤ Real.exp (-4 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)+
      2 * β * oppositeCost n v w) := by
  have hv := spatialWeight_le_one n β hβ v
  have hw := spatialWeight_le_one n β hβ w
  have hp := mul_le_mul hv hw (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)
  have he (u : Slice n) : weight n β v w u ≤
      Real.exp (-4 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)+
        2 * β * oppositeCost n v w) := by
    rw [weight_action]
    have ha : -action n β v w u ≤
        -4 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)+2 * β * oppositeCost n v w := by
      have hk := mul_le_mul_of_nonneg_left (kinetic_lower n u v w) hβ
      have hs := mul_nonneg hβ (WilsonSlabBounds.potential_bounds n u).1
      unfold action
      nlinarith
    exact (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans
      (by simpa only [one_mul] using Real.exp_le_exp.mpr ha)
  have hi := integral_mono (continuous_integrable (WilsonSlabOperator.measure n) _
    (weight_continuous n β v w))
    (integrable_const _) he
  simpa only [mass, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

/-- Gauge equivalence of opposite fields permits the local ground comparison. -/
theorem ground_comparison (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n) (v w : Slice n) :
    ground n β hβ w ≤ Real.exp (6 * β * oppositeCost n v w) * ground n β hβ v := by
  let q := w * (-v)⁻¹
  have hq : q * (-v) = w := by simp [q, mul_assoc]
  have hc := WilsonVarianceProfile.rotation_cost n q (-v)
  rw [hq, inputCost_symm] at hc
  have h := WilsonJointGroundLipschitz.ground_comparison n β hβ q (-v)
  rw [hq, ← hc, WilsonAntipodalBridge.physical_antipodal n heven
    (ground n β hβ) (ground_invariant n β hβ)] at h
  exact h

theorem endpoint_upper (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n) (v w : Slice n) :
    endpointWeight n β hβ v w ≤
      Real.exp (-4 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)+
        8 * β * oppositeCost n v w) / ‖transfer n β‖^2 * (ground n β hβ v)^2 := by
  have hg := mul_le_mul_of_nonneg_left (ground_comparison n β hβ heven v w)
    (ground_pos n β hβ v).le
  have hm := middle_mass_upper n β hβ v w
  have h := mul_le_mul (div_le_div_of_nonneg_right hg (sq_nonneg ‖transfer n β‖)) hm
    (mass_pos n β v w).le (div_nonneg (by positivity [ground_pos n β hβ v])
      (sq_nonneg ‖transfer n β‖))
  unfold endpointWeight
  apply h.trans_eq
  conv_rhs =>
    rw [show -4 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)+8 * β * oppositeCost n v w =
      6 * β * oppositeCost n v w+(-4 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)+
        2 * β * oppositeCost n v w) by ring, Real.exp_add]
  ring

/-- For average opposite chord at most 1 / 8, the actual endpoint density is
exponentially small relative to either endpoint's stationary density. -/
theorem endpoint_tube_upper (β : ℝ) (hβ : 0 ≤ β) (hlarge : 112 * Real.log 201 ≤ β)
    (heven : 2 ∣ n) (v w : Slice n)
    (htube : oppositeCost n v w ≤ (Fintype.card (SpatialVertex n × Fin 3) : ℝ) / 8) :
    endpointWeight n β hβ v w ≤
      Real.exp (-2 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)) * (ground n β hβ v)^2 := by
  apply (endpoint_upper n β hβ heven v w).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply (div_le_iff₀ (sq_pos_of_pos
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1)).mpr
  have hl := top_lower n β hβ hlarge
  have hs := pow_le_pow_left₀ (Real.exp_pos _).le hl 2
  have he := mul_le_mul_of_nonneg_left hs
    (Real.exp_pos (-2 * β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ))).le
  apply le_trans _ he
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left htube hβ
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonAntipodalSuppression
