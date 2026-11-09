/- The exact activity provides enough polynomial decay to retain a small
bad-bridge response even after multiplying by the inverse rotation scale
squared. This remains a fixed-root finite-difference estimate; it supplies
neither infinitesimal derivative control nor the complementary coercivity. -/
import UnifiedTheory.Clay.YangMills.WilsonBridgeResponseTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBridgeScaledResponse
noncomputable section
open WilsonSlabOperator WilsonTimeSlab WilsonBridgeOutputSum WilsonBridgeResponseTail
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonBridgeRotationStability
open WilsonClusterActivity WilsonClusterSourceDecay WilsonConnectedActivity
open SpatialPlaquetteCutGeometry
open scoped Quaternion

/-- This keeps the power 224 present in the already proved exact activity exponent. -/
theorem rate_power (β : ℝ) (hβ : 0 < β) :
    rate β (threshold β) ≤ ((2 * β + 5)^224)⁻¹ := by
  rw [rate_threshold, exponent_threshold β hβ]
  calc
    _ ≤ Real.exp (-(224 * Real.log (2 * β + 5))) := by
      apply Real.exp_le_exp.mpr
      have h : 0 ≤ 37632 / β := by positivity
      rw [neg_div]
      linarith
    _ = _ := by
      rw [Real.exp_neg]
      congr 1
      rw [show (224 : ℝ) = (224 : ℕ) by norm_num, Real.exp_nat_mul,
        Real.exp_log (by linarith : 0 < 2 * β + 5)]

theorem budget_power (β : ℝ) (hβ : 512 ≤ β) (m : ℕ) :
    budget (2 * rate β (threshold β)) m ≤
      (4 / (2 * β + 5)^224) * (1 / 2 : ℝ)^(m - 1) := by
  have hb : 0 < β := by linarith
  apply (WilsonConnectedWeakCoupling.budget_half _
    (mul_nonneg (by norm_num) (rate_pos β _).le)
    (WilsonMarkedClusterActivity.rate_half β hβ) m).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rate_power β hb) (by norm_num : (0 : ℝ) ≤ 4))
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (m - 1))
  convert h using 1
  generalize (2 * β + 5)^224 = D
  ring

/-- The two powers used to normalize the finite rotation do not consume the activity margin. -/
theorem scale_absorption (β : ℝ) (hβ : 0 < β) :
    (36 * β)^2 / (2 * β + 5)^224 ≤ 1296 / (2 * β + 5)^222 := by
  have hx : 0 < 2 * β + 5 := by linarith
  have hb : β^2 ≤ (2 * β + 5)^2 := by nlinarith
  have he : (2 * β + 5)^224 = (2 * β + 5)^2 * (2 * β + 5)^222 := by
    rw [← pow_add]
  rw [he]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hx _) (pow_pos hx _)) (pow_pos hx _)).mpr
  have h36 : (36 * β)^2 ≤ 1296 * (2 * β + 5)^2 := by nlinarith only [hb]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right h36 (pow_nonneg hx.le 222)

variable (n : ℕ) [NeZero n]

theorem slow_response_power (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q)
    (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ (36 * β)⁻¹)
    (f : C(Slice (2 * (2 * n)), ℝ)) (σ : ℝ) (hσ : 1 / 2 ≤ σ ^ 2)
    (heigen : step (2 * (2 * n)) β (by linarith) f = σ • f) :
    response n p m (bufferedThreshold β) β (by linarith) edges rotations f ≤
      (16 * (Real.exp 1 + 1) / (2 * β + 5)^224) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  have hb : 0 < β := by linarith
  have hcount := eigen_sum n p m hm β hb (threshold β) (threshold_margin β hb)
    (threshold_pos β hb) (by nlinarith [WilsonMarkedClusterActivity.rate_half β hβ]) f σ heigen
  have hc := mul_le_mul_of_nonneg_right (budget_power β hβ m)
    (mass_nonneg (2 * (2 * n)) β hb.le f)
  have hl := mul_le_mul_of_nonneg_right hσ
    (weightedCount_nonneg n p m (threshold β) β hb.le f)
  have hsmall : weightedCount n p m (threshold β) β hb.le f ≤
      2 * ((4 / (2 * β + 5)^224) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β hb.le f) := by
    have ha := hl.trans (hcount.trans hc)
    calc
      _ = 2 * ((1 / 2 : ℝ) * weightedCount n p m (threshold β) β hb.le f) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (by norm_num)
  have hr := response_le_count n p m (threshold β) (36 * β)⁻¹ β hb.le
    (by positivity) edges rotations hrot f
  rw [mul_inv_cancel₀ (by positivity : 36 * β ≠ 0)] at hr
  have h := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 2 * (Real.exp 1 + 1))
  apply (hr.trans h).trans_eq
  generalize (2 * β + 5)^224 = D
  ring

/-- At the stated finite rotation scale, the bad-bridge form decays with power 222. -/
theorem scaled_slow_response (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q)
    (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ (36 * β)⁻¹)
    (f : C(Slice (2 * (2 * n)), ℝ)) (σ : ℝ) (hσ : 1 / 2 ≤ σ ^ 2)
    (heigen : step (2 * (2 * n)) β (by linarith) f = σ • f) :
    (36 * β)^2 * response n p m (bufferedThreshold β) β (by linarith) edges rotations f ≤
      (20736 * (Real.exp 1 + 1) / (2 * β + 5)^222) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  have h := mul_le_mul_of_nonneg_left (slow_response_power n p m hm β hβ edges rotations
    hrot f σ hσ heigen) (sq_nonneg (36 * β))
  have hs := mul_le_mul_of_nonneg_right (scale_absorption β (by linarith))
    (show 0 ≤ 16 * (Real.exp 1 + 1) * (1 / 2 : ℝ)^(m - 1) *
      mass (2 * (2 * n)) β (by linarith) f from by
      exact mul_nonneg (by positivity) (mass_nonneg _ _ _ _))
  have he : (36 * β)^2 *
      ((16 * (Real.exp 1 + 1) / (2 * β + 5)^224) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f) =
      ((36 * β)^2 / (2 * β + 5)^224) *
        (16 * (Real.exp 1 + 1) * (1 / 2 : ℝ)^(m - 1) *
          mass (2 * (2 * n)) β (by linarith) f) := by
    generalize (2 * β + 5)^224 = D
    ring
  rw [he] at h
  apply (h.trans hs).trans_eq
  generalize (2 * β + 5)^222 = D
  ring

/-- The scaled tail concerns eigenfunctions of the same full physical transition. -/
theorem physical_scaled_slow_response (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q)
    (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ (36 * β)⁻¹)
    (f : C(Slice (2 * (2 * n)), ℝ)) (σ : ℝ)
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hσ : 1 / 2 ≤ σ ^ 2)
    (heigen : ∀ u, (∫ v, WilsonGroundLocalComparison.transition (2 * (2 * n)) β
      (by linarith) u v * f v ∂WilsonSlabOperator.measure (2 * (2 * n))) = σ * f u) :
    (36 * β)^2 * response n p m (bufferedThreshold β) β (by linarith) edges rotations f ≤
      (20736 * (Real.exp 1 + 1) / (2 * β + 5)^222) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  apply scaled_slow_response n p m hm β hβ edges rotations hrot f σ hσ
  ext u
  rw [step_full _ _ _ f hinv, heigen]
  rfl

end
end UnifiedTheory.Clay.YangMills.WilsonBridgeScaledResponse
