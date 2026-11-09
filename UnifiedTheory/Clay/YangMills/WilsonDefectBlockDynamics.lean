/- Quantitative original-transfer control of all fixed-block physical sources,
and the explicit error when a general source is only approximately local.
These estimates cannot be iterated by pretending a transfer step stays local. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalEnergyLoss
import UnifiedTheory.Clay.YangMills.WilsonBlockVarianceRemainder
import UnifiedTheory.Clay.YangMills.WilsonMaskedCoercivityObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonDefectBlockDynamics
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonLocalBlockCoercivity

def price (β : ℝ) (s : ℕ) : ℝ := Real.exp (24*β*(s : ℝ))*(1+Real.exp (12*β*(s : ℝ)))^2

theorem price_pos (β : ℝ) (s : ℕ) : 0 < price β s := by unfold price; positivity

theorem price_le (β : ℝ) (hβ : 0 ≤ β) (s : ℕ) : price β s ≤ 4*Real.exp (48*β*(s : ℝ)) := by
  have he : 1 ≤ Real.exp (12*β*(s : ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hh : (1+Real.exp (12*β*(s : ℝ)))^2 ≤ 4*Real.exp (24*β*(s : ℝ)) := by
    have hr : (Real.exp (12*β*(s : ℝ)))^2 = Real.exp (24*β*(s : ℝ)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hh (Real.exp_pos (24*β*(s : ℝ))).le
  have hr : Real.exp (24*β*(s : ℝ))*(4*Real.exp (24*β*(s : ℝ))) =
      4*Real.exp (48*β*(s : ℝ)) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  exact hp.trans_eq hr

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem local_variance_le_loss (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (hs : Supported n S f)
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    variance n β hβ f ≤ price β S.card*loss n β hβ f :=
  (variance_le_transferEnergy n β hβ S f hs).trans
    (mul_le_mul_of_nonneg_left (WilsonPhysicalEnergyLoss.transferEnergy_le_loss n β hβ f hf)
      (price_pos β S.card).le)

/-- This is one step on a supported input, not a spectral gap on an invariant subspace. -/
theorem local_contraction (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (hs : Supported n S f)
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    variance n β hβ (step n β hβ f) ≤ (1-(price β S.card)⁻¹)*variance n β hβ f := by
  have hh := local_variance_le_loss n β hβ S f hs hf
  have hp := price_pos β S.card
  have hd : variance n β hβ f/price β S.card ≤ loss n β hβ f :=
    (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
  rw [loss] at hd
  rw [sub_mul, one_mul]
  simpa only [div_eq_mul_inv, mul_comm] using (le_sub_iff_add_le.mpr (by linarith :
    variance n β hβ (step n β hβ f)+variance n β hβ f/price β S.card ≤ variance n β hβ f))

theorem approximate_variance_le_loss (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f g : C(Slice n, ℝ)) (hg : Supported n S g)
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    variance n β hβ f ≤ 4*price β S.card*loss n β hβ f+
      (4*Real.exp (24*β*(S.card : ℝ))+2)*mass n β hβ (f-g) := by
  have hh := WilsonBlockVarianceRemainder.approximate_local_coercivity n β hβ S f g hg
  have he := (WilsonHeatBathComparison.heatBathEnergy_le_transferEnergy n β hβ S f).trans
    (mul_le_mul_of_nonneg_left (WilsonPhysicalEnergyLoss.transferEnergy_le_loss n β hβ f hf)
      (sq_nonneg _))
  have hc := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*Real.exp (24*β*(S.card : ℝ)) by positivity)
  unfold price
  nlinarith

/-- A slow source must keep a quantified error from every fixed-block approximation. -/
theorem approximation_error_lower (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f g : C(Slice n, ℝ)) (hg : Supported n S g)
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    (variance n β hβ f-4*price β S.card*loss n β hβ f)/
      (4*Real.exp (24*β*(S.card : ℝ))+2) ≤ mass n β hβ (f-g) := by
  apply (div_le_iff₀ (by positivity : 0 < 4*Real.exp (24*β*(S.card : ℝ))+2)).mpr
  have hh := approximate_variance_le_loss n β hβ S f g hg hf
  nlinarith

def defectBlock : Finset (SpatialVertex n × Fin 3) :=
  WilsonSpatialCutEnergy.support n (WilsonMaskedCoercivityObstruction.base n)

omit [NeZero n] in
theorem defectBlock_card : (defectBlock n).card ≤ 4 := WilsonDefectMask.support_card n _

omit [NeZero n] in
theorem bump_local (t : ℝ) :
    Supported n (defectBlock n) (WilsonSpatialSourceObstruction.bump n t) := by
  intro u v huv
  have he := WilsonSpatialCutEnergy.defect_congr n
    (WilsonMaskedCoercivityObstruction.base n) u v huv
  rw [WilsonMaskedCoercivityObstruction.base_defect,
    WilsonMaskedCoercivityObstruction.base_defect] at he
  change max 0 (WilsonSpatialSourceObstruction.defect n u-t) =
    max 0 (WilsonSpatialSourceObstruction.defect n v-t)
  rw [he]

/-- The same physical witness invisible to masked updates is detected by a full block. -/
theorem bump_variance_le_loss (β : ℝ) (hβ : 0 ≤ β) :
    variance n β hβ (WilsonSpatialSourceObstruction.bump n 1) ≤
      4*Real.exp (192*β)*loss n β hβ (WilsonSpatialSourceObstruction.bump n 1) := by
  have hh := local_variance_le_loss n β hβ (defectBlock n)
    (WilsonSpatialSourceObstruction.bump n 1) (bump_local n 1)
    (WilsonSpatialSourceObstruction.bump_gauge n 1)
  have hc : ((defectBlock n).card : ℝ) ≤ 4 := by exact_mod_cast defectBlock_card n
  have he : price β (defectBlock n).card ≤ 4*Real.exp (192*β) :=
    (price_le β hβ _).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num))
  exact hh.trans (mul_le_mul_of_nonneg_right he (loss_nonneg n β hβ _))

variable [Fact (1 < n)]

theorem bump_heatBath_positive (β : ℝ) (hβ : 0 ≤ β) :
    0 < heatBathEnergy n β hβ (defectBlock n) (WilsonSpatialSourceObstruction.bump n 1) :=
  heatBath_positive n β hβ (defectBlock n) (WilsonSpatialSourceObstruction.bump n 1)
    (bump_local n 1) _ _
    (WilsonSpatialSourceObstruction.bump_nonconstant n 1 (by norm_num) (by norm_num))

end
end UnifiedTheory.Clay.YangMills.WilsonDefectBlockDynamics
