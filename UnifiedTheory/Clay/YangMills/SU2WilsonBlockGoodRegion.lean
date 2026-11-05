/- Quantitative source curvature for the actual retained block interaction.
The good-staple hypothesis and its source-dependent stability window are
explicit. Nothing here bounds how frequently the Wilson law enters that region. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonBlockEffectiveAction
import UnifiedTheory.Clay.YangMills.SU2HaarCovariance
import UnifiedTheory.Clay.YangMills.WilsonPhysicalCellWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonBlockGoodRegion
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks
open WilsonSingleLinkStaples SU2WilsonBlockApproximation SU2InducedAction
open SU2WilsonBlockEffectiveAction LocalFields
open Filter Topology
open scoped Quaternion RealInnerProductSpace

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

omit [Fact (1 < n)] in
theorem weightedStaple_norm_le_total (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (b : WilsonBlockMarginal.Outside (G := Q) S)
    (e : {e : Edge (Vertex n) // e ∈ S}) :
    ‖SU2WilsonBlockEffectiveAction.weightedStaple n S f e b‖ ≤ ∑ p, |f p| := by
  apply (exteriorWeightedStaple_norm_le n (edgeCoord n e.val).1
    (edgeCoord n e.val).2 (linkExterior n S e b) f).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _ => abs_nonneg (f p))

/-- The exact block Hessian has an inverse-radius estimate with no volume factor. -/
theorem curvature_good (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β t R : ℝ) (hR : 0 < R)
    (f : PlaquetteIndex n → ℝ) (b : WilsonBlockMarginal.Outside (G := Q) S)
    (hgood : ∀ e : {e : Edge (Vertex n) // e ∈ S}, R ≤
      ‖β • SU2WilsonBlockEffectiveAction.staple n S e b -
        t • SU2WilsonBlockEffectiveAction.weightedStaple n S f e b‖) :
    -(6 / R) * (∑ p, |f p|)^2 ≤
      deriv (fun s => deriv (effectiveAction n S β f b) s) t ∧
      deriv (fun s => deriv (effectiveAction n S β f b) s) t ≤ 0 := by
  refine ⟨?_, (effectiveAction_curvature_bounds n S hS β f b t).2⟩
  rw [effectiveAction_second n S hS]
  let V := fun e : {e : Edge (Vertex n) // e ∈ S} =>
    β • SU2WilsonBlockEffectiveAction.staple n S e b -
      t • SU2WilsonBlockEffectiveAction.weightedStaple n S f e b
  let B := fun e : {e : Edge (Vertex n) // e ∈ S} =>
    SU2WilsonBlockEffectiveAction.weightedStaple n S f e b
  have he (e : {e : Edge (Vertex n) // e ∈ S}) :
      covariance 1 (V e) (B e) (B e) ≤ (3 / (2 * R)) * ‖B e‖^2 := by
    have hn : 0 < ‖V e‖ := hR.trans_le (hgood e)
    have h := SU2HaarCovariance.covariance_le_inverse_tilt 1 (V e) (B e)
      (by norm_num) (norm_pos_iff.mp hn)
    simp only [mul_one] at h
    calc
      _ ≤ 3 * ‖B e‖^2 / (2 * ‖V e‖) := h
      _ ≤ 3 * ‖B e‖^2 / (2 * R) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (hgood e) (by norm_num))
      _ = _ := by ring
  have hs : (∑ e, covariance 1 (V e) (B e) (B e)) ≤
      (3 / (2 * R)) * (∑ p, |f p|)^2 := by
    calc
      _ ≤ ∑ e, (3 / (2 * R)) * ‖B e‖^2 := Finset.sum_le_sum (fun e _ => he e)
      _ = (3 / (2 * R)) * ∑ e, ‖B e‖^2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (weightedStaple_square_budget n S hS f b) (by positivity)
  have h := mul_le_mul_of_nonpos_left hs (by norm_num : (-4 : ℝ) ≤ 0)
  have hid : -4 * ((3 / (2 * R)) * (∑ p, |f p|)^2) =
      -(6 / R) * (∑ p, |f p|)^2 := by field_simp; ring
  rw [hid] at h
  exact h

omit [Fact (1 < n)] in
/-- An explicit real-source window preserves every selected good staple. -/
theorem source_window (S : Finset (Edge (Vertex n))) (β t r₀ : ℝ)
    (hβ : 0 < β) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S)
    (hgood : ∀ e : {e : Edge (Vertex n) // e ∈ S},
      r₀ ≤ ‖SU2WilsonBlockEffectiveAction.staple n S e b‖)
    (hwindow : |t| * (∑ p, |f p|) ≤ β * r₀ / 2)
    (e : {e : Edge (Vertex n) // e ∈ S}) :
    β * r₀ / 2 ≤ ‖β • SU2WilsonBlockEffectiveAction.staple n S e b -
      t • SU2WilsonBlockEffectiveAction.weightedStaple n S f e b‖ := by
  have hB := mul_le_mul_of_nonneg_left (weightedStaple_norm_le_total n S f b e)
    (abs_nonneg t)
  have hA := mul_le_mul_of_nonneg_left (hgood e) hβ.le
  have hnorm := norm_sub_norm_le (β • SU2WilsonBlockEffectiveAction.staple n S e b)
    (t • SU2WilsonBlockEffectiveAction.weightedStaple n S f e b)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hβ] at hnorm
  linarith

theorem curvature_source_window (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β t r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S)
    (hgood : ∀ e : {e : Edge (Vertex n) // e ∈ S},
      r₀ ≤ ‖SU2WilsonBlockEffectiveAction.staple n S e b‖)
    (hwindow : |t| * (∑ p, |f p|) ≤ β * r₀ / 2) :
    -(12 / (β * r₀)) * (∑ p, |f p|)^2 ≤
      deriv (fun s => deriv (effectiveAction n S β f b) s) t ∧
      deriv (fun s => deriv (effectiveAction n S β f b) s) t ≤ 0 := by
  have h := curvature_good n S hS β t (β * r₀ / 2) (by positivity) f b
    (source_window n S β t r₀ hβ f b hgood hwindow)
  have hc : 6 / (β * r₀ / 2) = 12 / (β * r₀) := by field_simp; norm_num
  rw [hc] at h
  exact h

/-- The curvature estimate is attached to the actual physical Schwartz cell weights. -/
theorem physical_curvature_source_window (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (a : ℝ) (plane : Plane)
    (β t r₀ : ℝ) (hβ : 0 < β) (hr₀ : 0 < r₀) (f : TestFunction)
    (b : WilsonBlockMarginal.Outside (G := Q) S)
    (hgood : ∀ e : {e : Edge (Vertex n) // e ∈ S},
      r₀ ≤ ‖SU2WilsonBlockEffectiveAction.staple n S e b‖)
    (hwindow : |t| * (∫ x, ‖f x‖) ≤ β * r₀ / 2) :
    -(12 / (β * r₀)) * (∫ x, ‖f x‖)^2 ≤
      deriv (fun s => deriv (effectiveAction n S β
        (WilsonPhysicalCellWeights.weight n a plane f) b) s) t ∧
      deriv (fun s => deriv (effectiveAction n S β
        (WilsonPhysicalCellWeights.weight n a plane f) b) s) t ≤ 0 := by
  have hw := WilsonPhysicalCellWeights.weight_budget n a plane f
  have h := curvature_source_window n S hS β t r₀ hβ hr₀
    (WilsonPhysicalCellWeights.weight n a plane f) b hgood
    ((mul_le_mul_of_nonneg_left hw (abs_nonneg t)).trans hwindow)
  refine ⟨?_, h.2⟩
  apply le_trans _ h.1
  exact mul_le_mul_of_nonpos_left
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hw 2)
    (neg_nonpos.mpr (by positivity))

omit n [NeZero n] [Fact (1 < n)] in
/-- A logarithmic coupling cannot compensate the fourth power of the cutoff. -/
theorem cutoff_fourth_times_coupling_tendsto {ι : Type*} {l : Filter ι}
    (a β : ι → ℝ) (b : ℝ) (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b)) :
    Tendsto (fun i => a i^4 * β i) l (𝓝 0) := by
  have hl := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 4)).comp ha
  have hl' : Tendsto (fun i => a i^4 * Real.log (a i)⁻¹) l (𝓝 0) := by
    simpa only [Function.comp_apply, Real.log_inv,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      neg_zero, mul_neg, neg_mul, mul_comm] using hl.neg
  have h := hβ.mul hl'
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [(CouplingTrajectoryRobustness.log_inverse_tendsto a ha).eventually_gt_atTop 0]
    with i hi
  calc
    _ = a i^4 * (β i / Real.log (a i)⁻¹ * Real.log (a i)⁻¹) := by ring
    _ = a i^4 * β i := by rw [div_mul_cancel₀ _ hi.ne']

omit n [NeZero n] [Fact (1 < n)] in
/-- With an a^-4 source normalization, the sufficient source-window radius
shrinks to zero. This limits this estimate, not the existence of a field theory. -/
theorem rescaled_source_window_tendsto {ι : Type*} {l : Filter ι}
    (a β : ι → ℝ) (b r₀ M : ℝ) (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b)) :
    Tendsto (fun i => a i^4 * β i * r₀ / (2 * M)) l (𝓝 0) := by
  simpa only [zero_mul, zero_div] using
    ((cutoff_fourth_times_coupling_tendsto a β b ha hβ).mul_const r₀).div_const (2 * M)

end
end UnifiedTheory.Clay.YangMills.SU2WilsonBlockGoodRegion
