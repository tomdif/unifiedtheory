/- Arbitrary pattern families share one loss charge. The pattern
activity sum is explicit and no spatial independence is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail
import UnifiedTheory.Clay.YangMills.WilsonPatchCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonClusterCover
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay
open SpatialPlaquetteCutGeometry WilsonGroundSlabEnergy WilsonClusterSourceDecay
open WilsonPatchCover (cover bad bad_measurable cover_range cover_supported cover_one)

variable (n : ℕ) [NeZero n] {I : Type*} [Fintype I]

theorem joint_output (β : ℝ) (hβ : 0 < β) (S : I → Finset (Plaquette (2 * n)))
    (R : I → ℝ) (hmargin : ∀ i, 96 * envelope β ≤ R i) (hR : ∀ i, 0 < R i)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∑ i, mass (2 * (2 * n)) β hβ.le (cover (2 * n) S R i *
      step (2 * (2 * n)) β hβ.le f)) ≤
      (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * (2 * n)) β hβ.le f := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => WilsonClusterSourceTail.cutoff_output n (S i) β hβ
    (R i) (hmargin i) (cover (2 * n) S R i) f
    (cover_range (2 * n) S R i) (cover_supported (2 * n) S R hR i))

/-- The number of patterns enters only the mass error, never the loss coefficient. -/
theorem weighted_union (β : ℝ) (hβ : 0 < β) (S : I → Finset (Plaquette (2 * n)))
    (R : I → ℝ) (hmargin : ∀ i, 96 * envelope β ≤ R i) (hR : ∀ i, 0 < R i)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (bad (2 * n) S R).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * loss (2 * (2 * n)) β hβ.le f +
        2 * (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * (2 * n)) β hβ.le f := by
  apply (WilsonCutoffCover.event_le_sum_mass (2 * (2 * n)) β hβ.le (cover (2 * n) S R) _
    (bad_measurable (2 * n) S R) (cover_one (2 * n) S R hR) f).trans
  exact WilsonCutoffCover.joint_localization (2 * (2 * n)) β hβ.le (cover (2 * n) S R)
    (CompactCutoffCover.sum_square_le _) (fun i => (rate β (R i)) ^ (S i).card)
    (fun i => pow_nonneg (rate_pos β (R i)).le _)
    (fun i g => WilsonClusterSourceTail.cutoff_output n (S i) β hβ (R i) (hmargin i)
      (cover (2 * n) S R i) g
      (cover_range (2 * n) S R i) (cover_supported (2 * n) S R hR i)) f

theorem union_decay (β : ℝ) (hβ : 0 < β) (S : I → Finset (Plaquette (2 * n)))
    (R : I → ℝ) (hmargin : ∀ i, 96 * envelope β ≤ R i) (hR : ∀ i, 0 < R i)
    (f : C(Slice (2 * (2 * n)), ℝ)) (hs : ∀ u, u ∉ bad (2 * n) S R → f u = 0) :
    mass (2 * (2 * n)) β hβ.le (step (2 * (2 * n)) β hβ.le f) ≤
      (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * (2 * n)) β hβ.le f := by
  apply WilsonCoverContraction.cover_decay (2 * (2 * n)) β hβ.le (cover (2 * n) S R)
    (CompactCutoffCover.sum_square_le _) (fun i => (rate β (R i)) ^ (S i).card)
    (fun i => pow_nonneg (rate_pos β (R i)).le _) (joint_output n β hβ S R hmargin hR) f
  ext u
  by_cases hu : u ∈ bad (2 * n) S R
  · simp only [ContinuousMap.mul_apply, WilsonCoverContraction.total_apply,
      cover_one (2 * n) S R hR u hu, one_mul]
  · simp only [ContinuousMap.mul_apply, hs u hu, mul_zero]

/-- A same-size family pays exactly its number of candidate patterns times rho^k. -/
theorem same_size_tail (β : ℝ) (hβ : 0 < β) (S : I → Finset (Plaquette (2 * n)))
    (k : ℕ) (hk : ∀ i, (S i).card = k)
    (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R) (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (bad (2 * n) S (fun _ => R)).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * loss (2 * (2 * n)) β hβ.le f +
        2 * (Fintype.card I : ℝ) * (rate β R) ^ k * mass (2 * (2 * n)) β hβ.le f := by
  have h := weighted_union n β hβ S (fun _ => R) (fun _ => hmargin) (fun _ => hR) f
  simpa only [hk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h


end
end UnifiedTheory.Clay.YangMills.WilsonClusterCover
