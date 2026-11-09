/- Quantitative original-action norm price for arbitrary collections of
disjoint six-plaquette cells. The fully disseminated comparison is proved
using the actual kernel bound and the original physical norm lower bound. -/
import UnifiedTheory.Clay.YangMills.WilsonCubeChessboard
import UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds
import UnifiedTheory.Clay.YangMills.WilsonHighFieldNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCubeNormBound
noncomputable section
open WilsonTimeSlab SpatialWilsonPatchWeights SpatialWilsonColumnTransfer
open WilsonCubeCells WilsonCubeChessboard WilsonModifiedNormBounds WilsonGroundSlabEnergy

variable (n : ℕ) [NeZero n]

theorem full_price (β : ℝ) :
    -(8 * envelope β) * (((deleted (2 * n) (fun _ => true)).card : ℝ) * β) =
      -2 * β * WilsonHighFieldNormalization.links (2 * (2 * n)) * envelope β := by
  rw [full_card]
  simp only [WilsonHighFieldNormalization.links, Fintype.card_prod, SpatialVertex,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem full_score_le (β : ℝ) (hβ : 0 < β) :
    score n β β (8 * envelope β) (fun _ => true) ≤
      ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖ := by
  have h := mul_le_mul_of_nonneg_right
    (norm_le_one (2 * n) (omitted (2 * n) (deleted (2 * n) (fun _ => true)) β)
      (omitted_nonneg _ _ β hβ.le) β hβ.le)
    (Real.exp_pos (-(8 * envelope β) * (((deleted (2 * n) (fun _ => true)).card : ℝ) * β))).le
  change score n β β (8 * envelope β) (fun _ => true) ≤ 1 * _ at h
  rw [one_mul, full_price] at h
  exact h.trans (WilsonHighFieldNormalization.top_lower (2 * (2 * n)) β hβ)

theorem empty_score_le (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) :
    score n β β a (fun _ => false) ≤ ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖ := by
  simpa only [score, WilsonFramedDeletion.priced, deleted_false, Finset.card_empty,
    Nat.cast_zero, zero_mul, mul_zero, Real.exp_zero, mul_one, omitted,
    Finset.notMem_empty, if_false] using raw_full_le_original (2 * n) β hβ

/-- All hypotheses of the block theorem have been discharged for this
actual Wilson family, including the fully marked quantitative comparison. -/
theorem score_le_original (β : ℝ) (hβ : 0 < β) (f : SpatialVertex (2 * n) → Bool) :
    score n β β (8 * envelope β) f ≤ ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖ :=
  (binary_bound n β hβ.le β hβ.le (8 * envelope β) f).trans
    (max_le (empty_score_le n β hβ.le _) (full_score_le n β hβ))

theorem deletion_norm (β : ℝ) (hβ : 0 < β) (f : SpatialVertex (2 * n) → Bool) :
    ‖transfer (2 * n) (omitted (2 * n) (deleted (2 * n) f) β) β‖ ≤
      Real.exp (8 * envelope β * (((deleted (2 * n) f).card : ℝ) * β)) *
        ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖ := by
  let t := 8 * envelope β * (((deleted (2 * n) f).card : ℝ) * β)
  have h := score_le_original n β hβ f
  change ‖transfer (2 * n) (omitted (2 * n) (deleted (2 * n) f) β) β‖ *
    Real.exp (-(8 * envelope β) * (((deleted (2 * n) f).card : ℝ) * β)) ≤ _ at h
  have ht : -(8 * envelope β) * (((deleted (2 * n) f).card : ℝ) * β) = -t := by
    dsimp [t]
    ring
  rw [ht] at h
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = (Real.exp t * Real.exp (-t)) *
        ‖transfer (2 * n) (omitted (2 * n) (deleted (2 * n) f) β) β‖ := by rw [he, one_mul]
    _ = Real.exp t * (‖transfer (2 * n) (omitted (2 * n) (deleted (2 * n) f) β) β‖ *
        Real.exp (-t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos t).le

/-- Each marked cell costs exp(48 beta envelope(beta)), independently of
the exterior volume and temporal chain length. -/
theorem cell_norm (β : ℝ) (hβ : 0 < β) (f : SpatialVertex (2 * n) → Bool) :
    ‖transfer (2 * n) (omitted (2 * n) (deleted (2 * n) f) β) β‖ ≤
      Real.exp (48 * β * envelope β * ((marked (2 * n) f).card : ℝ)) *
        ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖ := by
  have h := deletion_norm n β hβ f
  rw [deleted_card, Nat.cast_mul, Nat.cast_ofNat] at h
  have he : 8 * envelope β * (6 * ((marked (2 * n) f).card : ℝ) * β) =
      48 * β * envelope β * ((marked (2 * n) f).card : ℝ) := by ring
  rwa [he] at h

theorem cellSet_norm (β : ℝ) (hβ : 0 < β) (S : Finset (SpatialVertex (2 * n))) :
    ‖transfer (2 * n) (omitted (2 * n) (cellSet (2 * n) S) β) β‖ ≤
      Real.exp (48 * β * envelope β * (S.card : ℝ)) *
        ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖ := by
  simpa only [deleted_label, marked_label] using cell_norm n β hβ (label (2 * n) S)

end
end UnifiedTheory.Clay.YangMills.WilsonCubeNormBound
