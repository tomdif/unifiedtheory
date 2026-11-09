/- Actual transfer norm comparison for a cover of a fixed fraction of any
marked plaquette pattern, with no alignment or exterior-volume hypothesis. -/
import UnifiedTheory.Clay.YangMills.WilsonCubeCover
import UnifiedTheory.Clay.YangMills.WilsonCubeNormBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonClusterNorm
noncomputable section
open WilsonTimeSlab SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights
open SpatialWilsonColumnTransfer WilsonGroundSlabEnergy WilsonCubeCover

theorem envelope_nonneg (β : ℝ) (hβ : 0 < β) : 0 ≤ envelope β := by
  unfold envelope
  exact add_nonneg (by positivity)
    (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))

variable (n : ℕ) [NeZero n]

theorem cover_norm (S : Finset (Plaquette (2 * n))) (b : WilsonCubeCells.Offsets)
    (β : ℝ) (hβ : 0 < β) :
    ‖transfer (2 * n) (omitted (2 * n) (cover (2 * n) S b) β) β‖ ≤
      Real.exp (48 * β * envelope β * ((retained (2 * n) S b).card : ℝ)) *
        ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖ := by
  rw [cover, WilsonProfileNormTransport.norm_pushSet _ _ _ _ _ hβ.le]
  apply (WilsonCubeNormBound.cellSet_norm n β hβ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast cells_card (2 * n) S b)
    (mul_nonneg (by positivity) (envelope_nonneg β hβ))

/-- The selected subset A contains at least one quarter of the marked
plaquettes. Its cover C has a proved norm price per selected plaquette. -/
theorem exists_cover (S : Finset (Plaquette (2 * n))) (β : ℝ) (hβ : 0 < β) :
    ∃ A C : Finset (Plaquette (2 * n)), A ⊆ S ∧ A ⊆ C ∧ S.card ≤ 4 * A.card ∧
      ‖transfer (2 * n) (omitted (2 * n) C β) β‖ ≤
        Real.exp (48 * β * envelope β * (A.card : ℝ)) *
          ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖ := by
  obtain ⟨b,hb⟩ := retained_quarter (2 * n) S
  exact ⟨retained (2 * n) S b,cover (2 * n) S b,retained_subset (2 * n) S b,
    retained_cover (2 * n) S b,hb,cover_norm n S b β hβ⟩

end
end UnifiedTheory.Clay.YangMills.WilsonClusterNorm
