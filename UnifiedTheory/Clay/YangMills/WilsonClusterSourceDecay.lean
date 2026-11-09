/- Source-sensitive suppression for every finite plaquette pattern on
period 4*n. All plaquette orientations and arbitrary placements are allowed;
the original full ground law and eigenvalue remain in every estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonClusterNorm
import UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay
noncomputable section
open WilsonSlabOperator
open MeasureTheory WilsonTimeSlab WilsonGroundHeatBath WilsonHighFieldDecay WilsonPhysicalVariance
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights SpatialWilsonPlaquetteKernels
open WilsonGroundSlabEnergy WilsonPlaquetteColumnDecay

def rate (β R : ℝ) : ℝ := Real.exp (-β * (R - 96 * envelope β) / 4)

theorem rate_pos (β R : ℝ) : 0 < rate β R := Real.exp_pos _

theorem rate_le_one (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (hR : 96 * envelope β ≤ R) :
    rate β R ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) (sub_nonneg.mpr hR)) (by norm_num)

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem patchDefect_mono (A C : Finset (Plaquette (2 * n))) (hAC : A ⊆ C)
    (u : Slice (2 * (2 * n))) : patchDefect (2 * n) A u ≤ patchDefect (2 * n) C u := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hAC
  intro p _ _
  exact (WilsonSlabBounds.characterDefect_bounds _).1

theorem covered_decay (S A C : Finset (Plaquette (2 * n))) (hAS : A ⊆ S) (hAC : A ⊆ C)
    (β : ℝ) (hβ : 0 < β)
    (hc : ‖SpatialWilsonColumnTransfer.transfer (2 * n) (omitted (2 * n) C β) β‖ ≤
      Real.exp (48 * β * envelope β * (A.card : ℝ)) *
        ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖)
    (R : ℝ) (f : C(Slice (2 * (2 * n)), ℝ))
    (hs : ∀ u, (∃ p ∈ S, defect (2 * n) p u < R) → f u = 0) :
    mass (2 * (2 * n)) β hβ.le (step (2 * (2 * n)) β hβ.le f) ≤
      Real.exp (-β * (R - 96 * envelope β) * (A.card : ℝ)) *
        mass (2 * (2 * n)) β hβ.le f := by
  have hi := WilsonPatchSourceDecay.input_bound (2 * n) C β hβ.le ((A.card : ℝ) * R) f (by
    intro u hu
    apply hs u
    by_contra! hn
    have ha := WilsonPatchSourceDecay.patchDefect_lower (2 * n) A R u
      (fun p hp => hn p (hAS hp))
    exact (not_lt_of_ge (ha.trans (patchDefect_mono n A C hAC u))) hu)
  have hh := hi.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (norm_nonneg _))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
  simp only [mul_pow, output_norm, source_norm] at hsq
  have he : Real.exp (-β * ((A.card : ℝ) * R) / 2) ^ 2 *
      Real.exp (48 * β * envelope β * (A.card : ℝ)) ^ 2 =
      Real.exp (-β * (R - 96 * envelope β) * (A.card : ℝ)) := by
    rw [pow_two, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hn := (PositiveKernelGroundState.transfer_top_eigenvector
    (2 * (2 * n)) β hβ.le).1
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp
  calc
    _ = ‖WilsonSlabOperator.transfer (2 * (2 * n)) β‖^2 *
        mass (2 * (2 * n)) β hβ.le (step (2 * (2 * n)) β hβ.le f) := by ring
    _ ≤ _ := hsq
    _ = _ := by rw [← he]; ring

/-- Arbitrary noncoplanar patterns have a rate exponential in their full
cardinality, with only the fixed parity-cover loss of four. -/
theorem intersection_decay (S : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hR : 96 * envelope β ≤ R)
    (f : C(Slice (2 * (2 * n)), ℝ))
    (hs : ∀ u, (∃ p ∈ S, defect (2 * n) p u < R) → f u = 0) :
    mass (2 * (2 * n)) β hβ.le (step (2 * (2 * n)) β hβ.le f) ≤
      (rate β R) ^ S.card * mass (2 * (2 * n)) β hβ.le f := by
  obtain ⟨A,C,hAS,hAC,hcard,hc⟩ := WilsonClusterNorm.exists_cover n S β hβ
  apply (covered_decay n S A C hAS hAC β hβ hc R f hs).trans
  apply mul_le_mul_of_nonneg_right _ (mass_nonneg _ _ _ _)
  rw [rate, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hk : (S.card : ℝ) ≤ 4 * (A.card : ℝ) := by exact_mod_cast hcard
  have ht : 0 ≤ β * (R - 96 * envelope β) := mul_nonneg hβ.le (sub_nonneg.mpr hR)
  nlinarith [mul_le_mul_of_nonneg_left hk ht]

theorem intersection_loss (S : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hR : 96 * envelope β ≤ R)
    (f : C(Slice (2 * (2 * n)), ℝ))
    (hs : ∀ u, (∃ p ∈ S, defect (2 * n) p u < R) → f u = 0) :
    (1 - (rate β R) ^ S.card) * mass (2 * (2 * n)) β hβ.le f ≤
      loss (2 * (2 * n)) β hβ.le f := by
  rw [loss_mass]
  have h := intersection_decay n S β hβ R hR f hs
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay
