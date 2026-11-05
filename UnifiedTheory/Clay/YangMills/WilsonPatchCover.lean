/- Many simultaneous-defect patterns share one source residual. Their
pattern activities are summed, with no independence or disjointness premise. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail
import UnifiedTheory.Clay.YangMills.WilsonCoverContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchCover
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights
open WilsonPlaquetteColumnTail (rate rate_nonneg)

variable (n : ℕ) [NeZero n] {I : Type*} [Fintype I]

def cover (S : I → Finset (Plaquette n)) (R : I → ℝ) (i : I) : C(Slice (2 * n), ℝ) :=
  CompactCutoffCover.weight (fun j => WilsonPatchSourceTail.cutoff n (S j) (R j)) i

def bad (S : I → Finset (Plaquette n)) (R : I → ℝ) : Set (Slice (2 * n)) :=
  {u | ∃ i, u ∈ WilsonPatchSourceTail.hard n (S i) (R i)}

omit [Fintype I] in
theorem bad_measurable [Finite I] (S : I → Finset (Plaquette n)) (R : I → ℝ) :
    MeasurableSet (bad n S R) := by
  have he : bad n S R = ⋃ i, WilsonPatchSourceTail.hard n (S i) (R i) := by ext u; simp [bad]
  rw [he]
  exact MeasurableSet.iUnion (fun i => WilsonPatchSourceTail.hard_measurable n (S i) (R i))

omit [NeZero n] in
theorem cover_range (S : I → Finset (Plaquette n)) (R : I → ℝ)
    (i : I) (u : Slice (2 * n)) : cover n S R i u ∈ Set.Icc 0 1 :=
  CompactCutoffCover.weight_range _ (fun j => WilsonPatchSourceTail.cutoff_range n (S j) (R j)) i u

omit [NeZero n] in
theorem cover_supported (S : I → Finset (Plaquette n)) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (i : I) (u : Slice (2 * n))
    (hu : ∃ p ∈ S i, SpatialWilsonPlaquetteKernels.defect n p u < R i) : cover n S R i u = 0 :=
  CompactCutoffCover.weight_zero _ i u
    (WilsonPatchSourceTail.cutoff_supported n (S i) (R i) (hR i) u hu)

omit [NeZero n] in
theorem cover_one (S : I → Finset (Plaquette n)) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (u : Slice (2 * n)) (hu : u ∈ bad n S R) : ∑ i, (cover n S R i u) ^ 2 = 1 := by
  obtain ⟨i,hi⟩ := hu
  exact CompactCutoffCover.sum_square_one _ u ⟨i,
    WilsonPatchSourceTail.cutoff_one n (S i) (R i) (hR i) u (fun p hp => hi ⟨p,hp⟩)⟩

theorem joint_output (β : ℝ) (hβ : 3 / 4 ≤ β) (S : I → Finset (Plaquette n))
    (hS : ∀ i, Aligned n (S i)) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (f : C(Slice (2 * n), ℝ)) :
    (∑ i, mass (2 * n) β (by linarith) (cover n S R i * step (2 * n) β (by linarith) f)) ≤
      (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * n) β (by linarith) f := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => WilsonPatchSourceTail.cutoff_output n (S i) (hS i) β hβ
    (R i) (cover n S R i) f (cover_range n S R i) (cover_supported n S R hR i))

/-- The number of patterns enters only the mass error, never the loss coefficient. -/
theorem weighted_union (β : ℝ) (hβ : 3 / 4 ≤ β) (S : I → Finset (Plaquette n))
    (hS : ∀ i, Aligned n (S i)) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (bad n S R).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * n) β (by linarith) f := by
  apply (WilsonCutoffCover.event_le_sum_mass (2 * n) β (by linarith) (cover n S R) _
    (bad_measurable n S R) (cover_one n S R hR) f).trans
  exact WilsonCutoffCover.joint_localization (2 * n) β (by linarith) (cover n S R)
    (CompactCutoffCover.sum_square_le _) (fun i => (rate β (R i)) ^ (S i).card)
    (fun i => pow_nonneg (rate_nonneg β (R i)) _)
    (fun i g => WilsonPatchSourceTail.cutoff_output n (S i) (hS i) β hβ (R i) (cover n S R i) g
      (cover_range n S R i) (cover_supported n S R hR i)) f

theorem union_decay (β : ℝ) (hβ : 3 / 4 ≤ β) (S : I → Finset (Plaquette n))
    (hS : ∀ i, Aligned n (S i)) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (f : C(Slice (2 * n), ℝ)) (hs : ∀ u, u ∉ bad n S R → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * n) β (by linarith) f := by
  apply WilsonCoverContraction.cover_decay (2 * n) β (by linarith) (cover n S R)
    (CompactCutoffCover.sum_square_le _) (fun i => (rate β (R i)) ^ (S i).card)
    (fun i => pow_nonneg (rate_nonneg β (R i)) _) (joint_output n β hβ S hS R hR) f
  ext u
  by_cases hu : u ∈ bad n S R
  · simp only [ContinuousMap.mul_apply, WilsonCoverContraction.total_apply,
      cover_one n S R hR u hu, one_mul]
  · simp only [ContinuousMap.mul_apply, hs u hu, mul_zero]

/-- A same-size family pays exactly its number of candidate patterns times rho^k. -/
theorem same_size_tail (β : ℝ) (hβ : 3 / 4 ≤ β) (S : I → Finset (Plaquette n))
    (hS : ∀ i, Aligned n (S i)) (k : ℕ) (hk : ∀ i, (S i).card = k)
    (R : ℝ) (hR : 0 < R) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (bad n S (fun _ => R)).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (Fintype.card I : ℝ) * (rate β R) ^ k * mass (2 * n) β (by linarith) f := by
  have h := weighted_union n β hβ S hS (fun _ => R) (fun _ => hR) f
  simpa only [hk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h

end
end UnifiedTheory.Clay.YangMills.WilsonPatchCover
