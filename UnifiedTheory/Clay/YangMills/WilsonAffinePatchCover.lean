/- Patterns in different spatial reflection planes share one source loss.
Each pattern is transported by a constructed symmetry before the common
square partition is normalized. No relation between the planes is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights WilsonRawSymmetry
open WilsonPlaquetteColumnTail (rate rate_nonneg)

variable (n : ℕ) [NeZero n] {I : Type*} [Fintype I]

def seed (T : I → Symmetry (2 * n)) (S : I → Finset (Plaquette n)) (R : I → ℝ)
    (i : I) : C(Slice (2 * n), ℝ) :=
  pull (2 * n) (T i) (WilsonPatchSourceTail.cutoff n (S i) (R i))

def cover (T : I → Symmetry (2 * n)) (S : I → Finset (Plaquette n)) (R : I → ℝ)
    (i : I) : C(Slice (2 * n), ℝ) := CompactCutoffCover.weight (seed n T S R) i

def bad (T : I → Symmetry (2 * n)) (S : I → Finset (Plaquette n)) (R : I → ℝ) :
    Set (Slice (2 * n)) := {u | ∃ i, (T i).map u ∈ WilsonPatchSourceTail.hard n (S i) (R i)}

omit [Fintype I] in
theorem bad_measurable [Finite I] (T : I → Symmetry (2 * n))
    (S : I → Finset (Plaquette n)) (R : I → ℝ) : MeasurableSet (bad n T S R) := by
  have he : bad n T S R = ⋃ i, (T i).map ⁻¹' WilsonPatchSourceTail.hard n (S i) (R i) := by
    ext u
    simp [bad]
  rw [he]
  exact MeasurableSet.iUnion (fun i =>
    (WilsonPatchSourceTail.hard_measurable n (S i) (R i)).preimage (T i).preserving.measurable)

omit [Fintype I] in
theorem seed_range (T : I → Symmetry (2 * n)) (S : I → Finset (Plaquette n)) (R : I → ℝ)
    (i : I) (u : Slice (2 * n)) : seed n T S R i u ∈ Set.Icc 0 1 :=
  WilsonPatchSourceTail.cutoff_range n (S i) (R i) ((T i).map u)

theorem cover_range (T : I → Symmetry (2 * n)) (S : I → Finset (Plaquette n)) (R : I → ℝ)
    (i : I) (u : Slice (2 * n)) : cover n T S R i u ∈ Set.Icc 0 1 :=
  CompactCutoffCover.weight_range _ (seed_range n T S R) i u

theorem cover_supported (T : I → Symmetry (2 * n)) (S : I → Finset (Plaquette n))
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (i : I) (u : Slice (2 * n))
    (hu : ∃ p ∈ S i, SpatialWilsonPlaquetteKernels.defect n p ((T i).map u) < R i) :
    cover n T S R i u = 0 :=
  CompactCutoffCover.weight_zero _ i u
    (WilsonPatchSourceTail.cutoff_supported n (S i) (R i) (hR i) ((T i).map u) hu)

theorem cover_one (T : I → Symmetry (2 * n)) (S : I → Finset (Plaquette n))
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (u : Slice (2 * n)) (hu : u ∈ bad n T S R) :
    ∑ i, (cover n T S R i u) ^ 2 = 1 := by
  obtain ⟨i,hi⟩ := hu
  exact CompactCutoffCover.sum_square_one _ u ⟨i, WilsonPatchSourceTail.cutoff_one n (S i) (R i)
    (hR i) ((T i).map u) (fun p hp => hi ⟨p,hp⟩)⟩

theorem joint_output (β : ℝ) (hβ : 3 / 4 ≤ β) (T : I → Symmetry (2 * n))
    (S : I → Finset (Plaquette n)) (hS : ∀ i, Aligned n (S i))
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice (2 * n), ℝ)) :
    (∑ i, mass (2 * n) β (by linarith) (cover n T S R i * step (2 * n) β (by linarith) f)) ≤
      (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * n) β (by linarith) f := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => WilsonPatchSymmetry.cutoff_output n (T i) (S i) (hS i)
    β hβ (R i) (cover n T S R i) f (cover_range n T S R i) (cover_supported n T S R hR i))

/-- Even patterns in different planes pay the actual loss only once. -/
theorem weighted_union (β : ℝ) (hβ : 3 / 4 ≤ β) (T : I → Symmetry (2 * n))
    (S : I → Finset (Plaquette n)) (hS : ∀ i, Aligned n (S i))
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (bad n T S R).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * n) β (by linarith) f := by
  apply (WilsonCutoffCover.event_le_sum_mass (2 * n) β (by linarith) (cover n T S R) _
    (bad_measurable n T S R) (cover_one n T S R hR) f).trans
  exact WilsonCutoffCover.joint_localization (2 * n) β (by linarith) (cover n T S R)
    (CompactCutoffCover.sum_square_le _) (fun i => (rate β (R i)) ^ (S i).card)
    (fun i => pow_nonneg (rate_nonneg β (R i)) _)
    (fun i g => WilsonPatchSymmetry.cutoff_output n (T i) (S i) (hS i) β hβ (R i)
      (cover n T S R i) g (cover_range n T S R i) (cover_supported n T S R hR i)) f

theorem union_decay (β : ℝ) (hβ : 3 / 4 ≤ β) (T : I → Symmetry (2 * n))
    (S : I → Finset (Plaquette n)) (hS : ∀ i, Aligned n (S i))
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, u ∉ bad n T S R → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (∑ i, (rate β (R i)) ^ (S i).card) * mass (2 * n) β (by linarith) f := by
  apply WilsonCoverContraction.cover_decay (2 * n) β (by linarith) (cover n T S R)
    (CompactCutoffCover.sum_square_le _) (fun i => (rate β (R i)) ^ (S i).card)
    (fun i => pow_nonneg (rate_nonneg β (R i)) _) (joint_output n β hβ T S hS R hR) f
  ext u
  by_cases hu : u ∈ bad n T S R
  · simp only [ContinuousMap.mul_apply, WilsonCoverContraction.total_apply,
      cover_one n T S R hR u hu, one_mul]
  · simp only [ContinuousMap.mul_apply, hs u hu, mul_zero]

end
end UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover
