/- The joint high-defect estimates act on nonzero physical sources. An
explicit large field maximizes every marked plaquette, and a continuous
gauge-invariant product bump is supported in the simultaneous hard event. -/
import UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchWitness
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonPhysicalVariance WilsonHighFieldDecay
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights
open SpatialWilsonPlaquetteKernels (defect defect_continuous)

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem defect_large (p : Plaquette n) :
    defect n p (WilsonHighFieldSector.largeField (2 * n)) = 4 := by
  rw [SpatialWilsonPlaquetteKernels.defect, WilsonHighFieldSector.large_holonomy]
  norm_num [WilsonSingleLinkStaples.character_re, Unitary.coe_neg]

omit [NeZero n] in
theorem defect_flat (p : Plaquette n) : defect n p (1 : Slice (2 * n)) = 0 := by
  simp [SpatialWilsonPlaquetteKernels.defect, spatialHolonomy, WilsonSingleLinkStaples.character_re]

def factor (p : Plaquette n) (R : ℝ) : C(Slice (2 * n), ℝ) :=
  ⟨fun u => max 0 (defect n p u - 2 * R),
    continuous_const.max ((defect_continuous n p).sub continuous_const)⟩

def bump (S : Finset (Plaquette n)) (R : ℝ) : C(Slice (2 * n), ℝ) := ∏ p ∈ S, factor n p R

omit [NeZero n] in
theorem bump_large (S : Finset (Plaquette n)) (R : ℝ) (hR : R < 2) :
    bump n S R (WilsonHighFieldSector.largeField (2 * n)) = (4 - 2 * R) ^ S.card := by
  have he (p : Plaquette n) : factor n p R (WilsonHighFieldSector.largeField (2 * n)) =
      4 - 2 * R := by
    change max 0 (defect n p (WilsonHighFieldSector.largeField (2 * n)) - 2 * R) = _
    rw [defect_large, max_eq_right (by linarith)]
  simp only [bump, ContinuousMap.prod_apply, he, Finset.prod_const]

omit [NeZero n] in
theorem bump_flat (S : Finset (Plaquette n)) (hS : S.Nonempty) (R : ℝ) (hR : 0 < R) :
    bump n S R (1 : Slice (2 * n)) = 0 := by
  obtain ⟨p,hp⟩ := hS
  simp only [bump, ContinuousMap.prod_apply]
  apply Finset.prod_eq_zero hp
  change max 0 (defect n p (1 : Slice (2 * n)) - 2 * R) = 0
  rw [defect_flat]
  exact max_eq_left (by linarith)

omit [NeZero n] in
theorem bump_supported (S : Finset (Plaquette n)) (R : ℝ) (u : Slice (2 * n))
    (hu : u ∉ WilsonPatchSourceTail.hard n S R) : bump n S R u = 0 := by
  change ¬ ∀ p : S, 2 * R ≤ defect n p.val u at hu
  push_neg at hu
  obtain ⟨p,hp⟩ := hu
  simp only [bump, ContinuousMap.prod_apply]
  apply Finset.prod_eq_zero p.property
  exact max_eq_left (sub_nonpos.mpr hp.le)

omit [NeZero n] in
theorem bump_physical (S : Finset (Plaquette n)) (R : ℝ)
    (h : SliceGauge (2 * n) Q) (u : Slice (2 * n)) :
    bump n S R (gaugeSlice h u) = bump n S R u := by
  simp only [bump, ContinuousMap.prod_apply, factor, ContinuousMap.coe_mk,
    WilsonPlaquetteCover.defect_gauge]

theorem bump_mass_positive (S : Finset (Plaquette n)) (hS : S.Nonempty)
    (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (hR : 0 < R) (hR2 : R < 2) :
    0 < mass (2 * n) β hβ (bump n S R) := by
  have hn : bump n S R (1 : Slice (2 * n)) ≠
      bump n S R (WilsonHighFieldSector.largeField (2 * n)) := by
    rw [bump_flat n S hS R hR, bump_large n S R hR2]
    exact (pow_pos (by linarith : 0 < 4 - 2 * R) _).ne
  have hl := WilsonEndpointSupport.loss_positive (2 * n) β hβ (bump n S R) _ _ hn
  rw [loss_mass] at hl
  have hpos := mass_nonneg (2 * n) β hβ (step (2 * n) β hβ (bump n S R))
  linarith

/-- An explicit physical source obeys the joint-pattern lower bound. -/
theorem bump_coercivity (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) :
    (1 - (WilsonPlaquetteColumnTail.rate β R) ^ S.card) *
      mass (2 * n) β (by linarith) (bump n S R) ≤ loss (2 * n) β (by linarith) (bump n S R) := by
  apply WilsonPatchSourceDecay.intersection_loss n S hS β hβ R (bump n S R)
  intro u hu
  obtain ⟨p,hp,hu⟩ := hu
  apply bump_supported n S R u
  intro hh
  have hge := hh ⟨p,hp⟩
  linarith

omit [NeZero n] in
theorem large_field_event (A : Finset (Plaquette n)) (R : ℝ) (hR : R ≤ 2)
    (k : ℕ) (hk : k ≤ A.card) :
    WilsonHighFieldSector.largeField (2 * n) ∈ WilsonPatchCountTail.event n A R k := by
  classical
  have he : WilsonPatchCountTail.large n A R (WilsonHighFieldSector.largeField (2 * n)) = A := by
    apply Finset.filter_eq_self.mpr
    intro p _
    rw [defect_large]
    linarith
  change k ≤ (WilsonPatchCountTail.large n A R (WilsonHighFieldSector.largeField (2 * n))).card
  rwa [he]

omit [NeZero n] in
theorem flat_not_event (A : Finset (Plaquette n)) (R : ℝ) (hR : 0 < R) (k : ℕ) (hk : 0 < k) :
    (1 : Slice (2 * n)) ∉ WilsonPatchCountTail.event n A R k := by
  classical
  have he : WilsonPatchCountTail.large n A R (1 : Slice (2 * n)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p _
    rw [defect_flat]
    linarith
  change ¬ k ≤ (WilsonPatchCountTail.large n A R (1 : Slice (2 * n))).card
  rw [he, Finset.card_empty]
  omega

end
end UnifiedTheory.Clay.YangMills.WilsonPatchWitness
