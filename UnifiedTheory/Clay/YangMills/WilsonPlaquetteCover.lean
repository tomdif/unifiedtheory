/- Arbitrary finite families of spatial plaquettes have one joint source
localization estimate. No separation, independence, or density threshold is
used. The finite-family entropy price remains explicit. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteRelocation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteCover
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay SpatialPlaquetteCutGeometry
open SpatialWilsonPlaquetteKernels (defect defect_continuous)
open WilsonPlaquetteColumnTail (cutoff cutoff_range cutoff_supported cutoff_one rate rate_nonneg)

variable (n : ℕ) [NeZero n] {I : Type*} [Fintype I]

def cover (q : I → Plaquette n) (R : I → ℝ) (i : I) : C(Slice (2 * n), ℝ) :=
  CompactCutoffCover.weight (fun j => cutoff n (q j) (R j)) i

def bad (q : I → Plaquette n) (R : I → ℝ) : Set (Slice (2 * n)) :=
  {u | ∃ i, 2 * R i ≤ defect n (q i) u}

omit [Fintype I] in
theorem bad_measurable [Finite I] (q : I → Plaquette n) (R : I → ℝ) :
    MeasurableSet (bad n q R) := by
  have he : bad n q R = ⋃ i, {u | 2 * R i ≤ defect n (q i) u} := by ext u; simp [bad]
  rw [he]
  exact MeasurableSet.iUnion (fun i =>
    measurableSet_le measurable_const (defect_continuous n (q i)).measurable)

omit [NeZero n] in
theorem cover_range (q : I → Plaquette n) (R : I → ℝ) (i : I) (u : Slice (2 * n)) :
    cover n q R i u ∈ Set.Icc 0 1 :=
  CompactCutoffCover.weight_range _ (fun j => cutoff_range n (q j) (R j)) i u

omit [NeZero n] in
theorem cover_supported (q : I → Plaquette n) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (i : I) (u : Slice (2 * n)) (hu : defect n (q i) u < R i) : cover n q R i u = 0 :=
  CompactCutoffCover.weight_zero _ i u (cutoff_supported n (q i) (R i) (hR i) u hu)

omit [NeZero n] in
theorem cover_one (q : I → Plaquette n) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (u : Slice (2 * n)) (hu : u ∈ bad n q R) : ∑ i, (cover n q R i u) ^ 2 = 1 := by
  obtain ⟨i,hi⟩ := hu
  exact CompactCutoffCover.sum_square_one _ u ⟨i,cutoff_one n (q i) (R i) (hR i) u hi⟩

omit [NeZero n] in
theorem defect_gauge (q : Plaquette n) (h : SliceGauge (2 * n) Q) (u : Slice (2 * n)) :
    defect n q (gaugeSlice h u) = defect n q u := by
  have hc := WilsonSingleLinkStaples.character_classFunction
  unfold RegulatedGauge.ClassFunction at hc
  simp only [SpatialWilsonPlaquetteKernels.defect, WilsonSlabGauge.spatialHolonomy_gauge, hc]

omit [NeZero n] in
theorem cutoff_physical (q : Plaquette n) (R : ℝ)
    (h : SliceGauge (2 * n) Q) (u : Slice (2 * n)) :
    cutoff n q R (gaugeSlice h u) = cutoff n q R u := by
  change min 1 (max 0 ((defect n q (gaugeSlice h u) - R) / R)) = _
  rw [defect_gauge]
  rfl

omit [NeZero n] in
theorem cover_physical (q : I → Plaquette n) (R : I → ℝ) (i : I)
    (h : SliceGauge (2 * n) Q) (u : Slice (2 * n)) :
    cover n q R i (gaugeSlice h u) = cover n q R i u :=
  CompactCutoffCover.weight_eq_of_values _ _ _ (fun j => cutoff_physical n (q j) (R j) h u) i

omit [NeZero n] [Fintype I] in
theorem bad_physical (q : I → Plaquette n) (R : I → ℝ)
    (h : SliceGauge (2 * n) Q) (u : Slice (2 * n)) :
    gaugeSlice h u ∈ bad n q R ↔ u ∈ bad n q R := by
  simp only [bad, Set.mem_setOf_eq, defect_gauge]

theorem joint_output (β : ℝ) (hβ : 3 / 4 ≤ β) (q : I → Plaquette n)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice (2 * n), ℝ)) :
    (∑ i, mass (2 * n) β (by linarith) (cover n q R i * step (2 * n) β (by linarith) f)) ≤
      (∑ i, rate β (R i)) * mass (2 * n) β (by linarith) f := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => WilsonPlaquetteRelocation.cutoff_output n (q i) β hβ
    (R i) (cover n q R i) f (cover_range n q R i) (cover_supported n q R hR i))

/-- The union pays the source loss once, including overlapping and repeated plaquettes. -/
theorem weighted_union (β : ℝ) (hβ : 3 / 4 ≤ β) (q : I → Plaquette n)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (bad n q R).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (∑ i, rate β (R i)) * mass (2 * n) β (by linarith) f := by
  apply (WilsonCutoffCover.event_le_sum_mass (2 * n) β (by linarith) (cover n q R) _
    (bad_measurable n q R) (cover_one n q R hR) f).trans
  exact WilsonCutoffCover.joint_localization (2 * n) β (by linarith) (cover n q R)
    (CompactCutoffCover.sum_square_le _) (fun i => rate β (R i)) (fun i => rate_nonneg β (R i))
    (fun i g => WilsonPlaquetteRelocation.cutoff_output n (q i) β hβ (R i) (cover n q R i) g
      (cover_range n q R i) (cover_supported n q R hR i)) f

/-- One application of the actual transition already has small mass in the union. -/
theorem output_tail (β : ℝ) (hβ : 3 / 4 ≤ β) (q : I → Plaquette n)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (bad n q R).indicator (fun v => (step (2 * n) β (by linarith) f v) ^ 2) u
      ∂groundLaw (2 * n) β (by linarith)) ≤
        (∑ i, rate β (R i)) * mass (2 * n) β (by linarith) f :=
  (WilsonCutoffCover.event_le_sum_mass (2 * n) β (by linarith) (cover n q R) _
    (bad_measurable n q R) (cover_one n q R hR) _).trans (joint_output n β hβ q R hR f)

theorem plaquette_card : Fintype.card (Plaquette n) = 3 * (2 * n) ^ 3 := by
  have hp : Fintype.card SpatialPlane = 3 := by decide
  simp only [Plaquette, Fintype.card_prod, hp, SpatialVertex, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]
  omega

def allBad (R : ℝ) : Set (Slice (2 * n)) := bad n (fun q : Plaquette n => q) (fun _ => R)

/-- All translates and all spatial orientations, with the explicit lattice volume price. -/
theorem all_plaquettes_tail (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R)
    (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (allBad n R).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (3 * (2 * n : ℝ) ^ 3) * rate β R * mass (2 * n) β (by linarith) f := by
  have h := weighted_union n β hβ (fun q : Plaquette n => q) (fun _ => R) (fun _ => hR) f
  simpa only [Finset.sum_const, Finset.card_univ, plaquette_card, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using h

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteCover
