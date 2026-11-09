/- A maximally defective single plaquette survives every positive-size
adaptive box cutoff. A nonconstant physical source can live entirely there. -/
import UnifiedTheory.Clay.YangMills.WilsonDefectMask
import UnifiedTheory.Clay.YangMills.WilsonAdaptiveBoxCover
import UnifiedTheory.Clay.YangMills.WilsonSpatialSourceObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSparseRetainedWitness
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonGroundVarianceBudget WilsonSpatialCutEnergy
open WilsonPhysicalVariance WilsonHighFieldDecay
open WilsonSingleLinkStaples (character character_re character_classFunction)
open scoped Quaternion

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def field : Slice n := singleLink n 0 0 (-1)

omit [Fact (1 < n)] in
theorem flat_energy : potential character 2 (1 : Slice n) = 0 := by
  simp [potential, spatialHolonomy, character_re]

omit [Fact (1 < n)] in
theorem field_energy : potential character 2 (field n) ≤ 16 := by
  have h := WilsonSlabLocalComparison.potential_oscillation n Q character 2 (by norm_num)
    WilsonGroundLocalComparison.character_bound 2 0 0 (field n) 1 (by
      intro e he
      simp only [field, singleLink, Function.update_of_ne he])
  rw [flat_energy, sub_zero] at h
  simpa only [show (8 : ℝ)*2 = 16 by norm_num] using (abs_le.mp h).2

omit [NeZero n] in
theorem field_defect : WilsonSpatialSourceObstruction.defect n (field n) = 4 := by
  rw [field, WilsonSpatialSourceObstruction.defect_single]
  norm_num [character_re, Unitary.coe_neg]

omit [Fact (1 < n)] in
theorem field_retained (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : 0 < L) :
    field n ∉ WilsonAdaptiveBoxCover.allBad n β L := by
  intro h
  obtain ⟨a,ha⟩ := h
  have hv := (WilsonDefectMask.bulk_le_total n
    (WilsonSpatialCutTranslate.box n L a) (field n)).trans (field_energy n)
  have ht := WilsonAdaptiveBoxCover.threshold_ge_surface β hβ L
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith

omit [NeZero n] in
theorem field_not_flat (L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (h2 : δ < 2) :
    ¬WilsonAxialRegularity.FlatBox n (field n) (L + 1) δ := by
  apply WilsonSpatialSourceObstruction.bad_outside_flat n L δ hδ
  change δ^2 < WilsonSpatialSourceObstruction.defect n (field n)
  rw [field_defect]
  nlinarith

def source : C(Slice n, ℝ) :=
  WilsonSpatialSourceObstruction.bump n 1 *
    ⟨fun u => max 0 (32-WilsonHighFieldSector.potentialMap n u),
      continuous_const.max (continuous_const.sub (WilsonHighFieldSector.potentialMap n).continuous)⟩

omit [Fact (1 < n)] in
theorem source_gauge (h : SliceGauge n Q) (u : Slice n) :
    source n (gaugeSlice h u) = source n u := by
  change WilsonSpatialSourceObstruction.bump n 1 (gaugeSlice h u)*
    max 0 (32-potential character 2 (gaugeSlice h u)) = _
  rw [WilsonSpatialSourceObstruction.bump_gauge,
    WilsonSlabGauge.potential_gauge character character_classFunction]
  rfl

omit [Fact (1 < n)] in
theorem source_flat : source n (1 : Slice n) = 0 := by
  change max 0 (WilsonSpatialSourceObstruction.defect n (1 : Slice n)-1)*_ = 0
  have hd : WilsonSpatialSourceObstruction.defect n (1 : Slice n) = 0 := by
    simp [WilsonSpatialSourceObstruction.defect, WilsonPlaquetteTransport.plaquette,
      spatialHolonomy, character_re]
  rw [hd]
  norm_num

theorem source_field : 48 ≤ source n (field n) := by
  change max 0 (WilsonSpatialSourceObstruction.defect n (field n)-1)*
    max 0 (32-potential character 2 (field n)) ≥ 48
  rw [field_defect]
  norm_num only [show (4 : ℝ)-1 = 3 by norm_num, max_eq_right (by norm_num : (0:ℝ) ≤ 3)]
  have he := field_energy n
  have hm := le_max_right 0 (32-potential character 2 (field n))
  nlinarith

theorem source_nonconstant : source n (1 : Slice n) ≠ source n (field n) := by
  rw [source_flat]
  have h := source_field n
  linarith

omit [Fact (1 < n)] in
/-- The source is supported in the retained region for every admissible scale. -/
theorem source_retained (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : 0 < L) (u : Slice n)
    (hu : u ∈ WilsonAdaptiveBoxCover.allBad n β L) : source n u = 0 := by
  obtain ⟨a,ha⟩ := hu
  have hv := WilsonDefectMask.bulk_le_total n (WilsonSpatialCutTranslate.box n L a) u
  have ht := WilsonAdaptiveBoxCover.threshold_ge_surface β hβ L
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have he : 32-potential character 2 u ≤ 0 := by nlinarith
  change _*max 0 (32-potential character 2 u) = 0
  rw [max_eq_left he, mul_zero]

theorem source_variance_positive (β : ℝ) (hβ : 0 ≤ β) :
    0 < variance n β hβ (source n) :=
  WilsonGroundVarianceBudget.variance_positive n β hβ (source n) _ _ (source_nonconstant n)

theorem source_loss_positive (β : ℝ) (hβ : 0 ≤ β) : 0 < loss n β hβ (source n) :=
  WilsonEndpointSupport.loss_positive n β hβ (source n) _ _ (source_nonconstant n)

end
end UnifiedTheory.Clay.YangMills.WilsonSparseRetainedWitness
