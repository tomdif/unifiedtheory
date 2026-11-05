/- Retained boxes have a vanishing fraction of removed spatial directions.
The event that any box violates this budget has the actual source-tail bound. -/
import UnifiedTheory.Clay.YangMills.WilsonMaskedCurvature
import UnifiedTheory.Clay.YangMills.WilsonAdaptiveBoxCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoxDefectBudget
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonSpatialCutEnergy WilsonSpatialCutTranslate WilsonDefectMask
open WilsonPhysicalVariance WilsonHighFieldDecay CompactDensityEntropy
open scoped Quaternion

def fraction (β : ℝ) (L : ℕ) (δ : ℝ) : ℝ :=
  4*WilsonAdaptiveBoxCover.hardDensity β L/(3*δ^2)+32/(L : ℝ)

theorem fraction_tendsto {J : Type*} {l : Filter J} (β : J → ℝ) (L : J → ℕ) (δ : ℝ)
    (hβ : Filter.Tendsto β l Filter.atTop)
    (hL : Filter.Tendsto (fun j => (L j : ℝ)) l Filter.atTop) :
    Filter.Tendsto (fun j => fraction (β j) (L j) δ) l (nhds 0) := by
  have ha := ((WilsonAdaptiveBoxCover.hardDensity_tendsto β L hβ hL).const_mul 4).div_const (3*δ^2)
  have hb := (tendsto_inv_atTop_zero.comp hL).const_mul 32
  simpa only [fraction, div_eq_mul_inv, mul_zero, zero_mul, add_zero] using ha.add hb

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem removed_fraction (β : ℝ) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (δ : ℝ) (hδ : 0 < δ) (u : Slice n)
    (hu : u ∉ WilsonAdaptiveBoxCover.allBad n β L) (a : SpatialVertex n) :
    ((removed n (box n L a) δ u).card : ℝ) ≤ fraction β L δ*(box n L a).card := by
  have hV : bulkPotential n (box n L a) u < 2*WilsonAdaptiveBoxCover.threshold β L := by
    by_contra h
    exact hu ⟨a,le_of_not_gt h⟩
  rw [WilsonAdaptiveBoxCover.threshold_density β L hpos] at hV
  have hr := removed_budget n (box n L a) δ u
  have hb := box_boundary_le n L hL hpos a
  have hbs := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*δ^2 by positivity)
  have hcost : δ^2*((removed n (box n L a) δ u).card : ℝ) ≤
      4*WilsonAdaptiveBoxCover.hardDensity β L*(L : ℝ)^3+96*δ^2*(L : ℝ)^2 := by
    nlinarith
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hδ)).mp
  have he : δ^2*(fraction β L δ*(box n L a).card) =
      4*WilsonAdaptiveBoxCover.hardDensity β L*(L : ℝ)^3+96*δ^2*(L : ℝ)^2 := by
    rw [box_card n L hL a]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    unfold fraction
    field_simp [hδ.ne', (show (L : ℝ) ≠ 0 by positivity)]
    ring
  rw [he]
  exact hcost

theorem good_fraction (β : ℝ) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (δ : ℝ) (hδ : 0 < δ) (u : Slice n)
    (hu : u ∉ WilsonAdaptiveBoxCover.allBad n β L) (a : SpatialVertex n) :
    (1-fraction β L δ)*(box n L a).card ≤ ((good n (box n L a) δ u).card : ℝ) := by
  have hr := removed_fraction n β L hL hpos δ hδ u hu a
  have hc := Finset.card_sdiff_add_card_eq_card (good_subset n (box n L a) δ u)
  have hc' : ((removed n (box n L a) δ u).card : ℝ)+
      (good n (box n L a) δ u).card = (box n L a).card := by exact_mod_cast hc
  nlinarith

theorem good_nonempty (β : ℝ) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (δ : ℝ) (hδ : 0 < δ) (hf : fraction β L δ < 1) (u : Slice n)
    (hu : u ∉ WilsonAdaptiveBoxCover.allBad n β L) (a : SpatialVertex n) :
    (good n (box n L a) δ u).Nonempty := by
  have hg := good_fraction n β L hL hpos δ hδ u hu a
  have hs : (0 : ℝ) < (box n L a).card := by rw [box_card n L hL a]; positivity
  have hc : (0 : ℝ) < (good n (box n L a) δ u).card :=
    (mul_pos (sub_pos.mpr hf) hs).trans_le hg
  exact Finset.card_pos.mp (by exact_mod_cast hc)

/-- The actual event concerns how many link directions the mask removes. -/
def tooFew (β : ℝ) (L : ℕ) (δ : ℝ) : Set (Slice n) :=
  {u | ∃ a : SpatialVertex n, fraction β L δ*(box n L a).card <
    ((removed n (box n L a) δ u).card : ℝ)}

omit [Fact (1 < n)] in
theorem tooFew_measurable (β : ℝ) (L : ℕ) (δ : ℝ) : MeasurableSet (tooFew n β L δ) := by
  have he : tooFew n β L δ = ⋃ a : SpatialVertex n,
      {u : Slice n | fraction β L δ*(box n L a).card <
        ((removed n (box n L a) δ u).card : ℝ)} := by ext u; simp [tooFew]
  rw [he]
  exact MeasurableSet.iUnion (fun a =>
    measurableSet_lt measurable_const (removed_card_measurable n (box n L a) δ))

theorem tooFew_subset (β : ℝ) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (δ : ℝ) (hδ : 0 < δ) : tooFew n β L δ ⊆ WilsonAdaptiveBoxCover.allBad n β L := by
  intro u hu
  by_contra h
  obtain ⟨a,ha⟩ := hu
  exact (not_lt_of_ge (removed_fraction n β L hL hpos δ hδ u h a)) ha

theorem source_le_adaptive (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n)
    (hpos : 0 < L) (δ : ℝ) (hδ : 0 < δ) (f : C(Slice n, ℝ)) :
    (∫ u, (tooFew n β L δ).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      ∫ u, (WilsonAdaptiveBoxCover.allBad n β L).indicator (fun v => (f v)^2) u
        ∂groundLaw n β hβ.le := by
  letI := groundLaw_probability n β hβ.le
  have hi := continuous_integrable (groundLaw n β hβ.le) _ (f.continuous.pow 2)
  apply integral_mono (hi.indicator (tooFew_measurable n β L δ))
    (hi.indicator (WilsonSpatialCutUnion.bad_measurable n _ _))
  intro u
  by_cases hu : u ∈ tooFew n β L δ
  · rw [Set.indicator_of_mem hu]
    exact le_of_eq (Set.indicator_of_mem (tooFew_subset n β L hL hpos δ hδ hu)
      (fun v : Slice n => (f v)^2)).symm
  · rw [Set.indicator_of_notMem hu]
    exact Set.indicator_nonneg (fun v _ => sq_nonneg (f v)) u

theorem source_tail (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (δ : ℝ) (hδ : 0 < δ) (hv : 3 * Real.log (n : ℝ) ≤ 96 * β * (L : ℝ) ^ 2)
    (f : C(Slice n, ℝ)) :
    (∫ u, (tooFew n β L δ).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*Real.exp (-96*β*(L : ℝ)^2)*mass n β hβ.le f :=
  (source_le_adaptive n β hβ L hL hpos δ hδ f).trans
    (WilsonAdaptiveBoxCover.volume_tail n β hβ L hL hpos hv f)

/-- Pointwise curvature on the constructed almost-full spatial mask still
requires temporal pinning on those active links. -/
theorem retained_curvature (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (a : SpatialVertex n) (q v w u : Slice n)
    (hu : u ∉ WilsonAdaptiveBoxCover.allBad n β L)
    (hq : ∀ e, e ∉ good n (box n L a) (1 / 32) u → q e = 1)
    (hv : ∀ e ∈ good n (box n L a) (1 / 32) u, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ 1 / 2)
    (hw : ∀ e ∈ good n (box n L a) (1 / 32) u, ‖(u e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ 1 / 2) :
    (1-fraction β L (1 / 32))*(box n L a).card ≤
        ((good n (box n L a) (1 / 32) u).card : ℝ) ∧
      2*β*WilsonJointRotation.cost n q ≤
        WilsonMiddleBridge.action n β v w (q*u)+WilsonMiddleBridge.action n β v w (q⁻¹*u)-
          2*WilsonMiddleBridge.action n β v w u :=
  ⟨good_fraction n β L hL hpos (1 / 32) (by norm_num) u hu a,
    WilsonMaskedCurvature.good_middle_small n β hβ.le _ q v w u hq hv hw⟩


omit n [NeZero n] [Fact (1 < n)] in
/-- This controls the actual event that any box loses too many spatial
curvature directions, not a product-law replacement for that event. -/
theorem slow_mode_mask_concentration {J : Type*} {l : Filter J}
    (N : J → ℕ) [∀ j, NeZero (N j)] [∀ j, Fact (1 < N j)]
    (β : J → ℝ) (hβ : ∀ j, 0 < β j) (L : J → ℕ) (hpos : ∀ j, 0 < L j)
    (hfit : ∀ j, L j + 1 ≤ N j) (δ : ℝ) (hδ : 0 < δ)
    (hvolume : ∀ j, 3 * Real.log (N j : ℝ) ≤ 96 * β j * (L j : ℝ) ^ 2)
    (f : ∀ j, C(Slice (N j), ℝ))
    (hmass : ∀ j, mass (N j) (β j) (hβ j).le (f j) ≤ 1)
    (hloss : Filter.Tendsto (fun j => loss (N j) (β j) (hβ j).le (f j)) l (nhds 0))
    (hβgrow : Filter.Tendsto β l Filter.atTop)
    (hLgrow : Filter.Tendsto (fun j => (L j : ℝ)) l Filter.atTop) :
    Filter.Tendsto (fun j => fraction (β j) (L j) δ) l (nhds 0) ∧
      Filter.Tendsto (fun j => ∫ u, (tooFew (N j) (β j) (L j) δ).indicator
        (fun v => (f j v)^2) u ∂groundLaw (N j) (β j) (hβ j).le) l (nhds 0) := by
  refine ⟨fraction_tendsto β L δ hβgrow hLgrow, ?_⟩
  have hh := (WilsonAdaptiveBoxCover.slow_mode_concentration N β hβ L hpos hfit hvolume f
    hmass hloss hβgrow hLgrow).2
  apply squeeze_zero' _ _ hh
  · exact Filter.Eventually.of_forall (fun j => integral_nonneg (fun u =>
      Set.indicator_nonneg (fun v _ => sq_nonneg (f j v)) u))
  · exact Filter.Eventually.of_forall (fun j =>
      source_le_adaptive (N j) (β j) (hβ j) (L j) (hfit j) (hpos j) δ hδ (f j))

end
end UnifiedTheory.Clay.YangMills.WilsonBoxDefectBudget
