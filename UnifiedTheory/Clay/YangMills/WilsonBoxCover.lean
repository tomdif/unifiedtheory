/- All translated high-density boxes share one source residual. The remaining
number-of-boxes error has an explicit entropy-versus-energy budget. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutUnion
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutTranslate

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoxCover
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonSpatialCutEnergy
open WilsonSpatialCutUnion WilsonSpatialCutTranslate

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem box_rate (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) (a : SpatialVertex n) :
    rate n β (box n L a) ((L : ℝ) ^ 3) ≤ Real.exp (-β * (L : ℝ) ^ 3/4) := by
  have hb := box_boundary_le n L hL (by omega) a
  have hp := box_bulk_le n L hL a
  have hn := box_card n L hL a
  have h0 : (4096 : ℝ) ≤ L := by exact_mod_cast hlarge
  have he0 : 0 ≤ WilsonGroundSlabEnergy.envelope β := by
    have hl : 0 ≤ Real.log (2*β+5) := Real.log_nonneg (by linarith)
    unfold WilsonGroundSlabEnergy.envelope
    positivity
  have hcount : ((bulk n (box n L a)).card : ℝ)+(box n L a).card ≤ 6*(L : ℝ) ^ 3 := by
    rw [hn]
    have hh : ((bulk n (box n L a)).card : ℝ) ≤ 3*(L : ℝ) ^ 3 := by exact_mod_cast hp
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  have hprice := mul_le_mul_of_nonneg_right hcount he0
  have hbound := mul_le_mul_of_nonneg_left he (show 0 ≤ 24*(L : ℝ) ^ 3 by positivity)
  have hsurface : 8*((boundary n (box n L a)).card : ℝ) ≤ (L : ℝ) ^ 3/2 := by
    have hh := mul_nonneg (show 0 ≤ (L : ℝ)-384 by linarith) (sq_nonneg (L : ℝ))
    nlinarith
  unfold rate
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left
    (show (L : ℝ) ^ 3/4 ≤ (L : ℝ) ^ 3-8*(boundary n (box n L a)).card-
      4 * (((bulk n (box n L a)).card : ℝ)+(box n L a).card) *
        WilsonGroundSlabEnergy.envelope β by nlinarith) hβ.le
  nlinarith

variable {I : Type*} [Fintype I]

/-- Different scales and arbitrary overlapping translations are allowed. -/
theorem family_tail (β : ℝ) (hβ : 0 < β) (L : I → ℕ) (a : I → SpatialVertex n)
    (hL : ∀ i, L i + 1 ≤ n) (hlarge : ∀ i, 4096 ≤ L i)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) (f : C(Slice n, ℝ)) :
    (∫ u, (bad n (fun i => box n (L i) (a i)) (fun i => (L i : ℝ)^3)).indicator
      (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*(∑ i, Real.exp (-β*(L i : ℝ)^3/4))*mass n β hβ.le f := by
  apply (weighted_union n β hβ (fun i => box n (L i) (a i)) (fun i => (L i : ℝ)^3)
    (fun i => by have := hlarge i; positivity) f).trans
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    box_rate n β hβ (L i) (hL i) (hlarge i) he (a i))
  have hh := mul_le_mul_of_nonneg_right hs (mass_nonneg n β hβ.le f)
  linarith

theorem same_scale_tail (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n)
    (hlarge : 4096 ≤ L) (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96)
    (a : I → SpatialVertex n) (f : C(Slice n, ℝ)) :
    (∫ u, (bad n (fun i => box n L (a i)) (fun _ => (L : ℝ) ^ 3)).indicator
      (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+
        2*(Fintype.card I : ℝ)*Real.exp (-β * (L : ℝ) ^ 3/4)*mass n β hβ.le f :=
  weighted_union_rate n β hβ _ _ (fun _ => by positivity) _
    (fun i => box_rate n β hβ L hL hlarge he (a i)) f

def allBad (L : ℕ) : Set (Slice n) := bad n (box n L) (fun _ => (L : ℝ) ^ 3)

/-- The union is over every one of the n^3 periodic translates. -/
theorem all_boxes_tail (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n)
    (hlarge : 4096 ≤ L) (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96)
    (f : C(Slice n, ℝ)) :
    (∫ u, (allBad n L).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*(n : ℝ)^3*Real.exp (-β * (L : ℝ) ^ 3/4)*mass n β hβ.le f := by
  have h := same_scale_tail n β hβ L hL hlarge he (fun a : SpatialVertex n => a) f
  have hc : Fintype.card (SpatialVertex n) = n^3 := by simp [SpatialVertex]
  simpa only [hc, Nat.cast_pow] using h

omit [Fact (1 < n)] in
/-- A growing number of boxes is admissible when its logarithm fits this budget. -/
theorem volume_price (β : ℝ) (L : ℕ) (hv : 3 * Real.log (n : ℝ) ≤ β * (L : ℝ) ^ 3 / 8) :
    (n : ℝ)^3*Real.exp (-β * (L : ℝ) ^ 3/4) ≤ Real.exp (-β * (L : ℝ) ^ 3 / 8) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  calc
    _ = Real.exp (Real.log ((n : ℝ)^3)+ -β * (L : ℝ) ^ 3/4) := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith

theorem all_boxes_volume_tail (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n)
    (hlarge : 4096 ≤ L) (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96)
    (hv : 3 * Real.log (n : ℝ) ≤ β * (L : ℝ) ^ 3 / 8) (f : C(Slice n, ℝ)) :
    (∫ u, (allBad n L).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*Real.exp (-β * (L : ℝ) ^ 3 / 8)*mass n β hβ.le f := by
  have hh := mul_le_mul_of_nonneg_right (volume_price n β L hv) (mass_nonneg n β hβ.le f)
  have ht := all_boxes_tail n β hβ L hL hlarge he f
  linarith

/-- A supported source may spread across all bad boxes. The loss is still
bounded below once the stated finite-volume error is small. -/
theorem union_loss (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n)
    (hlarge : 4096 ≤ L) (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96)
    (hv : 3 * Real.log (n : ℝ) ≤ β * (L : ℝ) ^ 3 / 8) (f : C(Slice n, ℝ))
    (hs : ∀ u, u ∉ allBad n L → f u = 0) :
    (1/2-Real.exp (-β * (L : ℝ) ^ 3 / 8))*mass n β hβ.le f ≤ loss n β hβ.le f := by
  have ht := all_boxes_volume_tail n β hβ L hL hlarge he hv f
  have hi : (∫ u, (allBad n L).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) =
      mass n β hβ.le f := by
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ allBad n L
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, hs u hu, zero_pow (by decide : 2 ≠ 0)]
  rw [hi] at ht
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonBoxCover
