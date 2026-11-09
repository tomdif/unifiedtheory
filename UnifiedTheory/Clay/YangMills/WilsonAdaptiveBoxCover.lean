/- The joint box cover can use a surface-plus-free-energy threshold.
Its energy density vanishes when the box size and coupling both grow. -/
import UnifiedTheory.Clay.YangMills.WilsonBoxCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAdaptiveBoxCover
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonSpatialCutEnergy
open WilsonSpatialCutUnion WilsonSpatialCutTranslate

/-- The threshold pays twice the proved surface and local cap costs. -/
def threshold (β : ℝ) (L : ℕ) : ℝ :=
  384*(L : ℝ)^2+48*(L : ℝ)^3*WilsonGroundSlabEnergy.envelope β

theorem envelope_nonneg (β : ℝ) (hβ : 0 < β) : 0 ≤ WilsonGroundSlabEnergy.envelope β := by
  have hl : 0 ≤ Real.log (2*β+5) := Real.log_nonneg (by linarith)
  unfold WilsonGroundSlabEnergy.envelope
  positivity

theorem threshold_ge_surface (β : ℝ) (hβ : 0 < β) (L : ℕ) :
    384*(L : ℝ)^2 ≤ threshold β L := by
  have he := envelope_nonneg β hβ
  unfold threshold
  exact le_add_of_nonneg_right (by positivity)

theorem threshold_pos (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : 0 < L) : 0 < threshold β L :=
  (by positivity : 0 < 384*(L : ℝ)^2).trans_le (threshold_ge_surface β hβ L)

def hardDensity (β : ℝ) (L : ℕ) : ℝ :=
  768/(L : ℝ)+96*WilsonGroundSlabEnergy.envelope β

theorem threshold_density (β : ℝ) (L : ℕ) (hL : 0 < L) :
    2*threshold β L = hardDensity β L*(L : ℝ)^3 := by
  unfold threshold hardDensity
  field_simp [(show (L : ℝ) ≠ 0 by positivity)]
  ring

/-- This is a density limit, not a claimed continuum field or spectral limit. -/
theorem hardDensity_tendsto {J : Type*} {l : Filter J} (β : J → ℝ) (L : J → ℕ)
    (hβ : Filter.Tendsto β l Filter.atTop)
    (hL : Filter.Tendsto (fun j => (L j : ℝ)) l Filter.atTop) :
    Filter.Tendsto (fun j => hardDensity (β j) (L j)) l (nhds 0) := by
  have ha := (tendsto_inv_atTop_zero.comp hL).const_mul 768
  have hb := (WilsonGroundSlabEnergy.envelope_tendsto.comp hβ).const_mul 96
  simpa only [hardDensity, div_eq_mul_inv, mul_zero, add_zero] using ha.add hb

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem rate_bound (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (a : SpatialVertex n) :
    rate n β (box n L a) (threshold β L) ≤ Real.exp (-192*β*(L : ℝ)^2) := by
  have hb := box_boundary_le n L hL hpos a
  have hp := box_bulk_le n L hL a
  have hn := box_card n L hL a
  have he := envelope_nonneg β hβ
  have hcount : ((bulk n (box n L a)).card : ℝ)+(box n L a).card ≤ 6*(L : ℝ)^3 := by
    rw [hn]
    have hh : ((bulk n (box n L a)).card : ℝ) ≤ 3*(L : ℝ)^3 := by exact_mod_cast hp
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  have hprice := mul_le_mul_of_nonneg_right hcount he
  have hmargin : 192*(L : ℝ)^2 ≤ threshold β L-8*(boundary n (box n L a)).card-
      4 * (((bulk n (box n L a)).card : ℝ)+(box n L a).card) *
        WilsonGroundSlabEnergy.envelope β := by
    unfold threshold
    have hh : 0 ≤ (L : ℝ)^3*WilsonGroundSlabEnergy.envelope β := mul_nonneg (by positivity) he
    nlinarith
  unfold rate
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hmargin hβ.le
  nlinarith

def allBad (β : ℝ) (L : ℕ) : Set (Slice n) := bad n (box n L) (fun _ => threshold β L)

/-- All periodic translates, with one loss charge and the explicit n^3 error. -/
theorem all_boxes_tail (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (f : C(Slice n, ℝ)) :
    (∫ u, (allBad n β L).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*(n : ℝ)^3*Real.exp (-192*β*(L : ℝ)^2)*mass n β hβ.le f := by
  have h := weighted_union_rate n β hβ (box n L) (fun _ => threshold β L)
    (fun _ => threshold_pos β hβ L hpos) _ (rate_bound n β hβ L hL hpos) f
  have hc : Fintype.card (SpatialVertex n) = n^3 := by simp [SpatialVertex]
  simpa only [hc, Nat.cast_pow] using h

omit [Fact (1 < n)] in
theorem volume_price (β : ℝ) (L : ℕ)
    (hv : 3 * Real.log (n : ℝ) ≤ 96 * β * (L : ℝ) ^ 2) :
    (n : ℝ)^3*Real.exp (-192*β*(L : ℝ)^2) ≤ Real.exp (-96 * β * (L : ℝ) ^ 2) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  calc
    _ = Real.exp (Real.log ((n : ℝ)^3)+ -192*β*(L : ℝ)^2) := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith

/-- The volume condition is explicit and is not inferred from a physical trajectory. -/
theorem volume_tail (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L)
    (hv : 3 * Real.log (n : ℝ) ≤ 96 * β * (L : ℝ) ^ 2) (f : C(Slice n, ℝ)) :
    (∫ u, (allBad n β L).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*Real.exp (-96 * β * (L : ℝ) ^ 2)*mass n β hβ.le f := by
  have hh := mul_le_mul_of_nonneg_right (volume_price n β L hv) (mass_nonneg n β hβ.le f)
  have ht := all_boxes_tail n β hβ L hL hpos f
  linarith

omit n [NeZero n] [Fact (1 < n)] in
theorem threshold_le_cube (β : ℝ) (L : ℕ) (hlarge : 4096 ≤ L)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) : threshold β L ≤ (L : ℝ)^3 := by
  have h0 : (4096 : ℝ) ≤ L := by exact_mod_cast hlarge
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 48*(L : ℝ)^3 by positivity)
  have hs := mul_nonneg (show 0 ≤ (L : ℝ)-768 by linarith) (sq_nonneg (L : ℝ))
  unfold threshold
  nlinarith

/-- The adaptive excluded region is nonempty in the stated weak-coupling range. -/
theorem high_box_nonempty (β : ℝ) (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) (a : SpatialVertex n) :
    2*threshold β L < bulkPotential n (box n L a) (WilsonHighFieldSector.largeField n) := by
  have hm := WilsonSpatialCutBox.high_box_nonempty n L hL hlarge
  rw [WilsonSpatialCutBox.maximal_bulk] at hm
  rw [WilsonSpatialCutBox.maximal_bulk, box, bulk_card]
  have ht := threshold_le_cube β L hlarge he
  nlinarith

omit [Fact (1 < n)] in
theorem flat_not_bad (β : ℝ) (hβ : 0 < β) (L : ℕ) (hpos : 0 < L) :
    (1 : Slice n) ∉ allBad n β L := by
  intro h
  obtain ⟨a,ha⟩ := h
  rw [WilsonSpatialCutBox.flat_bulk] at ha
  have ht := threshold_pos β hβ L hpos
  linarith


omit n [NeZero n] [Fact (1 < n)] in
/-- Along an explicitly admissible regulator family, bounded-mass approximate
slow modes concentrate below a vanishing density in every translated box. -/
theorem slow_mode_concentration {J : Type*} {l : Filter J}
    (N : J → ℕ) [∀ j, NeZero (N j)] [∀ j, Fact (1 < N j)]
    (β : J → ℝ) (hβ : ∀ j, 0 < β j) (L : J → ℕ) (hpos : ∀ j, 0 < L j)
    (hfit : ∀ j, L j + 1 ≤ N j)
    (hvolume : ∀ j, 3 * Real.log (N j : ℝ) ≤ 96 * β j * (L j : ℝ) ^ 2)
    (f : ∀ j, C(Slice (N j), ℝ))
    (hmass : ∀ j, mass (N j) (β j) (hβ j).le (f j) ≤ 1)
    (hloss : Filter.Tendsto (fun j => loss (N j) (β j) (hβ j).le (f j)) l (nhds 0))
    (hβgrow : Filter.Tendsto β l Filter.atTop)
    (hLgrow : Filter.Tendsto (fun j => (L j : ℝ)) l Filter.atTop) :
    Filter.Tendsto (fun j => hardDensity (β j) (L j)) l (nhds 0) ∧
      Filter.Tendsto (fun j => ∫ u, (allBad (N j) (β j) (L j)).indicator
        (fun v => (f j v)^2) u ∂groundLaw (N j) (β j) (hβ j).le) l (nhds 0) := by
  refine ⟨hardDensity_tendsto β L hβgrow hLgrow, ?_⟩
  have he := (WilsonHighFieldNormalization.uniform_rate_tendsto 192 (by norm_num)).comp hβgrow
  have ht := (hloss.const_mul 2).add (he.const_mul 2)
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero' _ _ ht
  · exact Filter.Eventually.of_forall (fun j => integral_nonneg (fun u =>
      Set.indicator_nonneg (fun v _ => sq_nonneg (f j v)) u))
  · apply Filter.Eventually.of_forall
    intro j
    have ha := volume_tail (N j) (β j) (hβ j) (L j) (hfit j) (hpos j) (hvolume j) (f j)
    have hL1 : (1 : ℝ) ≤ L j := by exact_mod_cast hpos j
    have hp := mul_nonneg (hβ j).le (show 0 ≤ (L j : ℝ)^2-1 by nlinarith)
    have hx : Real.exp (-96 * β j * (L j : ℝ)^2) ≤ Real.exp (-β j*192/2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hb := mul_le_mul_of_nonneg_left (hmass j)
      (Real.exp_pos (-96 * β j * (L j : ℝ)^2)).le
    change _ ≤ 2*loss (N j) (β j) (hβ j).le (f j)+2*Real.exp (-β j*192/2)
    linarith

end
end UnifiedTheory.Clay.YangMills.WilsonAdaptiveBoxCover
