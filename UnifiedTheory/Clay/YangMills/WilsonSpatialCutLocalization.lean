/- Actual arbitrary-source localization in a finite box, with all exterior
variables retained. The small error is paid by L2 mass, not loss alone. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutBox
import UnifiedTheory.Clay.YangMills.WilsonHighFieldReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialCutLocalization
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay CompactDensityEntropy
open WilsonHighFieldReduction (pairing pairing_step pairing_sq mass_step_le
  cutoff_mass_le residual_le_loss)
open WilsonSpatialCutEnergy WilsonSpatialCutBox

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem cutoff_output (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) (χ f : C(Slice n, ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, bulkPotential n (links n L) u < (L : ℝ) ^ 3 → χ u = 0) :
    mass n β hβ.le (χ*step n β hβ.le f) ≤ Real.exp (-β*(L : ℝ) ^ 3/4)*mass n β hβ.le f := by
  let k := χ*step n β hβ.le f
  let h := χ*k
  have hid : pairing n β hβ.le h (step n β hβ.le f) = mass n β hβ.le k := by
    unfold pairing mass
    apply integral_congr_ae
    filter_upwards with u
    simp only [h, k, ContinuousMap.mul_apply]
    ring
  have hc := pairing_sq n β hβ.le (step n β hβ.le h) f
  rw [← pairing_step, hid] at hc
  have hd := box_decay n β hβ L hL hlarge he h (by
    intro u hu
    change χ u*k u = 0
    rw [hs u hu, zero_mul])
  have hh := cutoff_mass_le n β hβ.le χ k hχ
  have hm := mass_nonneg n β hβ.le f
  have he0 := (Real.exp_pos (-β*(L : ℝ) ^ 3/4)).le
  have hb := hc.trans (mul_le_mul_of_nonneg_right
    (hd.trans (mul_le_mul_of_nonneg_left hh he0)) hm)
  have hk := mass_nonneg n β hβ.le k
  by_cases hz : mass n β hβ.le k = 0
  · change mass n β hβ.le k ≤ _
    rw [hz]
    exact mul_nonneg he0 hm
  · have hp : 0 < mass n β hβ.le k := lt_of_le_of_ne hk (Ne.symm hz)
    change mass n β hβ.le k ≤ _
    nlinarith

/-- Slow modes concentrate away from this box high-density region.
The small remainder is paid by mass, not falsely by loss alone. -/
theorem slow_mode_highfield (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) (χ f : C(Slice n, ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, bulkPotential n (links n L) u < (L : ℝ) ^ 3 → χ u = 0) :
    mass n β hβ.le (χ*f) ≤
      2*loss n β hβ.le f+2*Real.exp (-β*(L : ℝ) ^ 3/4)*mass n β hβ.le f := by
  letI := groundLaw_probability n β hβ.le
  let P2 := step n β hβ.le (step n β hβ.le f)
  have hi := integral_mono
    (continuous_integrable (groundLaw n β hβ.le) _ ((χ*f).continuous.pow 2))
    (((continuous_integrable (groundLaw n β hβ.le) _ ((χ*(f-P2)).continuous.pow 2)).const_mul 2).add
      ((continuous_integrable (groundLaw n β hβ.le) _ ((χ*P2).continuous.pow 2)).const_mul 2))
    (fun u => show (χ u*f u)^2 ≤ 2*(χ u*(f u-P2 u))^2+2*(χ u*P2 u)^2 by
      nlinarith [sq_nonneg (χ u*(f u-2*P2 u))])
  simp only [Pi.add_apply] at hi
  rw [integral_add, integral_const_mul, integral_const_mul] at hi
  · change mass n β hβ.le (χ*f) ≤ 2*mass n β hβ.le (χ*(f-P2))+2*mass n β hβ.le (χ*P2) at hi
    have ha := (cutoff_mass_le n β hβ.le χ (f-P2) hχ).trans (residual_le_loss n β hβ.le f)
    have hb := (cutoff_output n β hβ L hL hlarge he χ (step n β hβ.le f) hχ hs).trans
      (mul_le_mul_of_nonneg_left (mass_step_le n β hβ.le f) (Real.exp_pos _).le)
    change mass n β hβ.le (χ*P2) ≤ _ at hb
    linarith
  · exact (continuous_integrable (groundLaw n β hβ.le) _ ((χ*(f-P2)).continuous.pow 2)).const_mul 2
  · exact (continuous_integrable (groundLaw n β hβ.le) _ ((χ*P2).continuous.pow 2)).const_mul 2


def boxPotential (L : ℕ) : C(Slice n, ℝ) :=
  ⟨bulkPotential n (links n L), part_continuous n (bulk n (links n L))⟩

def cutoff (L : ℕ) : C(Slice n, ℝ) :=
  ⟨fun u => min 1 (max 0 ((boxPotential n L u-(L : ℝ) ^ 3)/(L : ℝ) ^ 3)),
    continuous_const.min (continuous_const.max
      (((boxPotential n L).continuous.sub continuous_const).div_const _))⟩

omit [Fact (1 < n)] in
theorem cutoff_range (L : ℕ) (u : Slice n) : cutoff n L u ∈ Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

omit [Fact (1 < n)] in
theorem cutoff_supported (L : ℕ) (hL : 0 < L) (u : Slice n)
    (hu : bulkPotential n (links n L) u < (L : ℝ) ^ 3) : cutoff n L u = 0 := by
  change min 1 (max 0 ((bulkPotential n (links n L) u-(L : ℝ) ^ 3)/(L : ℝ) ^ 3)) = 0
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu.le) (by positivity))]
  norm_num

omit [Fact (1 < n)] in
theorem cutoff_one (L : ℕ) (hL : 0 < L) (u : Slice n)
    (hu : 2 * (L : ℝ) ^ 3 ≤ bulkPotential n (links n L) u) : cutoff n L u = 1 := by
  apply min_eq_left
  apply (le_max_right _ _).trans'
  apply (le_div_iff₀ (show 0 < (L : ℝ) ^ 3 by positivity)).mpr
  change 1*(L : ℝ) ^ 3 ≤ bulkPotential n (links n L) u-(L : ℝ) ^ 3
  linarith

omit [Fact (1 < n)] in
theorem cutoff_physical (L : ℕ) (h : SliceGauge n Q) (u : Slice n) :
    cutoff n L (gaugeSlice h u) = cutoff n L u := by
  change min 1 (max 0 ((partPotential n (bulk n (links n L)) (gaugeSlice h u)-(L : ℝ) ^ 3)/
    (L : ℝ) ^ 3)) = _
  rw [part_gauge]
  rfl

/-- A fully instantiated local source estimate; the ambient period enters only
through the box fit condition. -/
theorem localized_mass (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) (f : C(Slice n, ℝ)) :
    mass n β hβ.le (cutoff n L*f) ≤
      2*loss n β hβ.le f+2*Real.exp (-β*(L : ℝ) ^ 3/4)*mass n β hβ.le f :=
  slow_mode_highfield n β hβ L hL hlarge he (cutoff n L) f
    (cutoff_range n L) (cutoff_supported n L (by omega))

/-- The hard local energy event retains the actual f-squared source weight. -/
theorem weighted_box_tail (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) (f : C(Slice n, ℝ)) :
    (∫ u, {v | 2 * (L : ℝ) ^ 3 ≤ bulkPotential n (links n L) v}.indicator (fun v => (f v)^2) u
      ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*Real.exp (-β*(L : ℝ) ^ 3/4)*mass n β hβ.le f := by
  letI := groundLaw_probability n β hβ.le
  have hE : MeasurableSet {v : Slice n | 2 * (L : ℝ) ^ 3 ≤ bulkPotential n (links n L) v} :=
    measurableSet_le measurable_const (boxPotential n L).continuous.measurable
  have hi := integral_mono
    ((continuous_integrable (groundLaw n β hβ.le) _ (f.continuous.pow 2)).indicator hE)
    (continuous_integrable (groundLaw n β hβ.le) _ ((cutoff n L*f).continuous.pow 2))
    (fun u => show
      {v | 2 * (L : ℝ) ^ 3 ≤ bulkPotential n (links n L) v}.indicator (fun v => (f v)^2) u ≤
        ((cutoff n L*f) u)^2 from by
      by_cases hu : u ∈ {v | 2 * (L : ℝ) ^ 3 ≤ bulkPotential n (links n L) v}
      · rw [Set.indicator_of_mem hu]
        simp only [ContinuousMap.mul_apply, cutoff_one n L (by omega) u hu, one_mul, le_refl]
      · rw [Set.indicator_of_notMem hu]
        exact sq_nonneg _)
  exact hi.trans (localized_mass n β hβ L hL hlarge he f)

theorem cutoff_nonconstant (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L) :
    cutoff n L (1 : Slice n) ≠ cutoff n L (WilsonHighFieldSector.largeField n) := by
  have hf : cutoff n L (1 : Slice n) = 0 := cutoff_supported n L (by omega) _ (by
    rw [flat_bulk]
    positivity)
  have hm : cutoff n L (WilsonHighFieldSector.largeField n) = 1 :=
    cutoff_one n L (by omega) _ (high_box_nonempty n L hL hlarge).le
  rw [hf,hm]
  norm_num

theorem cutoff_mass_positive (β : ℝ) (hβ : 0 ≤ β) (L : ℕ)
    (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L) : 0 < mass n β hβ (cutoff n L) := by
  have h := WilsonEndpointSupport.loss_positive n β hβ (cutoff n L) _ _
    (cutoff_nonconstant n L hL hlarge)
  rw [loss_mass] at h
  have hn := mass_nonneg n β hβ (step n β hβ (cutoff n L))
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialCutLocalization
