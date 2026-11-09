/- Midpoint contraction on an actual normalized Haar chord cap. The cap
boundary stays in the space, and its nonzero normalizer is proved. -/
import UnifiedTheory.Clay.YangMills.QuaternionHaarDoubling

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.QuaternionCapContraction
noncomputable section
open MeasureTheory WilsonSlabOperator QuaternionHaarDoubling QuaternionChordMidpoint
open scoped Quaternion ENNReal

local instance haar_isHaar : (haar : Measure Q).IsHaarMeasure := by
  unfold haar RegulatedGauge.compactHaar
  infer_instance

def cap (b : Q) (ε : ℝ) : Set Q := {q | ‖(q : ℍ) - (b : ℍ)‖ ≤ ε}

theorem cap_closed (b : Q) (ε : ℝ) : IsClosed (cap b ε) :=
  isClosed_le ((continuous_subtype_val.sub continuous_const).norm) continuous_const

abbrev Cap (b : Q) (ε : ℝ) := cap b ε

instance cap_compact (b : Q) (ε : ℝ) : CompactSpace (Cap b ε) :=
  isCompact_iff_compactSpace.mp (cap_closed b ε).isCompact

def raw (b : Q) (ε : ℝ) : Measure (Cap b ε) :=
  haar.comap Subtype.val

instance raw_finite (b : Q) (ε : ℝ) : IsFiniteMeasure (raw b ε) := by
  unfold raw
  infer_instance

theorem raw_mass (b : Q) (ε : ℝ) : raw b ε Set.univ = haar (cap b ε) := by
  rw [raw, (MeasurableEmbedding.subtype_coe (cap_closed b ε).measurableSet).comap_apply]
  simp only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]

theorem raw_pos (b : Q) (ε : ℝ) (hε : 0 < ε) : 0 < raw b ε Set.univ := by
  rw [raw_mass]
  have ho : IsOpen {q : Q | ‖(q : ℍ) - (b : ℍ)‖ < ε} :=
    isOpen_lt ((continuous_subtype_val.sub continuous_const).norm) continuous_const
  have hp := ho.measure_pos (μ := haar) ⟨b, by
    simpa only [Set.mem_setOf_eq, sub_self, norm_zero] using hε⟩
  exact hp.trans_le (measure_mono (fun q hq =>
    show ‖(q : ℍ) - (b : ℍ)‖ ≤ ε from le_of_lt hq))

def measure (b : Q) (ε : ℝ) : Measure (Cap b ε) :=
  (raw b ε Set.univ)⁻¹ • raw b ε

theorem measure_probability (b : Q) (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (measure b ε) := by
  constructor
  rw [measure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (raw_pos b ε hε).ne' (measure_ne_top _ _)

def contract (b : Q) (ε : ℝ) (hε : ε ^ 2 < 2) (z : Cap b ε) (q : Cap b ε) : Cap b ε :=
  ⟨QuaternionChordMidpoint.midpoint z.1 q.1
    (sum_ne_zero z.1 q.1 b ε hε z.2 q.2),
    midpoint_cap z.1 q.1 b ε hε z.2 q.2 _⟩

theorem contract_continuous (b : Q) (ε : ℝ) (hε : ε ^ 2 < 2) (z : Cap b ε) :
    Continuous (contract b ε hε z) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun q : Cap b ε =>
    ‖(z.1 : ℍ) + (q.1 : ℍ)‖⁻¹ • ((z.1 : ℍ) + (q.1 : ℍ)))
  have hc : Continuous (fun q : Cap b ε => (z.1 : ℍ) + (q.1 : ℍ)) :=
    continuous_const.add (continuous_subtype_val.comp continuous_subtype_val)
  exact (hc.norm.inv₀ (fun q => norm_ne_zero_iff.mpr
    (sum_ne_zero z.1 q.1 b ε hε z.2 q.2))).smul hc

theorem fold_contract (b : Q) (ε : ℝ) (hε : ε ^ 2 < 2) (z q : Cap b ε) :
    fold z.1 (contract b ε hε z q).1 = q.1 :=
  fold_midpoint z.1 q.1 (sum_ne_zero z.1 q.1 b ε hε z.2 q.2)

theorem contract_injective (b : Q) (ε : ℝ) (hε : ε ^ 2 < 2) (z : Cap b ε) :
    Function.Injective (contract b ε hε z) := by
  intro x y h
  have hh := congrArg (fun q : Cap b ε => fold z.1 q.1) h
  simp only [fold_contract] at hh
  exact Subtype.ext hh

/-- The actual cap measure pushed through midpoint contraction is at most
81 times itself. The normalizing factor is retained and cancels exactly. -/
theorem raw_map_bound (b : Q) (ε : ℝ) (hε : ε ^ 2 < 2) (z : Cap b ε) :
    (raw b ε).map (contract b ε hε z) ≤ (81 : ℝ≥0∞) • raw b ε := by
  let T := contract b ε hε z
  have hT : MeasurableEmbedding T :=
    ((contract_continuous b ε hε z).isClosedEmbedding
      (contract_injective b ε hε z)).measurableEmbedding
  have hv : MeasurableEmbedding (Subtype.val : Cap b ε → Q) :=
    MeasurableEmbedding.subtype_coe (cap_closed b ε).measurableSet
  apply Measure.le_iff.mpr
  intro s hs
  let A := T ⁻¹' s
  have hA : MeasurableSet A := hT.measurable hs
  let B : Set Q := Subtype.val '' (T '' A)
  have hB : MeasurableSet B := hv.measurableSet_image.mpr (hT.measurableSet_image.mpr hA)
  have he : fold z.1 '' B = Subtype.val '' A := by
    simp only [B, Set.image_image]
    congr 1
    funext q
    exact fold_contract b ε hε z q
  have hb := fold_image_bound z.1 B hB (by rw [he]; exact hv.measurableSet_image.mpr hA)
  rw [he] at hb
  rw [Measure.map_apply hT.measurable hs, Measure.smul_apply, smul_eq_mul]
  change haar.comap Subtype.val A ≤ 81 * haar.comap Subtype.val s
  rw [hv.comap_apply, hv.comap_apply]
  exact hb.trans (mul_le_mul_right
    (measure_mono (Set.image_mono (Set.image_preimage_subset T s))) 81)

theorem measure_map_bound (b : Q) (ε : ℝ) (hε : ε ^ 2 < 2) (z : Cap b ε) :
    (measure b ε).map (contract b ε hε z) ≤ (81 : ℝ≥0∞) • measure b ε := by
  rw [measure, Measure.map_smul]
  calc
    _ ≤ (raw b ε Set.univ)⁻¹ • ((81 : ℝ≥0∞) • raw b ε) :=
      Measure.le_iff.mpr (fun s _ => by
        simp only [Measure.smul_apply, smul_eq_mul]
        exact mul_le_mul_right ((raw_map_bound b ε hε z) s) _)
    _ = _ := by rw [smul_smul, smul_smul]; congr 1; ac_rfl

end
end UnifiedTheory.Clay.YangMills.QuaternionCapContraction
