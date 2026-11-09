/- A reusable finite-range contact estimate with the full periodic tail retained.
The generic kernel hypotheses are checked separately for actual Wilson stages;
this theorem alone does not assert locality of an induced interaction. -/
import UnifiedTheory.Clay.YangMills.WilsonCompactContactSubtraction
import UnifiedTheory.Clay.YangMills.SchwartzWeightedTail
import UnifiedTheory.Clay.YangMills.WilsonContactDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteRangeSchwartzContact
noncomputable section
open MeasureTheory Filter LocalFields
open WilsonNoiseTubeMass WilsonCompactContactSubtraction SchwartzDiagonalTaylor
open scoped Topology

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume).IsAddHaarMeasure
  infer_instance

def cutoff (K : Spacetime × Spacetime → ℝ) (a R c : ℝ) : Spacetime × Spacetime → ℝ :=
  (tube R (c * a)).indicator K

def contact (K : Spacetime × Spacetime → ℝ) (a R c : ℝ)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  ∫ z, (cutoff K a R c z : ℂ) * diagonalJet F 4 z

def mass (B c R : ℝ) : ℝ :=
  B * 128 * Real.pi ^ 2 * c ^ 4 * volume.real (Metric.closedBall (0 : Spacetime) R)

theorem cutoff_integrable (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (hbound : ∀ z, |K z| ≤ B / a ^ 8) : Integrable (cutoff K a R c) :=
  tube_integrable R (c * a) K hK (B / a ^ 8) hbound

theorem cutoff_mul_continuous_integrable (K : Spacetime × Spacetime → ℝ)
    (hK : Measurable K) (a R c B : ℝ) (hbound : ∀ z, |K z| ≤ B / a ^ 8)
    (G : Spacetime × Spacetime → ℂ) (hG : Continuous G) :
    Integrable (fun z => (cutoff K a R c z : ℂ) * G z) := by
  obtain ⟨C, hC⟩ := (tube_compact R (c * a)).exists_bound_of_continuousOn hG.continuousOn
  have hm : Measurable (fun z => (cutoff K a R c z : ℂ) * G z) :=
    (Complex.continuous_ofReal.measurable.comp
      (hK.indicator (tube_measurable R (c * a)))).mul hG.measurable
  apply (((cutoff_integrable K hK a R c B hbound).abs).mul_const C).mono'
    hm.aestronglyMeasurable
  filter_upwards with z
  by_cases hz : z ∈ tube R (c * a)
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC z hz) (abs_nonneg _)
  · simp only [cutoff, Set.indicator_of_notMem hz, Complex.ofReal_zero, zero_mul,
      norm_zero, abs_zero, le_refl]

theorem cutoff_mass_bound (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hbound : ∀ z, |K z| ≤ B / a ^ 8) :
    (∫ z, |cutoff K a R c z|) ≤ mass B c R / a ^ 4 := by
  have h := tube_abs_mass_le R (c * a) K hK (B / a ^ 8) hbound
  change (∫ z, |cutoff K a R c z|) ≤ _ at h
  rw [tube_volume_real R (c * a) (mul_nonneg hc ha.le)] at h
  apply h.trans_eq
  unfold mass
  field_simp [ha.ne']

/-- The generic degree-four local remainder is derived from the actual kernel amplitude. -/
theorem local_bound (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hbound : ∀ z, |K z| ≤ B / a ^ 8)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    ‖(∫ z, (cutoff K a R c z : ℂ) * F z) - contact K a R c F‖ ≤
      (mass B c R * (4 * c) ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 F * a := by
  have hw : Integrable (fun z => ‖(cutoff K a R c z : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (cutoff_integrable K hK a R c B hbound).abs
  have hF : Integrable (fun z => (cutoff K a R c z : ℂ) *
      F ((z.1, z.1) + (0, z.2 - z.1))) := by
    simpa only [diagonal_add] using
      cutoff_mul_continuous_integrable K hK a R c B hbound F F.continuous
  have hJ := cutoff_mul_continuous_integrable K hK a R c B hbound
    (diagonalJet F 4) (diagonalJet_continuous F 4)
  have hd (z : Spacetime × Spacetime) (hz : (cutoff K a R c z : ℂ) ≠ 0) :
      ‖((0, z.2 - z.1) : Spacetime × Spacetime)‖ ≤ (4 * c) * a := by
    have ht : z ∈ tube R (c * a) := by
      by_contra ht
      exact hz (by simp only [cutoff, Set.indicator_of_notMem ht, Complex.ofReal_zero])
    simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), mul_assoc] using ht.2
  have hm : (∫ z, ‖(cutoff K a R c z : ℂ)‖) ≤ mass B c R / a ^ 4 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      cutoff_mass_bound K hK a R c B ha hc hbound
  have h := fourth_order_subtraction_bound volume (fun z => (cutoff K a R c z : ℂ))
    (fun z => (z.1, z.1)) (fun z => (0, z.2 - z.1)) hw F hF hJ
    a (4 * c) (mass B c R) ha (by positivity) hd hm
  simpa only [diagonal_add, contact, diagonalJet] using h

/-- Every periodic alias outside the physical pair ball is retained in this difference. -/
theorem tail_bound (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hbound : ∀ z, |K z| ≤ B / a ^ 8)
    (hlocal : ∀ z, ‖z.1‖ ≤ R → ‖z.2‖ ≤ R → (4 * c) * a < ‖z.1 - z.2‖ → K z = 0)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ) :
    ‖(∫ z, (K z : ℂ) * F z) - (∫ z, (cutoff K a R c z : ℂ) * F z)‖ ≤
      ((B / a ^ 8) / R ^ m) * SchwartzWeightedTail.weightedMoment volume m F := by
  have hi := SchwartzWeightedTail.bounded_mul_integrable volume (fun z => (K z : ℂ))
    (Complex.continuous_ofReal.measurable.comp hK).aestronglyMeasurable
    (B / a ^ 8) (by positivity)
    (fun z => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hbound z) F
  rw [← integral_sub hi (cutoff_mul_continuous_integrable K hK a R c B hbound F F.continuous)]
  have he (z : Spacetime × Spacetime) : (K z : ℂ) * F z -
      (cutoff K a R c z : ℂ) * F z = ((K z - cutoff K a R c z : ℝ) : ℂ) * F z := by
    rw [Complex.ofReal_sub, sub_mul]
  simp_rw [he]
  apply SchwartzWeightedTail.tail_pairing_bound volume
    (fun z => ((K z - cutoff K a R c z : ℝ) : ℂ)) (B / a ^ 8) R m (by positivity) hR
  · intro z
    by_cases hz : z ∈ tube R (c * a)
    · simp only [cutoff, Set.indicator_of_mem hz, sub_self, Complex.ofReal_zero, norm_zero]
      positivity
    · simpa only [cutoff, Set.indicator_of_notMem hz, sub_zero, Complex.norm_real,
        Real.norm_eq_abs] using hbound z
  · intro z hz
    have hxy : ‖z.1‖ ≤ R ∧ ‖z.2‖ ≤ R := max_le_iff.mp hz
    by_cases ht : z ∈ tube R (c * a)
    · simp only [cutoff, Set.indicator_of_mem ht, sub_self, Complex.ofReal_zero]
    · have hd : (4 * c) * a < ‖z.1 - z.2‖ := by
        have hn : ¬ ‖z.2 - z.1‖ ≤ 4 * (c * a) := fun h => ht ⟨hxy.1, h⟩
        simpa only [norm_sub_rev, mul_assoc] using lt_of_not_ge hn
      rw [cutoff, Set.indicator_of_notMem ht, hlocal z hxy.1 hxy.2 hd]
      simp

/-- Both the local error and the full global Schwartz tail have proved constants. -/
theorem subtraction_bound (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (ha : 0 < a) (hR : 0 < R) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hbound : ∀ z, |K z| ≤ B / a ^ 8)
    (hlocal : ∀ z, ‖z.1‖ ≤ R → ‖z.2‖ ≤ R → (4 * c) * a < ‖z.1 - z.2‖ → K z = 0)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ) :
    ‖(∫ z, (K z : ℂ) * F z) - contact K a R c F‖ ≤
      (mass B c R * (4 * c) ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 F * a +
        ((B / a ^ 8) / R ^ m) * SchwartzWeightedTail.weightedMoment volume m F := by
  have hl := local_bound K hK a R c B ha hc hbound F
  have ht := tail_bound K hK a R c B hB hR hbound hlocal F m
  have h := norm_sub_le_norm_sub_add_norm_sub (∫ z, (K z : ℂ) * F z)
    (∫ z, (cutoff K a R c z : ℂ) * F z) (contact K a R c F)
  linarith

theorem mass_scaling (B c R : ℝ) (hR : 0 ≤ R) : mass B c R = mass B c 1 * R ^ 4 := by
  unfold mass
  rw [ball_volume_real (0 : Spacetime) R hR,
    ball_volume_real (0 : Spacetime) 1 (by norm_num)]
  ring

/-- Separate test constants from the two regulator growth factors. -/
theorem subtraction_bound_scaled (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (ha : 0 < a) (hR : 0 < R) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hbound : ∀ z, |K z| ≤ B / a ^ 8)
    (hlocal : ∀ z, ‖z.1‖ ≤ R → ‖z.2‖ ≤ R → (4 * c) * a < ‖z.1 - z.2‖ → K z = 0)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ) :
    ‖(∫ z, (K z : ℂ) * F z) - contact K a R c F‖ ≤
      ((mass B c 1 * (4 * c) ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 F) * (a * R ^ 4) +
        (B * SchwartzWeightedTail.weightedMoment volume m F) * (a ^ 8 * R ^ m)⁻¹ := by
  have h := subtraction_bound K hK a R c B ha hR hc hB hbound hlocal F m
  rw [mass_scaling B c R hR.le] at h
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Derived finite-range and tail bounds imply full-Schwartz convergence for this kernel family. -/
theorem subtraction_tendsto_of_growth {ι : Type*} (l : Filter ι)
    (K : ι → Spacetime × Spacetime → ℝ) (hK : ∀ k, Measurable (K k))
    (a R : ι → ℝ) (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ)
    (ha : ∀ᶠ k in l, 0 < a k) (hR : ∀ᶠ k in l, 0 < R k)
    (hbound : ∀ᶠ k in l, ∀ z, |K k z| ≤ B / a k ^ 8)
    (hlocal : ∀ᶠ k in l, ∀ z, ‖z.1‖ ≤ R k → ‖z.2‖ ≤ R k →
      (4 * c) * a k < ‖z.1 - z.2‖ → K k z = 0)
    (hsmall : Tendsto (fun k => a k * R k ^ 4) l (𝓝 0))
    (htail : Tendsto (fun k => (a k ^ 8 * R k ^ m)⁻¹) l (𝓝 0)) :
    Tendsto (fun k => (∫ z, (K k z : ℂ) * F z) - contact (K k) (a k) (R k) c F)
      l (𝓝 0) := by
  have hb : ∀ᶠ k in l, ‖(∫ z, (K k z : ℂ) * F z) - contact (K k) (a k) (R k) c F‖ ≤
      ((mass B c 1 * (4 * c) ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 F) *
        (a k * R k ^ 4) + (B * SchwartzWeightedTail.weightedMoment volume m F) *
          (a k ^ 8 * R k ^ m)⁻¹ := by
    filter_upwards [ha, hR, hbound, hlocal] with k hak hRk hbk hlk
    exact subtraction_bound_scaled (K k) (hK k) (a k) (R k) c B hak hRk hc hB
      hbk hlk F m
  apply squeeze_zero_norm' hb
  simpa only [mul_zero, zero_add] using
    (hsmall.const_mul ((mass B c 1 * (4 * c) ^ 5 / 24) *
      SchwartzMap.seminorm ℝ 0 5 F)).add
      (htail.const_mul (B * SchwartzWeightedTail.weightedMoment volume m F))

theorem contact_add (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (hbound : ∀ z, |K z| ≤ B / a ^ 8)
    (F G : SchwartzMap (Spacetime × Spacetime) ℂ) :
    contact K a R c (F + G) = contact K a R c F + contact K a R c G := by
  unfold contact diagonalJet
  simp_rw [WilsonContactDistribution.jet_add, mul_add]
  exact integral_add
    (cutoff_mul_continuous_integrable K hK a R c B hbound
      (diagonalJet F 4) (diagonalJet_continuous F 4))
    (cutoff_mul_continuous_integrable K hK a R c B hbound
      (diagonalJet G 4) (diagonalJet_continuous G 4))

theorem contact_smul (K : Spacetime × Spacetime → ℝ) (a R c : ℝ)
    (d : ℂ) (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    contact K a R c (d • F) = d • contact K a R c F := by
  unfold contact diagonalJet
  simp_rw [WilsonContactDistribution.jet_smul, mul_smul_comm]
  exact integral_smul d _

/-- Finite-cutoff continuity of the actual integrated Taylor counterterm. -/
theorem contact_bound (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hbound : ∀ z, |K z| ≤ B / a ^ 8)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    ‖contact K a R c F‖ ≤
      ((mass B c R / a ^ 4) *
        (∑ j ∈ Finset.range 5, (j.factorial : ℝ)⁻¹ * ((4 * c) * a) ^ j)) *
        (Finset.Iic (0, 4)).sup (schwartzSeminormFamily ℂ (Spacetime × Spacetime) ℂ) F := by
  let P := (∑ j ∈ Finset.range 5, (j.factorial : ℝ)⁻¹ * ((4 * c) * a) ^ j) *
    (Finset.Iic (0, 4)).sup (schwartzSeminormFamily ℂ (Spacetime × Spacetime) ℂ) F
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hp (z : Spacetime × Spacetime) :
      ‖(cutoff K a R c z : ℂ) * diagonalJet F 4 z‖ ≤ |cutoff K a R c z| * P := by
    by_cases hz : cutoff K a R c z = 0
    · simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero, abs_zero, le_refl]
    have ht : z ∈ tube R (c * a) := by
      by_contra ht
      exact hz (Set.indicator_of_notMem ht K)
    have hd : ‖((0, z.2 - z.1) : Spacetime × Spacetime)‖ ≤ (4 * c) * a := by
      simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), mul_assoc] using ht.2
    have hj := WilsonContactDistribution.jet_bound F 4 (z.1, z.1) (0, z.2 - z.1)
      ((4 * c) * a) hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hj (abs_nonneg _)
  have h := norm_integral_le_of_norm_le
    (((cutoff_integrable K hK a R c B hbound).abs).mul_const P)
    (Filter.Eventually.of_forall hp)
  rw [integral_mul_const] at h
  apply h.trans
  have hm := mul_le_mul_of_nonneg_right (cutoff_mass_bound K hK a R c B ha hc hbound) hP
  convert hm using 1
  dsimp [P]
  ring

/-- The constructed finite-range contact belongs to the continuous Schwartz dual. -/
def contactCLM (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hbound : ∀ z, |K z| ≤ B / a ^ 8) :
    SchwartzMap (Spacetime × Spacetime) ℂ →L[ℂ] ℂ := by
  refine SchwartzMap.mkCLMtoNormedSpace (contact K a R c)
    (contact_add K hK a R c B hbound) (contact_smul K a R c) ?_
  refine ⟨Finset.Iic (0, 4), (mass B c R / a ^ 4) *
    (∑ j ∈ Finset.range 5, (j.factorial : ℝ)⁻¹ * ((4 * c) * a) ^ j), ?_, ?_⟩
  · dsimp [mass]
    positivity
  · exact contact_bound K hK a R c B ha hc hbound

theorem contactCLM_apply (K : Spacetime × Spacetime → ℝ) (hK : Measurable K)
    (a R c B : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hbound : ∀ z, |K z| ≤ B / a ^ 8) (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    contactCLM K hK a R c B ha hc hB hbound F = contact K a R c F := rfl

/-- The counterterm is supported on the diagonal for every kernel and every cutoff. -/
theorem contact_diagonal_support (K : Spacetime × Spacetime → ℝ) (a R c : ℝ)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hF : ∀ x : Spacetime, (x, x) ∉ tsupport F) : contact K a R c F = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with z
  simp only [Pi.zero_apply, diagonalJet,
    jet_eq_zero_of_not_mem_tsupport F 4 (z.1, z.1) (0, z.2 - z.1) (hF z.1), mul_zero]

end
end UnifiedTheory.Clay.YangMills.FiniteRangeSchwartzContact
