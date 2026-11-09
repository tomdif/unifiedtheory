/- Full-Schwartz control of the actual sampled one-block removed covariance.
The global periodic kernel is not assumed local: its discarded cutoff part is
bounded using an explicit Schwartz tail and the complete a^-8 amplitude. -/
import UnifiedTheory.Clay.YangMills.WilsonCompactContactSubtraction
import UnifiedTheory.Clay.YangMills.SchwartzWeightedTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSchwartzContactBound
noncomputable section
open MeasureTheory Filter RegulatedGauge LocalFields PeriodicLattice4
open WilsonIndependentBlocks WilsonInfluenceGeometry
open WilsonNoiseTubeMass WilsonNoisePhysicalSupport WilsonCompactContactSubtraction
open scoped Topology

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure
  infer_instance

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- The actual globally sampled kernel minus the explicit compact diagonal cutoff. -/
def cutoffRemainder (β a R : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (z : Spacetime × Spacetime) : ℝ :=
  kernel n β a S plane plane' z.1 z.2 - truncated n β a R S plane plane' z

theorem cutoffRemainder_measurable (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) : Measurable (cutoffRemainder n β a R S plane plane') :=
  (kernel_measurable n β a S plane plane').sub
    (truncated_measurable n β a R S plane plane')

/-- The discarded periodic images retain the literal a^-8 coefficient bound. -/
theorem cutoffRemainder_abs_le (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (z : Spacetime × Spacetime) :
    |cutoffRemainder n β a R S plane plane' z| ≤ 16 / a ^ 8 := by
  by_cases hz : z ∈ tube R a
  · simp only [cutoffRemainder, truncated, Set.indicator_of_mem hz, sub_self, abs_zero]
    positivity
  · simpa only [cutoffRemainder, truncated_zero_outside n β a R S plane plane' z hz,
      sub_zero] using kernel_abs_le n β a S plane plane' z.1 z.2

/-- Actual no-wrap geometry forces the cutoff error outside the physical pair ball. -/
theorem cutoffRemainder_zero_on_ball (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (plane plane' : Plane)
    (ha : 0 < a) (hperiod : 2 * R + 2 * a < (n : ℝ) * a)
    (z : Spacetime × Spacetime) (hz : ‖z‖ ≤ R) :
    cutoffRemainder n β a R S plane plane' z = 0 := by
  change max ‖z.1‖ ‖z.2‖ ≤ R at hz
  obtain ⟨hx, hy⟩ := max_le_iff.mp hz
  by_cases ht : z ∈ tube R a
  · simp only [cutoffRemainder, truncated, Set.indicator_of_mem ht, sub_self]
  · have hd : 4 * a < ‖z.1 - z.2‖ := by
      have hd' : ¬ ‖z.2 - z.1‖ ≤ 4 * a := fun h => ht ⟨hx, h⟩
      simpa only [norm_sub_rev] using lt_of_not_ge hd'
    rw [cutoffRemainder, truncated_zero_outside n β a R S plane plane' z ht,
      kernel_zero_far n β a R S hS ha hperiod plane plane' z.1 z.2 hx hy hd, sub_self]

/-- The literal periodic sampled covariance pairs integrably with every Schwartz test. -/
theorem pairing_integrable (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f : SchwartzMap (Spacetime × Spacetime) ℂ) :
    Integrable (fun z => (kernel n β a S plane plane' z.1 z.2 : ℂ) * f z) := by
  have hm : Measurable (fun z => (kernel n β a S plane plane' z.1 z.2 : ℂ) * f z) :=
    (Complex.continuous_ofReal.measurable.comp
      (kernel_measurable n β a S plane plane')).mul f.continuous.measurable
  apply (f.integrable.norm.const_mul (16 / a ^ 8)).mono' hm.aestronglyMeasurable
  filter_upwards with z
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (kernel_abs_le n β a S plane plane' z.1 z.2)
    (norm_nonneg _)

/-- Exact integrable splitting retains every periodic image in the error term. -/
theorem pairing_sub_truncated (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f : SchwartzMap (Spacetime × Spacetime) ℂ) :
    pairing n β a S plane plane' f -
      (∫ z, (truncated n β a R S plane plane' z : ℂ) * f z) =
      ∫ z, (cutoffRemainder n β a R S plane plane' z : ℂ) * f z := by
  rw [pairing, ← integral_sub (pairing_integrable n β a S plane plane' f)
    (truncated_mul_continuous_integrable n β a R S plane plane' f f.continuous)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [cutoffRemainder, Complex.ofReal_sub, sub_mul]

/-- An actual Schwartz-tail bound for every discarded periodic image and base tail. -/
theorem periodic_tail_bound (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ)
    (ha : 0 < a) (hR : 0 < R) (hperiod : 2 * R + 2 * a < (n : ℝ) * a) :
    ‖pairing n β a S plane plane' f -
      (∫ z, (truncated n β a R S plane plane' z : ℂ) * f z)‖ ≤
      ((16 / a ^ 8) / R ^ m) * SchwartzWeightedTail.weightedMoment volume m f := by
  rw [pairing_sub_truncated]
  apply SchwartzWeightedTail.tail_pairing_bound volume
    (fun z => (cutoffRemainder n β a R S plane plane' z : ℂ))
    (16 / a ^ 8) R m (by positivity) hR
  · intro z
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      cutoffRemainder_abs_le n β a R S plane plane' z
  · intro z hz
    rw [cutoffRemainder_zero_on_ball n β a R S hS plane plane' ha hperiod z hz,
      Complex.ofReal_zero]

/-- The local Taylor error and the complete periodic-image tail are both derived. -/
theorem schwartz_subtraction_bound (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ)
    (ha : 0 < a) (hR : 0 < R) (hperiod : 2 * R + 2 * a < (n : ℝ) * a) :
    ‖pairing n β a S plane plane' f - contact4 n β a R S plane plane' f‖ ≤
      (massConstant R * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f * a +
        ((16 / a ^ 8) / R ^ m) * SchwartzWeightedTail.weightedMoment volume m f := by
  have h := norm_sub_le_norm_sub_add_norm_sub (pairing n β a S plane plane' f)
    (∫ z, (truncated n β a R S plane plane' z : ℂ) * f z)
    (contact4 n β a R S plane plane' f)
  have ht := periodic_tail_bound n β a R S hS plane plane' f m ha hR hperiod
  have hl := truncated_subtraction_bound n β a R S plane plane' f ha
  linarith

omit [NeZero n] in
/-- The compact tube constant grows by exactly the fourth power of the base radius. -/
theorem massConstant_scaling (R : ℝ) (hR : 0 ≤ R) :
    massConstant R = massConstant 1 * R ^ 4 := by
  unfold massConstant
  rw [ball_volume_real (0 : Spacetime) R hR,
    ball_volume_real (0 : Spacetime) 1 (by norm_num)]
  ring

/-- A convenient separation of test constants from the two regulator growth factors. -/
theorem schwartz_subtraction_bound_scaled (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ)
    (ha : 0 < a) (hR : 0 < R) (hperiod : 2 * R + 2 * a < (n : ℝ) * a) :
    ‖pairing n β a S plane plane' f - contact4 n β a R S plane plane' f‖ ≤
      ((massConstant 1 * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f) * (a * R ^ 4) +
        (16 * SchwartzWeightedTail.weightedMoment volume m f) * (a ^ 8 * R ^ m)⁻¹ := by
  have h := schwartz_subtraction_bound n β a R S hS plane plane' f m ha hR hperiod
  rw [massConstant_scaling R hR.le] at h
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [NeZero n] in
/-- Explicit growth conditions suffice for full-Schwartz contact subtraction.
The divergent prefactors remain in these conditions; mere volume expansion is not assumed enough. -/
theorem subtraction_tendsto_of_growth {ι : Type*} (l : Filter ι) (N : ι → ℕ)
    [∀ k, NeZero (N k)] (β a R : ι → ℝ)
    (S : (k : ι) → Finset (Edge (Vertex (N k))))
    (hS : ∀ k, Independent (N k) ((S k).image (edgeCoord (N k))))
    (plane plane' : Plane) (f : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ)
    (ha : ∀ᶠ k in l, 0 < a k) (hR : ∀ᶠ k in l, 0 < R k)
    (hperiod : ∀ᶠ k in l, 2 * R k + 2 * a k < (N k : ℝ) * a k)
    (hlocal : Tendsto (fun k => a k * R k ^ 4) l (𝓝 0))
    (htail : Tendsto (fun k => (a k ^ 8 * R k ^ m)⁻¹) l (𝓝 0)) :
    Tendsto (fun k => pairing (N k) (β k) (a k) (S k) plane plane' f -
      contact4 (N k) (β k) (a k) (R k) (S k) plane plane' f) l (𝓝 0) := by
  have hb : ∀ᶠ k in l, ‖pairing (N k) (β k) (a k) (S k) plane plane' f -
      contact4 (N k) (β k) (a k) (R k) (S k) plane plane' f‖ ≤
      ((massConstant 1 * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f) *
        (a k * R k ^ 4) + (16 * SchwartzWeightedTail.weightedMoment volume m f) *
          (a k ^ 8 * R k ^ m)⁻¹ := by
    filter_upwards [ha, hR, hperiod] with k hak hRk hk
    exact schwartz_subtraction_bound_scaled (N k) (β k) (a k) (R k) (S k) (hS k)
      plane plane' f m hak hRk hk
  apply squeeze_zero_norm' hb
  simpa only [mul_zero, zero_add] using
    (hlocal.const_mul ((massConstant 1 * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f)).add
      (htail.const_mul (16 * SchwartzWeightedTail.weightedMoment volume m f))

end
end UnifiedTheory.Clay.YangMills.WilsonSchwartzContactBound
