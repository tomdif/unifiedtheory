/- Compact diagonal truncation of the actual sampled Wilson removed-noise kernel.
Its total-variation mass is bounded by an explicit multiple of a^-4. The hard
cutoff is stated explicitly; periodic-image tails are not included in this bound. -/
import UnifiedTheory.Clay.YangMills.WilsonNoisePhysicalSupport
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonNoiseTubeMass
noncomputable section
open MeasureTheory Set Filter LocalFields RegulatedGauge PeriodicLattice4

/-- A compact base ball and a genuine four-spacing neighborhood of the diagonal. -/
def tube (R a : ℝ) : Set (Spacetime × Spacetime) :=
  {z | ‖z.1‖ ≤ R ∧ ‖z.2 - z.1‖ ≤ 4 * a}

theorem tube_measurable (R a : ℝ) : MeasurableSet (tube R a) :=
  ((continuous_fst.norm).measurable measurableSet_Iic).inter
    (((continuous_snd.sub continuous_fst).norm).measurable measurableSet_Iic)

/-- The diagonal tube is compact, including for arbitrary real radius parameters. -/
theorem tube_compact (R a : ℝ) : IsCompact (tube R a) := by
  have hc : IsClosed (tube R a) :=
    (isClosed_le continuous_fst.norm continuous_const).inter
      (isClosed_le (continuous_snd.sub continuous_fst).norm continuous_const)
  apply (isCompact_closedBall (x := (0 : Spacetime)) (r := R)).prod
    (isCompact_closedBall (x := (0 : Spacetime)) (r := R + 4 * a)) |>.of_isClosed_subset hc
  intro z hz
  change ‖z.1‖ ≤ R ∧ ‖z.2 - z.1‖ ≤ 4 * a at hz
  simp only [mem_prod, Metric.mem_closedBall, dist_zero_right]
  refine ⟨hz.1, ?_⟩
  calc
    ‖z.2‖ = ‖(z.2 - z.1) + z.1‖ := by rw [sub_add_cancel]
    _ ≤ ‖z.2 - z.1‖ + ‖z.1‖ := norm_add_le _ _
    _ ≤ R + 4 * a := by linarith

theorem tube_volume (R a : ℝ) :
    volume (tube R a) = volume (Metric.closedBall (0 : Spacetime) R) *
      volume (Metric.closedBall (0 : Spacetime) (4 * a)) := by
  have h := (measurePreserving_prod_sub (volume : Measure Spacetime) volume).measure_preimage
    (s := Metric.closedBall (0 : Spacetime) R ×ˢ Metric.closedBall (0 : Spacetime) (4 * a))
    ((measurableSet_closedBall.prod measurableSet_closedBall).nullMeasurableSet)
  have he : (fun z : Spacetime × Spacetime => (z.1, z.2 - z.1)) ⁻¹'
      (Metric.closedBall (0 : Spacetime) R ×ˢ Metric.closedBall (0 : Spacetime) (4 * a)) =
      tube R a := by
    ext z
    simp only [mem_preimage, mem_prod, Metric.mem_closedBall, dist_zero_right, tube, mem_setOf_eq]
  rw [he, Measure.prod_prod] at h
  exact h

theorem tube_finite (R a : ℝ) : volume (tube R a) < ⊤ := by
  rw [tube_volume]
  exact ENNReal.mul_lt_top measure_closedBall_lt_top measure_closedBall_lt_top

/-- The exact four-dimensional closed-ball volume, in real-valued measure. -/
theorem ball_volume_real (x : Spacetime) (r : ℝ) (hr : 0 ≤ r) :
    volume.real (Metric.closedBall x r) = r ^ 4 * Real.pi ^ 2 / 2 := by
  rw [measureReal_def, InnerProductSpace.volume_closedBall_of_dim_even (k := 2) (by simp)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem tube_volume_real (R a : ℝ) (ha : 0 ≤ a) :
    volume.real (tube R a) =
      volume.real (Metric.closedBall (0 : Spacetime) R) * (128 * Real.pi ^ 2 * a ^ 4) := by
  calc
    _ = volume.real (Metric.closedBall (0 : Spacetime) R) *
        volume.real (Metric.closedBall (0 : Spacetime) (4 * a)) := by
      simp only [measureReal_def, tube_volume, ENNReal.toReal_mul]
    _ = _ := by
      rw [ball_volume_real (0 : Spacetime) (4 * a) (by positivity)]
      ring

/-- Every measurable bounded kernel becomes integrable on the actual compact tube. -/
theorem tube_integrable (R a : ℝ) (K : Spacetime × Spacetime → ℝ)
    (hK : Measurable K) (B : ℝ) (hbound : ∀ z, |K z| ≤ B) :
    Integrable ((tube R a).indicator K) := by
  apply (integrable_indicator_iff (tube_measurable R a)).mpr
  exact IntegrableOn.of_bound (tube_finite R a) hK.aestronglyMeasurable B
    (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound z))

/-- A derived tube-mass estimate, before substitution of the actual Wilson coefficient. -/
theorem tube_abs_mass_le (R a : ℝ) (K : Spacetime × Spacetime → ℝ)
    (hK : Measurable K) (B : ℝ) (hbound : ∀ z, |K z| ≤ B) :
    (∫ z, |(tube R a).indicator K z|) ≤ B * volume.real (tube R a) := by
  have hi := tube_integrable R a K hK B hbound
  have hc : Integrable ((tube R a).indicator (fun _ => B)) :=
    (integrable_indicator_iff (tube_measurable R a)).mpr
      (integrableOn_const (tube_finite R a).ne)
  have hp (z : Spacetime × Spacetime) :
      |(tube R a).indicator K z| ≤ (tube R a).indicator (fun _ => B) z := by
    by_cases hz : z ∈ tube R a
    · simpa only [indicator_of_mem hz] using hbound z
    · simp only [indicator_of_notMem hz, abs_zero, le_refl]
  have h := integral_mono hi.abs hc hp
  rw [integral_indicator_const B (tube_measurable R a), smul_eq_mul] at h
  simpa only [mul_comm] using h

/-- The explicit compact-base constant, independent of n, beta and the chosen block. -/
def massConstant (R : ℝ) : ℝ :=
  2048 * Real.pi ^ 2 * volume.real (Metric.closedBall (0 : Spacetime) R)

theorem massConstant_nonneg (R : ℝ) : 0 ≤ massConstant R := by
  unfold massConstant
  positivity

variable (n : ℕ) [NeZero n]

/-- The actual sampled Wilson noise, with a stated hard physical diagonal cutoff. -/
def truncated (β a R : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane) :
    Spacetime × Spacetime → ℝ :=
  (tube R a).indicator (fun z => WilsonNoisePhysicalSupport.kernel n β a S plane plane' z.1 z.2)

theorem truncated_measurable (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) : Measurable (truncated n β a R S plane plane') :=
  (WilsonNoisePhysicalSupport.kernel_measurable n β a S plane plane').indicator
    (tube_measurable R a)

theorem truncated_integrable (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) : Integrable (truncated n β a R S plane plane') :=
  tube_integrable R a _ (WilsonNoisePhysicalSupport.kernel_measurable n β a S plane plane')
    (16 / a ^ 8) (fun z => WilsonNoisePhysicalSupport.kernel_abs_le n β a S plane plane' z.1 z.2)

theorem truncated_abs_integrable (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) : Integrable (fun z => |truncated n β a R S plane plane' z|) :=
  (truncated_integrable n β a R S plane plane').abs

/-- The actual compact diagonal stencil has O(a^-4) total-variation mass. -/
theorem truncated_mass_le (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (ha : 0 < a) :
    (∫ z, |truncated n β a R S plane plane' z|) ≤ massConstant R / a ^ 4 := by
  have h := tube_abs_mass_le R a _
    (WilsonNoisePhysicalSupport.kernel_measurable n β a S plane plane') (16 / a ^ 8)
    (fun z => WilsonNoisePhysicalSupport.kernel_abs_le n β a S plane plane' z.1 z.2)
  change (∫ z, |truncated n β a R S plane plane' z|) ≤ _ at h
  rw [tube_volume_real R a ha.le] at h
  apply h.trans_eq
  unfold massConstant
  field_simp [ha.ne']
  ring

/-- Every nonzero truncated coefficient has the physical displacement required by Taylor. -/
theorem truncated_support (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (z : Spacetime × Spacetime)
    (hz : truncated n β a R S plane plane' z ≠ 0) :
    ‖z.1‖ ≤ R ∧ ‖z.2 - z.1‖ ≤ 4 * a := by
  by_contra h
  have hn : z ∉ tube R a := h
  exact hz (indicator_of_notMem hn _)

/-- The stated truncation vanishes outside its explicit diagonal tube. -/
theorem truncated_zero_outside (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (z : Spacetime × Spacetime) (hz : z ∉ tube R a) :
    truncated n β a R S plane plane' z = 0 :=
  indicator_of_notMem hz _

/-- Compactness supplies integrability against every continuous test or finite Taylor jet. -/
theorem truncated_mul_continuous_integrable (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (G : Spacetime × Spacetime → ℂ) (hG : Continuous G) :
    Integrable (fun z => (truncated n β a R S plane plane' z : ℂ) * G z) := by
  obtain ⟨C, hC⟩ := (tube_compact R a).exists_bound_of_continuousOn hG.continuousOn
  have hm : Measurable (fun z => (truncated n β a R S plane plane' z : ℂ) * G z) :=
    (Complex.continuous_ofReal.measurable.comp
      (truncated_measurable n β a R S plane plane')).mul hG.measurable
  apply ((truncated_abs_integrable n β a R S plane plane').mul_const C).mono'
    hm.aestronglyMeasurable
  filter_upwards with z
  by_cases hz : z ∈ tube R a
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC z hz) (abs_nonneg _)
  · rw [truncated_zero_outside n β a R S plane plane' z hz]
    simp

end
end UnifiedTheory.Clay.YangMills.WilsonNoiseTubeMass
