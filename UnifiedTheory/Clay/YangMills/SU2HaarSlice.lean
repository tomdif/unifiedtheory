/- Actual quaternion Haar first-coordinate averages are reduced to an explicit
planar integral. The proof constructs a volume-preserving real/imaginary split,
uses three-dimensional radial integration, and proves all required homogeneous
ball and planar integrability bounds, including the zero-coordinate case.
The final planar polar/cosine evaluation is a separate theorem, not assumed here.
No interacting-field correlation or continuum-limit assertion is made. -/
import UnifiedTheory.Clay.YangMills.SU2HaarSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2HaarSlice
noncomputable section
open MeasureTheory SU2HaarSphere SU2QuaternionEquivalence RegulatedGauge
open scoped ENNReal

abbrev ImaginarySpace := EuclideanSpace ℝ (Fin 3)

/-- The actual real/imaginary coordinate split, with the Euclidean norm on the imaginary part. -/
def coordinateSplit : Quaternion ℝ ≃ᵐ ℝ × ImaginarySpace :=
  Quaternion.linearIsometryEquivTuple.toMeasurableEquiv.trans
    ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm.trans
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
        ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))))

theorem coordinateSplit_re (q : Quaternion ℝ) : (coordinateSplit q).1 = q.re := rfl

theorem coordinateSplit_im (q : Quaternion ℝ) :
    (coordinateSplit q).2 = WithLp.toLp 2 ![q.imI, q.imJ, q.imK] := by
  ext i
  fin_cases i <;> rfl

/-- The coordinate split preserves the actual Euclidean volume measures. -/
theorem coordinateSplit_preserving : MeasurePreserving coordinateSplit := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 3))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).comp
      ((PiLp.volume_preserving_ofLp (Fin 4)).comp
        Quaternion.linearIsometryEquivTuple.measurePreserving))

theorem norm_sq_split (q : Quaternion ℝ) :
    ‖q‖ ^ 2 = (coordinateSplit q).1 ^ 2 + ‖(coordinateSplit q).2‖ ^ 2 := by
  rw [coordinateSplit_re, coordinateSplit_im, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  change ‖q‖ ^ 2 = q.re ^ 2 + (q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2)
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  ring

/-- Exact Fubini followed by three-dimensional radial integration. -/
theorem integral_radial_split (F : ℝ → ℝ → ℝ)
    (hF : Integrable (fun q : Quaternion ℝ => F q.re ‖(coordinateSplit q).2‖)) :
    (∫ q : Quaternion ℝ, F q.re ‖(coordinateSplit q).2‖) =
      ∫ t : ℝ, (4 * Real.pi) * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * F t r := by
  let f : ℝ × ImaginarySpace → ℝ := fun p => F p.1 ‖p.2‖
  have hi : Integrable f := by
    apply (coordinateSplit_preserving.integrable_comp_emb coordinateSplit.measurableEmbedding).mp
    simpa only [f, coordinateSplit_re] using hF
  calc
    (∫ q : Quaternion ℝ, F q.re ‖(coordinateSplit q).2‖) = ∫ p, f p :=
      coordinateSplit_preserving.integral_comp coordinateSplit.measurableEmbedding f
    _ = ∫ t : ℝ, ∫ y : ImaginarySpace, F t ‖y‖ := integral_prod f hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [integral_fun_norm_addHaar (volume : Measure ImaginarySpace)]
      norm_num [InnerProductSpace.volume_ball_of_dim_odd
        (k := 1) (by simp : Module.finrank ℝ ImaginarySpace = 2 * 1 + 1), measureReal_def]
      rw [ENNReal.toReal_ofReal (by positivity)]
      ring

/-- The real coordinate of a normalized nonzero quaternion; zero is assigned zero. -/
def directionCoordinate (q : Quaternion ℝ) : ℝ := q.re / ‖q‖

theorem directionCoordinate_measurable : Measurable directionCoordinate :=
  Quaternion.continuous_re.measurable.div continuous_norm.measurable

/-- Uniform volume on the actual four-dimensional unit ball. -/
def normalizedBall : Measure (Quaternion ℝ) :=
  (volume (Metric.ball (0 : Quaternion ℝ) 1))⁻¹ •
    volume.restrict (Metric.ball (0 : Quaternion ℝ) 1)

instance normalizedBall_probability : IsProbabilityMeasure normalizedBall where
  measure_univ := by
    rw [normalizedBall, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter]
    exact ENNReal.inv_mul_cancel
      (by rw [quaternion_unitBall_volume]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne')
      (measure_ball_lt_top.ne)

/-- Actual quaternion Haar's first-coordinate law is the angular law of the uniform ball. -/
theorem coordinateLaw_eq_ballDirection :
    (compactHaar UnitQuaternion).map (fun q : UnitQuaternion => (q : Quaternion ℝ).re) =
      normalizedBall.map directionCoordinate := by
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun q : UnitQuaternion => (q : Quaternion ℝ).re) :=
    (Quaternion.continuous_re.comp continuous_subtype_val).measurable
  rw [Measure.map_apply hm hs,
    Measure.map_apply directionCoordinate_measurable hs, normalizedBall,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (directionCoordinate_measurable hs)]
  change compactHaar UnitQuaternion {q | (q : Quaternion ℝ).re ∈ s} = _
  rw [compactHaar_coordinate_cone s hs]
  have he : volume {x : Quaternion ℝ | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x.re / ‖x‖ ∈ s} =
      volume (directionCoordinate ⁻¹' s ∩ Metric.ball (0 : Quaternion ℝ) 1) := by
    apply measure_congr
    filter_upwards [Measure.ae_ne (volume : Measure (Quaternion ℝ)) 0] with q hq
    apply propext
    change (0 < ‖q‖ ∧ ‖q‖ < 1 ∧ q.re / ‖q‖ ∈ s) ↔
      (directionCoordinate q ∈ s ∧ q ∈ Metric.ball (0 : Quaternion ℝ) 1)
    simp only [norm_pos_iff.mpr hq, true_and, directionCoordinate, Metric.mem_ball,
      dist_zero_right, and_comm]
  rw [he, div_eq_mul_inv, mul_comm]

/-- This is an exact Haar identity, with no unknown sphere slicing factor. -/
theorem compactHaar_integral_ball (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ q, F (q : Quaternion ℝ).re ∂compactHaar UnitQuaternion) =
      (Real.pi ^ 2 / 2)⁻¹ *
        ∫ q in Metric.ball (0 : Quaternion ℝ) 1, F (directionCoordinate q) := by
  calc
    (∫ q, F (q : Quaternion ℝ).re ∂compactHaar UnitQuaternion) =
        ∫ t, F t ∂(compactHaar UnitQuaternion).map
          (fun q : UnitQuaternion => (q : Quaternion ℝ).re) :=
      (integral_map (Quaternion.continuous_re.comp continuous_subtype_val).measurable.aemeasurable
        hF.aestronglyMeasurable).symm
    _ = ∫ t, F t ∂normalizedBall.map directionCoordinate := by rw [coordinateLaw_eq_ballDirection]
    _ = ∫ q, F (directionCoordinate q) ∂normalizedBall :=
      integral_map directionCoordinate_measurable.aemeasurable hF.aestronglyMeasurable
    _ = _ := by
      rw [normalizedBall, integral_smul_measure, quaternion_unitBall_volume,
        ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
      rfl


theorem directionCoordinate_mem_interval (q : Quaternion ℝ) :
    directionCoordinate q ∈ Set.Icc (-1 : ℝ) 1 := by
  by_cases hq : q = 0
  · simp [hq, directionCoordinate]
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hsq : q.re ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [norm_sq_split, coordinateSplit_re]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have habs : |q.re| ≤ ‖q‖ := by
    nlinarith [sq_abs q.re, abs_nonneg q.re]
  have hd : |directionCoordinate q| ≤ 1 := by
    rw [directionCoordinate, abs_div, abs_of_pos hn, div_le_one hn]
    exact habs
  exact abs_le.mp hd

/-- A continuous scalar test extended homogeneously inside the unit ball. -/
def angularBallTest (F : ℝ → ℝ) (q : Quaternion ℝ) : ℝ :=
  (Metric.ball (0 : Quaternion ℝ) 1).indicator (fun x => F (directionCoordinate x)) q

/-- Continuity of the scalar test supplies the needed integrability, including near zero. -/
theorem integrable_angularBallTest (F : ℝ → ℝ) (hF : Continuous F) :
    Integrable (angularBallTest F) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).bddAbove_image
    hF.norm.continuousOn
  have hc : IntegrableOn (fun _ : Quaternion ℝ => C) (Metric.ball (0 : Quaternion ℝ) 1) :=
    integrableOn_const (measure_ball_lt_top.ne)
  have hi : IntegrableOn (fun q : Quaternion ℝ => F (directionCoordinate q))
      (Metric.ball (0 : Quaternion ℝ) 1) := by
    apply hc.mono' (hF.measurable.comp directionCoordinate_measurable).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q =>
      hC ⟨directionCoordinate q, directionCoordinate_mem_interval q, rfl⟩)
  exact (integrable_indicator_iff measurableSet_ball).mpr hi

theorem norm_eq_sqrt_split (q : Quaternion ℝ) :
    ‖q‖ = Real.sqrt (q.re ^ 2 + ‖(coordinateSplit q).2‖ ^ 2) := by
  rw [← coordinateSplit_re q, ← norm_sq_split, Real.sqrt_sq (norm_nonneg q)]

/-- The remaining integrand is entirely two-dimensional and scalar. -/
def radialBallTest (F : ℝ → ℝ) (t r : ℝ) : ℝ :=
  if Real.sqrt (t ^ 2 + r ^ 2) < 1 then F (t / Real.sqrt (t ^ 2 + r ^ 2)) else 0

theorem angularBallTest_eq_radial (F : ℝ → ℝ) (q : Quaternion ℝ) :
    angularBallTest F q = radialBallTest F q.re ‖(coordinateSplit q).2‖ := by
  classical
  by_cases h : ‖q‖ < 1 <;>
    simp [angularBallTest, radialBallTest, ← norm_eq_sqrt_split, directionCoordinate,
      Metric.mem_ball, dist_zero_right, h]

/-- The actual Haar first-coordinate integral is reduced to one explicit planar polar integral. -/
theorem compactHaar_integral_radial (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ q, F (q : Quaternion ℝ).re ∂compactHaar UnitQuaternion) =
      (Real.pi ^ 2 / 2)⁻¹ *
        ∫ t : ℝ, (4 * Real.pi) *
          ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * radialBallTest F t r := by
  rw [compactHaar_integral_ball F hF]
  have hi : Integrable (fun q : Quaternion ℝ =>
      radialBallTest F q.re ‖(coordinateSplit q).2‖) := by
    simpa only [← angularBallTest_eq_radial] using integrable_angularBallTest F hF
  rw [← integral_indicator measurableSet_ball]
  change (Real.pi ^ 2 / 2)⁻¹ * ∫ q, angularBallTest F q = _
  simp_rw [angularBallTest_eq_radial]
  rw [integral_radial_split (radialBallTest F) hi]


/-- The planar angular coordinate stays in the scalar test's compact interval, even at zero. -/
theorem planar_direction_mem_interval (t r : ℝ) :
    t / Real.sqrt (t ^ 2 + r ^ 2) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hnonneg : 0 ≤ t ^ 2 + r ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases hz : Real.sqrt (t ^ 2 + r ^ 2) = 0
  · simp [hz]
  have hp : 0 < Real.sqrt (t ^ 2 + r ^ 2) :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
  have hb : |t| ≤ Real.sqrt (t ^ 2 + r ^ 2) := by
    nlinarith [Real.sq_sqrt hnonneg, sq_abs t, abs_nonneg t]
  apply abs_le.mp
  rw [abs_div, abs_of_pos hp, div_le_one hp]
  exact hb

/-- A scalar interval bound controls the entire planar test, uniformly at the origin. -/
theorem radialBallTest_norm_le (F : ℝ → ℝ) (C : ℝ)
    (hC : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖F u‖ ≤ C) (t r : ℝ) :
    ‖radialBallTest F t r‖ ≤ C := by
  have hzero : 0 ≤ C := (norm_nonneg (F 0)).trans (hC 0 (by norm_num))
  unfold radialBallTest
  split_ifs
  · exact hC _ (planar_direction_mem_interval t r)
  · simpa only [norm_zero] using hzero


/-- The unweighted planar integrand is globally integrable, by compact support and a bound. -/
theorem integrable_planarBallTest (F : ℝ → ℝ) (hF : Continuous F) :
    Integrable (fun p : ℝ × ℝ => p.2 ^ 2 * radialBallTest F p.1 p.2) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).bddAbove_image
    hF.norm.continuousOn
  have hb (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) : ‖F u‖ ≤ C := hC ⟨u, hu, rfl⟩
  have hc : 0 ≤ C := (norm_nonneg (F 0)).trans (hb 0 (by norm_num))
  let K : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
  have hk : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let g : ℝ × ℝ → ℝ := fun p => p.2 ^ 2 * radialBallTest F p.1 p.2
  have hg : Measurable g := by
    unfold g radialBallTest
    apply Measurable.mul (measurable_snd.pow_const 2)
    apply Measurable.ite
    · exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
    · exact hF.measurable.comp (measurable_fst.div (by fun_prop))
    · exact measurable_const
  have hi : IntegrableOn g K := by
    have hconst : IntegrableOn (fun _ : ℝ × ℝ => C) K := integrableOn_const hk.measure_ne_top
    apply hconst.mono' hg.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hk.measurableSet] with p hp
    have hr : p.2 ^ 2 ≤ 1 := by
      have hpr := hp.2
      nlinarith [hpr.1, hpr.2]
    change ‖p.2 ^ 2 * radialBallTest F p.1 p.2‖ ≤ C
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      p.2 ^ 2 * ‖radialBallTest F p.1 p.2‖ ≤ 1 * ‖radialBallTest F p.1 p.2‖ :=
        mul_le_mul_of_nonneg_right hr (norm_nonneg _)
      _ ≤ C := by simpa only [one_mul] using radialBallTest_norm_le F C hb p.1 p.2
  have hind : Integrable (K.indicator g) := (integrable_indicator_iff hk.measurableSet).mpr hi
  have heq : K.indicator g = g := by
    funext p
    by_cases hp : p ∈ K
    · exact Set.indicator_of_mem hp g
    · rw [Set.indicator_of_notMem hp]
      have hcut : ¬Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < 1 := by
        intro h
        have hsum : p.1 ^ 2 + p.2 ^ 2 < 1 := by
          simpa only [one_pow] using (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mp h
        apply hp
        change (-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ (-1 ≤ p.2 ∧ p.2 ≤ 1)
        constructor <;> constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2,
          sq_nonneg (p.1 + 1), sq_nonneg (p.1 - 1),
          sq_nonneg (p.2 + 1), sq_nonneg (p.2 - 1)]
      simp [g, radialBallTest, hcut]
  rw [heq] at hind
  exact hind

/-- In particular, the positive-radius iterated integral is justified by Fubini. -/
theorem integrableOn_planarBallTest (F : ℝ → ℝ) (hF : Continuous F) :
    IntegrableOn (fun p : ℝ × ℝ => p.2 ^ 2 * radialBallTest F p.1 p.2)
      (Set.univ ×ˢ Set.Ioi (0 : ℝ)) :=
  (integrable_planarBallTest F hF).integrableOn


/-- The radial cutoff has the standard unit-disk form. -/
theorem radialBallTest_eq_squared (F : ℝ → ℝ) (t r : ℝ) :
    radialBallTest F t r =
      if t ^ 2 + r ^ 2 < 1 then F (t / Real.sqrt (t ^ 2 + r ^ 2)) else 0 := by
  simp only [radialBallTest, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1), one_pow]

/-- A normalized, explicit planar integral for the actual Haar coordinate average. -/
theorem compactHaar_integral_planar (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ q, F (q : Quaternion ℝ).re ∂compactHaar UnitQuaternion) =
      (8 / Real.pi) * ∫ t : ℝ, ∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 * (if t ^ 2 + r ^ 2 < 1 then F (t / Real.sqrt (t ^ 2 + r ^ 2)) else 0) := by
  rw [compactHaar_integral_radial F hF, integral_const_mul]
  simp_rw [radialBallTest_eq_squared]
  field_simp [Real.pi_ne_zero]
  ring


end
end UnifiedTheory.Clay.YangMills.SU2HaarSlice
