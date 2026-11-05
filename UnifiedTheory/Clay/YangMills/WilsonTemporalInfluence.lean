/- Actual localized input tilts for the temporal-gauge transfer. Spatial
weights cancel from input ratios after the constructed ground normalization.
The remaining response is an exact covariance, not an assumed mixing bound. -/
import UnifiedTheory.Clay.YangMills.WilsonTemporalGauge
import UnifiedTheory.Clay.YangMills.LocalGibbsComparison
import UnifiedTheory.Clay.YangMills.PositiveKernelRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTemporalInfluence
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n]

def tilt (beta : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n) : ℝ :=
  Real.exp (beta * ∑ e ∈ S, ((character ((u e)⁻¹ * v e)).re -
    (character ((u' e)⁻¹ * v e)).re))

omit [NeZero n] in
theorem tilt_pos (beta : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n) :
    0 < tilt n beta S u u' v := Real.exp_pos _

omit [NeZero n] in
/-- The input tilt depends on precisely the indicated output coordinates. -/
theorem tilt_local (beta : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (u u' v w : Slice n)
    (hvw : ∀ e, e ∈ S → v e = w e) : tilt n beta S u u' v = tilt n beta S u u' w := by
  unfold tilt
  congr 2
  exact Finset.sum_congr rfl (fun e he => by rw [hvw e he])

/-- All input dependence outside S cancels exactly, including the character offset. -/
theorem kinetic_tilt (beta : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) :
    kineticWeight character beta 2 u v =
      tilt n beta S u u' v * kineticWeight character beta 2 u' v := by
  classical
  let d : SpatialVertex n × Fin 3 → ℝ := fun e =>
    (character ((u e)⁻¹ * v e)).re - (character ((u' e)⁻¹ * v e)).re
  have hs : (∑ e, d e) = ∑ e ∈ S, d e := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun e _ he => by simp [d, hu e he])
  have ha : kineticAction character 2 u' v - kineticAction character 2 u v = ∑ e ∈ S, d e := by
    rw [← hs]
    unfold kineticAction
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => by dsimp [d]; ring)
  unfold kineticWeight tilt
  rw [← Real.exp_add]
  congr 1
  change -beta * kineticAction character 2 u v =
    beta * (∑ e ∈ S, d e) + -beta * kineticAction character 2 u' v
  rw [← ha]
  ring

omit [NeZero n] in
theorem tilt_bounds (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n) :
    Real.exp (-(4 * beta * (S.card : ℝ))) ≤ tilt n beta S u u' v ∧
      tilt n beta S u u' v ≤ Real.exp (4 * beta * (S.card : ℝ)) := by
  have hd (e : SpatialVertex n × Fin 3) :
      |(character ((u e)⁻¹ * v e)).re - (character ((u' e)⁻¹ * v e)).re| ≤ 4 := by
    have h1 := (Complex.abs_re_le_norm (character ((u e)⁻¹ * v e))).trans (character_bound _)
    have h2 := (Complex.abs_re_le_norm (character ((u' e)⁻¹ * v e))).trans (character_bound _)
    exact (abs_sub _ _).trans (by linarith)
  have hs : |∑ e ∈ S, ((character ((u e)⁻¹ * v e)).re -
      (character ((u' e)⁻¹ * v e)).re)| ≤ 4 * (S.card : ℝ) := by
    calc
      _ ≤ ∑ e ∈ S, |(character ((u e)⁻¹ * v e)).re -
          (character ((u' e)⁻¹ * v e)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ S, (4 : ℝ) := Finset.sum_le_sum (fun e _ => hd e)
      _ = _ := by simp; ring
  have hb := mul_le_mul_of_nonneg_left hs hbeta
  have hh : |beta * ∑ e ∈ S, ((character ((u e)⁻¹ * v e)).re -
      (character ((u' e)⁻¹ * v e)).re)| ≤ 4 * beta * (S.card : ℝ) := by
    rw [abs_mul, abs_of_nonneg hbeta]
    nlinarith
  unfold tilt
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hh).1, Real.exp_le_exp.mpr (abs_le.mp hh).2⟩

/-- The entire output weight left after removing the input spatial factor. -/
def rowWeight (beta : ℝ) (hbeta : 0 ≤ beta) (u v : Slice n) : ℝ :=
  kineticWeight character beta 2 u v * spatialWeight character beta 2 v * ground n beta hbeta v

theorem rowWeight_continuous (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) :
    Continuous (rowWeight n beta hbeta u) := by
  have hc := character_continuous
  have hg := (ground n beta hbeta).continuous
  unfold rowWeight kineticWeight kineticAction spatialWeight potential spatialHolonomy
  fun_prop

theorem rowWeight_pos (beta : ℝ) (hbeta : 0 ≤ beta) (u v : Slice n) :
    0 < rowWeight n beta hbeta u v := by
  unfold rowWeight kineticWeight spatialWeight
  exact mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (ground_pos n beta hbeta v)

def rowPartition (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) : ℝ :=
  ∫ v, rowWeight n beta hbeta u v ∂WilsonSlabOperator.measure n

theorem rowPartition_pos (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) :
    0 < rowPartition n beta hbeta u :=
  PositiveKernelRatio.profile_integral_pos (WilsonSlabOperator.measure n)
    ⟨rowWeight n beta hbeta u, rowWeight_continuous n beta hbeta u⟩
    (rowWeight_pos n beta hbeta u)

theorem rowPartition_ground (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) :
    spatialWeight character beta 2 u * rowPartition n beta hbeta u =
      ‖transfer n beta‖ * ground n beta hbeta u := by
  rw [← ground_raw_equation n beta hbeta u]
  unfold rowPartition
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  unfold rowWeight rawKernel
  ring

/-- This quotient is exactly the constructed transition, not a replacement law. -/
theorem rawTransition_quotient (beta : ℝ) (hbeta : 0 ≤ beta) (u v : Slice n) :
    rawTransition n beta hbeta u v = rowWeight n beta hbeta u v / rowPartition n beta hbeta u := by
  unfold rawTransition
  rw [← rowPartition_ground n beta hbeta u]
  have hs : spatialWeight character beta 2 u ≠ 0 := (Real.exp_pos _).ne'
  unfold rawKernel rowWeight
  field_simp

def rowLaw (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) : Measure (Slice n) :=
  LocalGibbsComparison.weightedLaw (WilsonSlabOperator.measure n) (rowWeight n beta hbeta u)

theorem rowLaw_probability (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) :
    IsProbabilityMeasure (rowLaw n beta hbeta u) :=
  LocalGibbsComparison.weightedLaw_probability _ _
    (rowWeight_continuous n beta hbeta u).measurable
    ((rowWeight_continuous n beta hbeta u).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun v => (rowWeight_pos n beta hbeta u v).le) (rowPartition_pos n beta hbeta u)

theorem rowLaw_integral (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) (f : Slice n → ℝ) :
    (∫ v, f v ∂rowLaw n beta hbeta u) =
      ∫ v, rawTransition n beta hbeta u v * f v ∂WilsonSlabOperator.measure n := by
  unfold rowLaw
  rw [LocalGibbsComparison.weighted_integral _ _
    (rowWeight_continuous n beta hbeta u).measurable
    (fun v => (rowWeight_pos n beta hbeta u v).le) (rowPartition_pos n beta hbeta u)]
  simp_rw [rawTransition_quotient, div_mul_eq_mul_div]
  rw [integral_div]
  rfl

theorem rowWeight_tilt (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) :
    rowWeight n beta hbeta u v = tilt n beta S u u' v * rowWeight n beta hbeta u' v := by
  unfold rowWeight
  rw [kinetic_tilt n beta S u u' v hu]
  ring

theorem rowWeight_comparison (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) :
    rowWeight n beta hbeta u v ≤
      Real.exp (4 * beta * (S.card : ℝ)) * rowWeight n beta hbeta u' v := by
  rw [rowWeight_tilt n beta hbeta S u u' v hu]
  exact mul_le_mul_of_nonneg_right (tilt_bounds n beta hbeta S u u' v).2
    (rowWeight_pos n beta hbeta u' v).le

theorem rowPartition_comparison (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) :
    rowPartition n beta hbeta u ≤
      Real.exp (4 * beta * (S.card : ℝ)) * rowPartition n beta hbeta u' := by
  unfold rowPartition
  rw [← integral_const_mul]
  apply integral_mono
    ((rowWeight_continuous n beta hbeta u).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((continuous_const.mul (rowWeight_continuous n beta hbeta u')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  intro v
  exact rowWeight_comparison n beta hbeta S u u' v hu

/-- Input changes on b links have a sharper exp(8 beta b) normalized row
comparison in this exact temporal-gauge representation of physical observables. -/
theorem rawTransition_comparison (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) :
    rawTransition n beta hbeta u v ≤
      Real.exp (8 * beta * (S.card : ℝ)) * rawTransition n beta hbeta u' v := by
  have hw := rowWeight_comparison n beta hbeta S u u' v hu
  have hz := rowPartition_comparison n beta hbeta S u' u (fun e he => (hu e he).symm)
  have hp := mul_le_mul hw hz (rowPartition_pos n beta hbeta u').le
    (mul_nonneg (Real.exp_pos _).le (rowWeight_pos n beta hbeta u' v).le)
  have he : Real.exp (8 * beta * (S.card : ℝ)) = Real.exp (4 * beta * (S.card : ℝ)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp_rw [rawTransition_quotient]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (rowPartition_pos n beta hbeta u)
    (rowPartition_pos n beta hbeta u')).mpr
  rw [he]
  nlinarith

/-- The normalized row Radon--Nikodym factor is an explicit local tilt
times a single partition ratio. -/
theorem rawTransition_ratio (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) :
    rawTransition n beta hbeta u v / rawTransition n beta hbeta u' v =
      tilt n beta S u u' v * (rowPartition n beta hbeta u' / rowPartition n beta hbeta u) := by
  simp_rw [rawTransition_quotient]
  rw [rowWeight_tilt n beta hbeta S u u' v hu]
  field_simp [(rowWeight_pos n beta hbeta u' v).ne']

/-- Changing the input only on S changes the output likelihood ratio only
through S. This is not independence of separated output coordinates. -/
theorem likelihood_local (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' v w : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) (hvw : ∀ e, e ∈ S → v e = w e) :
    rawTransition n beta hbeta u v / rawTransition n beta hbeta u' v =
      rawTransition n beta hbeta u w / rawTransition n beta hbeta u' w := by
  rw [rawTransition_ratio n beta hbeta S u u' v hu,
    rawTransition_ratio n beta hbeta S u u' w hu, tilt_local n beta S u u' v w hvw]

theorem rowLaw_quotient (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) (f : Slice n → ℝ) :
    (∫ v, f v ∂rowLaw n beta hbeta u) =
      (∫ v, rowWeight n beta hbeta u v * f v ∂WilsonSlabOperator.measure n) /
        rowPartition n beta hbeta u :=
  LocalGibbsComparison.weighted_integral _ _
    (rowWeight_continuous n beta hbeta u).measurable
    (fun v => (rowWeight_pos n beta hbeta u v).le) (rowPartition_pos n beta hbeta u) f

theorem tilt_mean (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) :
    (∫ v, tilt n beta S u u' v ∂rowLaw n beta hbeta u') =
      rowPartition n beta hbeta u / rowPartition n beta hbeta u' := by
  rw [rowLaw_quotient]
  congr 1
  unfold rowPartition
  apply integral_congr_ae
  filter_upwards [] with v
  rw [rowWeight_tilt n beta hbeta S u u' v hu]
  ring

/-- Exact reweighting under the original constructed row law. -/
theorem reweighted_expectation (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) (f : Slice n → ℝ) :
    (∫ v, f v ∂rowLaw n beta hbeta u) =
      (∫ v, tilt n beta S u u' v * f v ∂rowLaw n beta hbeta u') /
        (∫ v, tilt n beta S u u' v ∂rowLaw n beta hbeta u') := by
  rw [tilt_mean n beta hbeta S u u' hu, rowLaw_quotient, rowLaw_quotient]
  have he : (∫ v, rowWeight n beta hbeta u v * f v ∂WilsonSlabOperator.measure n) =
      ∫ v, rowWeight n beta hbeta u' v * (tilt n beta S u u' v * f v)
        ∂WilsonSlabOperator.measure n := by
    apply integral_congr_ae
    filter_upwards [] with v
    rw [rowWeight_tilt n beta hbeta S u u' v hu]
    ring
  rw [he]
  field_simp [(rowPartition_pos n beta hbeta u').ne']

/-- The missing collective input is exposed as an actual covariance with
a local tilt. No covariance decay is assumed or concluded. -/
theorem response_covariance (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) (f : Slice n → ℝ) :
    (∫ v, f v ∂rowLaw n beta hbeta u) - (∫ v, f v ∂rowLaw n beta hbeta u') =
      ((∫ v, tilt n beta S u u' v * f v ∂rowLaw n beta hbeta u') -
        (∫ v, tilt n beta S u u' v ∂rowLaw n beta hbeta u') *
          (∫ v, f v ∂rowLaw n beta hbeta u')) /
        (∫ v, tilt n beta S u u' v ∂rowLaw n beta hbeta u') := by
  have hm : 0 < ∫ v, tilt n beta S u u' v ∂rowLaw n beta hbeta u' := by
    rw [tilt_mean n beta hbeta S u u' hu]
    exact div_pos (rowPartition_pos n beta hbeta u) (rowPartition_pos n beta hbeta u')
  rw [reweighted_expectation n beta hbeta S u u' hu f]
  field_simp

theorem rawKernel_symm (beta : ℝ) (u v : Slice n) :
    rawKernel character beta 2 u v = rawKernel character beta 2 v u := by
  unfold rawKernel
  rw [WilsonSlabGauge.kineticWeight_symm character character_inverse_re beta 2 u v]
  ring

/-- The unaveraged transition has the same actual stationary ground density. -/
theorem raw_detailed_balance (beta : ℝ) (hbeta : 0 ≤ beta) (u v : Slice n) :
    (ground n beta hbeta u) ^ 2 * rawTransition n beta hbeta u v =
      (ground n beta hbeta v) ^ 2 * rawTransition n beta hbeta v u := by
  unfold rawTransition
  rw [rawKernel_symm n beta u v]
  field_simp [(ground_pos n beta hbeta u).ne', (ground_pos n beta hbeta v).ne']

theorem rawTransition_continuous (beta : ℝ) (hbeta : 0 ≤ beta) :
    Continuous (fun uv : Slice n × Slice n => rawTransition n beta hbeta uv.1 uv.2) := by
  have hc := rawKernel_continuous character character_continuous beta 2 (n := n)
  have hg := (ground n beta hbeta).continuous
  exact (hc.mul (hg.comp continuous_snd)).div (continuous_const.mul
    (hg.comp continuous_fst)) (fun uv => mul_ne_zero
      (PositiveKernelGroundState.transfer_top_eigenvector n beta hbeta).1.ne'
      (ground_pos n beta hbeta uv.1).ne')

/-- On the physical invariant sector, the original full transition has
exactly the same one-step squared increments as the unaveraged representation. -/
theorem invariant_increment (beta : ℝ) (hbeta : 0 ≤ beta) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (u : Slice n) :
    (∫ v, WilsonGroundLocalComparison.transition n beta hbeta u v * (f u - f v) ^ 2
      ∂WilsonSlabOperator.measure n) =
      ∫ v, rawTransition n beta hbeta u v * (f u - f v) ^ 2
        ∂WilsonSlabOperator.measure n :=
  invariant_transition n beta hbeta (fun v => (f u - f v) ^ 2)
    ((continuous_const.sub f.continuous).pow 2) (fun h v => by dsimp only; rw [hinv]) u

end
end UnifiedTheory.Clay.YangMills.WilsonTemporalInfluence
