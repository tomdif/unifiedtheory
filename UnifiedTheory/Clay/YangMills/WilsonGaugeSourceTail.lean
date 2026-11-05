/- Actual source-weighted local gauge-instability tails. The conditional
bound is paid by row variance; its stationary average is paid by the
original transfer's variance loss, without an extensive normalizer. -/
import UnifiedTheory.Clay.YangMills.WilsonGaugeOrbitTail
import UnifiedTheory.Clay.YangMills.WilsonVariancePair

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGaugeSourceTail
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalVariance WilsonGroundHeatBath
open WilsonSiteGauge WilsonGaugeOrbitTail WilsonVariancePair CompactDensityEntropy
open WilsonSingleLinkStaples (character character_continuous character_classFunction)

variable (n : ℕ) [NeZero n]

omit n [NeZero n] in
def tailCap (β t : ℝ) : ℝ := Real.exp (-β*t)*peakCap β

omit n [NeZero n] in
theorem tailCap_nonneg (β t : ℝ) : 0 ≤ tailCap β t :=
  mul_nonneg (Real.exp_pos _).le (peakCap_nonneg β)

omit n [NeZero n] in
theorem tailCap_formula (β t : ℝ) (hβ : 0 ≤ β) :
    tailCap β t = Real.exp 1*SU2GaussianMass.cap 36*(β+1)^3*Real.exp (-β*t) := by
  rw [tailCap, peakCap_formula β hβ]
  ring

/-- Local normalization cancels against any nonnegative physical source. -/
theorem transition_tail (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (t : ℝ)
    (H : C(Slice n, ℝ)) (hH : ∀ h v, H (gaugeSlice h v) = H v)
    (hH0 : ∀ v, 0 ≤ H v) (u : Slice n) :
    (∫ v in {v | (u, v) ∈ bad n x t}, rawTransition n β hβ u v*H v
      ∂WilsonSlabOperator.measure n) ≤
      tailCap β t*(∫ v, rawTransition n β hβ u v*H v ∂WilsonSlabOperator.measure n) := by
  have hw : Continuous (fun v : Slice n => spatialWeight character β 2 v) := by
    have hc := character_continuous
    unfold spatialWeight potential spatialHolonomy
    fun_prop
  let S : C(Slice n, ℝ) := ⟨fun v => spatialWeight character β 2 v*ground n β hβ v*H v,
    (hw.mul (ground n β hβ).continuous).mul H.continuous⟩
  have hS (q : Q) (v : Slice n) : S (rotate n x q v) = S v := by
    dsimp only [S, ContinuousMap.coe_mk, rotate]
    rw [WilsonSlabGauge.spatialWeight_gauge character character_classFunction,
      ground_invariant, hH]
  have hS0 (v : Slice n) : 0 ≤ S v :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (ground_pos n β hβ v).le) (hH0 v)
  let A := spatialWeight character β 2 u/(‖transfer n β‖*ground n β hβ u)
  have hA : 0 ≤ A := div_nonneg (Real.exp_pos _).le
    (mul_nonneg (norm_nonneg _) (ground_pos n β hβ u).le)
  have he (v : Slice n) : rawTransition n β hβ u v*H v =
      A*(kineticWeight character β 2 u v*S v) := by
    unfold rawTransition rawKernel
    dsimp only [A, S, ContinuousMap.coe_mk]
    ring
  have h := mul_le_mul_of_nonneg_left (weighted_tail n β hβ x t u S hS hS0) hA
  simp_rw [he]
  rw [integral_const_mul, integral_const_mul]
  unfold tailCap
  nlinarith

/-- The other endpoint retains its actual conditional transition. -/
def pairProfile (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (z : Slice n × Slice n) : ℝ :=
  ∫ w, rawTransition n β hβ z.1 w*(f z.2-f w)^2 ∂WilsonSlabOperator.measure n

theorem pairProfile_continuous (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Continuous (pairProfile n β hβ f) := by
  unfold pairProfile
  apply GibbsMarginalTower.fiber_integral_continuous (WilsonSlabOperator.measure n)
    (fun z : (Slice n × Slice n) × Slice n =>
      rawTransition n β hβ z.1.1 z.2*(f z.1.2-f z.2)^2)
  exact ((rawTransition_continuous n β hβ).comp
    (f := fun z : (Slice n × Slice n) × Slice n => (z.1.1,z.2)) (by fun_prop)).mul
    (by fun_prop)

def source (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (z : Slice n × Slice n) : ℝ :=
  rawTransition n β hβ z.1 z.2*pairProfile n β hβ f z

theorem source_continuous (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Continuous (source n β hβ f) :=
  (rawTransition_continuous n β hβ).mul (pairProfile_continuous n β hβ f)

theorem source_nonneg (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (z : Slice n × Slice n) : 0 ≤ source n β hβ f z := by
  apply mul_nonneg (rawTransition_pos n β hβ z.1 z.2).le
  exact integral_nonneg (fun w => mul_nonneg (rawTransition_pos n β hβ z.1 w).le
    (sq_nonneg _))

theorem source_integral (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) :
    (∫ v, source n β hβ f (u, v) ∂WilsonSlabOperator.measure n)/2 =
      rowVariance n β hβ f u := by
  unfold source pairProfile
  simp_rw [← integral_const_mul, ← mul_assoc]
  exact rowVariance_pair n β hβ u f

/-- Literal binding to the already constructed correlated variance-pair density. -/
theorem source_ground (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u v : Slice n) :
    (ground n β hβ u)^2*source n β hβ f (u, v) =
      ∫ w, pairWeight n β hβ u v w*(f v-f w)^2 ∂WilsonSlabOperator.measure n := by
  unfold source pairProfile
  simp_rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  rw [← ground_cancel]
  ring

/-- One endpoint of the actual source pair is restricted by the local event. -/
def rowTail (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (t : ℝ)
    (f : C(Slice n, ℝ)) (u : Slice n) : ℝ :=
  (∫ v, (bad n x t).indicator (source n β hβ f) (u, v) ∂WilsonSlabOperator.measure n)/2

theorem rowTail_set_integral (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (t : ℝ)
    (f : C(Slice n, ℝ)) (u : Slice n) :
    rowTail n β hβ x t f u =
      (∫ v in {v | (u, v) ∈ bad n x t}, source n β hβ f (u, v)
        ∂WilsonSlabOperator.measure n)/2 := by
  let B := {v : Slice n | (u, v) ∈ bad n x t}
  have hB : MeasurableSet B := (bad_open n x t).measurableSet.preimage
    (measurable_const.prodMk measurable_id)
  change (∫ v, B.indicator (fun v => source n β hβ f (u, v)) v
    ∂WilsonSlabOperator.measure n)/2 = _
  rw [integral_indicator hB]

theorem rowTail_nonneg (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (t : ℝ)
    (f : C(Slice n, ℝ)) (u : Slice n) : 0 ≤ rowTail n β hβ x t f u := by
  rw [rowTail_set_integral]
  exact div_nonneg (integral_nonneg (fun v => source_nonneg n β hβ f (u, v))) (by norm_num)

theorem rowTail_upper (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (t : ℝ)
    (f : C(Slice n, ℝ)) (hF : ∀ h v, f (gaugeSlice h v) = f v) (u : Slice n) :
    rowTail n β hβ x t f u ≤ tailCap β t*rowVariance n β hβ f u := by
  let H : C(Slice n, ℝ) := ⟨fun v => pairProfile n β hβ f (u, v),
    (pairProfile_continuous n β hβ f).comp (continuous_const.prodMk continuous_id)⟩
  have hH (h : SliceGauge n Q) (v : Slice n) : H (gaugeSlice h v) = H v := by
    change (∫ w, rawTransition n β hβ u w*(f (gaugeSlice h v)-f w)^2
      ∂WilsonSlabOperator.measure n) = _
    rw [hF]
    rfl
  have hH0 (v : Slice n) : 0 ≤ H v :=
    integral_nonneg (fun w => mul_nonneg (rawTransition_pos n β hβ u w).le (sq_nonneg _))
  have h := transition_tail n β hβ x t H hH hH0 u
  rw [rowTail_set_integral, ← source_integral n β hβ f u]
  change (∫ v in {v | (u, v) ∈ bad n x t}, rawTransition n β hβ u v*H v
    ∂WilsonSlabOperator.measure n)/2 ≤
      tailCap β t*((∫ v, rawTransition n β hβ u v*H v ∂WilsonSlabOperator.measure n)/2)
  linarith

theorem rowTail_integrable (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (t : ℝ)
    (f : C(Slice n, ℝ)) : Integrable (rowTail n β hβ x t f) (groundLaw n β hβ) := by
  letI := groundLaw_probability n β hβ
  exact (((continuous_integrable ((groundLaw n β hβ).prod (WilsonSlabOperator.measure n)) _
    (source_continuous n β hβ f)).indicator
      (bad_open n x t).measurableSet).integral_prod_left).div_const 2

/-- A genuine local, source-weighted exceptional contribution paid by the
actual variance loss of the same physical transfer step. -/
theorem meanTail_upper (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (t : ℝ)
    (f : C(Slice n, ℝ)) (hF : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ u, rowTail n β hβ x t f u ∂groundLaw n β hβ) ≤ tailCap β t*loss n β hβ f := by
  letI := groundLaw_probability n β hβ
  have h := integral_mono (rowTail_integrable n β hβ x t f)
    ((continuous_integrable (groundLaw n β hβ) _ (rowVariance_continuous n β hβ f)).const_mul
      (tailCap β t)) (fun u => rowTail_upper n β hβ x t f hF u)
  rw [integral_const_mul, mean_rowVariance_eq_loss] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeSourceTail
