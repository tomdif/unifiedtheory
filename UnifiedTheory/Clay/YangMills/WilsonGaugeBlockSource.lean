/- Coordinated finite-block gauge-instability tails for the actual physical
variance-pair source. The normalization price depends on the block size,
not the full spatial volume. -/
import UnifiedTheory.Clay.YangMills.WilsonGaugeBlockTail
import UnifiedTheory.Clay.YangMills.WilsonGaugeSourceTail
import UnifiedTheory.Clay.YangMills.WilsonVariancePair
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGaugeBlockSource
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalVariance WilsonGroundHeatBath
open WilsonGaugeBlock WilsonGaugeBlockTail WilsonVariancePair CompactDensityEntropy
open WilsonGaugeOrbitTail (peakCap peakCap_nonneg)
open WilsonGaugeSourceTail (pairProfile pairProfile_continuous source source_continuous
  source_nonneg source_integral)
open WilsonSingleLinkStaples (character character_continuous character_classFunction)
open Filter
open scoped Topology

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
def tailCap (β t : ℝ) (B : Finset (SpatialVertex n)) : ℝ :=
  Real.exp (-β*t)*(peakCap β)^B.card

omit [NeZero n] in
theorem tailCap_nonneg (β t : ℝ) (B : Finset (SpatialVertex n)) : 0 ≤ tailCap n β t B :=
  mul_nonneg (Real.exp_pos _).le (pow_nonneg (peakCap_nonneg β) B.card)

omit [NeZero n] in
/-- An extensive improvement gives a power of the one-vertex numerical coefficient.
This identity does not assume independence of the Wilson interactions. -/
theorem tailCap_extensive (β δ : ℝ) (B : Finset (SpatialVertex n)) :
    tailCap n β (δ*(B.card : ℝ)) B = (WilsonGaugeSourceTail.tailCap β δ)^B.card := by
  unfold tailCap WilsonGaugeSourceTail.tailCap
  rw [show -β*(δ*(B.card : ℝ)) = (B.card : ℝ)*(-β*δ) by ring,
    Real.exp_nat_mul, mul_pow]

omit n [NeZero n] in
/-- The base of the block-volume power tends to zero at weak coupling. -/
theorem one_vertex_tail_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun β : ℝ => WilsonGaugeSourceTail.tailCap β δ) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x^3*Real.exp (-δ*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℕ) δ hδ
  have hs := h.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  have hm := hs.const_mul (Real.exp 1*SU2GaussianMass.cap 36*Real.exp δ)
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  rw [WilsonGaugeSourceTail.tailCap_formula β δ hβ]
  have he : Real.exp δ*Real.exp (-δ*(β+1)) = Real.exp (-β*δ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change (Real.exp 1*SU2GaussianMass.cap 36*Real.exp δ)*
    ((β+1)^3*Real.exp (-δ*(β+1))) = _
  calc
    _ = (Real.exp 1*SU2GaussianMass.cap 36)*(β+1)^3*
        (Real.exp δ*Real.exp (-δ*(β+1))) := by ring
    _ = _ := by rw [he]

omit n [NeZero n] in
/-- The weak-coupling threshold is independent of block size and ambient volume. -/
theorem eventually_subcritical (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop, 0 ≤ β ∧ WilsonGaugeSourceTail.tailCap β δ < 1 := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    (one_vertex_tail_tendsto δ hδ).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with β hβ htail
  exact ⟨hβ,htail⟩

/-- Local normalization cancels against any nonnegative physical source. -/
theorem transition_tail (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n)) (t : ℝ)
    (H : C(Slice n, ℝ)) (hH : ∀ h v, H (gaugeSlice h v) = H v)
    (hH0 : ∀ v, 0 ≤ H v) (u : Slice n) :
    (∫ v in {v | (u, v) ∈ bad n B t}, rawTransition n β hβ u v*H v
      ∂WilsonSlabOperator.measure n) ≤
      tailCap n β t B*(∫ v, rawTransition n β hβ u v*H v ∂WilsonSlabOperator.measure n) := by
  have hw : Continuous (fun v : Slice n => spatialWeight character β 2 v) := by
    have hc := character_continuous
    unfold spatialWeight potential spatialHolonomy
    fun_prop
  let S : C(Slice n, ℝ) := ⟨fun v => spatialWeight character β 2 v*ground n β hβ v*H v,
    (hw.mul (ground n β hβ).continuous).mul H.continuous⟩
  have hS (q : Parameters n B) (v : Slice n) : S (rotate n B q v) = S v := by
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
  have h := mul_le_mul_of_nonneg_left (weighted_tail n β hβ B t u S hS hS0) hA
  simp_rw [he]
  rw [integral_const_mul, integral_const_mul]
  unfold tailCap
  nlinarith

/-- One endpoint of the actual source pair is restricted by the local event. -/
def rowTail (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n)) (t : ℝ)
    (f : C(Slice n, ℝ)) (u : Slice n) : ℝ :=
  (∫ v, (bad n B t).indicator (source n β hβ f) (u, v) ∂WilsonSlabOperator.measure n)/2

theorem rowTail_set_integral (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n)) (t : ℝ)
    (f : C(Slice n, ℝ)) (u : Slice n) :
    rowTail n β hβ B t f u =
      (∫ v in {v | (u, v) ∈ bad n B t}, source n β hβ f (u, v)
        ∂WilsonSlabOperator.measure n)/2 := by
  let E := {v : Slice n | (u, v) ∈ bad n B t}
  have hE : MeasurableSet E := (bad_open n B t).measurableSet.preimage
    (measurable_const.prodMk measurable_id)
  change (∫ v, E.indicator (fun v => source n β hβ f (u, v)) v
    ∂WilsonSlabOperator.measure n)/2 = _
  rw [integral_indicator hE]

theorem rowTail_nonneg (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n)) (t : ℝ)
    (f : C(Slice n, ℝ)) (u : Slice n) : 0 ≤ rowTail n β hβ B t f u := by
  rw [rowTail_set_integral]
  exact div_nonneg (integral_nonneg (fun v => source_nonneg n β hβ f (u, v))) (by norm_num)

theorem rowTail_upper (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n)) (t : ℝ)
    (f : C(Slice n, ℝ)) (hF : ∀ h v, f (gaugeSlice h v) = f v) (u : Slice n) :
    rowTail n β hβ B t f u ≤ tailCap n β t B*rowVariance n β hβ f u := by
  let H : C(Slice n, ℝ) := ⟨fun v => pairProfile n β hβ f (u, v),
    (pairProfile_continuous n β hβ f).comp (continuous_const.prodMk continuous_id)⟩
  have hH (h : SliceGauge n Q) (v : Slice n) : H (gaugeSlice h v) = H v := by
    change (∫ w, rawTransition n β hβ u w*(f (gaugeSlice h v)-f w)^2
      ∂WilsonSlabOperator.measure n) = _
    rw [hF]
    rfl
  have hH0 (v : Slice n) : 0 ≤ H v :=
    integral_nonneg (fun w => mul_nonneg (rawTransition_pos n β hβ u w).le (sq_nonneg _))
  have h := transition_tail n β hβ B t H hH hH0 u
  rw [rowTail_set_integral, ← source_integral n β hβ f u]
  change (∫ v in {v | (u, v) ∈ bad n B t}, rawTransition n β hβ u v*H v
    ∂WilsonSlabOperator.measure n)/2 ≤
      tailCap n β t B*((∫ v, rawTransition n β hβ u v*H v ∂WilsonSlabOperator.measure n)/2)
  linarith

theorem rowTail_integrable (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n)) (t : ℝ)
    (f : C(Slice n, ℝ)) : Integrable (rowTail n β hβ B t f) (groundLaw n β hβ) := by
  letI := groundLaw_probability n β hβ
  exact (((continuous_integrable ((groundLaw n β hβ).prod (WilsonSlabOperator.measure n)) _
    (source_continuous n β hβ f)).indicator
      (bad_open n B t).measurableSet).integral_prod_left).div_const 2

/-- A genuine local, source-weighted exceptional contribution paid by the
actual variance loss of the same physical transfer step. -/
theorem meanTail_upper (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n)) (t : ℝ)
    (f : C(Slice n, ℝ)) (hF : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ u, rowTail n β hβ B t f u ∂groundLaw n β hβ) ≤ tailCap n β t B*loss n β hβ f := by
  letI := groundLaw_probability n β hβ
  have h := integral_mono (rowTail_integrable n β hβ B t f)
    ((continuous_integrable (groundLaw n β hβ) _ (rowVariance_continuous n β hβ f)).const_mul
      (tailCap n β t B)) (fun u => rowTail_upper n β hβ B t f hF u)
  rw [integral_const_mul, mean_rowVariance_eq_loss] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeBlockSource
