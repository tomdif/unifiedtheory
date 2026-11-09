/- Exact cancellation of the gauge part of the actual physical-transfer
response. The localized tilt covariance vanishes for a pure gauge input
change on every continuous gauge-invariant observable. -/
import UnifiedTheory.Clay.YangMills.WilsonTemporalInfluence

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSlabGauge
open WilsonGroundLocalComparison WilsonTemporalGauge WilsonTemporalInfluence
open WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n]

def rowMean (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) : ℝ :=
  ∫ v, f v ∂rowLaw n β hβ u

/-- The response is that of the original full transfer on the physical observable sector. -/
theorem rowMean_eq_full (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (u : Slice n) :
    rowMean n β hβ f u = ∫ v, transition n β hβ u v * f v ∂measure n := by
  rw [rowMean, rowLaw_integral]
  exact (invariant_transition n β hβ f f.continuous hinv u).symm

theorem full_transition_gauge_left (β : ℝ) (hβ : 0 ≤ β)
    (h : SliceGauge n WilsonSlabOperator.Q) (u v : Slice n) :
    transition n β hβ (gaugeSlice h u) v = transition n β hβ u v := by
  unfold transition GroundStateDirichlet.transition
  simp only [kernelMap, ContinuousMap.coe_mk,
    kernel_gauge_left character character_classFunction character_inverse_re,
    ground_invariant]

/-- Exact gauge invariance of the true normalized row expectation. -/
theorem rowMean_gauge (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u)
    (h : SliceGauge n WilsonSlabOperator.Q) (u : Slice n) :
    rowMean n β hβ f (gaugeSlice h u) = rowMean n β hβ f u := by
  rw [rowMean_eq_full n β hβ f hinv, rowMean_eq_full n β hβ f hinv]
  apply integral_congr_ae
  filter_upwards with v
  rw [full_transition_gauge_left]

/-- The literal collective covariance in the actual temporal-gauge ground-row law. -/
def tiltCovariance (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n) (f : C(Slice n, ℝ)) : ℝ :=
  (∫ v, tilt n β S u u' v * f v ∂rowLaw n β hβ u') -
    (∫ v, tilt n β S u u' v ∂rowLaw n β hβ u') * rowMean n β hβ f u'

theorem tilt_mean_pos (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) :
    0 < ∫ v, tilt n β S u u' v ∂rowLaw n β hβ u' := by
  rw [tilt_mean n β hβ S u u' hu]
  exact div_pos (rowPartition_pos n β hβ u) (rowPartition_pos n β hβ u')

theorem covariance_eq_response_mul (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e) (f : C(Slice n, ℝ)) :
    tiltCovariance n β hβ S u u' f =
      (rowMean n β hβ f u - rowMean n β hβ f u') *
        (∫ v, tilt n β S u u' v ∂rowLaw n β hβ u') := by
  have h := response_covariance n β hβ S u u' hu f
  change rowMean n β hβ f u - rowMean n β hβ f u' =
    tiltCovariance n β hβ S u u' f / _ at h
  exact (div_eq_iff (tilt_mean_pos n β hβ S u u' hu).ne').mp h.symm

/-- A possibly large finite gauge tilt has exactly zero covariance with physical observables. -/
theorem gauge_tilt_covariance_zero (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (h : SliceGauge n WilsonSlabOperator.Q) (u : Slice n)
    (hu : ∀ e, e ∉ S → gaugeSlice h u e = u e) (f : C(Slice n, ℝ))
    (hinv : ∀ k v, f (gaugeSlice k v) = f v) :
    tiltCovariance n β hβ S (gaugeSlice h u) u f = 0 := by
  rw [covariance_eq_response_mul n β hβ S _ u hu,
    rowMean_gauge n β hβ f hinv, sub_self, zero_mul]

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalResponse
