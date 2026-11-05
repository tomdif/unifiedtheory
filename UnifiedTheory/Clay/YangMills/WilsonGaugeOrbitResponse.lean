/- An attained gauge-orbit cost and a quantitative physical row-response
bound. Gauge directions are removed before taking absolute covariance.
No weak-coupling contraction or continuum mass gap is inferred. -/
import UnifiedTheory.Clay.YangMills.WilsonRowGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGaugeOrbitResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSlabGauge
open WilsonTemporalInfluence WilsonPhysicalResponse WilsonRowGeometry

variable (n : ℕ) [NeZero n]

theorem alignment_cost_continuous (u v : Slice n) :
    Continuous (fun h : SliceGauge n Q => inputCost n u (gaugeSlice h v)) := by
  unfold inputCost gaugeSlice
  fun_prop

/-- Compactness constructs an optimizer; no choice of a regular gauge fixing is assumed. -/
theorem exists_alignment (u v : Slice n) :
    ∃ h : SliceGauge n Q, ∀ k : SliceGauge n Q,
      inputCost n u (gaugeSlice h v) ≤ inputCost n u (gaugeSlice k v) := by
  obtain ⟨h, _, hh⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (SliceGauge n Q)).Nonempty)
    (alignment_cost_continuous n u v).continuousOn
  exact ⟨h, fun k => hh (Set.mem_univ k)⟩

def alignment (u v : Slice n) : SliceGauge n Q := (exists_alignment n u v).choose

def orbitCost (u v : Slice n) : ℝ := inputCost n u (gaugeSlice (alignment n u v) v)

theorem orbitCost_nonneg (u v : Slice n) : 0 ≤ orbitCost n u v :=
  inputCost_nonneg n u _

theorem orbitCost_le (u v : Slice n) (h : SliceGauge n Q) :
    orbitCost n u v ≤ inputCost n u (gaugeSlice h v) :=
  (exists_alignment n u v).choose_spec h

theorem orbitCost_le_inputCost (u v : Slice n) : orbitCost n u v ≤ inputCost n u v := by
  simpa only [gaugeSlice_one] using orbitCost_le n u v 1

theorem orbitCost_eq_zero_iff (u v : Slice n) :
    orbitCost n u v = 0 ↔ ∃ h : SliceGauge n Q, u = gaugeSlice h v := by
  constructor
  · intro hz
    exact ⟨alignment n u v, (inputCost_eq_zero_iff n u _).mp hz⟩
  · rintro ⟨h, hh⟩
    apply le_antisymm _ (orbitCost_nonneg n u v)
    calc
      _ ≤ inputCost n u (gaugeSlice h v) := orbitCost_le n u v h
      _ = 0 := by rw [← hh, inputCost_self]

theorem orbitCost_self (u : Slice n) : orbitCost n u u = 0 :=
  (orbitCost_eq_zero_iff n u u).mpr ⟨1, (gaugeSlice_one u).symm⟩

theorem inverse_alignment_cost (h : SliceGauge n Q) (u v : Slice n) :
    inputCost n v (gaugeSlice h⁻¹ u) = inputCost n u (gaugeSlice h v) := by
  rw [← inputCost_gauge n h v (gaugeSlice h⁻¹ u), ← gaugeSlice_mul,
    mul_inv_cancel, gaugeSlice_one]
  exact inputCost_symm n _ _

theorem orbitCost_le_reverse (u v : Slice n) : orbitCost n u v ≤ orbitCost n v u := by
  have h := orbitCost_le n u v (alignment n v u)⁻¹
  rw [inverse_alignment_cost n (alignment n v u) v u] at h
  exact h

theorem orbitCost_symm (u v : Slice n) : orbitCost n u v = orbitCost n v u :=
  le_antisymm (orbitCost_le_reverse n u v) (orbitCost_le_reverse n v u)

theorem orbitCost_triangle (u v w : Slice n) :
    orbitCost n u w ≤ orbitCost n u v + orbitCost n v w := by
  let g := alignment n u v
  let h := alignment n v w
  calc
    _ ≤ inputCost n u (gaugeSlice (g * h) w) := orbitCost_le n u w (g * h)
    _ = inputCost n u (gaugeSlice g (gaugeSlice h w)) := by rw [gaugeSlice_mul]
    _ ≤ inputCost n u (gaugeSlice g v) +
        inputCost n (gaugeSlice g v) (gaugeSlice g (gaugeSlice h w)) :=
      inputCost_triangle n u (gaugeSlice g v) (gaugeSlice g (gaugeSlice h w))
    _ = _ := by rw [inputCost_gauge n g v (gaugeSlice h w)]; rfl

theorem orbitCost_gauge_right (u v : Slice n) (h : SliceGauge n Q) :
    orbitCost n u (gaugeSlice h v) = orbitCost n u v := by
  have hz : orbitCost n (gaugeSlice h v) v = 0 :=
    (orbitCost_eq_zero_iff n _ v).mpr ⟨h, rfl⟩
  have hz' : orbitCost n v (gaugeSlice h v) = 0 := by rw [orbitCost_symm]; exact hz
  have ha := orbitCost_triangle n u v (gaugeSlice h v)
  have hb := orbitCost_triangle n u (gaugeSlice h v) v
  rw [hz', add_zero] at ha
  rw [hz, add_zero] at hb
  exact le_antisymm ha hb

theorem orbitCost_gauge_left (u v : Slice n) (h : SliceGauge n Q) :
    orbitCost n (gaugeSlice h u) v = orbitCost n u v := by
  rw [orbitCost_symm n (gaugeSlice h u) v, orbitCost_gauge_right, orbitCost_symm n v u]

/-- The actual response is controlled by physical orbit distance, with a constructed optimizer. -/
theorem rowMean_orbit_bound (β : ℝ) (hβ : 0 ≤ β) (u u' : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hlo : lo ≤ hi) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    |rowMean n β hβ f u - rowMean n β hβ f u'| ≤
      β * (hi - lo) * orbitCost n u u' := by
  have h := rowMean_difference_bound n β hβ u (gaugeSlice (alignment n u u') u')
    f lo hi hlo hf
  rw [rowMean_gauge n β hβ f hinv] at h
  exact h

/-- A chosen local alignment charges only its remaining actual changed links. -/
theorem rowMean_local_alignment_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n) (g : SliceGauge n Q)
    (hu : ∀ e, e ∉ S → u e = gaugeSlice g u' e)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hlo : lo ≤ hi) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    |rowMean n β hβ f u - rowMean n β hβ f u'| ≤
      β * (hi - lo) * ∑ e ∈ S, ‖(u e : Quaternion ℝ) - (gaugeSlice g u' e : Quaternion ℝ)‖ := by
  have h := rowMean_difference_bound n β hβ u (gaugeSlice g u') f lo hi hlo hf
  rw [rowMean_gauge n β hβ f hinv, inputCost_eq_support n S u _ hu] at h
  exact h

/-- The normalized collective covariance has the same bound, with its actual mean tilt. -/
theorem normalized_covariance_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hlo : lo ≤ hi) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    |tiltCovariance n β hβ S u u' f /
      (∫ v, tilt n β S u u' v ∂rowLaw n β hβ u')| ≤
        β * (hi - lo) * orbitCost n u u' := by
  rw [covariance_eq_response_mul n β hβ S u u' hu,
    mul_div_cancel_right₀ _ (tilt_mean_pos n β hβ S u u' hu).ne']
  exact rowMean_orbit_bound n β hβ u u' f hinv lo hi hlo hf

theorem covariance_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' : Slice n)
    (hu : ∀ e, e ∉ S → u e = u' e)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hlo : lo ≤ hi) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    |tiltCovariance n β hβ S u u' f| ≤ β * (hi - lo) * orbitCost n u u' *
      (∫ v, tilt n β S u u' v ∂rowLaw n β hβ u') := by
  have hm := tilt_mean_pos n β hβ S u u' hu
  have h := normalized_covariance_bound n β hβ S u u' hu f hinv lo hi hlo hf
  rw [abs_div, abs_of_pos hm] at h
  exact (div_le_iff₀ hm).mp h

/-- This controls the original full physical transfer response, with its original time step. -/
theorem full_transfer_orbit_bound (β : ℝ) (hβ : 0 ≤ β) (u u' : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hlo : lo ≤ hi) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    |(∫ v, WilsonGroundLocalComparison.transition n β hβ u v * f v ∂measure n) -
      (∫ v, WilsonGroundLocalComparison.transition n β hβ u' v * f v ∂measure n)| ≤
        β * (hi - lo) * orbitCost n u u' := by
  rw [← rowMean_eq_full n β hβ f hinv, ← rowMean_eq_full n β hβ f hinv]
  exact rowMean_orbit_bound n β hβ u u' f hinv lo hi hlo hf

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeOrbitResponse
