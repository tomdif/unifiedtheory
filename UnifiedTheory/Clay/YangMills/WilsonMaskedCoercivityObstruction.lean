/- Retaining almost all good links is not enough for direct coercivity.
Every sufficiently small masked rotation leaves an actual nonconstant
physical plaquette bump unchanged. Defect directions must also be controlled. -/
import UnifiedTheory.Clay.YangMills.WilsonMaskedCurvature
import UnifiedTheory.Clay.YangMills.WilsonSpatialSourceObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMaskedCoercivityObstruction
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonDefectMask
open WilsonJointRotation WilsonPhysicalVariance WilsonGroundHeatBath
open WilsonSingleLinkStaples (character)
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem defect_frozen (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (q u : Slice n)
    (p : Plaquette n) (hp : δ ^ 2 < defect n u p)
    (hq : ∀ e, e ∉ good n S δ u → q e = 1) : defect n (q*u) p = defect n u p := by
  apply defect_congr n p
  intro e he
  have hn : e ∉ good n S δ u := fun h => (not_lt_of_ge (good_touches n S δ u e h p he).2) hp
  simp only [Pi.mul_apply, hq e hn, one_mul]

omit [NeZero n] in
theorem defect_change (q u : Slice n) (p : Plaquette n) (r : ℝ)
    (hr : ∀ e ∈ support n p, displacement n q e ≤ r) :
    |defect n (q*u) p-defect n u p| ≤ 8*r := by
  have ht := WilsonPlaquetteTransport.character_difference
    (spatialHolonomy (q*u) p.1 p.2.1.1 p.2.1.2) (spatialHolonomy u p.1 p.2.1.1 p.2.1.2)
  have hd := (holonomy_variation n q u p.1 p.2.1.1 p.2.1.2).1
  simp only [mul_one] at hd
  have h1 := hr (p.1,p.2.1.1) (by simp [support])
  have h2 := hr (spatialStep n p.1 p.2.1.1,p.2.1.2) (by simp [support])
  have h3 := hr (spatialStep n p.1 p.2.1.2,p.2.1.1) (by simp [support])
  have h4 := hr (p.1,p.2.1.2) (by simp [support])
  unfold WilsonPlaquetteTransport.chord at ht
  have he : defect n (q*u) p-defect n u p =
      -((character (spatialHolonomy (q*u) p.1 p.2.1.1 p.2.1.2)).re-
        (character (spatialHolonomy u p.1 p.2.1.1 p.2.1.2)).re) := by unfold defect; ring
  rw [he, abs_neg]
  linarith

def base : Plaquette n := (0,⟨(0,1),by decide⟩)

omit [NeZero n] in
theorem base_defect (u : Slice n) : defect n u (base n) =
    WilsonSpatialSourceObstruction.defect n u := rfl

/-- Already bad plaquettes are frozen. Below the bad threshold, the small
rotation cannot cross the separate bump threshold. -/
theorem bump_invariant (S : Finset (SpatialVertex n × Fin 3)) (δ r t : ℝ)
    (hgap : δ ^ 2 + 8 * r ≤ t) (q u : Slice n)
    (hq : ∀ e, e ∉ good n S δ u → q e = 1) (hr : ∀ e, displacement n q e ≤ r) :
    WilsonSpatialSourceObstruction.bump n t (q*u) = WilsonSpatialSourceObstruction.bump n t u := by
  have hr0 : 0 ≤ r := (norm_nonneg ((q (0,0) : ℍ)-1)).trans (hr (0,0))
  by_cases hp : δ^2 < defect n u (base n)
  · have he := defect_frozen n S δ q u (base n) hp hq
    simp only [base_defect] at he
    change max 0 (WilsonSpatialSourceObstruction.defect n (q*u)-t) =
      max 0 (WilsonSpatialSourceObstruction.defect n u-t)
    rw [he]
  · have hh := defect_change n q u (base n) r (fun e _ => hr e)
    have h0 := le_of_not_gt hp
    have h1 := (abs_le.mp hh).2
    have ha : defect n u (base n) ≤ t := by linarith
    have hb : defect n (q*u) (base n) ≤ t := by linarith
    change max 0 (WilsonSpatialSourceObstruction.defect n (q*u)-t) =
      max 0 (WilsonSpatialSourceObstruction.defect n u-t)
    simp only [base_defect] at ha hb
    rw [max_eq_left (sub_nonpos.mpr hb), max_eq_left (sub_nonpos.mpr ha)]

theorem unit_bump_invariant (S : Finset (SpatialVertex n × Fin 3)) (q u : Slice n)
    (hq : ∀ e, e ∉ good n S (1 / 32) u → q e = 1)
    (hr : ∀ e, displacement n q e ≤ 1 / 16) :
    WilsonSpatialSourceObstruction.bump n 1 (q*u) = WilsonSpatialSourceObstruction.bump n 1 u :=
  bump_invariant n S (1 / 32) (1 / 16) 1 (by norm_num) q u hq hr

/-- Arbitrary masked rotations cannot decrease a bump supported above the
defect threshold. A stationary update therefore cannot change it almost surely. -/
theorem bump_monotone (S : Finset (SpatialVertex n × Fin 3)) (δ t : ℝ) (ht : δ ^ 2 ≤ t)
    (q u : Slice n) (hq : ∀ e, e ∉ good n S δ u → q e = 1) :
    WilsonSpatialSourceObstruction.bump n t u ≤ WilsonSpatialSourceObstruction.bump n t (q*u) := by
  by_cases hp : δ^2 < defect n u (base n)
  · have he := defect_frozen n S δ q u (base n) hp hq
    simp only [base_defect] at he
    change max 0 (WilsonSpatialSourceObstruction.defect n u-t) ≤
      max 0 (WilsonSpatialSourceObstruction.defect n (q*u)-t)
    rw [he]
  · have ha := (le_of_not_gt hp).trans ht
    rw [base_defect] at ha
    change max 0 (WilsonSpatialSourceObstruction.defect n u-t) ≤ max 0 _
    rw [max_eq_left (sub_nonpos.mpr ha)]
    exact le_max_left _ _

theorem stationary_bump_ae (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (δ t : ℝ) (ht : δ ^ 2 ≤ t)
    (q : Slice n → Slice n) (hq : ∀ u e, e ∉ good n S δ u → q u e = 1)
    (hp : MeasurePreserving (fun u => q u * u) (groundLaw n β hβ) (groundLaw n β hβ)) :
    (fun u => WilsonSpatialSourceObstruction.bump n t (q u * u)) =ᵐ[groundLaw n β hβ]
      WilsonSpatialSourceObstruction.bump n t := by
  letI := groundLaw_probability n β hβ
  have hi := CompactDensityEntropy.continuous_integrable (groundLaw n β hβ) _
    (WilsonSpatialSourceObstruction.bump n t).continuous
  have hj := hp.integrable_comp_of_integrable hi
  have he := integral_map_of_stronglyMeasurable (μ := groundLaw n β hβ) hp.measurable
    (WilsonSpatialSourceObstruction.bump n t).continuous.stronglyMeasurable
  rw [hp.map_eq] at he
  exact ((integral_eq_iff_of_ae_le hi hj
    (Filter.Eventually.of_forall (fun u => bump_monotone n S δ t ht (q u) u (hq u)))).mp he).symm

variable {I : Type*} [Fintype I]

/-- This response form makes no unproved stationarity claim for variable rotations. -/
def energy (β : ℝ) (hβ : 0 ≤ β) (q : I → Slice n → Slice n) (f : C(Slice n, ℝ)) : ℝ :=
  ∑ i, ∫ u, (f (q i u * u)-f u)^2 ∂groundLaw n β hβ

theorem bump_energy_zero (β : ℝ) (hβ : 0 ≤ β)
    (S : I → Finset (SpatialVertex n × Fin 3)) (q : I → Slice n → Slice n)
    (hq : ∀ i u e, e ∉ good n (S i) (1 / 32) u → q i u e = 1)
    (hr : ∀ i u e, displacement n (q i u) e ≤ 1 / 16) :
    energy n β hβ q (WilsonSpatialSourceObstruction.bump n 1) = 0 := by
  have hh (i : I) (u : Slice n) := unit_bump_invariant n (S i) (q i u) u (hq i u) (hr i u)
  simp only [energy, hh, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero,
    Finset.sum_const_zero]

/-- Stationarity supplies the obstruction without a small-rotation restriction. -/
theorem stationary_bump_energy_zero (β : ℝ) (hβ : 0 ≤ β)
    (S : I → Finset (SpatialVertex n × Fin 3)) (q : I → Slice n → Slice n)
    (hq : ∀ i u e, e ∉ good n (S i) (1 / 32) u → q i u e = 1)
    (hp : ∀ i, MeasurePreserving (fun u => q i u * u) (groundLaw n β hβ) (groundLaw n β hβ)) :
    energy n β hβ q (WilsonSpatialSourceObstruction.bump n 1) = 0 := by
  unfold energy
  apply Finset.sum_eq_zero
  intro i _
  have ha := stationary_bump_ae n β hβ (S i) (1 / 32) 1 (by norm_num) (q i) (hq i) (hp i)
  calc
    _ = ∫ _u : Slice n, (0 : ℝ) ∂groundLaw n β hβ := by
      apply integral_congr_ae
      filter_upwards [ha] with u hu
      rw [hu, sub_self]
      norm_num
    _ = 0 := integral_zero _ _

variable [Fact (1 < n)]

/-- No direct all-physical variance comparison can discard the removed
plaquette directions and use only this small masked response family. -/
theorem no_variance_comparison (β : ℝ) (hβ : 0 ≤ β)
    (S : I → Finset (SpatialVertex n × Fin 3)) (q : I → Slice n → Slice n)
    (hq : ∀ i u e, e ∉ good n (S i) (1 / 32) u → q i u e = 1)
    (hr : ∀ i u e, displacement n (q i u) e ≤ 1 / 16) (C : ℝ) :
    ¬∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance n β hβ f ≤ C*energy n β hβ q f := by
  intro h
  have hp := WilsonGroundVarianceBudget.variance_positive n β hβ
    (WilsonSpatialSourceObstruction.bump n 1) _ _
    (WilsonSpatialSourceObstruction.bump_nonconstant n 1 (by norm_num) (by norm_num))
  have hh := h (WilsonSpatialSourceObstruction.bump n 1)
    (WilsonSpatialSourceObstruction.bump_gauge n 1)
  rw [bump_energy_zero n β hβ S q hq hr, mul_zero] at hh
  linarith


/-- A stationary family of masked updates is not repaired by allowing large
rotations: the same physical witness has positive variance and zero energy. -/
theorem no_stationary_variance_comparison (β : ℝ) (hβ : 0 ≤ β)
    (S : I → Finset (SpatialVertex n × Fin 3)) (q : I → Slice n → Slice n)
    (hq : ∀ i u e, e ∉ good n (S i) (1 / 32) u → q i u e = 1)
    (hp : ∀ i, MeasurePreserving (fun u => q i u * u) (groundLaw n β hβ) (groundLaw n β hβ))
    (C : ℝ) :
    ¬∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance n β hβ f ≤ C*energy n β hβ q f := by
  intro h
  have hv := WilsonGroundVarianceBudget.variance_positive n β hβ
    (WilsonSpatialSourceObstruction.bump n 1) _ _
    (WilsonSpatialSourceObstruction.bump_nonconstant n 1 (by norm_num) (by norm_num))
  have hh := h (WilsonSpatialSourceObstruction.bump n 1)
    (WilsonSpatialSourceObstruction.bump_gauge n 1)
  rw [stationary_bump_energy_zero n β hβ S q hq hp, mul_zero] at hh
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonMaskedCoercivityObstruction
