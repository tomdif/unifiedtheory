/- The actual retained response changes by an integrated middle covariance
when an endpoint link is rotated. The extra source tilt is kept explicitly;
no spatial decay or closure of a two-source hierarchy is inferred. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryMiddleCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMiddleSourceTransport
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonBoundaryConnected
open WilsonBoundaryMiddleCovariance WilsonSymmetricLinkChange

variable (n : ℕ) [NeZero n]

/-- The endpoint perturbation is another literal local kinetic insertion. -/
theorem endpoint_action_shift (β : ℝ) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q) (s t : ℝ) (v : Slice n) :
    WilsonTiltedMiddleAction.action n β u (shift n b p w) e d q r s t v =
      WilsonTiltedMiddleAction.action n β u w e d q r s t v - source n β b p w v := by
  unfold WilsonTiltedMiddleAction.action WilsonMiddleBridge.action source
  rw [WilsonTiltedMiddleAction.kinetic_symmetric n v w,
    WilsonTiltedMiddleAction.kinetic_symmetric n v (shift n b p w)]
  ring

theorem endpoint_expectation_one (β : ℝ) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q) (s t : ℝ) (F : Slice n → ℝ) :
    CompactGibbsSource.expectation (WilsonSlabOperator.measure n)
      (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) F 1 =
      response n β u e d q r s t F (shift n b p w) := by
  rw [response_integral]
  unfold CompactGibbsSource.expectation
  congr 2
  funext v
  simp only [CompactGibbsSource.action, one_mul, endpoint_action_shift]

theorem endpoint_expectation_zero (β : ℝ) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q) (s t : ℝ) (F : Slice n → ℝ) :
    CompactGibbsSource.expectation (WilsonSlabOperator.measure n)
      (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) F 0 =
      response n β u e d q r s t F w := by
  rw [response_integral]
  unfold CompactGibbsSource.expectation
  congr 2
  funext v
  simp only [CompactGibbsSource.action, zero_mul, sub_zero]

/-- The retained response really propagates through an additional sourced
middle covariance. All three tilts remain inside its normalized law. -/
theorem endpoint_difference (β : ℝ) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q) (s t : ℝ)
    (F : Slice n → ℝ) (hF : Continuous F) :
    response n β u e d q r s t F (shift n b p w) - response n β u e d q r s t F w =
      ∫ a in (0 : ℝ)..1, CompactGibbsSource.covariance (WilsonSlabOperator.measure n)
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w)
        F (source n β b p w) a := by
  have h := CompactConnectedRectangle.source_difference (WilsonSlabOperator.measure n)
    (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) F
    (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
    (source_continuous n β b p w) hF
  rw [endpoint_expectation_one, endpoint_expectation_zero] at h
  exact h.symm

/-- The additional endpoint tilt has its own exact local curvature correction. -/
theorem transport_action_second (β : ℝ) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q) (s t h : ℝ) (v a : Slice n) :
    CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
      (source n β b p w) h (a * v) +
    CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
      (source n β b p w) h (a⁻¹ * v) -
    2 * CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
      (source n β b p w) h v =
      WilsonTiltedMiddleAction.action n β u w e d q r s t (a * v) +
      WilsonTiltedMiddleAction.action n β u w e d q r s t (a⁻¹ * v) -
      2 * WilsonTiltedMiddleAction.action n β u w e d q r s t v +
      h * (WilsonJointRotation.displacement n a b) ^ 2 * source n β b p w v := by
  have hb := WilsonTiltedMiddleAction.source_second n β b p w v a
  unfold CompactGibbsSource.action
  linear_combination -h * hb

/-- The entire extra source interval preserves a positive small-field
coefficient for beta greater than two, even when its link overlaps an earlier insertion. -/
theorem transport_action_second_small (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : Quaternion ℝ) - 1‖ ≤ 1)
    (hr : β * ‖(r : Quaternion ℝ) - 1‖ ≤ 1)
    (hp : β * ‖(p : Quaternion ℝ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (v a : Slice n)
    (hflat : ∀ (x : SpatialVertex n) (z : SpatialPlane),
      ‖((spatialHolonomy v x z.1.1 z.1.2 : Q) : Quaternion ℝ) - 1‖ ≤ 1 / 32)
    (hu : ∀ c, ‖(v c : Quaternion ℝ) - (u c : Quaternion ℝ)‖ ^ 2 ≤ 1 / 2)
    (hw : ∀ c, ‖(v c : Quaternion ℝ) - (w c : Quaternion ℝ)‖ ^ 2 ≤ 1 / 2) :
    (2 * β - 4) * WilsonJointRotation.cost n a ≤
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h (a * v) +
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h (a⁻¹ * v) -
      2 * CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h v := by
  have hbase := WilsonTiltedMiddleAction.action_second_small n β hβ u w e d hed
    q r hq hr s t hs ht v a hflat hu hw
  have hb : -2 ≤ source n β b p w v := by
    have hbound := (abs_le.mp (source_bound n β hβ b p w v)).1
    linarith
  have hsour : -2 ≤ h * source n β b p w v := by nlinarith only [hb, hh.1, hh.2]
  have hm := mul_le_mul_of_nonneg_right hsour
    (sq_nonneg (WilsonJointRotation.displacement n a b))
  have hc : (WilsonJointRotation.displacement n a b) ^ 2 ≤ WilsonJointRotation.cost n a :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  rw [transport_action_second]
  nlinarith only [hbase, hm, hc]

end
end UnifiedTheory.Clay.YangMills.WilsonMiddleSourceTransport
