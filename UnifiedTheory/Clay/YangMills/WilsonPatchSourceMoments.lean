/- The actual two- and three-source local-energy terms are compared to
the previously constructed unsourced middle bridge. The factors exp(8)
and exp(12) include both partitions and are independent of spatial volume.
The unsourced moment and retained covariances still require estimates. -/
import UnifiedTheory.Clay.YangMills.GibbsPositiveMomentComparison
import UnifiedTheory.Clay.YangMills.WilsonPatchAveragedCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchSourceMoments
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonBoundaryConnected
open WilsonPatchComplementTail WilsonPatchLocalEnergy WilsonPatchAveragedCovariance
open WilsonPatchEligibility WilsonPatchExteriorDecomposition
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- The reference measure is exactly the existing middle bridge with its
true normalized product of two interacting raw kernels. -/
theorem bridge_law (β : ℝ) (u w : Slice n) :
    CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
      (WilsonMiddleBridge.action n β u w) = WilsonMiddleBridge.law n β u w := by
  unfold WilsonMiddleBridge.law
  have he := WilsonMiddleBridge.weight_action n β u w
  have hw : WilsonMiddleBridge.weight n β u w = fun v =>
      (spatialWeight WilsonSingleLinkStaples.character β 2 u *
        spatialWeight WilsonSingleLinkStaples.character β 2 w) *
          Real.exp (-WilsonMiddleBridge.action n β u w v) := funext he
  rw [hw]
  exact (GibbsConstantShift.weightedLaw_const_mul (WilsonSlabOperator.measure n)
    (fun v => Real.exp (-WilsonMiddleBridge.action n β u w v))
    (WilsonMiddleBridge.action_continuous n β u w).neg.rexp.measurable
    _ (mul_pos (Real.exp_pos _) (Real.exp_pos _))).symm

theorem two_action_distance (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (v : Slice n) :
    |WilsonMiddleBridge.action n β u w v -
      WilsonTiltedMiddleAction.action n β u w e d q r s t v| ≤ 4 := by
  have he := source_strength_bound n β hβ e q hq u v s hs
  have hd := source_strength_bound n β hβ d r hr u v t ht
  rw [show WilsonMiddleBridge.action n β u w v -
      WilsonTiltedMiddleAction.action n β u w e d q r s t v =
      s * source n β e q u v + t * source n β d r u v by
        unfold WilsonTiltedMiddleAction.action; ring]
  exact (abs_add_le _ _).trans (by linarith only [he, hd])

theorem transport_action_distance (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (v : Slice n) :
    |WilsonMiddleBridge.action n β u w v -
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h v| ≤ 6 := by
  have he := two_action_distance n β hβ u w e d q r hq hr s t hs ht v
  have hb := source_strength_bound n β hβ b p hp w v h hh
  rw [show WilsonMiddleBridge.action n β u w v -
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h v =
      (WilsonMiddleBridge.action n β u w v -
        WilsonTiltedMiddleAction.action n β u w e d q r s t v) +
          h * source n β b p w v by unfold CompactGibbsSource.action; ring]
  exact (abs_add_le _ _).trans (by linarith only [he, hb])

/-- F may be the local energy times any nonnegative continuous response
weight. The source links may coincide. -/
theorem two_source_moment (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (F : Slice n → ℝ) (hF : Continuous F) (hF0 : ∀ v, 0 ≤ F v) :
    (∫ v, F v ∂CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
      (WilsonTiltedMiddleAction.action n β u w e d q r s t)) ≤
        Real.exp 8 * ∫ v, F v ∂WilsonMiddleBridge.law n β u w := by
  have hb := GibbsPositiveMomentComparison.positive_moment (WilsonSlabOperator.measure n)
    _ _ F (WilsonMiddleBridge.action_continuous n β u w)
    (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t) hF hF0 4
    (two_action_distance n β hβ u w e d q r hq hr s t hs ht)
  rw [bridge_law] at hb
  norm_num only [show (2 : ℝ) * 4 = 8 by norm_num] at hb
  exact hb

theorem transport_moment (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (F : Slice n → ℝ) (hF : Continuous F) (hF0 : ∀ v, 0 ≤ F v) :
    (∫ v, F v ∂CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
      (CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h)) ≤
      Real.exp 12 * ∫ v, F v ∂WilsonMiddleBridge.law n β u w := by
  have hb := GibbsPositiveMomentComparison.positive_moment (WilsonSlabOperator.measure n)
    _ _ F (WilsonMiddleBridge.action_continuous n β u w)
    (CompactGibbsSource.action_continuous _ _
      (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
      (source_continuous n β b p w) h) hF hF0 6
    (transport_action_distance n β hβ u w e d b q r p hq hr hp s t h hs ht hh)
  rw [bridge_law] at hb
  norm_num only [show (2 : ℝ) * 6 = 12 by norm_num] at hb
  exact hb

theorem two_source_energy (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) :
    energyMoment n S u w (WilsonTiltedMiddleAction.action n β u w e d q r s t) ≤
      Real.exp 8 * ∫ v, localEnergy n S v u w ∂WilsonMiddleBridge.law n β u w :=
  two_source_moment n β hβ u w e d q r hq hr s t hs ht _
    (WilsonPatchBackgroundReset.local_continuous n S u w) (fun v => local_nonneg n S v u w)

theorem transport_energy (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (S : Finset (SpatialVertex n × Fin 3)) :
    energyMoment n S u w
      (CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h) ≤
      Real.exp 12 * ∫ v, localEnergy n S v u w ∂WilsonMiddleBridge.law n β u w :=
  transport_moment n β hβ u w e d b q r p hq hr hp s t h hs ht hh _
    (WilsonPatchBackgroundReset.local_continuous n S u w) (fun v => local_nonneg n S v u w)

/-- The response weight stays inside the unsourced moment. This does
not replace a weighted bad event by its unweighted probability. -/
theorem weighted_coverage (β : ℝ) (S : Finset (SpatialVertex n × Fin 3))
    (u w : Slice n) (A W : Slice n → ℝ) (hA : Continuous A) (hW : Continuous W)
    (hW0 : ∀ v, 0 ≤ W v) (M : ℝ)
    (hAM : ∀ v, |WilsonMiddleBridge.action n β u w v - A v| ≤ M) :
    (∫ v in (WilsonPatchBackgroundReset.outsideOf n S) ⁻¹'
        WilsonPatchCoverage.ineligible n S u w,
      W v ∂CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) ≤
      ((70 / threshold) * Real.exp (2 * M)) *
        ∫ v, localEnergy n S v u w * W v ∂WilsonMiddleBridge.law n β u w := by
  letI := CompactGibbsContinuity.law_probability (WilsonSlabOperator.measure n) A hA
  have hc := WilsonPatchCoverage.weighted_coverage n S u w
    (CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) W hW hW0
  have hm := GibbsPositiveMomentComparison.positive_moment (WilsonSlabOperator.measure n)
    _ A (fun v => localEnergy n S v u w * W v)
    (WilsonMiddleBridge.action_continuous n β u w) hA
    ((WilsonPatchBackgroundReset.local_continuous n S u w).mul hW)
    (fun v => mul_nonneg (local_nonneg n S v u w) (hW0 v)) M hAM
  rw [bridge_law] at hm
  exact (hc.trans (mul_le_mul_of_nonneg_left hm
    (div_nonneg (by norm_num) threshold_pos.le))).trans_eq (by ring)

theorem connected_bound (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) :
    |WilsonBoundaryMiddleCovariance.middleCovariance n β u w e d q r s t
      (source n β e q u) (source n β d r u)| ≤
      budget n β S 1 4 + ((280 / threshold) * Real.exp 8) *
        (∫ v, localEnergy n S v u w ∂WilsonMiddleBridge.law n β u w) +
      |retainedCovariance n S (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β e q u) (source n β d r u)| := by
  have hc := WilsonPatchAveragedCovariance.connected_bound n β hβ u w e d hed q r
    hq hr s t hs ht S
  have hm := two_source_energy n β (by linarith) u w e d q r hq hr s t hs ht S
  apply hc.trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  exact (mul_le_mul_of_nonneg_left hm
    (div_nonneg (by norm_num) threshold_pos.le)).trans_eq (by ring)

theorem transport_bound (β : ℝ) (hβ : 2 < β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (S : Finset (SpatialVertex n × Fin 3)) :
    |GibbsCrossCovariance.covariance (CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
        (CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
          (source n β b p w) h)) (source n β e q u) (source n β b p w)| ≤
      budget n β S 2 6 + ((280 / threshold) * Real.exp 12) *
        (∫ v, localEnergy n S v u w ∂WilsonMiddleBridge.law n β u w) +
      |retainedCovariance n S
        (CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
          (source n β b p w) h) (source n β e q u) (source n β b p w)| := by
  have hc := WilsonPatchAveragedCovariance.transport_bound n β hβ u w e d b hed q r p
    hq hr hp s t h hs ht hh S
  have hm := transport_energy n β (by linarith) u w e d b q r p hq hr hp s t h hs ht hh S
  apply hc.trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  exact (mul_le_mul_of_nonneg_left hm
    (div_nonneg (by norm_num) threshold_pos.le)).trans_eq (by ring)

end
end UnifiedTheory.Clay.YangMills.WilsonPatchSourceMoments
