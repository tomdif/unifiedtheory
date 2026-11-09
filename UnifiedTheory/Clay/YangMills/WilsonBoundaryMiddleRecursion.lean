/- Exact one-step exposure of the finite Wilson boundary recursion under
both source tilts. The middle conditional has an explicit action; the true
propagated endpoint remains in the joint law and its retained marginal. -/
import UnifiedTheory.Clay.YangMills.WilsonTiltedMiddleAction
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance
import UnifiedTheory.Clay.YangMills.GibbsConstantShift

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryMiddleRecursion
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonBoundaryPointwise
open WilsonBoundaryConnected WilsonBoundaryMixedLimit CompactDensityEntropy
open WilsonSingleLinkStaples (character character_continuous)

variable (n : ℕ) [NeZero n]

def outputAction (β : ℝ) (j : ℕ) (u : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) : Slice n → ℝ :=
  CompactGibbsSource.action
    (CompactGibbsSource.action (boundaryAction n β j u) (source n β e q u) s)
    (source n β d r u) t

theorem outputAction_continuous (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) :
    Continuous (outputAction n β j u e d q r s t) :=
  CompactGibbsSource.action_continuous _ _
    (CompactGibbsSource.action_continuous _ _ (boundaryAction_continuous n β j u)
      (source_continuous n β e q u) s) (source_continuous n β d r u) t

def jointAction (β : ℝ) (j : ℕ) (u : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) (z : Slice n × Slice n) : ℝ :=
  WilsonTiltedMiddleAction.action n β u z.1 e d q r s t z.2 -
    Real.log (spatialWeight character β 2 z.1) - Real.log (boundaryMessage n β j z.1)

theorem jointAction_continuous (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) :
    Continuous (jointAction n β j u e d q r s t) := by
  have hc := character_continuous
  have hw : Continuous (fun z : Slice n × Slice n => spatialWeight character β 2 z.1) := by
    unfold spatialWeight potential spatialHolonomy
    fun_prop
  exact ((WilsonTiltedMiddleAction.action_joint_continuous n β u e d q r s t).sub
    (hw.log (fun _ => (Real.exp_pos _).ne'))).sub
    (((boundaryMessage n β j).continuous.comp continuous_fst).log
      (fun z => (boundaryMessage_pos n β j z.1).ne'))

theorem middle_weight (β : ℝ) (u w : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) (v : Slice n) :
    Real.exp (-WilsonTiltedMiddleAction.action n β u w e d q r s t v) =
      kineticWeight character β 2 u v * (spatialWeight character β 2 v) ^ 2 *
        kineticWeight character β 2 v w *
          Real.exp (s * source n β e q u v + t * source n β d r u v) := by
  unfold WilsonTiltedMiddleAction.action WilsonMiddleBridge.action kineticWeight spatialWeight
  simp only [pow_two, ← Real.exp_add]
  congr 1
  rw [WilsonTiltedMiddleAction.kinetic_symmetric n v u]
  ring

/-- The full endpoint factor is present before conditioning. -/
theorem joint_weight (β : ℝ) (j : ℕ) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) (v : Slice n) :
    Real.exp (-jointAction n β j u e d q r s t (w, v)) =
      (spatialWeight character β 2 w * boundaryMessage n β j w) *
        Real.exp (-WilsonTiltedMiddleAction.action n β u w e d q r s t v) := by
  rw [show -jointAction n β j u e d q r s t (w, v) =
    (Real.log (spatialWeight character β 2 w) + Real.log (boundaryMessage n β j w)) +
      -WilsonTiltedMiddleAction.action n β u w e d q r s t v by unfold jointAction; ring,
    Real.exp_add, Real.exp_add,
    Real.exp_log (show 0 < spatialWeight character β 2 w from Real.exp_pos _),
    Real.exp_log (boundaryMessage_pos n β j w)]

/-- Integrating the exposed endpoint gives exactly the next finite message,
throughout the two-source rectangle and for arbitrary real source strengths. -/
theorem joint_weight_fiber (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) (v : Slice n) :
    (∫ w, Real.exp (-jointAction n β j u e d q r s t (w, v))
      ∂WilsonSlabOperator.measure n) = Real.exp (-outputAction n β (j + 1) u e d q r s t v) := by
  simp_rw [joint_weight, middle_weight]
  have he (w : Slice n) :
      (spatialWeight character β 2 w * boundaryMessage n β j w) *
        (kineticWeight character β 2 u v * (spatialWeight character β 2 v) ^ 2 *
          kineticWeight character β 2 v w *
            Real.exp (s * source n β e q u v + t * source n β d r u v)) =
      (kineticWeight character β 2 u v * (spatialWeight character β 2 v) ^ 2 *
        Real.exp (s * source n β e q u v + t * source n β d r u v)) *
        (kineticWeight character β 2 v w * spatialWeight character β 2 w *
          boundaryMessage n β j w) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  change _ * boundaryPartition n β j v =
    CompactGibbsSource.weight
      (CompactGibbsSource.action (boundaryAction n β (j + 1) u) (source n β e q u) s)
      (source n β d r u) t v
  rw [tilted_weight, boundaryMessage_partition]
  ring

theorem joint_unnormalized (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ)
    (H : Slice n → ℝ) (hH : Continuous H) :
    (∫ z : Slice n × Slice n, Real.exp (-jointAction n β j u e d q r s t z) * H z.2
      ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) =
      ∫ v, Real.exp (-outputAction n β (j + 1) u e d q r s t v) * H v
        ∂WilsonSlabOperator.measure n := by
  have hc : Continuous (fun z : Slice n × Slice n =>
      Real.exp (-jointAction n β j u e d q r s t z) * H z.2) :=
    ((jointAction_continuous n β j u e d q r s t).neg.rexp).mul (hH.comp continuous_snd)
  rw [integral_prod_symm _ (continuous_integrable _ _ hc)]
  simp_rw [integral_mul_const, joint_weight_fiber]

theorem joint_partition (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) :
    (∫ z : Slice n × Slice n, Real.exp (-jointAction n β j u e d q r s t z)
      ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) =
      ∫ v, Real.exp (-outputAction n β (j + 1) u e d q r s t v)
        ∂WilsonSlabOperator.measure n := by
  simpa only [mul_one] using joint_unnormalized n β j u e d q r s t (fun _ => 1)
    continuous_const

/-- Equality of the normalized observable integrals, with the actual common partition. -/
theorem joint_integral (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ)
    (H : Slice n → ℝ) (hH : Continuous H) :
    (∫ z : Slice n × Slice n, H z.2 ∂CompactGibbsContinuity.law
      ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))
      (jointAction n β j u e d q r s t)) =
      ∫ v, H v ∂CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
        (outputAction n β (j + 1) u e d q r s t) := by
  unfold CompactGibbsContinuity.law
  rw [LocalGibbsComparison.weighted_integral _ _
      ((jointAction_continuous n β j u e d q r s t).neg.rexp).measurable
      (fun _ => (Real.exp_pos _).le)
      (CompactGibbsContinuity.partition_positive _ _
        (jointAction_continuous n β j u e d q r s t)),
    LocalGibbsComparison.weighted_integral _ _
      ((outputAction_continuous n β (j + 1) u e d q r s t).neg.rexp).measurable
      (fun _ => (Real.exp_pos _).le)
      (CompactGibbsContinuity.partition_positive _ _
        (outputAction_continuous n β (j + 1) u e d q r s t)),
    joint_unnormalized n β j u e d q r s t H hH, joint_partition]

/-- Only in the conditional middle law does the depth-dependent endpoint
factor cancel. It remains in the retained endpoint distribution. -/
theorem middle_conditional (β : ℝ) (j : ℕ) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) :
    CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
      (fun v => jointAction n β j u e d q r s t (w, v)) =
      CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) := by
  have he : (fun v => jointAction n β j u e d q r s t (w, v)) =
      (fun v => (-Real.log (spatialWeight character β 2 w) -
        Real.log (boundaryMessage n β j w)) +
          WilsonTiltedMiddleAction.action n β u w e d q r s t v) := by
    funext v
    unfold jointAction
    ring
  rw [he, GibbsConstantShift.law_const_add _ _
    (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)]

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryMiddleRecursion
