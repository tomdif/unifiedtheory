/- The exact sourced boundary covariance splits into a middle conditional
covariance and a retained endpoint covariance. Neither term is discarded.
The middle conditional is independent of the propagated boundary depth. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryMiddleRecursion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryMiddleCovariance
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonBoundaryPointwise
open WilsonBoundaryConnected WilsonBoundaryMiddleRecursion
open WilsonSingleLinkStaples (character)

variable (n : ℕ) [NeZero n]

def response (β : ℝ) (u : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) (F : Slice n → ℝ) : Slice n → ℝ :=
  GibbsMarginalTower.response (WilsonSlabOperator.measure n)
    (fun z => WilsonTiltedMiddleAction.action n β u z.1 e d q r s t z.2)
    (fun z => F z.2)

theorem response_continuous (β : ℝ) (u : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) (F : Slice n → ℝ) (hF : Continuous F) :
    Continuous (response n β u e d q r s t F) :=
  GibbsMarginalTower.response_continuous _ _ _
    (WilsonTiltedMiddleAction.action_joint_continuous n β u e d q r s t)
    (hF.comp continuous_snd)

theorem response_integral (β : ℝ) (u w : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) (F : Slice n → ℝ) :
    response n β u e d q r s t F w =
      ∫ v, F v ∂CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) :=
  GibbsMarginalTower.response_eq_expectation _ _ _
    (WilsonTiltedMiddleAction.action_joint_continuous n β u e d q r s t) w

def middleCovariance (β : ℝ) (u w : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) (F G : Slice n → ℝ) : ℝ :=
  GibbsCrossCovariance.covariance
    (CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
      (WilsonTiltedMiddleAction.action n β u w e d q r s t)) F G

def retainedLaw (β : ℝ) (j : ℕ) (u : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) : Measure (Slice n) :=
  GibbsMarginalTower.marginal (WilsonSlabOperator.measure n) (WilsonSlabOperator.measure n)
    (jointAction n β j u e d q r s t)

theorem retainedLaw_probability (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) :
    IsProbabilityMeasure (retainedLaw n β j u e d q r s t) :=
  GibbsMarginalTower.marginal_probability _ _ _
    (jointAction_continuous n β j u e d q r s t)

/-- The retained marginal includes both the old endpoint message and the
new middle partition. It is not replaced by Haar or the old unsourced law. -/
theorem retainedLaw_weight (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) :
    retainedLaw n β j u e d q r s t =
      LocalGibbsComparison.weightedLaw (WilsonSlabOperator.measure n)
        (fun w => spatialWeight character β 2 w * boundaryMessage n β j w *
          ∫ v, Real.exp (-WilsonTiltedMiddleAction.action n β u w e d q r s t v)
            ∂WilsonSlabOperator.measure n) := by
  rw [retainedLaw, GibbsMarginalTower.marginal_eq_weightedLaw _ _ _
    (jointAction_continuous n β j u e d q r s t)]
  congr 1
  funext w
  unfold GibbsMarginalTower.fiberMass
  simp_rw [joint_weight, integral_const_mul]

/-- Exact cancellation of the depth-dependent endpoint in the conditional response. -/
theorem joint_response (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) (F : Slice n → ℝ) :
    GibbsMarginalTower.response (WilsonSlabOperator.measure n)
      (jointAction n β j u e d q r s t) (fun z => F z.2) =
      response n β u e d q r s t F := by
  funext w
  rw [GibbsMarginalTower.response_eq_expectation _ _ _
    (jointAction_continuous n β j u e d q r s t), middle_conditional, response_integral]

theorem joint_conditionalCovariance (β : ℝ) (j : ℕ) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) (F G : Slice n → ℝ) :
    GibbsCrossCovariance.conditionalCovariance (WilsonSlabOperator.measure n)
      (jointAction n β j u e d q r s t) (fun z => F z.2) (fun z => G z.2) w =
      middleCovariance n β u w e d q r s t F G := by
  unfold GibbsCrossCovariance.conditionalCovariance
  rw [joint_response n β j u e d q r s t (fun v => F v * G v)]
  simp only [joint_response, response_integral, middleCovariance, GibbsCrossCovariance.covariance]

theorem joint_covariance (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ)
    (F G : Slice n → ℝ) (hF : Continuous F) (hG : Continuous G) :
    GibbsCrossCovariance.covariance
      (CompactGibbsContinuity.law
        ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))
        (jointAction n β j u e d q r s t)) (fun z => F z.2) (fun z => G z.2) =
      GibbsCrossCovariance.covariance
        (CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
          (outputAction n β (j + 1) u e d q r s t)) F G := by
  unfold GibbsCrossCovariance.covariance
  rw [joint_integral n β j u e d q r s t (fun v => F v * G v) (hF.mul hG),
    joint_integral n β j u e d q r s t F hF, joint_integral n β j u e d q r s t G hG]

/-- Complete covariance recursion for arbitrary continuous middle observables. -/
theorem covariance_recursion (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ)
    (F G : Slice n → ℝ) (hF : Continuous F) (hG : Continuous G) :
    GibbsCrossCovariance.covariance
      (CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
        (outputAction n β (j + 1) u e d q r s t)) F G =
      (∫ w, middleCovariance n β u w e d q r s t F G
        ∂retainedLaw n β j u e d q r s t) +
      GibbsCrossCovariance.covariance (retainedLaw n β j u e d q r s t)
        (response n β u e d q r s t F) (response n β u e d q r s t G) := by
  have h := GibbsCrossCovariance.total_covariance
    (WilsonSlabOperator.measure n) (WilsonSlabOperator.measure n)
    (jointAction n β j u e d q r s t) (fun z => F z.2) (fun z => G z.2)
    (jointAction_continuous n β j u e d q r s t)
    (hF.comp continuous_snd) (hG.comp continuous_snd)
  rw [joint_covariance n β j u e d q r s t F G hF hG] at h
  simpa only [joint_conditionalCovariance, joint_response, retainedLaw] using h

/-- This is exactly the connected covariance in the distant mixed-ground
criterion, with its local insertions and the same two source strengths. -/
theorem connected_recursion (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ) :
    WilsonBoundaryDecayBudget.connected n β (j + 1) e d q r u s t =
      (∫ w, middleCovariance n β u w e d q r s t
        (source n β e q u) (source n β d r u) ∂retainedLaw n β j u e d q r s t) +
      GibbsCrossCovariance.covariance (retainedLaw n β j u e d q r s t)
        (response n β u e d q r s t (source n β e q u))
        (response n β u e d q r s t (source n β d r u)) :=
  covariance_recursion n β j u e d q r s t _ _
    (source_continuous n β e q u) (source_continuous n β d r u)

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryMiddleCovariance
