/- Exact full-slice covariance with a capped interior and its complement.
Both the exterior marginal and the covariance of its conditional means
are retained. No exterior configuration is assumed to be a good background. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchCovarianceTransfer
import UnifiedTheory.Clay.YangMills.WilsonBoundaryMiddleCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchExteriorDecomposition
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonChordPatchLaw
open WilsonPatchConditioning GibbsCrossCovariance

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

abbrev Outside (S : Finset (SpatialVertex n × Fin 3)) :=
  WilsonBlockMarginal.Outside (G := Q) S

abbrev outsideHaar (S : Finset (SpatialVertex n × Fin 3)) : Measure (Outside n S) :=
  WilsonBlockMarginal.outsideMeasure S QuaternionHaarDoubling.haar

def background (S : Finset (SpatialVertex n × Fin 3)) (c : Slice n) (b : Outside n S) : Slice n :=
  WilsonBlockMarginal.assemble S (b, fun e => c e.1)

omit [NeZero n] in
theorem insert_background (S : Finset (SpatialVertex n × Fin 3)) (c : Slice n)
    (b : Outside n S) (x : Inside n S) :
    insert n S (background n S c b) x = WilsonBlockMarginal.assemble S (b, x) := by
  funext e
  by_cases he : e ∈ S
  · simp only [WilsonPatchConditioning.insert, WilsonBlockMarginal.assemble_inside S _ e he]
  · simp only [WilsonPatchConditioning.insert,
      WilsonBlockMarginal.assemble_outside S _ e he, background]

def splitAction (S : Finset (SpatialVertex n × Fin 3)) (A : Slice n → ℝ) :
    Outside n S × Inside n S → ℝ := A ∘ WilsonBlockMarginal.assemble S

theorem split_preserving (S : Finset (SpatialVertex n × Fin 3))
    (A : Slice n → ℝ) (hA : Continuous A) :
    MeasurePreserving (WilsonBlockMarginal.assemble S)
      (CompactGibbsContinuity.law ((outsideHaar n S).prod (haar n S)) (splitAction n S A))
      (CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) :=
  WilsonBlockMarginal.weightedLaw_preserving _ _ _
    (WilsonBlockMarginal.assemble_preserving S QuaternionHaarDoubling.haar)
    _ hA.neg.rexp.measurable

theorem split_integral (S : Finset (SpatialVertex n × Fin 3))
    (A : Slice n → ℝ) (hA : Continuous A) (F : Slice n → ℝ) :
    (∫ v, F v ∂CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) =
      ∫ z, F (WilsonBlockMarginal.assemble S z)
        ∂CompactGibbsContinuity.law ((outsideHaar n S).prod (haar n S)) (splitAction n S A) :=
  ((split_preserving n S A hA).integral_comp
    (WilsonBlockMarginal.assemble S).measurableEmbedding F).symm

def outsideLaw (S : Finset (SpatialVertex n × Fin 3)) (A : Slice n → ℝ) :
    Measure (Outside n S) :=
  GibbsMarginalTower.marginal (outsideHaar n S) (haar n S) (splitAction n S A)

theorem outside_probability (S : Finset (SpatialVertex n × Fin 3))
    (A : Slice n → ℝ) (hA : Continuous A) : IsProbabilityMeasure (outsideLaw n S A) :=
  GibbsMarginalTower.marginal_probability _ _ _
    (hA.comp (WilsonBlockMarginal.assemble_continuous S))

theorem outside_density (S : Finset (SpatialVertex n × Fin 3))
    (A : Slice n → ℝ) (hA : Continuous A) :
    outsideLaw n S A = LocalGibbsComparison.weightedLaw (outsideHaar n S)
      (GibbsMarginalTower.fiberMass (haar n S) (splitAction n S A)) :=
  GibbsMarginalTower.marginal_eq_weightedLaw _ _ _
    (hA.comp (WilsonBlockMarginal.assemble_continuous S))

def outsideResponse (S : Finset (SpatialVertex n × Fin 3)) (A F : Slice n → ℝ) :
    Outside n S → ℝ := GibbsMarginalTower.response (haar n S) (splitAction n S A)
      (F ∘ WilsonBlockMarginal.assemble S)

theorem conditional_covariance (S : Finset (SpatialVertex n × Fin 3)) (c : Slice n)
    (A F G : Slice n → ℝ) (hA : Continuous A) (b : Outside n S) :
    GibbsCrossCovariance.conditionalCovariance (haar n S) (splitAction n S A)
      (F ∘ WilsonBlockMarginal.assemble S) (G ∘ WilsonBlockMarginal.assemble S) b =
      covariance (interiorLaw n S (background n S c b) A)
        (F ∘ insert n S (background n S c b)) (G ∘ insert n S (background n S c b)) := by
  have hsplit : Continuous (splitAction n S A) :=
    hA.comp (WilsonBlockMarginal.assemble_continuous S)
  unfold GibbsCrossCovariance.conditionalCovariance covariance
  simp_rw [GibbsMarginalTower.response_eq_expectation _ _ _ hsplit b]
  simp only [interiorLaw, Function.comp_def, insert_background, splitAction]

theorem covariance_decomposition (S : Finset (SpatialVertex n × Fin 3)) (c : Slice n)
    (A F G : Slice n → ℝ) (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) :
    covariance (CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) F G =
      (∫ b, covariance (interiorLaw n S (background n S c b) A)
        (F ∘ insert n S (background n S c b)) (G ∘ insert n S (background n S c b))
        ∂outsideLaw n S A) +
      covariance (outsideLaw n S A) (outsideResponse n S A F) (outsideResponse n S A G) := by
  have he : covariance (CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) F G =
      covariance
        (CompactGibbsContinuity.law ((outsideHaar n S).prod (haar n S)) (splitAction n S A))
        (F ∘ WilsonBlockMarginal.assemble S) (G ∘ WilsonBlockMarginal.assemble S) := by
    unfold covariance
    rw [split_integral n S A hA (fun v => F v * G v),
      split_integral n S A hA F, split_integral n S A hA G]
    rfl
  rw [he, GibbsCrossCovariance.total_covariance (outsideHaar n S) (haar n S)
    (splitAction n S A) (F ∘ WilsonBlockMarginal.assemble S)
    (G ∘ WilsonBlockMarginal.assemble S)
    (hA.comp (WilsonBlockMarginal.assemble_continuous S))
    (hF.comp (WilsonBlockMarginal.assemble_continuous S))
    (hG.comp (WilsonBlockMarginal.assemble_continuous S))]
  simp_rw [conditional_covariance n S c A F G hA]
  rfl

/-- The bad-event covariance and both conditional means use their actual
normalized complement law, with zero-mass cases handled exactly. -/
def eventContribution (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (A F G : Slice n → ℝ) : ℝ :=
  let ν := interiorLaw n S v₀ A
  let E := event n S v₀ ε
  let F₀ := F ∘ insert n S v₀
  let G₀ := G ∘ insert n S v₀
  let good := ProbabilityTheory.cond ν E
  let bad := ProbabilityTheory.cond ν Eᶜ
  ν.real E * covariance (law n S v₀ ε A)
      (F ∘ assemble n S v₀ ε) (G ∘ assemble n S v₀ ε) +
    ν.real Eᶜ * covariance bad F₀ G₀ +
    ν.real E * ν.real Eᶜ * ((∫ x, F₀ x ∂good) - ∫ x, F₀ x ∂bad) *
      ((∫ x, G₀ x ∂good) - ∫ x, G₀ x ∂bad)

theorem eventContribution_eq (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A F G : Slice n → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) :
    eventContribution n S v₀ ε A F G =
      covariance (interiorLaw n S v₀ A) (F ∘ insert n S v₀) (G ∘ insert n S v₀) := by
  letI := interior_probability n S v₀ A hA
  have hFc := hF.comp (insert_continuous n S v₀)
  have hGc := hG.comp (insert_continuous n S v₀)
  have hh := GibbsEventCovariance.covariance_split (interiorLaw n S v₀ A)
    (event n S v₀ ε) (event_measurable n S v₀ ε) (F ∘ insert n S v₀) (G ∘ insert n S v₀)
    (hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hGc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hFc.mul hGc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [conditioned_covariance n S v₀ ε hε A hA F G] at hh
  exact hh.symm

/-- Exact unrestricted covariance, with both the event complement and
retained exterior response. All exterior fields are integrated. -/
theorem full_patch_decomposition (S : Finset (SpatialVertex n × Fin 3)) (c : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A F G : Slice n → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) :
    covariance (CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) F G =
      (∫ b, eventContribution n S (background n S c b) ε A F G ∂outsideLaw n S A) +
      covariance (outsideLaw n S A) (outsideResponse n S A F) (outsideResponse n S A G) := by
  simp_rw [eventContribution_eq n S _ ε hε A F G hA hF hG]
  exact covariance_decomposition n S c A F G hA hF hG


theorem middle_patch_decomposition (β : ℝ) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ)
    (S : Finset (SpatialVertex n × Fin 3)) (c : Slice n) (ε : ℝ) (hε : 0 < ε)
    (F G : Slice n → ℝ) (hF : Continuous F) (hG : Continuous G) :
    WilsonBoundaryMiddleCovariance.middleCovariance n β u w e d q r s t F G =
      (∫ b, eventContribution n S (background n S c b) ε
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) F G
        ∂outsideLaw n S (WilsonTiltedMiddleAction.action n β u w e d q r s t)) +
      covariance (outsideLaw n S (WilsonTiltedMiddleAction.action n β u w e d q r s t))
        (outsideResponse n S (WilsonTiltedMiddleAction.action n β u w e d q r s t) F)
        (outsideResponse n S (WilsonTiltedMiddleAction.action n β u w e d q r s t) G) :=
  full_patch_decomposition n S c ε hε _ F G
    (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t) hF hG

/-- The distant connected quantity has two retained covariance terms:
spatial exterior response inside each middle bridge, and the propagated
endpoint response outside it. Neither is discarded by cap conditioning. -/
theorem connected_patch_decomposition (β : ℝ) (j : ℕ) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (s t : ℝ)
    (S : Finset (SpatialVertex n × Fin 3)) (c : Slice n) (ε : ℝ) (hε : 0 < ε) :
    WilsonBoundaryDecayBudget.connected n β (j + 1) e d q r u s t =
      (∫ w,
        ((∫ b, eventContribution n S (background n S c b) ε
            (WilsonTiltedMiddleAction.action n β u w e d q r s t)
            (WilsonBoundaryConnected.source n β e q u) (WilsonBoundaryConnected.source n β d r u)
            ∂outsideLaw n S (WilsonTiltedMiddleAction.action n β u w e d q r s t)) +
          covariance (outsideLaw n S (WilsonTiltedMiddleAction.action n β u w e d q r s t))
            (outsideResponse n S (WilsonTiltedMiddleAction.action n β u w e d q r s t)
              (WilsonBoundaryConnected.source n β e q u))
            (outsideResponse n S (WilsonTiltedMiddleAction.action n β u w e d q r s t)
              (WilsonBoundaryConnected.source n β d r u)))
        ∂WilsonBoundaryMiddleCovariance.retainedLaw n β j u e d q r s t) +
      covariance (WilsonBoundaryMiddleCovariance.retainedLaw n β j u e d q r s t)
        (WilsonBoundaryMiddleCovariance.response n β u e d q r s t
          (WilsonBoundaryConnected.source n β e q u))
        (WilsonBoundaryMiddleCovariance.response n β u e d q r s t
          (WilsonBoundaryConnected.source n β d r u)) := by
  rw [WilsonBoundaryMiddleCovariance.connected_recursion]
  simp_rw [middle_patch_decomposition n β u _ e d q r s t S c ε hε _ _
    (WilsonBoundaryConnected.source_continuous n β e q u)
    (WilsonBoundaryConnected.source_continuous n β d r u)]

end
end UnifiedTheory.Clay.YangMills.WilsonPatchExteriorDecomposition
