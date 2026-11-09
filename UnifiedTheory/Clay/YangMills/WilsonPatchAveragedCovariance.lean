/- The local patch estimate is averaged under the full interacting middle
law. Ineligible backgrounds cost an actual local-energy moment. The
retained exterior-response covariance is kept as a separate term. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchCoverage
import UnifiedTheory.Clay.YangMills.GibbsBoundedResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchAveragedCovariance
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonPatchLocalEnergy
open WilsonPatchComplementTail WilsonPatchEligibility WilsonPatchBackgroundReset
open WilsonPatchExteriorDecomposition WilsonPatchCoverage WilsonPatchConditioning
open WilsonBoundaryConnected GibbsCrossCovariance
open scoped Quaternion

section GoodBad
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem good_bad_integral (C : X → ℝ) (hC : Continuous C) (E : Set X)
    (hE : MeasurableSet E) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |C x| ≤ 4) (hgood : ∀ x ∉ E, |C x| ≤ B) :
    (∫ x, |C x| ∂μ) ≤ B + 4 * μ.real E := by
  have hI := hC.abs.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (E.indicator (fun _ : X => (4 : ℝ))) μ :=
    (integrable_const _).indicator hE
  calc
    _ ≤ ∫ x, B + E.indicator (fun _ => (4 : ℝ)) x ∂μ := by
      apply integral_mono hI ((integrable_const _).add hJ)
      intro x
      simp only [Pi.add_apply]
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx]
        linarith only [hbound x, hB]
      · rw [Set.indicator_of_notMem hx, add_zero]
        exact hgood x hx
    _ = _ := by
      rw [integral_add (integrable_const _) hJ, integral_indicator hE, setIntegral_const]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      ring
end GoodBad

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def energyMoment (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n)
    (A : Slice n → ℝ) : ℝ :=
  ∫ v, localEnergy n S v u w ∂CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A

theorem energyMoment_nonneg (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n)
    (A : Slice n → ℝ) : 0 ≤ energyMoment n S u w A :=
  integral_nonneg (fun v => local_nonneg n S v u w)

def retainedCovariance (S : Finset (SpatialVertex n × Fin 3)) (A F G : Slice n → ℝ) : ℝ :=
  covariance (outsideLaw n S A) (outsideResponse n S A F) (outsideResponse n S A G)

/-- A proved eligible-fiber estimate extends to the full law with an
explicit energy-moment cost and the genuine retained covariance. -/
theorem full_bound (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n)
    (A F G : Slice n → ℝ) (B : ℝ) (hA : Continuous A) (hF : Continuous F) (hG : Continuous G)
    (hFb : ∀ v, |F v| ≤ 2) (hGb : ∀ v, |G v| ≤ 2) (hB : 0 ≤ B)
    (hgood : ∀ v₀, backgroundCost n S v₀ u w ≤ threshold →
      |covariance (interiorLaw n S v₀ A) (F ∘ insert n S v₀) (G ∘ insert n S v₀)| ≤ B) :
    |covariance (CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) F G| ≤
      B + (280 / threshold) * energyMoment n S u w A + |retainedCovariance n S A F G| := by
  let C := GibbsCrossCovariance.conditionalCovariance (haar n S) (splitAction n S A)
    (F ∘ WilsonBlockMarginal.assemble S) (G ∘ WilsonBlockMarginal.assemble S)
  have hAs : Continuous (splitAction n S A) :=
    hA.comp (WilsonBlockMarginal.assemble_continuous S)
  have hFs := hF.comp (WilsonBlockMarginal.assemble_continuous S)
  have hGs := hG.comp (WilsonBlockMarginal.assemble_continuous S)
  have hC : Continuous C :=
    (GibbsMarginalTower.response_continuous (haar n S) _ _ hAs (hFs.mul hGs)).sub
      ((GibbsMarginalTower.response_continuous (haar n S) _ _ hAs hFs).mul
        (GibbsMarginalTower.response_continuous (haar n S) _ _ hAs hGs))
  have hCb (b : Outside n S) : |C b| ≤ 4 := by
    have hh := GibbsBoundedResponse.conditional_covariance_abs_le (haar n S) _ _ _
      hAs hFs hGs (-2) 2 (-2) 2 (by norm_num) (by norm_num)
      (fun z => abs_le.mp (hFb _)) (fun z => abs_le.mp (hGb _)) b
    norm_num at hh
    exact hh
  have hCg (b : Outside n S) (hb : b ∉ ineligible n S u w) : |C b| ≤ B := by
    rw [show C b = covariance (interiorLaw n S (background n S u b) A)
      (F ∘ insert n S (background n S u b)) (G ∘ insert n S (background n S u b)) from
        conditional_covariance n S u A F G hA b]
    apply hgood
    exact le_of_not_gt hb
  letI := outside_probability n S A hA
  have hI := good_bad_integral (outsideLaw n S A) C hC (ineligible n S u w)
    (ineligible_measurable n S u w) B hB hCb hCg
  have hP := probability_bound n S u w A hA
  have hbound : (∫ b, |C b| ∂outsideLaw n S A) ≤
      B + (280 / threshold) * energyMoment n S u w A := by
    calc
      _ ≤ B + 4 * (outsideLaw n S A).real (ineligible n S u w) := hI
      _ ≤ B + 4 * ((70 / threshold) * energyMoment n S u w A) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hP (by norm_num))
      _ = _ := by ring
  have he := covariance_decomposition n S u A F G hA hF hG
  simp_rw [← conditional_covariance n S u A F G hA] at he
  change covariance _ F G = (∫ b, C b ∂outsideLaw n S A) + retainedCovariance n S A F G at he
  rw [he]
  exact (abs_add_le _ _).trans
    (add_le_add (abs_integral_le_integral_abs.trans hbound) le_rfl)

/-- The full two-source middle law is now bounded for arbitrary endpoints.
The local energy moment and the exterior-response covariance are actual
remaining quantities, rather than assumed good-background coverage. -/
theorem connected_bound (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) :
    |WilsonBoundaryMiddleCovariance.middleCovariance n β u w e d q r s t
      (source n β e q u) (source n β d r u)| ≤
      budget n β S 1 4 + (280 / threshold) * energyMoment n S u w
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) +
      |retainedCovariance n S (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β e q u) (source n β d r u)| :=
  full_bound n S u w _ _ _ _
    (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
    (source_continuous n β e q u) (source_continuous n β d r u)
    (scaled_source_bound n β (by linarith) e q hq u)
    (scaled_source_bound n β (by linarith) d r hr u)
    (budget_nonneg n β S 1 4 hβ)
    (fun v₀ hg => connected_good n β hβ u w e d hed q r hq hr s t hs ht S v₀ hg)

theorem transport_bound (β : ℝ) (hβ : 2 < β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) :
    |covariance (CompactGibbsContinuity.law (WilsonSlabOperator.measure n)
        (CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
          (source n β b p w) h)) (source n β e q u) (source n β b p w)| ≤
      budget n β S 2 6 + (280 / threshold) * energyMoment n S u w
        (CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
          (source n β b p w) h) +
      |retainedCovariance n S
        (CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
          (source n β b p w) h) (source n β e q u) (source n β b p w)| :=
  full_bound n S u w _ _ _ _
    (CompactGibbsSource.action_continuous _ _
      (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
      (source_continuous n β b p w) h)
    (source_continuous n β e q u) (source_continuous n β b p w)
    (scaled_source_bound n β (by linarith) e q hq u)
    (scaled_source_bound n β (by linarith) b p hp w)
    (budget_nonneg n β S 2 6 hβ)
    (fun v₀ hg => transport_good n β hβ u w e d b hed q r p hq hr hp s t h hs ht hh S v₀ hg)

end
end UnifiedTheory.Clay.YangMills.WilsonPatchAveragedCovariance
