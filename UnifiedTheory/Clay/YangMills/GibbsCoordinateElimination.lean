/- Genuine coordinate elimination on one fixed configuration space.
Removed coordinates are reintroduced only as independent reference variables;
all retained expectations use the actual induced marginal. This makes repeated
elimination definable without changing the type of each physical observable. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsBlockUpdate
import UnifiedTheory.Clay.YangMills.GibbsSuccessiveCovariance
import UnifiedTheory.Clay.YangMills.GibbsBoundedResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsCoordinateElimination
noncomputable section
open MeasureTheory WilsonBlockMarginal CompactGibbsBlockUpdate GibbsMarginalTower
open GibbsCrossCovariance GibbsSuccessiveCovariance

section Boundary
variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

omit [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] in
theorem effective_boundary (A : B → ℝ) :
    effectiveAction μX (fun z : B × X => A z.1) = A := by
  funext b
  simp [effectiveAction, fiberMass, Real.log_exp]

theorem boundary_law_integral (A H : B → ℝ) (hA : Continuous A) (hH : Continuous H) :
    (∫ z : B × X, H z.1 ∂CompactGibbsContinuity.law (μB.prod μX) (fun z => A z.1)) =
      ∫ b, H b ∂CompactGibbsContinuity.law μB A := by
  rw [boundary_integral μB μX (fun z => A z.1) H (hA.comp continuous_fst) hH,
    marginal_eq_effectiveLaw μB μX (fun z : B × X => A z.1)
      (hA.comp continuous_fst), effective_boundary]

end Boundary

variable {I X : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- The actual negative-log fiber partition, lifted back to the fixed configuration space. -/
def blockAction (T : Finset I) (A : C(I → X, ℝ)) : C(I → X, ℝ) :=
  ⟨fun U => effectiveAction (insideMeasure T μ) (A.comp (join T)) ((split T U).1),
    (effectiveAction_continuous (insideMeasure T μ) _ (A.comp (join T)).continuous).comp
      (continuous_fst.comp (split T).continuous)⟩

/-- The genuine conditional response, lifted over the newly irrelevant coordinates. -/
def blockResponse (T : Finset I) (A F : C(I → X, ℝ)) : C(I → X, ℝ) :=
  blockAverage μ A T F

theorem blockAction_assemble (T : Finset I) (A : C(I → X, ℝ))
    (z : Outside (G := X) T × Inside (G := X) T) :
    blockAction μ T A (assemble T z) =
      effectiveAction (insideMeasure T μ) (A.comp (join T)) z.1 := by
  change effectiveAction _ _ (split T (join T z)).1 = _
  rw [split_join]

theorem blockResponse_assemble (T : Finset I) (A F : C(I → X, ℝ))
    (z : Outside (G := X) T × Inside (G := X) T) :
    blockResponse μ T A F (assemble T z) =
      response (insideMeasure T μ) (A.comp (join T)) (F.comp (join T)) z.1 := by
  exact blockAverage_assemble μ A T F z

/-- Every exterior observable is integrated against the true original marginal. -/
theorem blockAction_boundary_integral (T : Finset I) (A : C(I → X, ℝ))
    (H : Outside (G := X) T → ℝ) (hH : Continuous H) :
    (∫ U, H (split T U).1
      ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (blockAction μ T A)) =
      ∫ b, H b ∂marginal (outsideMeasure T μ) (insideMeasure T μ) (A.comp (join T)) := by
  rw [integral_coordinates μ (blockAction μ T A) T]
  have he : (blockAction μ T A).comp (join T) =
      (⟨fun z : Outside (G := X) T × Inside (G := X) T =>
        effectiveAction (insideMeasure T μ) (A.comp (join T)) z.1,
        (effectiveAction_continuous _ _ (A.comp (join T)).continuous).comp continuous_fst⟩ :
          C(Outside (G := X) T × Inside (G := X) T, ℝ)) := by
    ext z
    exact blockAction_assemble μ T A z
  rw [he]
  have hs (z : Outside (G := X) T × Inside (G := X) T) :
      split T (assemble T z) = z := split_join T z
  simp only [hs]
  rw [marginal_eq_effectiveLaw (outsideMeasure T μ) (insideMeasure T μ)
    (A.comp (join T)) (A.comp (join T)).continuous]
  exact boundary_law_integral (outsideMeasure T μ) (insideMeasure T μ)
    (effectiveAction (insideMeasure T μ) (A.comp (join T))) H
    (effectiveAction_continuous (insideMeasure T μ) _ (A.comp (join T)).continuous) hH

/-- The covariance under the lifted effective law is exactly the retained marginal covariance. -/
theorem blockAction_covariance (T : Finset I) (A F G : C(I → X, ℝ)) :
    covariance (CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (blockAction μ T A))
      (blockResponse μ T A F) (blockResponse μ T A G) =
      covariance (marginal (outsideMeasure T μ) (insideMeasure T μ) (A.comp (join T)))
        (response (insideMeasure T μ) (A.comp (join T)) (F.comp (join T)))
        (response (insideMeasure T μ) (A.comp (join T)) (G.comp (join T))) := by
  unfold covariance
  change (∫ U, response (insideMeasure T μ) (A.comp (join T)) (F.comp (join T)) (split T U).1 *
      response (insideMeasure T μ) (A.comp (join T)) (G.comp (join T)) (split T U).1 ∂_) -
    (∫ U, response (insideMeasure T μ) (A.comp (join T)) (F.comp (join T)) (split T U).1 ∂_) *
    (∫ U, response (insideMeasure T μ) (A.comp (join T)) (G.comp (join T)) (split T U).1 ∂_) = _
  have hF := response_continuous (insideMeasure T μ) _ _
    (A.comp (join T)).continuous (F.comp (join T)).continuous
  have hG := response_continuous (insideMeasure T μ) _ _
    (A.comp (join T)).continuous (G.comp (join T)).continuous
  rw [blockAction_boundary_integral μ T A
      (fun b => response (insideMeasure T μ) (A.comp (join T)) (F.comp (join T)) b *
        response (insideMeasure T μ) (A.comp (join T)) (G.comp (join T)) b) (hF.mul hG),
    blockAction_boundary_integral μ T A _ hF, blockAction_boundary_integral μ T A _ hG]

/-- The fluctuation Gram is measured under the actual pre-elimination action. -/
def removedGram (T : Finset I) (A F G : C(I → X, ℝ)) : ℝ :=
  ∫ U, (F U - blockResponse μ T A F U) * (G U - blockResponse μ T A G U)
    ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A

theorem removedGram_eq (T : Finset I) (A F G : C(I → X, ℝ)) :
    removedGram μ T A F G = gram (outsideMeasure T μ) (insideMeasure T μ)
      (A.comp (join T)) (F.comp (join T)) (G.comp (join T)) := by
  unfold removedGram
  rw [integral_coordinates μ A T]
  simp only [blockResponse_assemble]
  rfl

/-- Exact one-step covariance accounting on a fixed configuration space. -/
theorem covariance_decomposition (T : Finset I) (A F G : C(I → X, ℝ)) :
    covariance (CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A) F G =
      removedGram μ T A F G +
      covariance (CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (blockAction μ T A))
        (blockResponse μ T A F) (blockResponse μ T A G) := by
  rw [removedGram_eq, blockAction_covariance]
  have h := GibbsSuccessiveCovariance.covariance_decomposition
    (outsideMeasure T μ) (insideMeasure T μ) (A.comp (join T))
    (F.comp (join T)) (G.comp (join T)) (A.comp (join T)).continuous
    (F.comp (join T)).continuous (G.comp (join T)).continuous
  rw [← h]
  unfold covariance
  rw [integral_coordinates μ A T, integral_coordinates μ A T, integral_coordinates μ A T]
  rfl

theorem response_bounds (T : Finset I) (A F : C(I → X, ℝ)) (lo hi : ℝ)
    (hF : ∀ U, F U ∈ Set.Icc lo hi) (U : I → X) :
    blockResponse μ T A F U ∈ Set.Icc lo hi :=
  GibbsBoundedResponse.response_bounds (insideMeasure T μ) (A.comp (join T))
    (F.comp (join T)) (A.comp (join T)).continuous (F.comp (join T)).continuous
    lo hi (fun z => hF (join T z)) (split T U).1

theorem removedGram_abs_le (T : Finset I) (A F G : C(I → X, ℝ))
    (lo hi lo' hi' : ℝ) (hlo : lo ≤ hi) (hlo' : lo' ≤ hi')
    (hF : ∀ U, F U ∈ Set.Icc lo hi) (hG : ∀ U, G U ∈ Set.Icc lo' hi') :
    |removedGram μ T A F G| ≤ (hi - lo) * (hi' - lo') / 4 := by
  rw [removedGram_eq]
  exact GibbsBoundedResponse.gram_abs_le (outsideMeasure T μ) (insideMeasure T μ)
    (A.comp (join T)) (F.comp (join T)) (G.comp (join T))
    (A.comp (join T)).continuous (F.comp (join T)).continuous (G.comp (join T)).continuous
    lo hi lo' hi' hlo hlo' (fun z => hF (join T z)) (fun z => hG (join T z))

theorem removedGram_self_nonneg (T : Finset I) (A F : C(I → X, ℝ)) :
    0 ≤ removedGram μ T A F F := integral_nonneg (fun _ => mul_self_nonneg _)

end
end UnifiedTheory.Clay.YangMills.GibbsCoordinateElimination
